// The go side of the pubsub interop checks (scripts/pubsub-interop.sh):
// go-libp2p-pubsub v0.19.0 and go-libp2p v0.51.0, both built from the
// local clones that go.mod replaces them with.
//
// Modes:
//
//	record SEED SEQ ADDR...  print the hex of the signed peer record that
//	                         go-libp2p seals for the Ed25519 key of 32
//	                         bytes of SEED, with SEQ and the addresses.
//	verify HEX               consume a signed peer record as gossipsub's
//	                         peer exchange does, and print its peer, seq,
//	                         and addresses.
//	node FLAGS               run one pubsub host, with the flags below.
//
// A node prints `ADDR <multiaddr>/p2p/<id>` once it listens, `GOT <data>`
// for each message from a peer, `TOPIC-PEERS <n>` when its topic peer
// count changes, and `CONNECTED <id>` for each new connection. It exits
// 0 when a message with the -expect prefix arrives or a -watch peer
// connects, and 1 at -timeout. The message id is the data, as in the
// consensus layer, so each -publish message carries a count.
//
// With -partial request or -partial support, the node runs the v1.3
// partial-messages extension on its topic. It prints `PARTIAL <from>
// data=<data> meta=<metadata>` for each partial message from a peer.
// With -publish-partial, it offers one partial message of group `g`
// every 200 ms. It exits 0 when a partial message arrives with data
// that starts with the -expect-partial prefix. It also exits 0 when the
// metadata starts with the -expect-meta prefix.
package main

import (
	"context"
	"crypto/ed25519"
	"encoding/hex"
	"flag"
	"fmt"
	"iter"
	"log/slog"
	"os"
	"strconv"
	"strings"
	"time"

	"github.com/libp2p/go-libp2p"
	pubsub "github.com/libp2p/go-libp2p-pubsub"
	"github.com/libp2p/go-libp2p-pubsub/partialmessages"
	pb "github.com/libp2p/go-libp2p-pubsub/pb"
	"github.com/libp2p/go-libp2p/core/crypto"
	"github.com/libp2p/go-libp2p/core/network"
	"github.com/libp2p/go-libp2p/core/peer"
	"github.com/libp2p/go-libp2p/core/record"
	ma "github.com/multiformats/go-multiaddr"
)

func die(format string, args ...any) {
	fmt.Fprintf(os.Stderr, "go: "+format+"\n", args...)
	os.Exit(1)
}

// keyOf is the Ed25519 key of 32 bytes of one character, the seed form
// the Lean side uses too.
func keyOf(seed string) crypto.PrivKey {
	if len(seed) != 1 {
		die("a seed is one character, got %q", seed)
	}
	s := []byte(strings.Repeat(seed, 32))
	k, err := crypto.UnmarshalEd25519PrivateKey(ed25519.NewKeyFromSeed(s))
	if err != nil {
		die("key: %v", err)
	}
	return k
}

func recordMode(args []string) {
	if len(args) < 2 {
		die("record SEED SEQ ADDR...")
	}
	key := keyOf(args[0])
	seq, err := strconv.ParseUint(args[1], 10, 64)
	if err != nil {
		die("seq: %v", err)
	}
	id, err := peer.IDFromPrivateKey(key)
	if err != nil {
		die("peer id: %v", err)
	}
	rec := &peer.PeerRecord{PeerID: id, Seq: seq}
	for _, a := range args[2:] {
		m, err := ma.NewMultiaddr(a)
		if err != nil {
			die("address %s: %v", a, err)
		}
		rec.Addrs = append(rec.Addrs, m)
	}
	env, err := record.Seal(rec, key)
	if err != nil {
		die("seal: %v", err)
	}
	b, err := env.Marshal()
	if err != nil {
		die("marshal: %v", err)
	}
	fmt.Println(hex.EncodeToString(b))
}

func verifyMode(args []string) {
	if len(args) != 1 {
		die("verify HEX")
	}
	b, err := hex.DecodeString(args[0])
	if err != nil {
		die("hex: %v", err)
	}
	_, r, err := record.ConsumeEnvelope(b, peer.PeerRecordEnvelopeDomain)
	if err != nil {
		die("consume: %v", err)
	}
	rec, ok := r.(*peer.PeerRecord)
	if !ok {
		die("the payload is not a peer record")
	}
	addrs := make([]string, 0, len(rec.Addrs))
	for _, a := range rec.Addrs {
		addrs = append(addrs, a.String())
	}
	fmt.Printf("OK %s %d %s\n", rec.PeerID, rec.Seq, strings.Join(addrs, ","))
}

type list []string

func (l *list) String() string     { return strings.Join(*l, ",") }
func (l *list) Set(v string) error { *l = append(*l, v); return nil }

func nodeMode(args []string) {
	fs := flag.NewFlagSet("node", flag.ExitOnError)
	seed := fs.String("seed", "G", "identity seed character")
	port := fs.Int("port", 0, "TCP port on 127.0.0.1")
	topic := fs.String("topic", "interop", "topic")
	router := fs.String("router", "gossipsub", "gossipsub or floodsub")
	px := fs.Bool("px", false, "send peer exchange on prune")
	d := fs.Int("d", 6, "D")
	dlo := fs.Int("dlo", 5, "D_lo")
	dhi := fs.Int("dhi", 12, "D_hi")
	publish := fs.String("publish", "", "publish this text and a count every 200 ms")
	expect := fs.String("expect", "", "exit 0 once a message with this prefix arrives")
	timeout := fs.Int("timeout", 30, "seconds before exit 1")
	partial := fs.String("partial", "", "request or support partial messages on the topic")
	publishPartial := fs.String("publish-partial", "", "offer a partial message with this text and a count every 200 ms")
	expectPartial := fs.String("expect-partial", "", "exit 0 once partial data with this prefix arrives")
	expectMeta := fs.String("expect-meta", "", "exit 0 once partial metadata with this prefix arrives")
	var connect, watch list
	fs.Var(&connect, "connect", "dial this multiaddr (repeatable)")
	fs.Var(&watch, "watch", "exit 0 once this peer id connects (repeatable)")
	if err := fs.Parse(args); err != nil {
		die("flags: %v", err)
	}

	ctx, cancel := context.WithTimeout(context.Background(), time.Duration(*timeout)*time.Second)
	defer cancel()
	h, err := libp2p.New(
		libp2p.Identity(keyOf(*seed)),
		libp2p.ListenAddrStrings(fmt.Sprintf("/ip4/127.0.0.1/tcp/%d", *port)),
	)
	if err != nil {
		die("host: %v", err)
	}
	defer h.Close()

	done := make(chan string, 4)
	watched := map[peer.ID]bool{}
	for _, w := range watch {
		id, err := peer.Decode(w)
		if err != nil {
			die("watch %s: %v", w, err)
		}
		watched[id] = true
	}
	h.Network().Notify(&network.NotifyBundle{
		ConnectedF: func(_ network.Network, c network.Conn) {
			fmt.Printf("CONNECTED %s\n", c.RemotePeer())
			if watched[c.RemotePeer()] {
				done <- "watch"
			}
		},
	})

	// The consensus policy, which the Lean router validates with: no
	// author, no signature, and the message id from the data.
	common := []pubsub.Option{
		pubsub.WithMessageSignaturePolicy(pubsub.StrictNoSign),
		pubsub.WithNoAuthor(),
		pubsub.WithMessageIdFn(func(m *pb.Message) string { return string(m.Data) }),
	}
	// The partial-messages extension. It prints each partial message. It
	// keeps no application state per peer, because each offer carries
	// the whole text.
	var topicOpts []pubsub.TopicOpt
	switch *partial {
	case "":
	case "request":
		topicOpts = append(topicOpts, pubsub.RequestPartialMessages())
	case "support":
		topicOpts = append(topicOpts, pubsub.SupportsPartialMessages())
	default:
		die("partial %s", *partial)
	}
	if *partial != "" {
		ext := &partialmessages.PartialMessagesExtension[struct{}]{
			Logger: slog.New(slog.NewTextHandler(os.Stderr, &slog.HandlerOptions{Level: slog.LevelWarn})),
			OnIncomingRPC: func(from peer.ID, _ map[peer.ID]struct{}, rpc *pb.PartialMessagesExtension) error {
				data, meta := string(rpc.GetPartialMessage()), string(rpc.GetPartsMetadata())
				fmt.Printf("PARTIAL %s data=%s meta=%s\n", from, data, meta)
				if (*expectPartial != "" && strings.HasPrefix(data, *expectPartial)) ||
					(*expectMeta != "" && strings.HasPrefix(meta, *expectMeta)) {
					// The router's loop calls this, so it must not block.
					select {
					case done <- "partial":
					default:
					}
				}
				return nil
			},
			OnEmitGossip: func(string, []byte, []peer.ID, map[peer.ID]struct{}) {},
		}
		common = append(common, pubsub.WithPartialMessagesExtension(ext))
	}

	var ps *pubsub.PubSub
	switch *router {
	case "floodsub":
		if *partial != "" {
			die("partial messages need gossipsub")
		}
		ps, err = pubsub.NewFloodSub(ctx, h, common...)
	case "gossipsub":
		params := pubsub.DefaultGossipSubParams()
		params.D, params.Dlo, params.Dhi = *d, *dlo, *dhi
		if params.Dscore > params.D {
			params.Dscore = params.D
		}
		if params.Dout >= params.Dlo || params.Dout > params.D/2 {
			params.Dout = 0
		}
		ps, err = pubsub.NewGossipSub(ctx, h, append(common, pubsub.WithPeerExchange(*px),
			pubsub.WithGossipSubParams(params))...)
	default:
		die("router %s", *router)
	}
	if err != nil {
		die("pubsub: %v", err)
	}
	t, err := ps.Join(*topic, topicOpts...)
	if err != nil {
		die("join: %v", err)
	}
	sub, err := t.Subscribe()
	if err != nil {
		die("subscribe: %v", err)
	}

	for _, a := range h.Addrs() {
		fmt.Printf("ADDR %s/p2p/%s\n", a, h.ID())
	}
	for _, c := range connect {
		info, err := peer.AddrInfoFromString(c)
		if err != nil {
			die("connect %s: %v", c, err)
		}
		if err := h.Connect(ctx, *info); err != nil {
			die("connect %s: %v", c, err)
		}
	}

	go func() {
		for {
			m, err := sub.Next(ctx)
			if err != nil {
				return
			}
			if m.ReceivedFrom == h.ID() {
				// Our own publish, delivered locally.
				continue
			}
			fmt.Printf("GOT %s\n", m.Data)
			if *expect != "" && strings.HasPrefix(string(m.Data), *expect) {
				done <- "expect"
			}
		}
	}()
	if *publish != "" {
		go func() {
			tick := time.NewTicker(200 * time.Millisecond)
			defer tick.Stop()
			last := -1
			// The message id is the data, so each publish carries a
			// count. The routers would drop a repeat as a duplicate.
			count := 0
			for {
				select {
				case <-ctx.Done():
					return
				case <-tick.C:
					// The topic peers go sends to: a change shows when
					// our subscription reached go.
					if n := len(t.ListPeers()); n != last {
						fmt.Printf("TOPIC-PEERS %d\n", n)
						last = n
					}
					count++
					if err := t.Publish(ctx, []byte(fmt.Sprintf("%s-%d", *publish, count))); err != nil {
						fmt.Fprintf(os.Stderr, "go: publish: %v\n", err)
					}
				}
			}
		}()
	}

	if *publishPartial != "" {
		go func() {
			tick := time.NewTicker(200 * time.Millisecond)
			defer tick.Stop()
			meta := []byte("meta-" + *publishPartial)
			count := 0
			for {
				select {
				case <-ctx.Done():
					return
				case <-tick.C:
					count++
					data := []byte(fmt.Sprintf("%s-%d", *publishPartial, count))
					// The data goes only to a peer that requested partial
					// messages. The metadata goes to each peer.
					actions := func(states map[peer.ID]struct{}, requests func(peer.ID) bool) iter.Seq2[peer.ID, partialmessages.PublishAction] {
						return func(yield func(peer.ID, partialmessages.PublishAction) bool) {
							for p := range states {
								a := partialmessages.PublishAction{EncodedPartsMetadata: meta}
								if requests(p) {
									a.EncodedPartialMessage = data
								}
								if !yield(p, a) {
									return
								}
							}
						}
					}
					if err := pubsub.PublishPartial(ps, *topic, []byte("g"), actions); err != nil {
						fmt.Fprintf(os.Stderr, "go: publish partial: %v\n", err)
					}
				}
			}
		}()
	}

	if *expect == "" && *expectPartial == "" && *expectMeta == "" && len(watched) == 0 {
		// A helper node: serve until the timeout.
		<-ctx.Done()
		return
	}
	select {
	case why := <-done:
		fmt.Printf("DONE %s\n", why)
		// Let the other side see our last messages.
		time.Sleep(2 * time.Second)
	case <-ctx.Done():
		fmt.Println("TIMEOUT")
		os.Exit(1)
	}
}

func main() {
	if len(os.Args) < 2 {
		die("mode: record, verify, or node")
	}
	switch os.Args[1] {
	case "record":
		recordMode(os.Args[2:])
	case "verify":
		verifyMode(os.Args[2:])
	case "node":
		nodeMode(os.Args[2:])
	default:
		die("unknown mode %s", os.Args[1])
	}
}
