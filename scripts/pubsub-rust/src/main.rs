//! The rust side of the partial-messages interop check
//! (scripts/pubsub-rust-interop.sh): rust-libp2p's gossipsub at the clone's
//! c449090, with the v1.3 partial-messages extension.
//!
//! Usage: `pubsub-rust request|support ADDR SECS`.
//!
//! 1. The node takes the Ed25519 key of 32 bytes of `R`, and dials ADDR.
//! 2. It enables partial messages on the topic `interop`. It requests
//!    them, or it only supports them.
//! 3. It subscribes to the topic.
//! 4. Every 200 ms, it publishes the full message `from-rust-full-<n>`.
//!    In the same round, it publishes the partial message of group `g<n>`,
//!    with data `from-rust-partial-<n>` and metadata `meta-rust-<n>`. rust
//!    sends the data only to a peer that requested it.
//!
//! The node prints `PARTIAL <peer> data=<data> meta=<metadata>` for each
//! partial message. It prints `GOT <data>` for each full message. The
//! first partial message that shows our choice at work ends the check:
//! data `from-lean-partial` when we request, and metadata `meta-lean` when
//! we only support. The node exits 0 two seconds after that message. It
//! exits 1 at SECS.

use std::time::{Duration, Instant};

use libp2p::gossipsub::partial_messages::{Metadata, Partial, PartialAction, PartialError};
use libp2p::{
    Multiaddr, PeerId, futures::StreamExt, gossipsub, identity, noise, swarm::SwarmEvent, tcp,
    yamux,
};

/// Metadata as plain bytes. An update replaces the bytes.
#[derive(Debug, Clone)]
struct Meta(Vec<u8>);

impl Metadata for Meta {
    fn as_slice(&self) -> &[u8] {
        &self.0
    }
    fn update(&mut self, data: &[u8]) -> Result<bool, PartialError> {
        if self.0 == data {
            return Ok(false);
        }
        self.0 = data.to_vec();
        Ok(true)
    }
}

/// One partial message: a group with one part.
struct Part {
    group: Vec<u8>,
    data: Vec<u8>,
    meta: Meta,
}

impl Partial for Part {
    fn group_id(&self) -> Vec<u8> {
        self.group.clone()
    }
    fn metadata(&self) -> Box<dyn Metadata> {
        Box::new(self.meta.clone())
    }
    // Send the part to each requester, whatever the requester holds.
    // Give each inbound part to the application.
    fn partial_action_from_metadata(
        &self,
        _peer: PeerId,
        _metadata: Option<&[u8]>,
    ) -> Result<PartialAction, PartialError> {
        Ok(PartialAction {
            need: true,
            send: Some((self.data.clone(), Box::new(self.meta.clone()))),
        })
    }
}

fn die(msg: String) -> ! {
    eprintln!("rust: {msg}");
    std::process::exit(1)
}

#[tokio::main]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() != 4 {
        die("usage: pubsub-rust request|support ADDR SECS".into());
    }
    let requests = match args[1].as_str() {
        "request" => true,
        "support" => false,
        other => die(format!("mode {other}")),
    };
    let target: Multiaddr = args[2]
        .parse()
        .unwrap_or_else(|e| die(format!("address: {e}")));
    let secs: u64 = args[3]
        .parse()
        .unwrap_or_else(|e| die(format!("seconds: {e}")));

    let key = identity::Keypair::ed25519_from_bytes([b'R'; 32])
        .unwrap_or_else(|e| die(format!("key: {e}")));
    // The consensus policy: no author, no signature, and the message id
    // from the data.
    let config = gossipsub::ConfigBuilder::default()
        .validation_mode(gossipsub::ValidationMode::Anonymous)
        .message_id_fn(|m: &gossipsub::Message| gossipsub::MessageId::from(m.data.clone()))
        .build()
        .unwrap_or_else(|e| die(format!("config: {e}")));
    let mut behaviour: gossipsub::Behaviour =
        gossipsub::Behaviour::new(gossipsub::MessageAuthenticity::Anonymous, config)
            .unwrap_or_else(|e| die(format!("gossipsub: {e}")));
    let topic = gossipsub::IdentTopic::new("interop");
    // Partial messages must be enabled before the subscription.
    behaviour.enable_partials_for_topic(topic.hash(), requests);
    behaviour
        .subscribe(&topic)
        .unwrap_or_else(|e| die(format!("subscribe: {e}")));

    let mut swarm = libp2p::SwarmBuilder::with_existing_identity(key)
        .with_tokio()
        .with_tcp(
            tcp::Config::default(),
            noise::Config::new,
            yamux::Config::default,
        )
        .unwrap_or_else(|e| die(format!("transport: {e}")))
        .with_behaviour(|_| behaviour)
        .unwrap_or_else(|e| die(format!("behaviour: {e}")))
        .with_swarm_config(|c| c.with_idle_connection_timeout(Duration::from_secs(60)))
        .build();
    swarm
        .dial(target)
        .unwrap_or_else(|e| die(format!("dial: {e}")));

    let deadline = tokio::time::sleep(Duration::from_secs(secs));
    tokio::pin!(deadline);
    let mut tick = tokio::time::interval(Duration::from_millis(200));
    let mut count = 0u64;
    let mut done_at: Option<Instant> = None;
    loop {
        tokio::select! {
            _ = &mut deadline => {
                println!("TIMEOUT");
                std::process::exit(1);
            }
            _ = tick.tick() => {
                if done_at.is_some_and(|t| Instant::now() >= t) {
                    std::process::exit(0);
                }
                count += 1;
                let gs = swarm.behaviour_mut();
                // Both fail until a peer subscribes. The next round tries again.
                let _ = gs.publish(topic.clone(), format!("from-rust-full-{count}"));
                let _ = gs.publish_partial(topic.clone(), Part {
                    group: format!("g{count}").into_bytes(),
                    data: format!("from-rust-partial-{count}").into_bytes(),
                    meta: Meta(format!("meta-rust-{count}").into_bytes()),
                });
            }
            event = swarm.select_next_some() => match event {
                SwarmEvent::ConnectionEstablished { peer_id, .. } => println!("CONNECTED {peer_id}"),
                SwarmEvent::Behaviour(gossipsub::Event::Message { message, .. }) => {
                    println!("GOT {}", String::from_utf8_lossy(&message.data));
                }
                SwarmEvent::Behaviour(gossipsub::Event::Partial { peer_id, message, metadata, .. }) => {
                    let data = String::from_utf8_lossy(message.as_deref().unwrap_or_default()).into_owned();
                    let meta = String::from_utf8_lossy(metadata.as_deref().unwrap_or_default()).into_owned();
                    println!("PARTIAL {peer_id} data={data} meta={meta}");
                    let honoured = if requests {
                        data.starts_with("from-lean-partial")
                    } else {
                        meta.starts_with("meta-lean")
                    };
                    if honoured && done_at.is_none() {
                        println!("DONE partial");
                        // Let the other side see our last messages.
                        done_at = Some(Instant::now() + Duration::from_secs(2));
                    }
                }
                _ => {}
            },
        }
    }
}
