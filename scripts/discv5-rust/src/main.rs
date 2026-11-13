//! discv5 interop helper over the sigp discv5 crate, the version
//! Lighthouse runs (0.12.0).
//!
//! `query <port> <enr>`: start a node on 127.0.0.1:<port>, then PING the
//! target, FINDNODE it at distance 0, and TALKREQ its `echo` protocol.
//! Prints one line per answer and exits 0 when all three came back right.
//!
//! `serve <port> <seconds>`: start a node on 127.0.0.1:<port>, print
//! `ENR <text>`, answer TALKREQ `echo` with the request (any other
//! protocol empty), and serve for <seconds>.

use enr::{CombinedKey, Enr};
use discv5::{ConfigBuilder, Discv5, Event, ListenConfig};
use std::net::Ipv4Addr;
use std::time::Duration;

fn usage() -> ! {
    eprintln!("usage: discv5-rust query <port> <enr> | serve <port> <seconds>");
    std::process::exit(2)
}

async fn node(port: u16) -> Discv5 {
    let key = CombinedKey::generate_secp256k1();
    let mut builder = Enr::builder();
    builder.ip4(Ipv4Addr::LOCALHOST);
    builder.udp4(port);
    let enr = builder.build(&key).expect("enr");
    let config = ConfigBuilder::new(ListenConfig::Ipv4 { ip: Ipv4Addr::LOCALHOST, port }).build();
    let mut d = Discv5::new(enr, key, config).expect("discv5");
    d.start().await.expect("start");
    d
}

#[tokio::main]
async fn main() {
    let args: Vec<String> = std::env::args().collect();
    if args.len() < 4 {
        usage()
    }
    let port: u16 = args[2].parse().unwrap_or_else(|_| usage());
    match args[1].as_str() {
        "query" => {
            let target: Enr<CombinedKey> = args[3].parse().expect("target enr");
            let d = node(port).await;
            d.add_enr(target.clone()).expect("add_enr");
            let mut ok = true;
            match d.send_ping(target.clone()).await {
                Ok(p) => println!("PONG seq {} ip {} port {}", p.enr_seq, p.ip, p.port),
                Err(e) => {
                    println!("PING failed: {e:?}");
                    ok = false
                }
            }
            match d.find_node_designated_peer(target.clone(), vec![0]).await {
                Ok(rs) => {
                    let me = rs.iter().any(|r| r.node_id() == target.node_id());
                    println!("NODES {} self {}", rs.len(), me);
                    ok &= me
                }
                Err(e) => {
                    println!("FINDNODE failed: {e:?}");
                    ok = false
                }
            }
            let contact = discv5::NodeContact::try_from_enr(target.clone(), d.ip_mode()).expect("contact");
            match d.talk_req(contact, b"echo".to_vec(), vec![1, 2, 3]).await {
                Ok(resp) => {
                    println!("TALKRESP {resp:?}");
                    ok &= resp == vec![1, 2, 3]
                }
                Err(e) => {
                    println!("TALKREQ failed: {e:?}");
                    ok = false
                }
            }
            std::process::exit(if ok { 0 } else { 1 })
        }
        "serve" => {
            let secs: u64 = args[3].parse().unwrap_or_else(|_| usage());
            let d = node(port).await;
            println!("ENR {}", d.local_enr().to_base64());
            let mut events = d.event_stream().await.expect("events");
            let until = tokio::time::sleep(Duration::from_secs(secs));
            tokio::pin!(until);
            loop {
                tokio::select! {
                    _ = &mut until => break,
                    ev = events.recv() => match ev {
                        Some(Event::TalkRequest(req)) => {
                            let resp = if req.protocol() == b"echo" { req.body().to_vec() } else { vec![] };
                            let _ = req.respond(resp);
                        }
                        Some(_) => {}
                        None => break,
                    }
                }
            }
        }
        _ => usage(),
    }
}
