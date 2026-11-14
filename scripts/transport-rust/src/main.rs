//! The transport-interop test-plan peer over sigp's rust-libp2p, the
//! fork that Lighthouse runs (accba72).
//!
//! The environment is the test plan's
//! (`vendor/test-plans/transport-interop/README.md`):
//! - `transport`: `tcp` or `quic-v1`
//! - `security`: `noise` or `tls`, for `tcp`
//! - `muxer`: `yamux` or `mplex`, for `tcp`
//! - `is_dialer`: `true` or `false`
//! - `redis_addr`: the `host:port` of the Redis server
//! - `test_timeout_seconds`: the bound of the run
//! - `ip`: the listener's address, `127.0.0.1` when unset
//!
//! The listener publishes its address with the `/p2p/<id>` suffix through
//! `RPUSH listenerAddr`, then serves pings until the runner kills it. A
//! listener that reaches the timeout exits 1. The dialer takes the
//! address through `BLPOP listenerAddr`, dials it, and prints the timing
//! record when the first ping returns. The key is secp256k1, as
//! Lighthouse's is.
//!
//! The Redis client speaks the two commands and the RESP2 replies that
//! the test plan needs, so the helper builds offline from the local
//! registry.

use std::time::{Duration, Instant};

use libp2p::futures::StreamExt;
use libp2p::swarm::{Swarm, SwarmEvent};
use libp2p::{Multiaddr, SwarmBuilder, identity, noise, ping, tcp, tls, yamux};
use tokio::io::{AsyncBufReadExt, AsyncReadExt, AsyncWriteExt, BufReader};
use tokio::net::TcpStream;

type Res<T> = Result<T, Box<dyn std::error::Error + Send + Sync>>;

fn env(name: &str) -> Res<String> {
    std::env::var(name).map_err(|_| format!("{name} is not set").into())
}

/// One RESP2 command, as an array of bulk strings, and its reply line.
/// A bulk or array reply returns its header line, and the caller reads
/// the rest.
async fn command(r: &mut BufReader<TcpStream>, args: &[&str]) -> Res<String> {
    let mut out = format!("*{}\r\n", args.len());
    for a in args {
        out.push_str(&format!("${}\r\n{}\r\n", a.len(), a));
    }
    r.get_mut().write_all(out.as_bytes()).await?;
    let mut line = String::new();
    r.read_line(&mut line).await?;
    Ok(line.trim_end().to_string())
}

/// One bulk string after its `$<len>` header.
async fn bulk(r: &mut BufReader<TcpStream>) -> Res<String> {
    let mut header = String::new();
    r.read_line(&mut header).await?;
    let len: usize = header
        .trim_end()
        .strip_prefix('$')
        .ok_or("a bulk reply with no $")?
        .parse()?;
    let mut buf = vec![0u8; len + 2];
    r.read_exact(&mut buf).await?;
    buf.truncate(len);
    Ok(String::from_utf8(buf)?)
}

async fn rpush(r: &mut BufReader<TcpStream>, key: &str, value: &str) -> Res<()> {
    let reply = command(r, &["RPUSH", key, value]).await?;
    if !reply.starts_with(':') {
        return Err(format!("RPUSH answered {reply}").into());
    }
    Ok(())
}

async fn blpop(r: &mut BufReader<TcpStream>, key: &str, timeout: u64) -> Res<String> {
    let reply = command(r, &["BLPOP", key, &timeout.to_string()]).await?;
    if reply != "*2" {
        return Err(format!("BLPOP answered {reply}").into());
    }
    let _key = bulk(r).await?;
    bulk(r).await
}

fn swarm(
    transport: &str,
    security: &str,
    muxer: &str,
) -> Res<(Swarm<ping::Behaviour>, &'static str)> {
    let key = identity::Keypair::generate_secp256k1();
    let behaviour = |_: &identity::Keypair| ping::Behaviour::new(ping::Config::new());
    let idle = |c: libp2p::swarm::Config| c.with_idle_connection_timeout(Duration::from_secs(300));
    let b = SwarmBuilder::with_existing_identity(key).with_tokio();
    let s = match (transport, security, muxer) {
        ("quic-v1", _, _) => {
            let s = b
                .with_quic()
                .with_behaviour(behaviour)?
                .with_swarm_config(idle)
                .build();
            return Ok((s, "udp/0/quic-v1"));
        }
        ("tcp", "noise", "yamux") => b
            .with_tcp(
                tcp::Config::default(),
                noise::Config::new,
                yamux::Config::default,
            )?
            .with_behaviour(behaviour)?
            .with_swarm_config(idle)
            .build(),
        ("tcp", "noise", "mplex") => b
            .with_tcp(
                tcp::Config::default(),
                noise::Config::new,
                libp2p_mplex::Config::default,
            )?
            .with_behaviour(behaviour)?
            .with_swarm_config(idle)
            .build(),
        ("tcp", "tls", "yamux") => b
            .with_tcp(
                tcp::Config::default(),
                tls::Config::new,
                yamux::Config::default,
            )?
            .with_behaviour(behaviour)?
            .with_swarm_config(idle)
            .build(),
        ("tcp", "tls", "mplex") => b
            .with_tcp(
                tcp::Config::default(),
                tls::Config::new,
                libp2p_mplex::Config::default,
            )?
            .with_behaviour(behaviour)?
            .with_swarm_config(idle)
            .build(),
        other => return Err(format!("unsupported stack {other:?}").into()),
    };
    Ok((s, "tcp/0"))
}

async fn listen(
    mut s: Swarm<ping::Behaviour>,
    port: &str,
    mut redis: BufReader<TcpStream>,
    timeout: u64,
) -> Res<()> {
    let ip = std::env::var("ip").unwrap_or_else(|_| "127.0.0.1".to_string());
    s.listen_on(format!("/ip4/{ip}/{port}").parse()?)?;
    let me = *s.local_peer_id();
    let until = tokio::time::sleep(Duration::from_secs(timeout));
    tokio::pin!(until);
    loop {
        tokio::select! {
            _ = &mut until => return Err("the listener reached the test timeout".into()),
            ev = s.select_next_some() => match ev {
                SwarmEvent::NewListenAddr { address, .. } => {
                    rpush(&mut redis, "listenerAddr", &format!("{address}/p2p/{me}")).await?;
                }
                SwarmEvent::ConnectionEstablished { peer_id, endpoint, .. } => {
                    eprintln!("connected {peer_id} {endpoint:?}");
                }
                _ => {}
            },
        }
    }
}

async fn dial(
    mut s: Swarm<ping::Behaviour>,
    mut redis: BufReader<TcpStream>,
    timeout: u64,
) -> Res<()> {
    let addr: Multiaddr = blpop(&mut redis, "listenerAddr", timeout).await?.parse()?;
    let start = Instant::now();
    s.dial(addr)?;
    let until = tokio::time::sleep(Duration::from_secs(timeout));
    tokio::pin!(until);
    loop {
        tokio::select! {
            _ = &mut until => return Err("the dialer reached the test timeout".into()),
            ev = s.select_next_some() => match ev {
                SwarmEvent::Behaviour(ping::Event { result: Ok(rtt), .. }) => {
                    let total = start.elapsed();
                    println!(
                        "{{\"handshakePlusOneRTTMillis\":{:.3},\"pingRTTMilllis\":{:.3}}}",
                        total.as_secs_f64() * 1000.0,
                        rtt.as_secs_f64() * 1000.0
                    );
                    return Ok(());
                }
                SwarmEvent::Behaviour(ping::Event { result: Err(e), .. }) => {
                    return Err(format!("ping failed: {e}").into());
                }
                SwarmEvent::OutgoingConnectionError { error, .. } => {
                    return Err(format!("dial failed: {error}").into());
                }
                _ => {}
            },
        }
    }
}

#[tokio::main]
async fn main() {
    if let Err(e) = run().await {
        eprintln!("transport-rust: {e}");
        std::process::exit(1);
    }
}

async fn run() -> Res<()> {
    let transport = env("transport")?;
    let security = std::env::var("security").unwrap_or_default();
    let muxer = std::env::var("muxer").unwrap_or_default();
    let dialer = env("is_dialer")? == "true";
    let timeout: u64 = std::env::var("test_timeout_seconds")
        .unwrap_or_else(|_| "180".to_string())
        .parse()?;
    let redis = BufReader::new(TcpStream::connect(env("redis_addr")?).await?);
    let (s, port) = swarm(&transport, &security, &muxer)?;
    if dialer {
        dial(s, redis, timeout).await
    } else {
        listen(s, port, redis, timeout).await
    }
}
