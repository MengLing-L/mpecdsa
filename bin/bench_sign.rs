use std::env;
use std::net::{TcpListener, TcpStream};
use std::thread::sleep;
/// This program handles benchmarking for both signing and setup
use std::time::{Duration, Instant};

extern crate rand;
use rand::{thread_rng, Rng};

extern crate curves;
use curves::f_4141::FSecp256Ord;
use curves::{Ford, SecpOrd, Secp, ECGroup};

extern crate mpecdsa;

extern crate getopts;
use self::getopts::{Matches, Options};

pub fn process_options() -> Option<Matches> {
    let args: Vec<String> = env::args().collect();

    println!("args: {:?}", args);

    let mut opts = Options::new();
    opts.optopt("o", "", "set output file name", "NAME");
    opts.optopt("p", "port", "set port", "PORT");
    opts.optopt("n", "iterations", "number of iterations", "ITERS");
    opts.optopt("c", "client", "set ip address of server", "IP");

    opts.optflag("h", "help", "print this help menu");
    opts.optflag("b", "bob", "run as bob");
    opts.optflag("", "bench_setup", "benchmark setup");

    let matches = match opts.parse(&args[1..]) {
        Ok(m) => m,
        Err(f) => {
            panic!()
        }
    };

    if matches.opt_present("h") {
        let program = args[0].clone();
        let brief = format!("Usage: {} [options]", program);
        print!("{}", opts.usage(&brief));
        return Option::None;
    }

    return Option::Some(matches);
}

fn main() {
    const FR_BITS: usize = SecpOrd::NBITS;
    const fr_bytes: usize = (FR_BITS + 7) / 8;
	const secp_bytes: usize = Secp::NBYTES;

    let msg = "this is a test".as_bytes();

    let matches = process_options();
    if let None = matches {
        ::std::process::exit(1);
    }
    let matches = matches.unwrap();

    let (mut streamrecv, mut streamsend) = if matches.opt_present("c") {
        let port = format!(
            "{}:{}",
            matches.opt_str("c").unwrap(),
            matches.opt_str("p").unwrap_or("12345".to_owned())
        );

        println!("Connecting to server {:?}...", port);
        let mut stream1 = TcpStream::connect(&port);
        let connection_wait_time = 2 * 60;
        let poll_interval = 100;
        for _ in 0..(connection_wait_time * 1000 / poll_interval) {
            if stream1.is_err() {
                sleep(Duration::from_millis(poll_interval));
                stream1 = TcpStream::connect(&port);
            }
        }
        let stream1 = stream1.unwrap();
        let stream2 = stream1.try_clone().unwrap();
        (stream1, stream2)
    } else {
        let port = format!(
            "0.0.0.0:{}",
            matches.opt_str("p").unwrap_or("12345".to_owned())
        );
        println!("Waiting for client to connect on {}", port);
        let listener = TcpListener::bind(port).unwrap_or_else(|e| panic!());
        let (stream1, _) = listener.accept().unwrap_or_else(|e| panic!());
        let stream2 = stream1.try_clone().unwrap();
        (stream2, stream1)
    };

    streamsend.set_nodelay(true).expect("Could not set nodelay");
    streamrecv.set_nodelay(true).expect("Could not set nodelay");
    let iters = matches
        .opt_str("n")
        .unwrap_or("1000".to_owned())
        .parse::<i32>()
        .unwrap();
    let mut rng = thread_rng();

    println!("Connected. Performing {} Iteration Benchmark...", iters);
    if matches.opt_present("b") {
        let skb = FSecp256Ord::from_slice(&[
            0xb75db4463a602ff0,
            0x83b6a76e7fad1ec,
            0xa33f33b8e9c84dbd,
            0xb94fceb9fff7cfb2,
        ]);

        if matches.opt_present("bench_setup") {
            let signstart = Instant::now();
            for _ in 0..iters {
                mpecdsa::mpecdsa::Bob2P::<FR_BITS, fr_bytes, secp_bytes>::new(
                    &skb,
                    &mut rng,
                    &mut streamrecv,
                    &mut streamsend,
                )
                .unwrap();
            }
            println!(
                "{:.3} ms avg",
                (signstart.elapsed().as_millis() as f64) / (iters as f64)
            );
        } else {
            let bob = mpecdsa::mpecdsa::Bob2P::<FR_BITS, fr_bytes, secp_bytes>::new(
                &skb,
                &mut rng,
                &mut streamrecv,
                &mut streamsend,
            )
            .unwrap();
            let signstart = Instant::now();
            for _ in 0..iters {
                bob.sign(&msg, &mut rng, &mut streamrecv, &mut streamsend)
                    .unwrap();
            }
            println!(
                "{:.3} ms avg",
                (signstart.elapsed().as_millis() as f64) / (iters as f64)
            );
        }
    } else {
        let ska = FSecp256Ord::from_slice(&[
            0xc93d9fa738a8b4b6,
            0xe8dd5f4af65e7462,
            0xcbdf97aeca50c5c4,
            0x67498f7dcab40d3,
        ]);
        if matches.opt_present("bench_setup") {
            let signstart = Instant::now();
            for _ in 0..iters {
                mpecdsa::mpecdsa::Alice2P::<FR_BITS, fr_bytes, secp_bytes>::new(
                    &ska,
                    &mut rng,
                    &mut streamrecv,
                    &mut streamsend,
                )
                .unwrap();
            }
            println!(
                "{:.3} ms avg",
                (signstart.elapsed().as_millis() as f64) / (iters as f64)
            );
        } else {
            let alice = mpecdsa::mpecdsa::Alice2P::<FR_BITS, fr_bytes, secp_bytes>::new(
                &ska,
                &mut rng,
                &mut streamrecv,
                &mut streamsend,
            )
            .unwrap();
            let signstart = Instant::now();
            for _ in 0..iters {
                alice
                    .sign(&msg, &mut rng, &mut streamrecv, &mut streamsend)
                    .unwrap();
            }
            println!(
                "{:.3} ms avg",
                (signstart.elapsed().as_millis() as f64) / (iters as f64)
            );
        }
    }
}
