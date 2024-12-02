use std::net::{Ipv4Addr, Ipv6Addr};
use rocket::{get, routes};
use itertools::Itertools;

#[get("/")]
fn index() -> &'static str {
    "Hello, bird!"
}

#[get("/2/dest?<from>&<key>")]
fn c_2_dest(from: Ipv4Addr, key: Ipv4Addr) -> String {
    let (a, b, c, d) = from.octets()
        .into_iter()
        .zip(key.octets())
        .map(|(f, k)| f.overflowing_add(k).0)
        .next_tuple().unwrap();
    Ipv4Addr::new(a, b, c, d).to_string()
}

#[get("/2/key?<from>&<to>")]
fn c_2_key(from: Ipv4Addr, to: Ipv4Addr) -> String {
    let (a, b, c, d) = from.octets()
        .into_iter()
        .zip(to.octets())
        .map(|(f, t)| t.overflowing_sub(f).0)
        .next_tuple().unwrap();
    Ipv4Addr::new(a, b, c, d).to_string()
}

#[get("/2/v6/dest?<from>&<key>")]
fn c_2_v6_dest(from: Ipv6Addr, key: Ipv6Addr) -> String {
    let (a, b, c, d, e, f, g, h) = from.segments()
        .into_iter()
        .zip(key.segments())
        .map(|(f, k)| f ^ k)
        .next_tuple().unwrap();
    Ipv6Addr::new(a, b, c, d, e, f, g, h).to_string()
}

#[get("/2/v6/key?<from>&<to>")]
fn c_2_v6_key(from: Ipv6Addr, to: Ipv6Addr) -> String {
    let (a, b, c, d, e, f, g, h) = from.segments()
        .into_iter()
        .zip(to.segments())
        .map(|(f, t)| t ^ f)
        .next_tuple().unwrap();
    Ipv6Addr::new(a, b, c, d, e, f, g, h).to_string()
}

#[shuttle_runtime::main]
async fn main() -> shuttle_rocket::ShuttleRocket {
    let rocket = rocket::build().mount("/", routes![
        index,
        c_2_dest,
        c_2_key,
        c_2_v6_dest,
        c_2_v6_key,
    ]);

    Ok(rocket.into())
}
