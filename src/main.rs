//#![feature(never_type)]

use cargo_manifest::Manifest;
use itertools::{Either, Itertools};
use rocket::http::Status;
use rocket::request::FromRequest;
use rocket::response::status::{BadRequest, NoContent};
use rocket::response::Redirect;
use rocket::serde::json::Json;
use rocket::serde::{Deserialize, Serialize};
use rocket::{get, post, routes, Request, Responder};
use std::net::{Ipv4Addr, Ipv6Addr};
use std::sync::{LazyLock, Mutex};
use std::time::Instant;
use toml::Table;

#[get("/")]
fn index() -> &'static str {
    "Hello, bird!"
}

#[get("/-1/seek")]
fn c_m1_seek() -> Redirect {
    Redirect::found("https://www.youtube.com/watch?v=9Gc4QTqslN4")
}

#[get("/2/dest?<from>&<key>")]
fn c_2_dest(from: Ipv4Addr, key: Ipv4Addr) -> String {
    let (a, b, c, d) = from
        .octets()
        .into_iter()
        .zip(key.octets())
        .map(|(f, k)| f.overflowing_add(k).0)
        .next_tuple()
        .unwrap();
    Ipv4Addr::new(a, b, c, d).to_string()
}

#[get("/2/key?<from>&<to>")]
fn c_2_key(from: Ipv4Addr, to: Ipv4Addr) -> String {
    let (a, b, c, d) = from
        .octets()
        .into_iter()
        .zip(to.octets())
        .map(|(f, t)| t.overflowing_sub(f).0)
        .next_tuple()
        .unwrap();
    Ipv4Addr::new(a, b, c, d).to_string()
}

#[get("/2/v6/dest?<from>&<key>")]
fn c_2_v6_dest(from: Ipv6Addr, key: Ipv6Addr) -> String {
    let (a, b, c, d, e, f, g, h) = from
        .segments()
        .into_iter()
        .zip(key.segments())
        .map(|(f, k)| f ^ k)
        .next_tuple()
        .unwrap();
    Ipv6Addr::new(a, b, c, d, e, f, g, h).to_string()
}

#[get("/2/v6/key?<from>&<to>")]
fn c_2_v6_key(from: Ipv6Addr, to: Ipv6Addr) -> String {
    let (a, b, c, d, e, f, g, h) = from
        .segments()
        .into_iter()
        .zip(to.segments())
        .map(|(f, t)| t ^ f)
        .next_tuple()
        .unwrap();
    Ipv6Addr::new(a, b, c, d, e, f, g, h).to_string()
}

struct ContentType(Option<String>);

#[derive(Debug)]
enum ContentTypeError {}

#[rocket::async_trait]
impl<'r> FromRequest<'r> for ContentType {
    type Error = ContentTypeError;

    async fn from_request(request: &'r Request<'_>) -> rocket::request::Outcome<Self, Self::Error> {
        // dbg!(request.headers().iter().find(|x| x.name() == "Content-Type"));
        rocket::request::Outcome::Success(ContentType(
            request
                .headers()
                .iter()
                .find(|x| x.name() == "Content-Type")
                .map(|x| x.value().to_owned()),
        ))
    }
}

#[post("/5/manifest", data = "<input>")]
fn c_5_manifest(
    content_type: ContentType,
    mut input: String,
) -> Result<String, Either<NoContent, Either<BadRequest<&'static str>, Status>>> {
    match content_type.0 {
        None => {}
        Some(s) if s == "application/toml" => {}
        Some(s) if s == "application/json" => {
            let v: toml::Value = serde_json::from_str(&input).unwrap();
            input = toml::to_string(&v).unwrap()
        }
        Some(s) if s == "application/yaml" => {
            let v: toml::Value = serde_yaml::from_str(&input).unwrap();
            input = toml::to_string(&v).unwrap()
        }
        Some(_) => return Err(Either::Right(Either::Right(Status::UnsupportedMediaType))),
    }

    let _manifest = Manifest::from_slice(input.as_bytes())
        .map_err(|_err| Either::Right(Either::Left(BadRequest("Invalid manifest"))))?;
    if !input.contains("\"Christmas 2024\"") {
        return Err(Either::Right(Either::Left(BadRequest(
            "Magic keyword not provided",
        ))));
    }

    let table = input.parse::<Table>().unwrap();
    let package = table
        .get("package")
        .ok_or(Either::Left(NoContent))?
        .as_table()
        .ok_or(Either::Left(NoContent))?;
    let metadata = package
        .get("metadata")
        .ok_or(Either::Left(NoContent))?
        .as_table()
        .ok_or(Either::Left(NoContent))?;
    let orders = metadata
        .get("orders")
        .ok_or(Either::Left(NoContent))?
        .as_array()
        .ok_or(Either::Left(NoContent))?;
    let res = orders
        .into_iter()
        .filter_map(|order| {
            if let Some(order) = order.as_table() {
                if let (Some(item), Some(quantity)) = (
                    order.get("item")?.as_str(),
                    order.get("quantity")?.as_integer(),
                ) {
                    Some(format!("{item}: {quantity}"))
                } else {
                    None
                }
            } else {
                None
            }
        })
        .join("\n");
    if res.is_empty() {
        Err(Either::Left(NoContent))
    } else {
        Ok(res)
    }
}

static MILK_BUCKET: LazyLock<Mutex<u64>> = LazyLock::new(|| Mutex::new(5));
static LAST_FILL_TIME: LazyLock<Mutex<Instant>> = LazyLock::new(|| Mutex::new(Instant::now()));

#[derive(Responder)]
enum MilkResponse {
    #[response(status = 200)]
    WithDrawn(&'static str),
    #[response(status = 429)]
    NotAvailable(&'static str),
    #[response(status = 200)]
    Conversion(Json<Converter>),
}

#[derive(Responder)]
enum MilkError {
    #[response(status = 400)]
    BadRequest(()),
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
enum Converter {
    Liters(f32),
    Gallons(f32),
    Litres(f32),
    Pints(f32),
}

impl Converter {
    fn convert(self) -> Self {
        match self {
            Self::Liters(n) => Self::Gallons(n * 0.264172),
            Self::Gallons(n) => Self::Liters(n / 0.264172),
            Self::Litres(n) => Self::Pints(n * 1.75975),
            Self::Pints(n) => Self::Litres(n / 1.75975),
        }
    }
}

#[post("/9/milk", data = "<input>")]
fn c_9_milk(content_type: ContentType, input: String) -> Result<MilkResponse, MilkError> {
    if LAST_FILL_TIME.lock().unwrap().elapsed().as_secs() >= 1 {
        println!("Filling time");
        let mut current = MILK_BUCKET.lock().unwrap();
        if *current < 5 {
            *current += LAST_FILL_TIME.lock().unwrap().elapsed().as_secs().min(5);
        }
        *LAST_FILL_TIME.lock().unwrap() = Instant::now();
    }

    match content_type.0 {
        Some(s) if s == "application/json" => {
            if *MILK_BUCKET.lock().unwrap() >= 1 {
                *MILK_BUCKET.lock().unwrap() -= 1;
                println!("{} left!", *MILK_BUCKET.lock().unwrap());
                let converter: Converter =
                    serde_json::from_str(&input).map_err(|_| MilkError::BadRequest(()))?;
                let converter = converter.convert();
                Ok(MilkResponse::Conversion(Json(converter)))
            } else {
                Ok(MilkResponse::NotAvailable("No milk available\n"))
            }
        }
        None | Some(_) => {
            if *MILK_BUCKET.lock().unwrap() >= 1 {
                *MILK_BUCKET.lock().unwrap() -= 1;
                println!("{} left!", *MILK_BUCKET.lock().unwrap());
                Ok(MilkResponse::WithDrawn("Milk withdrawn\n"))
            } else {
                Ok(MilkResponse::NotAvailable("No milk available\n"))
            }
        }
    }
}

#[post("/9/refill")]
fn c_9_refill() {
    *MILK_BUCKET.lock().unwrap() = 5;
}

#[shuttle_runtime::main]
async fn main() -> shuttle_rocket::ShuttleRocket {
    let rocket = rocket::build().mount(
        "/",
        routes![
            index,
            c_m1_seek,
            c_2_dest,
            c_2_key,
            c_2_v6_dest,
            c_2_v6_key,
            c_5_manifest,
            c_9_milk,
            c_9_refill,
        ],
    );

    Ok(rocket.into())
}
