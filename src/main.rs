//#![feature(never_type)]

use std::cmp::PartialEq;
use std::fmt::Display;
use std::iter::repeat_with;
use cargo_manifest::Manifest;
use itertools::{Either, Itertools};
use rocket::http::Status;
use rocket::request::{FromParam, FromRequest};
use rocket::response::status::{BadRequest, NoContent};
use rocket::response::Redirect;
use rocket::serde::json::Json;
use rocket::serde::{Deserialize, Serialize};
use rocket::{get, post, routes, Request, Responder};
use std::net::{Ipv4Addr, Ipv6Addr};
use std::str::FromStr;
use std::sync::{LazyLock, Mutex};
use std::time::Instant;
use grid::Grid;
use rand::{Rng, SeedableRng};
use rand::prelude::StdRng;
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
        .iter()
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


const BOARD_SIZE: usize = 4;

struct Board {
    grid: Grid<State>,
}

impl Display for Board {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        for row in self.grid.iter_rows() {
            writeln!(f, "⬜{}⬜", row.map(|x| x.to_string()).collect::<String>())?;
        }
        writeln!(f, "{}", "⬜".repeat(self.grid.cols() + 2))?;
        write!(f, "{}", self.winner())?;
        Ok(())
    }
}

impl Board {
    fn new() -> Self {
        Self { grid: Grid::new(BOARD_SIZE, BOARD_SIZE) }
    }

    fn winner(&self) -> Winner {
        // Vertical
        for column in self.grid.iter_cols() {
            let column: Vec<_> = column.collect();
            if column.iter().all_equal() {
                if let State::Filled(team) = column.first().unwrap() {
                    return Winner::Yes(*team);
                }
            }
        }
        // Horizontal
        for row in self.grid.iter_rows() {
            let row: Vec<_> = row.collect();
            if row.iter().all_equal() {
                if let State::Filled(team) = row.first().unwrap() {
                    return Winner::Yes(*team);
                }
            }
        }
        // Diagonal
        assert_eq!(self.grid.cols(), self.grid.rows(), "Grid is not square");
        fn do_diagonal<F>(grid: &Grid<State>, coord_fn: F) -> Option<Winner>
            where F: Fn(usize) -> (usize, usize)
        {
            let mut first = None;
            let mut good = true;
            for i in 0..grid.cols() {
                let coord = coord_fn(i);
                let curr = &grid[coord];
                if first.is_none() {
                    if let State::Filled(team) = curr {
                        first = Some(team);
                    } else {
                        good = false;
                        break;
                    }
                }
                let first = first.unwrap();
                if State::Filled(*first) != *curr {
                    good = false;
                    break;
                }
            }
            if good {
                Some(Winner::Yes(*first.unwrap()))
            } else {
                None
            }
        }
        //   Top left - bottom right
        if let Some(winner) = do_diagonal(&self.grid, |i| (i, i)) {
            return winner;
        }
        //   Top right - bottom left
        if let Some(winner) = do_diagonal(&self.grid, |i| (i, self.grid.cols() - 1 - i)) {
            return winner;
        }

        if self.grid.iter().all(|x| matches!(x, State::Filled(_))) {
            Winner::No
        } else {
            Winner::InProgress
        }
    }

    fn place(&mut self, team: Team, column: Column) -> Result<(), ServiceUnavailable> {
        let column = column.0;
        let first_space = self.grid.iter_col(column).rposition(|x| matches!(x, State::Empty));
        match first_space {
            None => Err(ServiceUnavailable(self.to_string())),
            Some(first_space) => {
                self.grid[(first_space, column)] = State::Filled(team);
                Ok(())
            }
        }
    }

    fn new_random(rand: &mut StdRng) -> Self {
        Board { grid: Grid::from_vec(
            repeat_with(|| rand.gen::<bool>())
                .take(BOARD_SIZE * BOARD_SIZE)
                .map(|x| match x {
                    true => State::Filled(Team::Cookie),
                    false => State::Filled(Team::Milk),
                })
                .collect(),
            BOARD_SIZE,
        ) }
    }
}

#[derive(Debug)]
enum Winner {
    InProgress,
    No,
    Yes(Team),
}

impl Display for Winner {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::InProgress => (),
            Self::No => writeln!(f, "No winner.")?,
            Self::Yes(team) => writeln!(f, "{} wins!", team)?,
        }
        Ok(())
    }
}

impl Winner {
    fn is_finished(&self) -> bool {
        match self {
            Winner::InProgress => false,
            Winner::No => true,
            Winner::Yes(_) => true,
        }
    }
}

#[derive(Debug, PartialEq)]
enum State {
    Empty,
    Filled(Team),
}

impl Default for State {
    fn default() -> Self {
        Self::Empty
    }
}

impl Display for State {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Empty => write!(f, "⬛"),
            Self::Filled(team) => team.fmt(f),
        }
    }
}

#[derive(Debug, PartialEq, Clone, Copy)]
enum Team {
    Cookie,
    Milk,
}

impl Display for Team {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Cookie => write!(f, "🍪"),
            Self::Milk => write!(f, "🥛"),
        }
    }
}

impl FromStr for Team {
    type Err = BadRequest<()>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        match s {
            "cookie" => Ok(Self::Cookie),
            "milk" => Ok(Self::Milk),
            _ => Err(BadRequest(())),
        }
    }
}

impl FromParam<'_> for Team {
    type Error = <Team as FromStr>::Err;

    fn from_param(param: &str) -> Result<Self, Self::Error> {
        param.parse()
    }
}

struct Column(usize);

impl FromStr for Column {
    type Err = BadRequest<()>;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let n = s.parse().map_err(|_| BadRequest(()))?;
        match n {
            1..=BOARD_SIZE => Ok(Self(n - 1)), // It's 1-indexed
            _ => Err(BadRequest(())),
        }
    }
}

impl FromParam<'_> for Column {
    type Error = <Column as FromStr>::Err;

    fn from_param(param: &str) -> Result<Self, Self::Error> {
        param.parse()
    }
}

static BOARD: LazyLock<Mutex<Board>> = LazyLock::new(|| Mutex::new(Board::new()));

fn new_rng() -> StdRng {
    StdRng::seed_from_u64(2024)
}

static RNG: LazyLock<Mutex<StdRng>> = LazyLock::new(|| Mutex::new(new_rng()));

#[get("/12/board")]
fn c_12_board() -> String {
    BOARD.lock().unwrap().to_string()
}

#[post("/12/reset")]
fn c_12_reset() -> String {
    *BOARD.lock().unwrap() = Board::new();
    *RNG.lock().unwrap() = new_rng();
    BOARD.lock().unwrap().to_string()
}

#[derive(Responder)]
#[response(status = 503)]
struct ServiceUnavailable(String);

#[post("/12/place/<team>/<column>")]
fn c_12_place(team: Result<Team, BadRequest<()>>, column: Result<Column, BadRequest<()>>) -> Result<String, Either<ServiceUnavailable, BadRequest<()>>> {
    if BOARD.lock().unwrap().winner().is_finished() {
        return Err(Either::Left(ServiceUnavailable(BOARD.lock().unwrap().to_string())));
    }

    match (team, column) {
        (Ok(team), Ok(column)) => {
            BOARD.lock().unwrap().place(team, column).map_err(Either::Left)?;
            Ok(BOARD.lock().unwrap().to_string())
        }
        (Err(error), _) => Err(Either::Right(error)),
        (_, Err(error)) => Err(Either::Right(error)),
    }
}

#[get("/12/random-board")]
fn c_12_random_board() -> String {
    let board = Board::new_random(&mut RNG.lock().unwrap());
    board.to_string()
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
            c_12_board,
            c_12_reset,
            c_12_place,
            c_12_random_board,
        ],
    );

    Ok(rocket.into())
}
