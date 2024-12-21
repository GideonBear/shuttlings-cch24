//#![feature(never_type)]

use cargo_manifest::Manifest;
use grid::Grid;
use itertools::{Either, Itertools};
use rand::prelude::StdRng;
use rand::{Rng, SeedableRng};
use rocket::http::Status;
use rocket::request::{FromParam, FromRequest};
use rocket::response::status::{BadRequest, Created, NoContent, NotFound};
use rocket::response::Redirect;
use rocket::serde::json::Json;
use rocket::serde::{Deserialize, Serialize};
use rocket::{delete, get, post, put, routes, Request, Responder};
use shuttle_runtime::CustomError;
use sqlx::Executor;
use std::cmp::PartialEq;
use std::fmt::Display;
use std::iter::repeat_with;
use std::net::{Ipv4Addr, Ipv6Addr};
use std::str::FromStr;
use std::sync::{LazyLock, Mutex};
use std::time::Instant;
use toml::Table;

const SECRET_KEY: &'static str = "4aac49450b24879475bc77b9deb6eddd";

mod day_minus_1 {
    use super::*;

    #[get("/")]
    pub fn index() -> &'static str {
        "Hello, bird!"
    }

    #[get("/-1/seek")]
    pub fn seek() -> Redirect {
        Redirect::found("https://www.youtube.com/watch?v=9Gc4QTqslN4")
    }
}

mod day_2 {
    use super::*;

    #[get("/2/dest?<from>&<key>")]
    pub fn dest(from: Ipv4Addr, key: Ipv4Addr) -> String {
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
    pub fn key(from: Ipv4Addr, to: Ipv4Addr) -> String {
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
    pub fn v6_dest(from: Ipv6Addr, key: Ipv6Addr) -> String {
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
    pub fn v6_key(from: Ipv6Addr, to: Ipv6Addr) -> String {
        let (a, b, c, d, e, f, g, h) = from
            .segments()
            .into_iter()
            .zip(to.segments())
            .map(|(f, t)| t ^ f)
            .next_tuple()
            .unwrap();
        Ipv6Addr::new(a, b, c, d, e, f, g, h).to_string()
    }
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

mod day_5 {
    use super::*;

    #[post("/5/manifest", data = "<input>")]
    pub fn manifest(
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
}

mod day_9 {
    use super::*;

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
    pub fn milk(content_type: ContentType, input: String) -> Result<MilkResponse, MilkError> {
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
    pub fn refill() {
        *MILK_BUCKET.lock().unwrap() = 5;
    }
}

mod day_12 {
    use super::*;

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
            Self {
                grid: Grid::new(BOARD_SIZE, BOARD_SIZE),
            }
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
            where
                F: Fn(usize) -> (usize, usize),
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
            let first_space = self
                .grid
                .iter_col(column)
                .rposition(|x| matches!(x, State::Empty));
            match first_space {
                None => Err(ServiceUnavailable(self.to_string())),
                Some(first_space) => {
                    self.grid[(first_space, column)] = State::Filled(team);
                    Ok(())
                }
            }
        }

        fn new_random(rand: &mut StdRng) -> Self {
            Board {
                grid: Grid::from_vec(
                    repeat_with(|| rand.gen::<bool>())
                        .take(BOARD_SIZE * BOARD_SIZE)
                        .map(|x| match x {
                            true => State::Filled(Team::Cookie),
                            false => State::Filled(Team::Milk),
                        })
                        .collect(),
                    BOARD_SIZE,
                ),
            }
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
    pub fn board() -> String {
        BOARD.lock().unwrap().to_string()
    }

    #[post("/12/reset")]
    pub fn reset() -> String {
        *BOARD.lock().unwrap() = Board::new();
        *RNG.lock().unwrap() = new_rng();
        BOARD.lock().unwrap().to_string()
    }

    #[derive(Responder)]
    #[response(status = 503)]
    struct ServiceUnavailable(String);

    #[post("/12/place/<team>/<column>")]
    pub fn place(
        team: Result<Team, BadRequest<()>>,
        column: Result<Column, BadRequest<()>>,
    ) -> Result<String, Either<ServiceUnavailable, BadRequest<()>>> {
        if BOARD.lock().unwrap().winner().is_finished() {
            return Err(Either::Left(ServiceUnavailable(
                BOARD.lock().unwrap().to_string(),
            )));
        }

        match (team, column) {
            (Ok(team), Ok(column)) => {
                BOARD
                    .lock()
                    .unwrap()
                    .place(team, column)
                    .map_err(Either::Left)?;
                Ok(BOARD.lock().unwrap().to_string())
            }
            (Err(error), _) => Err(Either::Right(error)),
            (_, Err(error)) => Err(Either::Right(error)),
        }
    }

    #[get("/12/random-board")]
    pub fn random_board() -> String {
        let board = Board::new_random(&mut RNG.lock().unwrap());
        board.to_string()
    }
}

mod day_16 {
    use super::*;
    use jsonwebtoken::{
        decode, encode, get_current_timestamp, Algorithm, DecodingKey, EncodingKey, Header,
        Validation,
    };
    use rocket::request::Outcome;
    use rocket::response::Responder;
    use rocket::Response;

    #[derive(Debug, Serialize, Deserialize)]
    struct Claims {
        gift: String,
        exp: u64,
    }

    #[rocket::async_trait]
    impl<'r> FromRequest<'r> for Claims {
        type Error = ();

        async fn from_request(request: &'r Request<'_>) -> Outcome<Self, Self::Error> {
            let token = match request.cookies().get("gift") {
                None => return Outcome::Error((Status::BadRequest, ())),
                Some(x) => x.value(),
            };
            Outcome::Success(
                decode::<Claims>(
                    &token,
                    &DecodingKey::from_secret(SECRET_KEY.as_ref()),
                    &Validation::default(),
                )
                .unwrap()
                .claims,
            )
        }
    }

    struct WrapResponse(String);

    impl<'r> Responder<'r, 'static> for WrapResponse {
        fn respond_to(self, req: &'r Request<'_>) -> rocket::response::Result<'static> {
            Response::build_from(().respond_to(req)?)
                .raw_header("Set-Cookie", format!("gift={}", self.0))
                .ok()
        }
    }

    #[post("/16/wrap", data = "<input>")]
    pub fn wrap(input: String) -> WrapResponse {
        let claims = Claims {
            gift: input,
            exp: get_current_timestamp(),
        };
        let token = encode(
            &Header::default(),
            &claims,
            &EncodingKey::from_secret(SECRET_KEY.as_ref()),
        )
        .unwrap();
        WrapResponse(token)
    }

    #[get("/16/unwrap")]
    pub fn unwrap(claims: Claims) -> String {
        claims.gift
    }

    #[derive(Responder)]
    enum DecodeResponse {
        #[response(status = 200)]
        Claims(String),
        #[response(status = 400)]
        Invalid(()),
        #[response(status = 401)]
        SignatureInvalid(()),
    }

    const PUBLIC_KEY: &'static [u8] = include_bytes!("../day16_santa_public_key.pem");

    #[post("/16/decode", data = "<input>")]
    pub fn decode_(input: String) -> DecodeResponse {
        let decoding_key = DecodingKey::from_rsa_pem(PUBLIC_KEY).unwrap();
        let mut validation = Validation::default();
        validation.algorithms = vec![Algorithm::RS256, Algorithm::RS512];
        validation.validate_exp = false;
        validation.set_required_spec_claims::<&'static str>(&[]);
        match decode::<serde_json::Value>(&input, &decoding_key, &validation) {
            Err(err) => {
                println!("{err:?}");
                if let jsonwebtoken::errors::ErrorKind::InvalidSignature = err.into_kind() {
                    DecodeResponse::SignatureInvalid(())
                } else {
                    DecodeResponse::Invalid(())
                }
            }
            Ok(x) => DecodeResponse::Claims(serde_json::to_string(&x.claims).unwrap()),
        }
    }
}

mod day_19 {
    use super::*;
    use rocket::State;
    use sqlx::types::chrono::{DateTime, Utc};
    use sqlx::types::Uuid;
    use sqlx::FromRow;
    use std::collections::HashMap;

    #[derive(Deserialize)]
    struct QuotePart {
        author: String,
        quote: String,
    }

    #[derive(Serialize, FromRow, Clone)]
    struct Quote {
        id: Uuid,
        author: String,
        quote: String,
        created_at: DateTime<Utc>,
        version: i32,
    }

    impl From<QuotePart> for Quote {
        fn from(part: QuotePart) -> Self {
            Self {
                id: Uuid::new_v4(),
                author: part.author,
                quote: part.quote,
                created_at: Utc::now(),
                version: 1,
            }
        }
    }

    async fn get_quote(
        id: &Uuid,
        state: &State<MyState>,
    ) -> Result<Quote, Either<NotFound<String>, BadRequest<String>>> {
        Ok(sqlx::query_as("SELECT * FROM quotes WHERE id = $1")
            .bind(id)
            .fetch_one(&state.pool)
            .await
            .map_err(|e| Either::Left(NotFound(e.to_string())))?)
    }

    fn process_uuid(
        uuid: Result<Uuid, rocket::serde::uuid::Error>,
    ) -> Result<Uuid, Either<NotFound<String>, BadRequest<String>>> {
        match uuid {
            Ok(uuid) => Ok(uuid),
            Err(_) => Err(Either::Right(BadRequest("Bad UUID".to_string()))),
        }
    }

    #[post("/19/reset")]
    pub async fn reset(state: &State<MyState>) {
        // Clear the quotes table in the database.
        sqlx::query("DELETE FROM quotes")
            .execute(&state.pool)
            .await
            .unwrap();
    }

    #[get("/19/cite/<id>")]
    pub async fn cite(
        id: Result<Uuid, rocket::serde::uuid::Error>,
        state: &State<MyState>,
    ) -> Result<Json<Quote>, Either<NotFound<String>, BadRequest<String>>> {
        let id = process_uuid(id)?;
        // Respond with the quote of the given ID.
        // Use 404 Not Found if a quote with the ID does not exist.
        let quote = get_quote(&id, state).await?;

        Ok(Json(quote))
    }

    #[delete("/19/remove/<id>")]
    pub async fn remove(
        id: Result<Uuid, rocket::serde::uuid::Error>,
        state: &State<MyState>,
    ) -> Result<Json<Quote>, Either<NotFound<String>, BadRequest<String>>> {
        let id = process_uuid(id)?;
        // Delete and respond with the quote of the given ID.
        // Use 404 Not Found if a quote with the ID does not exist.
        let quote = get_quote(&id, state).await?;

        sqlx::query("DELETE FROM quotes WHERE id = $1")
            .bind(id)
            .execute(&state.pool)
            .await
            .map_err(|e| Either::Left(NotFound(e.to_string())))?;

        Ok(Json(quote))
    }

    #[put("/19/undo/<id>", data = "<input>")]
    pub async fn undo(
        id: Result<Uuid, rocket::serde::uuid::Error>,
        input: Json<QuotePart>,
        state: &State<MyState>,
    ) -> Result<Json<Quote>, Either<NotFound<String>, BadRequest<String>>> {
        let id = process_uuid(id)?;
        // Update the author and text, and increment the version number of the quote of the given ID.
        // Respond with the updated quote.
        // Use 404 Not Found if a quote with the ID does not exist.
        let mut quote = get_quote(&id, state).await?;
        quote.author = input.author.clone();
        quote.quote = input.quote.clone();
        quote.version += 1;

        sqlx::query("UPDATE quotes SET author = $1, quote = $2, version = $3 WHERE id = $4")
            .bind(&input.author)
            .bind(&input.quote)
            .bind(&quote.version)
            .bind(id)
            .execute(&state.pool)
            .await
            .map_err(|e| Either::Left(NotFound(e.to_string())))?;

        Ok(Json(quote))
    }

    #[post("/19/draft", data = "<input>")]
    pub async fn draft(input: Json<QuotePart>, state: &State<MyState>) -> Created<Json<Quote>> {
        // Add a quote with a random UUID v4.
        // Respond with the quote and 201 Created.
        let quote = Quote::from(input.0);
        sqlx::query("INSERT INTO quotes (id, author, quote, created_at, version) values ($1, $2, $3, $4, $5)")
            .bind(&quote.id)
            .bind(&quote.author)
            .bind(&quote.quote)
            .bind(&quote.created_at)
            .bind(&quote.version)
            .execute(&state.pool)
            .await
            .unwrap();
        Created::new("ha").body(Json(quote))
    }

    #[derive(Serialize)]
    struct ListResponse {
        quotes: Vec<Quote>,
        page: i32,
        next_token: Option<String>,
    }

    static TOKENS: LazyLock<Mutex<HashMap<String, i32>>> =
        LazyLock::new(|| Mutex::new(HashMap::new()));
    const CHARSET: &str = "abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789";

    #[get("/19/list?<token>")]
    pub async fn list(
        state: &State<MyState>,
        token: Option<String>,
    ) -> Result<Json<ListResponse>, BadRequest<()>> {
        let next_token = random_string::generate(16, CHARSET);
        let page = match token {
            Some(token) => *TOKENS.lock().unwrap().get(&token).ok_or(BadRequest(()))?,
            None => 1,
        };
        TOKENS.lock().unwrap().insert(next_token.clone(), page + 1);

        let quotes: Vec<Quote> =
            sqlx::query_as("SELECT * FROM quotes ORDER BY created_at ASC LIMIT 4 OFFSET $1")
                .bind((page - 1) * 3)
                .fetch_all(&state.pool)
                .await
                .unwrap();
        let (quotes, last_page) = match quotes.len() {
            0..4 => (quotes, true),
            4 => (quotes[0..3].to_vec(), false),
            _ => unreachable!(),
        };
        println!("{}, {last_page}", quotes.len());

        let next_token = match last_page {
            true => None,
            false => Some(next_token),
        };

        Ok(Json(ListResponse {
            quotes,
            page,
            next_token,
        }))
    }
}

struct MyState {
    pool: sqlx::PgPool,
}

#[shuttle_runtime::main]
async fn main(#[shuttle_shared_db::Postgres] pool: sqlx::PgPool) -> shuttle_rocket::ShuttleRocket {
    pool.execute(include_str!("../schema.sql"))
        .await
        .map_err(CustomError::new)?;

    let state = MyState { pool };
    let rocket = rocket::build()
        .mount(
            "/",
            routes![
                day_minus_1::index,
                day_minus_1::seek,
                day_2::dest,
                day_2::key,
                day_2::v6_dest,
                day_2::v6_key,
                day_5::manifest,
                day_9::milk,
                day_9::refill,
                day_12::board,
                day_12::reset,
                day_12::place,
                day_12::random_board,
                day_16::wrap,
                day_16::unwrap,
                day_16::decode_,
                day_19::reset,
                day_19::cite,
                day_19::remove,
                day_19::undo,
                day_19::draft,
                day_19::list,
            ],
        )
        .manage(state);

    Ok(rocket.into())
}
