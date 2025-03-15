pub mod basic;
pub mod capture;
pub mod common;
pub mod constants;

// /**
//  * Demonstrates ZKEmail where the body hash is regexed from the header
//  */
// #[export]
// pub fn bench(header: BoundedVec<u8, MAX_EMAIL_HEADER_LENGTH>) -> [u8; TIMESTAMP_LEN] {
//     // 5. get the timestamp (cuz why not)
//     let timestamp = timestamp_regex::regex_match(header);
//     timestamp
// }

use crate::capture::composite::{decoded_body_hash, timestamp as timestamp_regex};
use sha256::sha256_var;
use std::hash::pedersen_hash;
// use zkemail::{dkim::RSAPubkey, KEY_LIMBS_2048};

global MAX_EMAIL_HEADER_LENGTH: u32 = 512;
global MAX_EMAIL_BODY_LENGTH: u32 = 1024;

pub struct Output {
    pubkey_hash: Field, // the hash of the pubkey
    email_nullifier: Field, // the unique nullifier of the email
    timestamp: Field, // timestamp from dkim signature over email
}

pub struct Foo {
    a: [u8; 32],
    b: [u8; 10],
}

#[export]
pub fn bench_regex_match(header: BoundedVec<u8, MAX_EMAIL_HEADER_LENGTH>) -> Foo {
    let signed_body_hash = decoded_body_hash::regex_match(header);
    let timestamp = timestamp_regex::regex_match(header);
    Foo { a: signed_body_hash, b: timestamp }
}

#[export]
pub fn bench_regex_timestamp(header: BoundedVec<u8, MAX_EMAIL_HEADER_LENGTH>) -> [u8; 10] {
    let timestamp = timestamp_regex::regex_match(header);
    timestamp
}

#[export]
pub fn bench_regex_header(header: BoundedVec<u8, MAX_EMAIL_HEADER_LENGTH>) -> [u8; 32] {
    let signed_body_hash = decoded_body_hash::regex_match(header);
    signed_body_hash
}
