use std::convert::AsRef;
use std::fmt::{Debug, Display, Formatter};
use std::hash::{Hash, Hasher};
use std::io::{Error, ErrorKind, Write};
use std::str::FromStr;

use borsh::{BorshDeserialize, BorshSerialize};
use ed25519_dalek::ed25519::signature::{Signer, Verifier};
use rand::rngs::OsRng;
use serde::{Deserialize, Serialize};

#[derive(Debug, Copy, Clone, Serialize, Deserialize)]
pub enum KeyType {
    ED25519 = 0,
}

impl Display for KeyType {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        f.write_str(match self {
            KeyType::ED25519 => "ed25519",
        })
    }
}

impl FromStr for KeyType {
    type Err = crate::errors::ParseKeyTypeError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let lowercase_key_type = value.to_ascii_lowercase();
        match lowercase_key_type.as_str() {
            "ed25519" => Ok(KeyType::ED25519),
            &_ => Err(crate::ParseKeyTypeError::UnknownKeyType {
                unknown_key_type: "Unknown (secp256k1 not accepted on WASM)".to_string(),
            }),
        }
    }
}

impl TryFrom<u8> for KeyType {
    type Error = crate::errors::ParseKeyTypeError;

    fn try_from(value: u8) -> Result<Self, Self::Error> {
        match value {
            0 => Ok(KeyType::ED25519),
            1_u8..=u8::MAX => Err(crate::errors::ParseKeyTypeError::UnknownKeyType {
                unknown_key_type: "Unknown (secp256k1 not accepted on WASM)".to_string(),
            }),
        }
    }
}

fn split_key_type_data(value: &str) -> Result<(KeyType, &str), crate::errors::ParseKeyTypeError> {
    if let Some(idx) = value.find(':') {
        let (prefix, key_data) = value.split_at(idx);
        Ok((KeyType::from_str(prefix)?, &key_data[1..]))
    } else {
        // If there is no prefix then we Default to ED25519.
        Ok((KeyType::ED25519, value))
    }
}

#[derive(Clone, Eq, Ord, PartialEq, PartialOrd, derive_more::AsRef, derive_more::From)]
#[as_ref(forward)]
pub struct ED25519PublicKey(pub [u8; ed25519_dalek::PUBLIC_KEY_LENGTH]);

impl TryFrom<&[u8]> for ED25519PublicKey {
    type Error = crate::errors::ParseKeyError;

    fn try_from(data: &[u8]) -> Result<Self, Self::Error> {
        data.try_into().map(Self).map_err(|_| Self::Error::InvalidLength {
            expected_length: ed25519_dalek::PUBLIC_KEY_LENGTH,
            received_length: data.len(),
        })
    }
}

impl std::fmt::Debug for ED25519PublicKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        Display::fmt(&Bs58(&self.0), f)
    }
}

/// Public key container supporting different curves.
#[derive(Clone, PartialEq, PartialOrd, Ord, Eq)]
pub enum PublicKey {
    /// 256 bit elliptic curve based public-key.
    ED25519(ED25519PublicKey),
}

impl PublicKey {
    pub fn len(&self) -> usize {
        match self {
            Self::ED25519(_) => ed25519_dalek::PUBLIC_KEY_LENGTH + 1,
        }
    }

    pub fn empty(key_type: KeyType) -> Self {
        match key_type {
            KeyType::ED25519 => {
                PublicKey::ED25519(ED25519PublicKey([0u8; ed25519_dalek::PUBLIC_KEY_LENGTH]))
            }
        }
    }

    pub fn key_type(&self) -> KeyType {
        match self {
            Self::ED25519(_) => KeyType::ED25519,
        }
    }

    pub fn key_data(&self) -> &[u8] {
        match self {
            Self::ED25519(key) => key.as_ref(),
        }
    }

    pub fn unwrap_as_ed25519(&self) -> &ED25519PublicKey {
        match self {
            Self::ED25519(key) => key,
        }
    }
}

// This `Hash` implementation is safe since it retains the property
// `k1 == k2 ⇒ hash(k1) == hash(k2)`.
#[allow(clippy::derive_hash_xor_eq)]
impl Hash for PublicKey {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            PublicKey::ED25519(public_key) => {
                state.write_u8(0u8);
                state.write(&public_key.0);
            }
        }
    }
}

impl Display for PublicKey {
    fn fmt(&self, fmt: &mut Formatter) -> std::fmt::Result {
        let (key_type, key_data) = match self {
            PublicKey::ED25519(public_key) => (KeyType::ED25519, &public_key.0[..]),
        };
        write!(fmt, "{}:{}", key_type, Bs58(key_data))
    }
}

impl Debug for PublicKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        Display::fmt(self, f)
    }
}

impl BorshSerialize for PublicKey {
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        match self {
            PublicKey::ED25519(public_key) => {
                BorshSerialize::serialize(&0u8, writer)?;
                writer.write_all(&public_key.0)?;
            }
        }
        Ok(())
    }
}

impl BorshDeserialize for PublicKey {
    fn deserialize(buf: &mut &[u8]) -> Result<Self, Error> {
        let key_type = KeyType::try_from(<u8 as BorshDeserialize>::deserialize(buf)?)
            .map_err(|err| Error::new(ErrorKind::InvalidData, err.to_string()))?;
        match key_type {
            KeyType::ED25519 => {
                Ok(PublicKey::ED25519(ED25519PublicKey(BorshDeserialize::deserialize(buf)?)))
            }
        }
    }
}

impl serde::Serialize for PublicKey {
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<<S as serde::Serializer>::Ok, <S as serde::Serializer>::Error>
    where
        S: serde::Serializer,
    {
        serializer.collect_str(self)
    }
}

impl<'de> serde::Deserialize<'de> for PublicKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, <D as serde::Deserializer<'de>>::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = <String as serde::Deserialize>::deserialize(deserializer)?;
        s.parse()
            .map_err(|err: crate::errors::ParseKeyError| serde::de::Error::custom(err.to_string()))
    }
}

impl FromStr for PublicKey {
    type Err = crate::errors::ParseKeyError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let (key_type, key_data) = split_key_type_data(value)?;
        Ok(match key_type {
            KeyType::ED25519 => Self::ED25519(ED25519PublicKey(decode_bs58(key_data)?)),
        })
    }
}

impl From<ED25519PublicKey> for PublicKey {
    fn from(ed25519: ED25519PublicKey) -> Self {
        Self::ED25519(ed25519)
    }
}

#[derive(Clone, Eq)]
// This is actually a keypair, because ed25519_dalek api only has keypair.sign
// From ed25519_dalek doc: The first SECRET_KEY_LENGTH of bytes is the SecretKey
// The last PUBLIC_KEY_LENGTH of bytes is the public key, in total it's KEYPAIR_LENGTH
pub struct ED25519SecretKey(pub [u8; ed25519_dalek::KEYPAIR_LENGTH]);

impl PartialEq for ED25519SecretKey {
    fn eq(&self, other: &Self) -> bool {
        self.0[..ed25519_dalek::SECRET_KEY_LENGTH] == other.0[..ed25519_dalek::SECRET_KEY_LENGTH]
    }
}

impl std::fmt::Debug for ED25519SecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        Display::fmt(&Bs58(&self.0[..ed25519_dalek::SECRET_KEY_LENGTH]), f)
    }
}

/// Secret key container supporting different curves.
#[derive(Clone, Eq, PartialEq, Debug)]
pub enum SecretKey {
    ED25519(ED25519SecretKey),
}

impl SecretKey {
    pub fn key_type(&self) -> KeyType {
        match self {
            SecretKey::ED25519(_) => KeyType::ED25519,
        }
    }

    pub fn from_random(key_type: KeyType) -> SecretKey {
        match key_type {
            KeyType::ED25519 => {
                let keypair = ed25519_dalek::Keypair::generate(&mut OsRng);
                SecretKey::ED25519(ED25519SecretKey(keypair.to_bytes()))
            }
        }
    }

    pub fn sign(&self, data: &[u8]) -> Signature {
        match &self {
            SecretKey::ED25519(secret_key) => {
                let keypair = ed25519_dalek::Keypair::from_bytes(&secret_key.0).unwrap();
                Signature::ED25519(keypair.sign(data))
            }
        }
    }

    pub fn public_key(&self) -> PublicKey {
        match &self {
            SecretKey::ED25519(secret_key) => PublicKey::ED25519(ED25519PublicKey(
                secret_key.0[ed25519_dalek::SECRET_KEY_LENGTH..].try_into().unwrap(),
            )),
        }
    }

    pub fn unwrap_as_ed25519(&self) -> &ED25519SecretKey {
        match self {
            SecretKey::ED25519(key) => key,
        }
    }
}

impl std::fmt::Display for SecretKey {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let (key_type, key_data) = match self {
            SecretKey::ED25519(secret_key) => (KeyType::ED25519, &secret_key.0[..]),
        };
        write!(f, "{}:{}", key_type, Bs58(key_data))
    }
}

impl FromStr for SecretKey {
    type Err = crate::errors::ParseKeyError;

    fn from_str(s: &str) -> Result<Self, Self::Err> {
        let (key_type, key_data) = split_key_type_data(s)?;
        Ok(match key_type {
            KeyType::ED25519 => Self::ED25519(ED25519SecretKey(decode_bs58(key_data)?)),
        })
    }
}

impl serde::Serialize for SecretKey {
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<<S as serde::Serializer>::Ok, <S as serde::Serializer>::Error>
    where
        S: serde::Serializer,
    {
        serializer.collect_str(self)
    }
}

impl<'de> serde::Deserialize<'de> for SecretKey {
    fn deserialize<D>(deserializer: D) -> Result<Self, <D as serde::Deserializer<'de>>::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = <String as serde::Deserialize>::deserialize(deserializer)?;
        Self::from_str(&s).map_err(|err| serde::de::Error::custom(err.to_string()))
    }
}

/// Signature container supporting different curves.
#[derive(Clone, PartialEq, Eq)]
pub enum Signature {
    ED25519(ed25519_dalek::Signature),
}

impl Hash for Signature {
    fn hash<H: Hasher>(&self, state: &mut H) {
        match self {
            Signature::ED25519(sig) => sig.to_bytes().hash(state),
        };
    }
}

impl Signature {
    /// Construct Signature from key type and raw signature blob
    pub fn from_parts(
        signature_type: KeyType,
        signature_data: &[u8],
    ) -> Result<Self, crate::errors::ParseSignatureError> {
        match signature_type {
            KeyType::ED25519 => Ok(Signature::ED25519(
                ed25519_dalek::Signature::from_bytes(signature_data).map_err(|err| {
                    crate::errors::ParseSignatureError::InvalidData {
                        error_message: err.to_string(),
                    }
                })?,
            )),
        }
    }

    /// Verifies that this signature is indeed signs the data with given public key.
    /// Also if public key doesn't match on the curve returns `false`.
    pub fn verify(&self, data: &[u8], public_key: &PublicKey) -> bool {
        match (&self, public_key) {
            (Signature::ED25519(signature), PublicKey::ED25519(public_key)) => {
                match ed25519_dalek::PublicKey::from_bytes(&public_key.0) {
                    Err(_) => false,
                    Ok(public_key) => public_key.verify(data, signature).is_ok(),
                }
            }
            _ => false,
        }
    }

    pub fn key_type(&self) -> KeyType {
        match self {
            Signature::ED25519(_) => KeyType::ED25519,
        }
    }
}

impl Default for Signature {
    fn default() -> Self {
        Signature::empty(KeyType::ED25519)
    }
}

impl BorshSerialize for Signature {
    fn serialize<W: Write>(&self, writer: &mut W) -> Result<(), Error> {
        match self {
            Signature::ED25519(signature) => {
                BorshSerialize::serialize(&0u8, writer)?;
                writer.write_all(&signature.to_bytes())?;
            }
        }
        Ok(())
    }
}

impl BorshDeserialize for Signature {
    fn deserialize(buf: &mut &[u8]) -> Result<Self, Error> {
        let key_type = KeyType::try_from(<u8 as BorshDeserialize>::deserialize(buf)?)
            .map_err(|err| Error::new(ErrorKind::InvalidData, err.to_string()))?;
        match key_type {
            KeyType::ED25519 => {
                let array: [u8; ed25519_dalek::SIGNATURE_LENGTH] =
                    BorshDeserialize::deserialize(buf)?;
                Ok(Signature::ED25519(
                    ed25519_dalek::Signature::from_bytes(&array)
                        .map_err(|e| Error::new(ErrorKind::InvalidData, e.to_string()))?,
                ))
            }
        }
    }
}

impl Display for Signature {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> Result<(), std::fmt::Error> {
        let (key_type, key_data) = match self {
            Signature::ED25519(signature) => (KeyType::ED25519, signature.as_ref()),
        };
        write!(f, "{}:{}", key_type, Bs58(key_data))
    }
}

impl Debug for Signature {
    fn fmt(&self, f: &mut Formatter<'_>) -> Result<(), std::fmt::Error> {
        Display::fmt(self, f)
    }
}

impl serde::Serialize for Signature {
    fn serialize<S>(
        &self,
        serializer: S,
    ) -> Result<<S as serde::Serializer>::Ok, <S as serde::Serializer>::Error>
    where
        S: serde::Serializer,
    {
        serializer.serialize_str(&self.to_string())
    }
}

impl FromStr for Signature {
    type Err = crate::errors::ParseSignatureError;

    fn from_str(value: &str) -> Result<Self, Self::Err> {
        let (sig_type, sig_data) = split_key_type_data(value)?;
        Ok(match sig_type {
            KeyType::ED25519 => {
                let data = decode_bs58::<{ ed25519_dalek::SIGNATURE_LENGTH }>(sig_data)?;
                let sig = ed25519_dalek::Signature::from_bytes(&data)
                    .map_err(|err| Self::Err::InvalidData { error_message: err.to_string() })?;
                Signature::ED25519(sig)
            }
        })
    }
}

impl<'de> serde::Deserialize<'de> for Signature {
    fn deserialize<D>(deserializer: D) -> Result<Self, <D as serde::Deserializer<'de>>::Error>
    where
        D: serde::Deserializer<'de>,
    {
        let s = <String as serde::Deserialize>::deserialize(deserializer)?;
        s.parse().map_err(|err: crate::errors::ParseSignatureError| {
            serde::de::Error::custom(err.to_string())
        })
    }
}

/// Helper struct which provides Display implementation for bytes slice
/// encoding them using base58.
// TODO(mina86): Get rid of it once bs58 has this feature.  There’s currently PR
// for that: https://github.com/Nullus157/bs58-rs/pull/97
struct Bs58<'a>(&'a [u8]);

impl<'a> core::fmt::Display for Bs58<'a> {
    fn fmt(&self, fmt: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        debug_assert!(self.0.len() <= 65);
        // The largest buffer we’re ever encoding is 65-byte long.  Base58
        // increases size of the value by less than 40%.  96-byte buffer is
        // therefore enough to fit the largest value we’re ever encoding.
        let mut buf = [0u8; 96];
        let len = bs58::encode(self.0).into(&mut buf[..]).unwrap();
        let output = &buf[..len];
        // SAFETY: we know that alphabet can only include ASCII characters
        // thus our result is an ASCII string.
        fmt.write_str(unsafe { std::str::from_utf8_unchecked(output) })
    }
}

/// Helper which decodes fixed-length base58-encoded data.
///
/// If the encoded string decodes into a buffer of different length than `N`,
/// returns error.  Similarly returns error if decoding fails.
fn decode_bs58<const N: usize>(encoded: &str) -> Result<[u8; N], DecodeBs58Error> {
    let mut buffer = [0u8; N];
    decode_bs58_impl(&mut buffer[..], encoded)?;
    Ok(buffer)
}

fn decode_bs58_impl(dst: &mut [u8], encoded: &str) -> Result<(), DecodeBs58Error> {
    let expected = dst.len();
    match bs58::decode(encoded).into(dst) {
        Ok(received) if received == expected => Ok(()),
        Ok(received) => Err(DecodeBs58Error::BadLength { expected, received }),
        Err(bs58::decode::Error::BufferTooSmall) => {
            Err(DecodeBs58Error::BadLength { expected, received: expected + 1 })
        }
        Err(err) => Err(DecodeBs58Error::BadData(err.to_string())),
    }
}

enum DecodeBs58Error {
    BadLength { expected: usize, received: usize },
    BadData(String),
}

impl std::convert::From<DecodeBs58Error> for crate::errors::ParseKeyError {
    fn from(err: DecodeBs58Error) -> Self {
        match err {
            DecodeBs58Error::BadLength { expected, received } => {
                crate::errors::ParseKeyError::InvalidLength {
                    expected_length: expected,
                    received_length: received,
                }
            }
            DecodeBs58Error::BadData(error_message) => Self::InvalidData { error_message },
        }
    }
}

impl std::convert::From<DecodeBs58Error> for crate::errors::ParseSignatureError {
    fn from(err: DecodeBs58Error) -> Self {
        match err {
            DecodeBs58Error::BadLength { expected, received } => {
                Self::InvalidLength { expected_length: expected, received_length: received }
            }
            DecodeBs58Error::BadData(error_message) => Self::InvalidData { error_message },
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_sign_verify() {
        for key_type in vec![KeyType::ED25519] {
            let secret_key = SecretKey::from_random(key_type);
            let public_key = secret_key.public_key();
            use sha2::Digest;
            let data = sha2::Sha256::digest(b"123").to_vec();
            let signature = secret_key.sign(&data);
            assert!(signature.verify(&data, &public_key));
        }
    }

    #[test]
    fn test_json_serialize_ed25519() {
        let sk = SecretKey::from_seed(KeyType::ED25519, "test");
        let pk = sk.public_key();
        let expected = "\"ed25519:DcA2MzgpJbrUATQLLceocVckhhAqrkingax4oJ9kZ847\"";
        assert_eq!(serde_json::to_string(&pk).unwrap(), expected);
        assert_eq!(pk, serde_json::from_str(expected).unwrap());
        assert_eq!(
            pk,
            serde_json::from_str("\"DcA2MzgpJbrUATQLLceocVckhhAqrkingax4oJ9kZ847\"").unwrap()
        );
        let pk2: PublicKey = pk.to_string().parse().unwrap();
        assert_eq!(pk, pk2);

        let expected = "\"ed25519:3KyUuch8pYP47krBq4DosFEVBMR5wDTMQ8AThzM8kAEcBQEpsPdYTZ2FPX5ZnSoLrerjwg66hwwJaW1wHzprd5k3\"";
        assert_eq!(serde_json::to_string(&sk).unwrap(), expected);
        assert_eq!(sk, serde_json::from_str(expected).unwrap());

        let signature = sk.sign(b"123");
        let expected = "\"ed25519:3s1dvZdQtcAjBksMHFrysqvF63wnyMHPA4owNQmCJZ2EBakZEKdtMsLqrHdKWQjJbSRN6kRknN2WdwSBLWGCokXj\"";
        assert_eq!(serde_json::to_string(&signature).unwrap(), expected);
        assert_eq!(signature, serde_json::from_str(expected).unwrap());
        let signature_str: String = signature.to_string();
        let signature2: Signature = signature_str.parse().unwrap();
        assert_eq!(signature, signature2);
    }

    #[test]
    fn test_borsh_serialization() {
        use sha2::Digest;
        let data = sha2::Sha256::digest(b"123").to_vec();
        for key_type in vec![KeyType::ED25519] {
            let sk = SecretKey::from_seed(key_type, "test");
            let pk = sk.public_key();
            let bytes = pk.try_to_vec().unwrap();
            assert_eq!(PublicKey::try_from_slice(&bytes).unwrap(), pk);

            let signature = sk.sign(&data);
            let bytes = signature.try_to_vec().unwrap();
            assert_eq!(Signature::try_from_slice(&bytes).unwrap(), signature);

            assert!(PublicKey::try_from_slice(&[0]).is_err());
            assert!(Signature::try_from_slice(&[0]).is_err());
        }
    }
}
