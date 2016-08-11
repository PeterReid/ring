// Copyright 2015-2016 Brian Smith.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

#![allow(unsafe_code)]

/// RSA PKCS#1 1.5 signatures.

use {bssl, c, der, digest, error, signature};

#[cfg(feature = "rsa_signing")]
use rand;

#[cfg(feature = "rsa_signing")]
use std;

use untrusted;

mod padding;

// `RSA_PKCS1_SHA1` is intentionally not exposed.
use self::padding::{RSAPadding, RSA_PKCS1_SHA1};
pub use self::padding::{RSA_PKCS1_SHA256, RSA_PKCS1_SHA384, RSA_PKCS1_SHA512};

/// Parameters for RSA verification.
pub struct RSAParameters {
    padding_alg: &'static RSAPadding,
    min_bits: usize,
}

impl signature::VerificationAlgorithm for RSAParameters {
    fn verify(&self, public_key: untrusted::Input, msg: untrusted::Input,
              signature: untrusted::Input) -> Result<(), error::Unspecified> {
        const MAX_BITS: usize = 8192;

        let (n, e) = try!(parse_public_key(public_key));
        let signature = signature.as_slice_less_safe();

        let mut decoded = [0u8; (MAX_BITS + 7) / 8];
        if signature.len() > decoded.len() {
            return Err(error::Unspecified);
        }
        let decoded = &mut decoded[..signature.len()];
        try!(bssl::map_result(unsafe {
            GFp_rsa_public_decrypt(decoded.as_mut_ptr(), decoded.len(),
                                   n.as_ptr(), n.len(), e.as_ptr(), e.len(),
                                   signature.as_ptr(), signature.len(),
                                   self.min_bits, MAX_BITS)
        }));

        untrusted::Input::from(decoded).read_all(error::Unspecified, |decoded| {
            if try!(decoded.read_byte()) != 0 ||
               try!(decoded.read_byte()) != 1 {
                return Err(error::Unspecified);
            }

            let mut ps_len = 0;
            loop {
                match try!(decoded.read_byte()) {
                    0xff => { ps_len += 1; },
                    0x00 => { break; },
                    _ => { return Err(error::Unspecified); }
                }
            }
            if ps_len < 8 {
                return Err(error::Unspecified);
            }

            let decoded_digestinfo_prefix =
                try!(decoded.skip_and_get_input(
                        self.padding_alg.digestinfo_prefix.len()));
            if decoded_digestinfo_prefix != self.padding_alg.digestinfo_prefix {
                return Err(error::Unspecified);
            }

            let digest_alg = self.padding_alg.digest_alg;
            let decoded_digest =
                try!(decoded.skip_and_get_input(digest_alg.output_len));
            let digest = digest::digest(digest_alg, msg.as_slice_less_safe());
            if decoded_digest != digest.as_ref() {
                return Err(error::Unspecified);
            }

            Ok(())
        })
    }
}

macro_rules! rsa_pkcs1 {
    ( $VERIFY_ALGORITHM:ident, $min_bits:expr, $PADDING_ALGORITHM:ident,
      $doc_str:expr ) => {
        #[doc=$doc_str]
        ///
        /// Only available in `use_heap` mode.
        pub static $VERIFY_ALGORITHM: RSAParameters =
            RSAParameters {
                padding_alg: &$PADDING_ALGORITHM,
                min_bits: $min_bits,
            };
    }
}

rsa_pkcs1!(RSA_PKCS1_2048_8192_SHA1, 2048, RSA_PKCS1_SHA1,
           "Verification of signatures using RSA keys of 2048-8192 bits,
            PKCS#1.5 padding, and SHA-1.");
rsa_pkcs1!(RSA_PKCS1_2048_8192_SHA256, 2048, RSA_PKCS1_SHA256,
           "Verification of signatures using RSA keys of 2048-8192 bits,
            PKCS#1.5 padding, and SHA-256.");
rsa_pkcs1!(RSA_PKCS1_2048_8192_SHA384, 2048, RSA_PKCS1_SHA384,
           "Verification of signatures using RSA keys of 2048-8192 bits,
            PKCS#1.5 padding, and SHA-384.");
rsa_pkcs1!(RSA_PKCS1_2048_8192_SHA512, 2048, RSA_PKCS1_SHA512,
           "Verification of signatures using RSA keys of 2048-8192 bits,
            PKCS#1.5 padding, and SHA-512.");
rsa_pkcs1!(RSA_PKCS1_3072_8192_SHA384, 3072, RSA_PKCS1_SHA384,
           "Verification of signatures using RSA keys of 3072-8192 bits,
            PKCS#1.5 padding, and SHA-384.");

fn parse_public_key<'a>(input: untrusted::Input<'a>) ->
                        Result<(&'a [u8], &'a [u8]), error::Unspecified> {
    input.read_all(error::Unspecified, |input| {
        der::nested(input, der::Tag::Sequence, error::Unspecified, |input| {
            let n = try!(der::positive_integer(input));
            let e = try!(der::positive_integer(input));
            Ok((n.as_slice_less_safe(), e.as_slice_less_safe()))
        })
    })
}


/// An RSA key pair, used for signing. Feature: `rsa_signing`.
#[cfg(feature = "rsa_signing")]
pub struct RSAKeyPair {
    rsa: std::boxed::Box<RSA>,
    blinding: std::sync::Mutex<*mut BN_BLINDING>,
}

#[cfg(feature = "rsa_signing")]
impl RSAKeyPair {
    /// Parse a private key in DER-encoded ASN.1 `RSAPrivateKey` form (see
    /// [RFC 3447 Appendix A.1.2]).
    ///
    /// Only two-prime keys (version 0) keys are supported. The public modulus
    /// (n) must be at least 2048 bits. Currently, the public modulus must be
    /// no larger than 4096 bits.
    ///
    /// Here's one way to generate a key in the required format using OpenSSL:
    ///
    /// ```sh
    /// openssl genpkey -algorithm RSA \
    ///                 -pkeyopt rsa_keygen_bits:2048 \
    ///                 -outform der \
    ///                 -out private_key.der
    /// ```
    ///
    /// Often, keys generated for use in OpenSSL-based software are
    /// encoded in PEM format, which is not supported by *ring*. PEM-encoded
    /// keys that are in `RSAPrivateKey` format can be decoded into the using
    /// an OpenSSL command like this:
    ///
    /// ```sh
    /// openssl rsa -in private_key.pem -outform DER -out private_key.der
    /// ```
    ///
    /// If these commands don't work, it is likely that the private key is in a
    /// different format like PKCS#8, which isn't supported yet. An upcoming
    /// version of *ring* will likely replace the support for the
    /// `RSAPrivateKey` format with support for the PKCS#8 format.
    ///
    /// [RFC 3447 Appendix A.1.2]:
    ///     https://tools.ietf.org/html/rfc3447#appendix-A.1.2
    pub fn from_der(input: untrusted::Input)
                    -> Result<RSAKeyPair, error::Unspecified> {
        input.read_all(error::Unspecified, |input| {
            der::nested(input, der::Tag::Sequence, error::Unspecified,
                        |input| {
                let version = try!(der::small_nonnegative_integer(input));
                if version != 0 {
                    return Err(error::Unspecified);
                }
                let mut n = try!(PositiveInteger::from_der(input));
                let mut e = try!(PositiveInteger::from_der(input));
                let mut d = try!(PositiveInteger::from_der(input));
                let mut p = try!(PositiveInteger::from_der(input));
                let mut q = try!(PositiveInteger::from_der(input));
                let mut dmp1 = try!(PositiveInteger::from_der(input));
                let mut dmq1 = try!(PositiveInteger::from_der(input));
                let mut iqmp = try!(PositiveInteger::from_der(input));
                let mut rsa = std::boxed::Box::new(RSA {
                    n: n.into_raw(), e: e.into_raw(), d: d.into_raw(),
                    p: p.into_raw(), q: q.into_raw(), dmp1: dmp1.into_raw(),
                    dmq1: dmq1.into_raw(), iqmp: iqmp.into_raw(),
                    mont_n: std::ptr::null_mut(), mont_p: std::ptr::null_mut(),
                    mont_q: std::ptr::null_mut(),
                    mont_qq: std::ptr::null_mut(),
                    qmn_mont: std::ptr::null_mut(),
                    iqmp_mont: std::ptr::null_mut(),
                });
                try!(bssl::map_result(unsafe {
                    rsa_new_end(rsa.as_mut())
                }));
                let blinding = unsafe { BN_BLINDING_new() };
                if blinding.is_null() {
                    return Err(error::Unspecified);
                }

                Ok(RSAKeyPair {
                    rsa: rsa,
                    blinding: std::sync::Mutex::new(blinding),
                })
            })
        })
    }

    /// Returns the length in bytes of the key pair's public modulus.
    ///
    /// A signature has the same length as the public modulus.
    pub fn public_modulus_len(&self) -> usize {
        unsafe { RSA_size(self.rsa.as_ref()) }
    }

    /// Sign `msg`. `msg` is digested using the digest algorithm from
    /// `padding_alg` and the digest is then padded using the padding algorithm
    /// from `padding_alg`. The signature it written into `signature`;
    /// `signature`'s length must be exactly the length returned by
    /// `public_modulus_len()`. `rng` is used for blinding the message during
    /// signing, to mitigate some side-channel (e.g. timing) attacks.
    ///
    /// Many other crypto libraries have signing functions that takes a
    /// precomputed digest as input, instead of the message to digest. This
    /// function does *not* take a precomputed digest; instead, `sign`
    /// calculates the digest itself.
    ///
    /// Lots of effort has been made to make the signing operations close to
    /// constant time to protect the private key from side channel attacks. On
    /// x86-64, this is done pretty well, but not perfectly. On other
    /// platforms, it is done less perfectly. To help mitigate the current
    /// imperfections, and for defense-in-depth, base blinding is always done.
    /// Exponent blinding is not done, but it may be done in the future.
    pub fn sign(&self, padding_alg: &'static RSAPadding,
                rng: &rand::SecureRandom, msg: &[u8], signature: &mut [u8])
                -> Result<(), error::Unspecified> {
        if signature.len() != self.public_modulus_len() {
            return Err(error::Unspecified);
        }

        try!(padding_alg.pad(msg, signature));
        let mut rand = rand::RAND::new(rng);
        bssl::map_result(unsafe {
            let blinding = *(self.blinding.lock().unwrap());
            GFp_rsa_private_transform(self.rsa.as_ref(),
                                      signature.as_mut_ptr(),
                                      signature.len(), blinding,
                                      &mut rand)
        })
    }
}

#[cfg(feature = "rsa_signing")]
impl Drop for RSAKeyPair {
    fn drop(&mut self) {
        unsafe {
            BN_free(self.rsa.n);
            BN_free(self.rsa.e);
            BN_free(self.rsa.d);
            BN_free(self.rsa.p);
            BN_free(self.rsa.q);
            BN_free(self.rsa.dmp1);
            BN_free(self.rsa.dmq1);
            BN_free(self.rsa.iqmp);
            BN_MONT_CTX_free(self.rsa.mont_n);
            BN_MONT_CTX_free(self.rsa.mont_p);
            BN_MONT_CTX_free(self.rsa.mont_q);
            BN_MONT_CTX_free(self.rsa.mont_qq);
            BN_free(self.rsa.qmn_mont);
            BN_free(self.rsa.iqmp_mont);
            BN_BLINDING_free(*(self.blinding.lock().unwrap()));
        }
    }
}

/// Needs to be kept in sync with `struct rsa_st` (in `include/openssl/rsa.h`).
#[cfg(feature = "rsa_signing")]
#[repr(C)]
struct RSA {
    n: *mut BIGNUM,
    e: *mut BIGNUM,
    d: *mut BIGNUM,
    p: *mut BIGNUM,
    q: *mut BIGNUM,
    dmp1: *mut BIGNUM,
    dmq1: *mut BIGNUM,
    iqmp: *mut BIGNUM,
    mont_n: *mut BN_MONT_CTX,
    mont_p: *mut BN_MONT_CTX,
    mont_q: *mut BN_MONT_CTX,
    mont_qq: *mut BN_MONT_CTX,
    qmn_mont: *mut BIGNUM,
    iqmp_mont: *mut BIGNUM,
}

#[cfg(feature = "rsa_signing")]
struct PositiveInteger {
    value: Option<*mut BIGNUM>,
}

#[cfg(feature = "rsa_signing")]
impl PositiveInteger {
    // Parses a single ASN.1 DER-encoded `Integer`, which most be positive.
    fn from_der(input: &mut untrusted::Reader)
                -> Result<PositiveInteger, error::Unspecified> {
        let bytes = try!(der::positive_integer(input)).as_slice_less_safe();
        let res = unsafe {
            BN_bin2bn(bytes.as_ptr(), bytes.len(), std::ptr::null_mut())
        };
        if res.is_null() {
            return Err(error::Unspecified);
        }
        Ok(PositiveInteger { value: Some(res) })
    }

    fn into_raw(&mut self) -> *mut BIGNUM {
        let res = self.value.unwrap();
        self.value = None;
        res
    }
}

#[cfg(feature = "rsa_signing")]
impl Drop for PositiveInteger {
    fn drop(&mut self) {
        match self.value {
            Some(val) => unsafe { BN_free(val); },
            None => { },
        }
    }
}

#[cfg(feature = "rsa_signing")]
enum BIGNUM {}

/// Needs to be kept in sync with `bn_blinding_st` in `crypto/rsa/blinding.c`.
#[cfg(feature = "rsa_signing")]
#[allow(non_camel_case_types)]
#[repr(C)]
struct BN_BLINDING {
    a: *mut BIGNUM,
    ai: *mut BIGNUM,
    counter: u32,
}

#[cfg(feature = "rsa_signing")]
#[allow(non_camel_case_types)]
enum BN_MONT_CTX {}


#[cfg(feature = "rsa_signing")]
extern {
    fn BN_BLINDING_new() -> *mut BN_BLINDING;
    fn BN_BLINDING_free(b: *mut BN_BLINDING);
    fn BN_bin2bn(in_: *const u8, len: c::size_t, ret: *mut BIGNUM)
                 -> *mut BIGNUM;
    fn BN_free(bn: *mut BIGNUM);
    fn BN_MONT_CTX_free(mont: *mut BN_MONT_CTX);

    fn rsa_new_end(rsa: *mut RSA) -> c::int;
    fn RSA_size(rsa: *const RSA) -> c::size_t;
}

extern {
    fn GFp_rsa_public_decrypt(out: *mut u8, out_len: c::size_t,
                              public_key_n: *const u8,
                              public_key_n_len: c::size_t,
                              public_key_e: *const u8,
                              public_key_e_len: c::size_t,
                              ciphertext: *const u8, ciphertext_len: c::size_t,
                              min_bits: c::size_t, max_bits: c::size_t)
                              -> c::int;
}

#[cfg(feature = "rsa_signing")]
#[allow(improper_ctypes)]
extern {
    fn GFp_rsa_private_transform(rsa: *const RSA, inout: *mut u8,
                                 len: c::size_t, blinding: *mut BN_BLINDING,
                                 rng: *mut rand::RAND) -> c::int;
}


#[cfg(test)]
mod tests {
    use {der, error, signature, test};

    #[cfg(feature = "rsa_signing")]
    use rand;

    #[cfg(feature = "rsa_signing")]
    use std;

    use super::*;
    use untrusted;

    #[cfg(feature = "rsa_signing")]
    extern { static GFp_BN_BLINDING_COUNTER: u32; }

    #[test]
    fn test_signature_rsa_pkcs1_verify() {
        test::from_file("src/rsa/rsa_pkcs1_verify_tests.txt",
                        |section, test_case| {
            assert_eq!(section, "");

            let digest_name = test_case.consume_string("Digest");
            let alg = if digest_name == "SHA1" {
                &RSA_PKCS1_2048_8192_SHA1
            } else if digest_name == "SHA256" {
                &RSA_PKCS1_2048_8192_SHA256
            } else if digest_name == "SHA384" {
                &RSA_PKCS1_2048_8192_SHA384
            } else if digest_name == "SHA512" {
                &RSA_PKCS1_2048_8192_SHA512
            } else {
                panic!("Unsupported digest: {}", digest_name);
            };

            let public_key = test_case.consume_bytes("Key");
            let public_key = untrusted::Input::from(&public_key);

            // Sanity check that we correctly DER-encoded the originally-
            // provided separate (n, e) components. When we add test vectors
            // for improperly-encoded signatures, we'll have to revisit this.
            assert!(public_key.read_all(error::Unspecified, |input| {
                der::nested(input, der::Tag::Sequence, error::Unspecified,
                            |input| {
                    let _ = try!(der::positive_integer(input));
                    let _ = try!(der::positive_integer(input));
                    Ok(())
                })
            }).is_ok());

            let msg = test_case.consume_bytes("Msg");
            let msg = untrusted::Input::from(&msg);

            let sig = test_case.consume_bytes("Sig");
            let sig = untrusted::Input::from(&sig);

            let expected_result = test_case.consume_string("Result");

            let actual_result = signature::verify(alg, public_key, msg, sig);
            assert_eq!(actual_result.is_ok(), expected_result == "P");

            Ok(())
        });
    }

    #[cfg(feature = "rsa_signing")]
    #[test]
    fn test_signature_rsa_pkcs1_sign() {
        let rng = rand::SystemRandom::new();
        test::from_file("src/rsa/rsa_pkcs1_sign_tests.txt",
                        |section, test_case| {
            let digest_name = test_case.consume_string("Digest");
            // Note that SHA-1 isn't recognized here because we don't expose
            // PKCS#1 SHA-1 signing, because we don't have test vectors for it.
            let alg = if digest_name == "SHA256" {
                &RSA_PKCS1_SHA256
            } else if digest_name == "SHA384" {
                &RSA_PKCS1_SHA384
            } else if digest_name == "SHA512" {
                &RSA_PKCS1_SHA512
            } else {
                panic!("Unsupported digest: {}", digest_name);
            };

            let private_key = test_case.consume_bytes("Key");
            let msg = test_case.consume_bytes("Msg");
            let expected = test_case.consume_bytes("Sig");
            let result = test_case.consume_string("Result");

            let private_key = untrusted::Input::from(&private_key);
            let key_pair = RSAKeyPair::from_der(private_key);
            if key_pair.is_err() && result == "Fail-Invalid-Key" {
                return Ok(());
            }
            let key_pair = key_pair.unwrap();

            // XXX: This test is too slow on Android ARM Travis CI builds.
            // TODO: re-enable these tests on Android ARM.
            if section == "Skipped on Android ARM due to Travis CI Timeouts" &&
               cfg!(all(target_os = "android", target_arch = "arm")) {
               return Ok(());
            }

            let mut actual: std::vec::Vec<u8> =
                vec![0; key_pair.public_modulus_len()];
            try!(key_pair.sign(alg, &rng, &msg, actual.as_mut_slice()));
            assert_eq!(actual.as_slice() == &expected[..], result == "Pass");
            Ok(())
        });
    }

    // `RSAKeyPair::sign` requires that the output buffer is the same length as
    // the public key modulus. Test what happens when it isn't the same length.
    #[cfg(feature = "rsa_signing")]
    #[test]
    fn test_signature_rsa_pkcs1_sign_output_buffer_len() {
        // Sign the message "hello, world", using PKCS#1 v1.5 padding and the
        // SHA256 digest algorithm.
        const MESSAGE: &'static [u8] = b"hello, world";
        let rng = rand::SystemRandom::new();

        const PRIVATE_KEY_DER: &'static [u8] =
            include_bytes!("signature_rsa_example_private_key.der");
        let key_bytes_der = untrusted::Input::from(PRIVATE_KEY_DER);
        let key_pair = RSAKeyPair::from_der(key_bytes_der).unwrap();

        // The output buffer is one byte too short.
        let mut signature = vec![0; key_pair.public_modulus_len() - 1];
        assert!(key_pair.sign(&RSA_PKCS1_SHA256, &rng, MESSAGE,
                              &mut signature).is_err());

        // The output buffer is the right length.
        signature.push(0);
        assert!(key_pair.sign(&RSA_PKCS1_SHA256, &rng, MESSAGE,
                              &mut signature).is_ok());


        // The output buffer is one byte too long.
        signature.push(0);
        assert!(key_pair.sign(&RSA_PKCS1_SHA256, &rng, MESSAGE,
                              &mut signature).is_err());
    }

    // Once the `BN_BLINDING` in an `RSAKeyPair` has been used
    // `GFp_BN_BLINDING_COUNTER` times, a new blinding should be created. we
    // don't check that a new blinding was created; we just make sure to
    // exercise the code path, so this is basically a coverage test.
    #[cfg(feature = "rsa_signing")]
    #[test]
    fn test_signature_rsa_pkcs1_sign_blinding_reuse() {
        const MESSAGE: &'static [u8] = b"hello, world";
        let rng = rand::SystemRandom::new();

        const PRIVATE_KEY_DER: &'static [u8] =
            include_bytes!("signature_rsa_example_private_key.der");
        let key_bytes_der = untrusted::Input::from(PRIVATE_KEY_DER);
        let key_pair = RSAKeyPair::from_der(key_bytes_der).unwrap();

        let mut signature = vec![0; key_pair.public_modulus_len()];

        for _ in 0 .. GFp_BN_BLINDING_COUNTER + 1 {
            let prev_counter = unsafe {
                let blinding = *(key_pair.blinding.lock().unwrap());
                (*blinding).counter
            };

            let _ = key_pair.sign(&RSA_PKCS1_SHA256, &rng, MESSAGE,
                                  &mut signature);

            let counter = unsafe {
                let blinding = *(key_pair.blinding.lock().unwrap());
                (*blinding).counter
            };

            assert_eq!(counter, (prev_counter + 1) % GFp_BN_BLINDING_COUNTER);
        }
    }

    // In `crypto/rsa/blinding.c`, when `bn_blinding_create_param` fails to
    // randomly generate an invertible blinding factor too many times in a
    // loop, it returns an error. Check that we observe this.
    #[cfg(feature = "rsa_signing")]
    #[test]
    fn test_signature_rsa_pkcs1_sign_blinding_creation_failure() {
        const MESSAGE: &'static [u8] = b"hello, world";

        // Stub RNG that is constantly 0. In `bn_blinding_create_param`, this
        // causes the candidate blinding factors to always be 0, which has no
        // inverse, so `BN_mod_inverse_no_branch` fails.
        let rng = rand::test_util::FixedByteRandom { byte: 0x00 };

        const PRIVATE_KEY_DER: &'static [u8] =
            include_bytes!("signature_rsa_example_private_key.der");
        let key_bytes_der = untrusted::Input::from(PRIVATE_KEY_DER);
        let key_pair = RSAKeyPair::from_der(key_bytes_der).unwrap();

        let mut signature = vec![0; key_pair.public_modulus_len()];

        let result = key_pair.sign(&RSA_PKCS1_SHA256, &rng, MESSAGE,
                                   &mut signature);

        assert!(result.is_err());
    }
}
