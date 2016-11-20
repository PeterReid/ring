// Copyright 2015-2016 Brian Smith.
// Portions Copyright (c) 2014, 2015, Google Inc.
//
// Permission to use, copy, modify, and/or distribute this software for any
// purpose with or without fee is hereby granted, provided that the above
// copyright notice and this permission notice appear in all copies.
//
// THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHORS DISCLAIM ALL WARRANTIES
// WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
// MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHORS BE LIABLE FOR ANY
// SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
// WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN ACTION
// OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF OR IN
// CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.

// TODO: enforce maximum input length.

use {c, chacha, constant_time, error};
use core;
use polyfill::slice::u32_from_le_u8;

struct AlignedBlockState<'a> {
    buf: [u8; BLOCK_STATE_SIZE + 7],
    inner: &'a mut [u8; BLOCK_STATE_SIZE],
}
impl<'a> AlignedBlockState<'a> {
    pub fn new(inner: &mut [u8; BLOCK_STATE_SIZE]) -> AlignedBlockState {
        let mut st = AlignedBlockState {
            buf: [0u8; BLOCK_STATE_SIZE + 7],
            inner: inner,
        };
        AlignedBlockState::align(&mut st.buf).copy_from_slice(&st.inner[..]);
        st
    }
    fn align(xs: &mut [u8; BLOCK_STATE_SIZE + 7]) -> &mut [u8; BLOCK_STATE_SIZE] {
        let aligned_start = (xs.as_ptr() as usize + 7) & !7;
        let offset = aligned_start - (xs.as_ptr() as usize);
        slice_as_array_ref_mut!(&mut xs[offset..offset+BLOCK_STATE_SIZE], BLOCK_STATE_SIZE).unwrap()
    }
    pub fn aligned_buf(&mut self) -> &mut [u8; BLOCK_STATE_SIZE] {
        AlignedBlockState::align(&mut self.buf)
    }
}
impl<'a> Drop for AlignedBlockState<'a> {
    fn drop(&mut self) {
        self.inner.copy_from_slice(AlignedBlockState::align(&mut self.buf));
    }
}

impl SigningContext {
    #[inline]
    pub fn from_key(key: Key) -> SigningContext {
        let mut ctx = SigningContext{
            opaque: [0; BLOCK_STATE_SIZE],
            nonce: [0; 4],
            buf: [0; BLOCK_LEN],
            buf_used: 0,
            func: Funcs {
                blocks_fn: GFp_poly1305_blocks,
                emit_fn: GFp_poly1305_emit
            }
        };
        check_block_state_layout();

        let set_fns = init(AlignedBlockState::new(&mut ctx.opaque).aligned_buf(), &key.bytes, &mut ctx.func) == 0;
        // TODO XXX: It seems at least some implementations |poly1305_init| always
        // return the same value, so this conditional logic isn't always necessary.
        // And, for platforms that have such conditional logic also in the ASM code,
        // it seems it would be better to move the conditional logic out of the asm
        // and into the higher-level code.
        if !set_fns {
            ctx.func.blocks_fn = GFp_poly1305_blocks;
            ctx.func.emit_fn = GFp_poly1305_emit;
        }

        ctx.nonce = [
            u32_from_le_u8(slice_as_array_ref!(&key.bytes[16..20], 4).unwrap()),
            u32_from_le_u8(slice_as_array_ref!(&key.bytes[20..24], 4).unwrap()),
            u32_from_le_u8(slice_as_array_ref!(&key.bytes[24..28], 4).unwrap()),
            u32_from_le_u8(slice_as_array_ref!(&key.bytes[28..32], 4).unwrap()),
        ];
        ctx
    }

    pub fn update(&mut self, mut input: &[u8]) {
        let mut block_state = AlignedBlockState::new(&mut self.opaque);
        let block_state_buf = block_state.aligned_buf();

        if self.buf_used != 0 {
            let todo = core::cmp::min(input.len(), BLOCK_LEN - self.buf_used);

            self.buf[self.buf_used .. self.buf_used + todo].copy_from_slice(&input[..todo]);
            self.buf_used += todo;
            input = &input[todo..];

            if self.buf_used == BLOCK_LEN {
                self.func.blocks(block_state_buf, &mut self.buf, 1 /* pad */);
                self.buf_used = 0;
            }
        }

        if input.len() >= BLOCK_LEN {
            let todo = input.len() & !(BLOCK_LEN - 1);
            let (complete_blocks, remainder) = input.split_at(todo);
            self.func.blocks(block_state_buf, complete_blocks, 1 /* pad */);
            input = remainder;
        }

        if input.len() != 0 {
            self.buf[..input.len()].copy_from_slice(input);
            self.buf_used = input.len();
        }
    }

    pub fn sign(mut self, tag_out: &mut Tag) {
        let mut block_state = AlignedBlockState::new(&mut self.opaque);
        let block_state_buf = block_state.aligned_buf();

        if self.buf_used != 0 {
            self.buf[self.buf_used] = 1;
            for byte in &mut self.buf[self.buf_used+1..] {
                *byte = 0;
            }
            self.func.blocks(block_state_buf, &self.buf[..], 0 /* already padded */);
        }

        self.func.emit(block_state_buf, tag_out, &self.nonce);
    }
}

pub fn verify(key: Key, msg: &[u8], tag: &Tag)
              -> Result<(), error::Unspecified> {
    let mut calculated_tag = [0u8; TAG_LEN];
    sign(key, msg, &mut calculated_tag);
    constant_time::verify_slices_are_equal(&calculated_tag[..], tag)
}

pub fn sign(key: Key, msg: &[u8], tag: &mut Tag) {
    let mut ctx = SigningContext::from_key(key);
    ctx.update(msg);
    ctx.sign(tag)
}

#[inline]
fn check_block_state_layout() {
    let required_block_state_size =
        if cfg!(target_arch = "x86") {
            // See comment above |_poly1305_init_sse2| in poly1305-x86.pl.
            Some(4 * (5 + 1 + 4 + 2 + 4 * 9))
        } else if cfg!(target_arch = "x86_64") {
            // See comment above |__poly1305_block| in poly1305-x86_64.pl.
            Some(4 * (5 + 1 + 2 * 2 + 2 + 4 * 9))
        } else {
            // TODO(davidben): Figure out the layout of the struct. For now,
            // |POLY1305_BLOCK_STATE_SIZE| is taken from OpenSSL.
            None
        };

    if let Some(required_block_state_size) = required_block_state_size {
        assert!(core::mem::size_of::<BlockState>() >= required_block_state_size);
    }
    
    if false {
        sillytest();
    }
}

/// A Poly1305 key.
pub struct Key {
    bytes: KeyBytes,
}

impl Key {
    pub fn derive_using_chacha(chacha20_key: &chacha::Key,
                               counter: &chacha::Counter) -> Key {
        let mut bytes = [0u8; KEY_LEN];
        chacha::chacha20_xor_in_place(chacha20_key, counter, &mut bytes);
        Key { bytes: bytes }
    }

    #[cfg(test)]
    pub fn from_test_vector(bytes: &[u8; KEY_LEN]) -> Key {
        Key { bytes: *bytes }
    }
}

type KeyBytes = [u8; KEY_LEN];

/// The length of a `key`.
pub const KEY_LEN: usize = 32;

/// A Poly1305 tag.
pub type Tag = [u8; TAG_LEN];

/// The length of a `Tag`.
pub const TAG_LEN: usize = 128 / 8;

const BLOCK_STATE_SIZE: usize = 192;

const BLOCK_LEN: usize = 16;

/// The memory manipulated by the assembly. Using u64s ensures 8-byte alignment,
/// which some of the assembly implementations need.
pub type BlockState = [u8; BLOCK_STATE_SIZE];

#[repr(C)]
struct Funcs {
    blocks_fn: unsafe extern fn(*mut BlockState, *const u8, c::size_t, u32), 
    emit_fn: unsafe extern fn(*mut BlockState, *mut Tag, *const [u32; 4]),
}

fn init(state: &mut BlockState, key: &KeyBytes, func: *mut Funcs) -> i32 {
    unsafe {
        GFp_poly1305_init_asm(state, key, func)
    }
}

impl Funcs {
    #[inline]
    fn blocks(&self, state: &mut BlockState, data: &[u8], should_pad: u32) {
        println!("opaque(pre) = {:?}", state.to_vec());
        println!("data[0..{}] = {:?}", data.len(), data.to_vec());
        unsafe {
            (self.blocks_fn)(state, data.as_ptr(), data.len(), should_pad)
        };
        println!("opaque(post) = {:?}", state.to_vec());
    }

    #[inline]
    fn emit(&self, state: &mut BlockState, tag: &mut Tag, nonce: &[u32; 4]) {
        unsafe {
             (self.emit_fn)(state, tag, nonce);
        }
    }
}

pub struct SigningContext {
    opaque: BlockState,
    nonce: [u32; 4],
    buf: [u8; BLOCK_LEN],
    buf_used: usize,
    func: Funcs
}

extern "C" {
    fn GFp_poly1305_init_asm(state: *mut BlockState, key: *const KeyBytes, out_func: *mut Funcs) -> c::int;
    fn GFp_poly1305_blocks(state: *mut BlockState, input: *const u8, len: c::size_t, padbit: u32);
    fn GFp_poly1305_emit(state: *mut BlockState, mac: *mut Tag, nonce: *const [u32; 4]);
}

pub fn sillytest() {
    unsafe {
        let mut opaque = [10u8; BLOCK_STATE_SIZE];
        let mut opaque_aligned = AlignedBlockState::new(&mut opaque);
        let xs = [1u8; 60];
        GFp_poly1305_blocks(opaque_aligned.aligned_buf(), xs.as_ptr(), xs.len(), 1);
        panic!("state = {:?}", opaque_aligned.aligned_buf().to_vec());
    }
}

#[cfg(test)]
mod tests {
    use {error, test};
    use core;
    use super::*;

    #[test]
    pub fn silly() {
        sillytest();
    }

    // Adapted from BoringSSL's crypto/poly1305/poly1305_test.cc.
    #[test]
    pub fn test_poly1305() {
        test::from_file("src/poly1305_test.txt", |section, test_case| {
            assert_eq!(section, "");
            let key = test_case.consume_bytes("Key");
            let key = slice_as_array_ref!(&key, KEY_LEN).unwrap();
            let input = test_case.consume_bytes("Input");
            let expected_mac = test_case.consume_bytes("MAC");
            let expected_mac =
                slice_as_array_ref!(&expected_mac, TAG_LEN).unwrap();

            // Test single-shot operation.
            {
                let key = Key::from_test_vector(&key);
                let mut ctx = SigningContext::from_key(key);
                ctx.update(&input);
                let mut actual_mac = [0; TAG_LEN];
                ctx.sign(&mut actual_mac);
                assert_eq!(&expected_mac[..], &actual_mac[..]);
            }
            if true { panic!("see"); }
            {
                let key = Key::from_test_vector(&key);
                let mut actual_mac = [0; TAG_LEN];
                sign(key, &input, &mut actual_mac);
                assert_eq!(&expected_mac[..], &actual_mac[..]);
            }
            {
                let key = Key::from_test_vector(&key);
                assert_eq!(Ok(()), verify(key, &input, &expected_mac));
            }

            // Test streaming byte-by-byte.
            {
                let key = Key::from_test_vector(&key);
                let mut ctx = SigningContext::from_key(key);
                for chunk in input.chunks(1) {
                    ctx.update(chunk);
                }
                let mut actual_mac = [0u8; TAG_LEN];
                ctx.sign(&mut actual_mac);
                assert_eq!(&expected_mac[..], &actual_mac[..]);
            }

            try!(test_poly1305_simd(0, key, &input, expected_mac));
            try!(test_poly1305_simd(16, key, &input, expected_mac));
            try!(test_poly1305_simd(32, key, &input, expected_mac));
            try!(test_poly1305_simd(48, key, &input, expected_mac));

            Ok(())
        })
    }

    fn test_poly1305_simd(excess: usize, key: &[u8; KEY_LEN], input: &[u8],
                          expected_mac: &[u8; TAG_LEN])
                          -> Result<(), error::Unspecified> {
        let key = Key::from_test_vector(&key);
        let mut ctx = SigningContext::from_key(key);

        // Some implementations begin in non-SIMD mode and upgrade on demand.
        // Stress the upgrade path.
        let init = core::cmp::min(input.len(), 16);
        ctx.update(&input[..init]);

        let long_chunk_len = 128 + excess;
        for chunk in input[init..].chunks(long_chunk_len + excess) {
            if chunk.len() > long_chunk_len {
                let (long, short) = chunk.split_at(long_chunk_len);

                // Feed 128 + |excess| bytes to test SIMD mode.
                ctx.update(long);

                // Feed |excess| bytes to ensure SIMD mode can handle short
                // inputs.
                ctx.update(short);
            } else {
                // Handle the last chunk.
                ctx.update(chunk);
            }
        }

        let mut actual_mac = [0u8; TAG_LEN];
        ctx.sign(&mut actual_mac);
        assert_eq!(&expected_mac[..], &actual_mac);

        Ok(())
    }
}
