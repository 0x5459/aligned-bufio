#![feature(read_buf)]
#![feature(can_vector)]
#![feature(maybe_uninit_slice)]
#![feature(new_uninit)]
#![feature(allocator_api)]
#![feature(vec_into_raw_parts)]

#[cfg(feature = "bufreader")]
mod bufreader;
#[cfg(feature = "bufwriter")]
mod bufwriter;

#[cfg(feature = "bufreader")]
pub use bufreader::BufReader;
#[cfg(feature = "bufwriter")]
pub use bufwriter::BufWriter;

use std::mem;

#[repr(C, align(4096))]
pub struct Aligned4096([u8; 4096]);

pub unsafe fn aligned_vec<Align>(n_bytes: usize) -> Vec<u8> {
    // Lazy math to ensure we always have enough.
    let n_units = (n_bytes / mem::size_of::<Align>()) + 1;

    let aligned: Vec<Align> = Vec::with_capacity(n_units);

    let (ptr, len_units, cap_units) = aligned.into_raw_parts();

    Vec::from_raw_parts(
        ptr as *mut u8,
        len_units * mem::size_of::<Align>(),
        cap_units * mem::size_of::<Align>(),
    )
}
