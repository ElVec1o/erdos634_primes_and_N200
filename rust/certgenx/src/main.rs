//! certgenx: exact replay of a float search tree (rust/mrv2 hints) into a `Refl.CheckN` certificate, STREAMING.
//! Same certificate format as rust/certgenm (which is kept unchanged: the manifest hashes of the existing certificates
//! are tied to it).  Differences:
//!   * bounded memory: only the float tree is held; exact geometry is recomputed along the current path and the Lean
//!     modules are written as the pieces are completed (certgenm keeps every exact node: about 7 KB per node);
//!   * the soundness glue is split into modules `M<NAME>SoundP<j>` of at most `sound_chunk` theorems
//!     (certgenm writes one file, 2 lines per node);
//!   * MIRROR mode (`CERTGENX_MIRROR=1`): the target `T0 T1 T2` has `|T0T1| = |T0T2|`, and the float tree was searched
//!     with only some of the live root placements (`MRV_ROOTSLOTS` of rust/mrv2).  A live root placement `t` without a
//!     subtree is refuted through its mirror image `t'` (`Refl.sound_mirror`): the configuration `[t']` gets a
//!     one-node refutation whose live placements must all be explored root placements.
//! Usage: certgenx <NAME> <Dn> "<target x,y; x,y; x,y>" "<a b c>" <hints.tree> <outdir> [piece_cap] [module_nodes] [sound_chunk]
//! Target/points are in the rescaled coordinates (X, Y) meaning the real point (X, Y*sqrt(Dn)).
mod geo;
mod int;
mod rat;
mod xgen;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 7 { eprintln!("usage: certgenx NAME Dn TARGET SIDES HINTS OUTDIR [piece_cap] [module_nodes] [sound_chunk]"); std::process::exit(2); }
    let cap: usize = a.get(7).map(|x| x.parse().unwrap()).unwrap_or(150);
    let modn: usize = a.get(8).map(|x| x.parse().unwrap()).unwrap_or(700);
    let schunk: usize = a.get(9).map(|x| x.parse().unwrap()).unwrap_or(4000);
    let mirror = std::env::var("CERTGENX_MIRROR").map(|v| v == "1").unwrap_or(false);
    let args = (a[1].clone(), a[2].clone(), a[3].clone(), a[4].clone(), a[5].clone(), a[6].clone());
    std::thread::Builder::new().stack_size(1 << 31).spawn(move || xgen::run(&args.0, &args.1, &args.2, &args.3, &args.4, &args.5, cap, modn, schunk, mirror)).unwrap().join().unwrap();
}
