//! certgenm: exact replay of a float search tree (rust/mrv2 hints) into a `Refl.CheckM` certificate.
//! Usage: certgenm <NAME> <Dn> "<target x,y; x,y; x,y>" "<a b c>" <hints.tree> <outdir> [piece_cap] [module_nodes]
//! Target/points are in the rescaled coordinates (X, Y) meaning the real point (X, Y*sqrt(Dn)).
mod geo;
mod int;
mod mgen;
mod rat;
fn main() {
    let a: Vec<String> = std::env::args().collect();
    if a.len() < 7 { eprintln!("usage: certgenm NAME Dn TARGET SIDES HINTS OUTDIR [piece_cap] [module_nodes]"); std::process::exit(2); }
    let cap: usize = a.get(7).map(|x| x.parse().unwrap()).unwrap_or(150);
    let modn: usize = a.get(8).map(|x| x.parse().unwrap()).unwrap_or(1200);
    let args = (a[1].clone(), a[2].clone(), a[3].clone(), a[4].clone(), a[5].clone(), a[6].clone());
    std::thread::Builder::new().stack_size(1 << 30).spawn(move || mgen::run(&args.0, &args.1, &args.2, &args.3, &args.4, &args.5, cap, modn)).unwrap().join().unwrap();
}
