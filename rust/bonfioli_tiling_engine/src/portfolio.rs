//! M4b: randomized portfolio.  One driver, <= 2 threads, over the (up to) 6 orientations of the target (3 cyclic x 2 mirror: the
//! assignment of the three target sides to the roles ga, gb, gc of `Target::from_sides`) x 3 arms {lex + random tie-break, band:K + random
//! tie-break, mrv la=1 + random tie-break}.  Each (orientation, arm) runs short Luby-scheduled slices (restart = new random order); ALL slices
//! of one orientation share ONE `S`, hence one nogood store (nogoods are sets of tile keys, valid under every order of the same instance).
//! Orientation o is owned by thread (o mod threads).  First verdict wins:
//!   FOUND      : the tiles are written and re-verified exactly (bte verify code) by the caller;
//!   NO_TILING  : only when a slice of ONE orientation finishes WITHOUT abort, i.e. that orientation's search tree was explored to
//!                completion (all orientations are equivalent problems, so one complete search suffices; the driver reports which).
use crate::field::*;
use crate::geom::*;
use crate::search::*;
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::time::{Duration, Instant};

pub struct PfCfg { pub seed: u64, pub unit: f64, pub ngcap: usize, pub tl: f64, pub threads: usize, pub arms: Vec<u8>, pub orient: Option<usize> }
pub struct PfOut { pub verdict: &'static str, pub orient: usize, pub arm: u8, pub slices: u64, pub calls: u64, pub nogoods: usize, pub tiles: Vec<[Pt; 3]>, pub tgt: Option<[Pt; 3]>, pub norient: usize, pub secs: f64, pub orient_desc: String }

fn luby(i: u64) -> u64 { let mut i = i; loop { let mut k = 1u64; while (1u64 << k) - 1 < i { k += 1; } if (1u64 << k) - 1 == i { return 1u64 << (k - 1); } i -= (1u64 << (k - 1)) - 1; } }
struct Rng(u64);
impl Rng { fn next(&mut self) -> u64 { self.0 ^= self.0 << 13; self.0 ^= self.0 >> 7; self.0 ^= self.0 << 17; self.0 } }

pub fn orientations(inst: &Instance) -> Vec<Instance> {
    let l = inst.target.len;
    let perms = [[0, 1, 2], [1, 2, 0], [2, 0, 1], [0, 2, 1], [2, 1, 0], [1, 0, 2]]; // 3 cyclic, then the 3 mirrored
    let mut out: Vec<Instance> = Vec::new();
    for p in perms.iter() {
        let t = Target::from_sides(l[p[0]], l[p[1]], l[p[2]], inst.spec.dd);
        if out.iter().any(|o| o.target.v == t.v) { continue; }
        out.push(Instance { spec: inst.spec.clone(), n: inst.n, target: t, name: format!("{}#{}{}{}", inst.name, p[0], p[1], p[2]), d_declared: inst.d_declared });
    }
    out
}

pub fn run(inst: &Instance, pc: &PfCfg) -> PfOut {
    let t0 = Instant::now();
    let stop = Arc::new(AtomicBool::new(false));
    let deadline = if pc.tl > 0.0 { Some(t0 + Duration::from_secs_f64(pc.tl)) } else { None };
    let norient = if pc.orient.is_some() { 1 } else { orientations(inst).len() };
    let res: Mutex<Option<PfOut>> = Mutex::new(None);
    let stats: Mutex<(u64, u64, usize)> = Mutex::new((0, 0, 0)); // slices, calls, nogoods
    let nth = pc.threads.max(1).min(2).min(norient);
    std::thread::scope(|sc| {
        for th in 0..nth {
            let (stop, res, stats) = (stop.clone(), &res, &stats);
            sc.spawn(move || {
                let mut insts = orientations(inst); if let Some(k) = pc.orient { let x = insts.remove(k.min(insts.len() - 1)); insts = vec![x]; }
                let mine: Vec<usize> = (0..insts.len()).filter(|i| i % nth == th).collect();
                let mut ss: Vec<S> = Vec::new();
                for &o in &mine {
                    let mut cfg = Cfg::default();
                    cfg.notree = true; cfg.ng = true; cfg.cbj = true; cfg.ngcap = pc.ngcap; cfg.report_secs = 1e9; cfg.seed = pc.seed.wrapping_mul(1315423911).wrapping_add(o as u64 * 97 + 1);
                    cfg.stop = Some(stop.clone()); cfg.deadline = deadline;
                    ss.push(S::new(&insts[o], cfg));
                }
                let roots: Vec<_> = ss.iter_mut().map(|s| s.root_opts()).collect();
                let mut rng = Rng((pc.seed.wrapping_mul(0x9E3779B97F4A7C15) ^ (th as u64 + 1).wrapping_mul(0xD1B54A32D192ED03)) | 1);
                for _ in 0..8 { rng.next(); }
                let maxside = *inst.spec.sides.iter().max().unwrap() as f64;
                let mut counter = vec![[0u64; 8]; mine.len()];
                let mut slices = 0u64;
                let finish = |ss: &Vec<S>, slices: u64| { let mut g = stats.lock().unwrap(); g.0 += slices; g.1 += ss.iter().map(|s| s.calls).sum::<u64>(); g.2 += ss.iter().map(|s| s.nogoods.len()).sum::<usize>(); };
                loop {
                    for oi in 0..mine.len() {
                        for &arm in &pc.arms {
                            let a = arm as usize;
                            counter[oi][a] += 1;
                            let secs = pc.unit * luby(counter[oi][a]) as f64;
                            let s = &mut ss[oi];
                            s.set_tb(rng.next()); s.set_shuffle(arm == 3);
                            match arm {
                                0 => { s.cfg.order = Order::Lex; s.cfg.la = 0; }
                                1 => { let k = [1.0, 2.0, 3.0][(rng.next() % 3) as usize]; s.cfg.order = Order::Band(k * maxside); s.cfg.la = 0; }
                                3 => { s.cfg.order = Order::Lex; s.cfg.la = 0; }
                                _ => { s.cfg.order = Order::Mrv; s.cfg.la = 1 }
                            }
                            slices += 1;
                            let v = s.run_slice(&roots[oi], 0, secs);
                            match v {
                                "FOUND" | "NO_TILING" => {
                                    let mut g = res.lock().unwrap();
                                    if g.is_none() {
                                        let d = format!("{}", insts[mine[oi]].name.rsplit('#').next().unwrap());
                                        *g = Some(PfOut { verdict: if v == "FOUND" { "FOUND" } else { "NO_TILING" }, orient: mine[oi], arm, slices: 0, calls: 0, nogoods: 0, tiles: if v == "FOUND" { s.found_tiles.clone() } else { vec![] }, tgt: Some(insts[mine[oi]].target.v), norient, secs: 0.0, orient_desc: d });
                                    }
                                    stop.store(true, Ordering::Relaxed);
                                    finish(&ss, slices); return;
                                }
                                "STOP" => { finish(&ss, slices); return; }
                                _ => {}
                            }
                            if stop.load(Ordering::Relaxed) { finish(&ss, slices); return; }
                        }
                    }
                }
            });
        }
    });
    let st = *stats.lock().unwrap();
    let mut o = res.into_inner().unwrap().unwrap_or(PfOut { verdict: "TIMEOUT", orient: 0, arm: 0, slices: 0, calls: 0, nogoods: 0, tiles: vec![], tgt: None, norient, secs: 0.0, orient_desc: String::new() });
    o.slices = st.0; o.calls = st.1; o.nogoods = st.2; o.secs = t0.elapsed().as_secs_f64(); o.norient = norient;
    o
}
