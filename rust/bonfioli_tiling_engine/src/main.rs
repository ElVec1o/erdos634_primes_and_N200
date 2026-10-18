mod field; mod geom; mod verify; mod search; mod portfolio; mod macros;
use geom::*; use search::*;
use std::collections::HashMap;

pub fn write_tiling(inst: &Instance, tv: &[field::Pt; 3], tiles: &[[field::Pt; 3]], out: &str) {
    let mut o = format!("# {} tiles, each with sides ({},{},{}); target ({}, {}*sqrt({})), ({}, {}*sqrt({})), ({}, {}*sqrt({})); each line: X0 Y0 X1 Y1 X2 Y2, a vertex is the point (X, Y*sqrt({})); found by bonfioli_tiling_engine (exact)\n",
        tiles.len(), inst.spec.sides[0], inst.spec.sides[1], inst.spec.sides[2],
        tv[0].x, tv[0].y, inst.spec.dd, tv[1].x, tv[1].y, inst.spec.dd, tv[2].x, tv[2].y, inst.spec.dd, inst.spec.dd);
    for t in tiles { o.push_str(&format!("{} {} {} {} {} {}\n", t[0].x, t[0].y, t[1].x, t[1].y, t[2].x, t[2].y)); }
    std::fs::write(out, &o).unwrap();
}

fn usage() -> ! {
    eprintln!("usage:\n  bte verify FILE...                         exact verification of tilings (X0 Y0 X1 Y1 X2 Y2 per line; .gz and OBLIQUE supported)\n  bte FILE:<instance> search [options]       exhaustive tile-layer search (launch ONLY through code/guard_run.sh)\noptions: --order lex|mrv|band:K  --la N  --cbj 0|1  --cap CALLS  --tl SECS  --ng 0|1  --ngcap N  --notree\n         --tree PATH  --tiling PATH  --restart UNIT (Luby unit, main calls)  --stall K (frozen ticks)  --tick CALLS  --noperturb  --seed S\n         --progress PATH  --report SECS  --ck PATH (verdict-mode checkpoint)  --rootslots 0,1,..");
    std::process::exit(2)
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    if args.is_empty() { usage(); }
    if args[0] == "verify" {
        let mut all_ok = true;
        for f in &args[1..] {
            let t0 = std::time::Instant::now();
            let mut t = verify::load(f);
            let r = verify::verify(&mut t);
            let sd = (r.d as f64).sqrt();
            println!("{} tiles={} D={} congruent={} hull_is_triangle={} disjoint={} (bad pairs {}, pairs tested {}) area={} sides^2=({},{},{}) target=[{}] {:.1}s : {}",
                f, r.n, r.d, r.congruent, r.hull3, r.disjoint, r.bad_pairs, r.pairs_tested, r.area, r.sides2[0], r.sides2[1], r.sides2[2],
                r.target.iter().map(|p| format!("({}, {}*sqrt{})", p.x, p.y, r.d)).collect::<Vec<_>>().join(" "), t0.elapsed().as_secs_f64(), if r.ok() { "VERIFIED" } else { "FAILED" });
            let _ = sd;
            all_ok &= r.ok();
        }
        std::process::exit(if all_ok { 0 } else { 1 });
    }
    let mut inst_path: Option<String> = None; let mut opts: HashMap<String, String> = HashMap::new(); let mut flags: Vec<String> = Vec::new();
    let mut i = 0;
    while i < args.len() {
        let a = &args[i];
        if let Some(p) = a.strip_prefix("FILE:") { inst_path = Some(p.to_string()); }
        else if let Some(k) = a.strip_prefix("--") {
            if ["notree", "noperturb", "selfcheck", "sym", "wallgap"].contains(&k) { flags.push(k.to_string()); }
            else { i += 1; opts.insert(k.to_string(), args.get(i).cloned().unwrap_or_default()); }
        }
        i += 1;
    }
    let path = inst_path.unwrap_or_else(|| usage());
    let inst = parse_instance(&path);
    let g = |k: &str| opts.get(k).cloned();
    if args.iter().any(|a| a == "info") {
        let t = &inst.target; println!("INFO D={} target={};{};{} sides={} {} {}", inst.spec.dd, format!("{},{}", t.v[0].x, t.v[0].y), format!("{},{}", t.v[1].x, t.v[1].y), format!("{},{}", t.v[2].x, t.v[2].y), inst.spec.sides[0], inst.spec.sides[1], inst.spec.sides[2]);
        return;
    }
    if args.iter().any(|a| a == "portfolio") {
        let mut pc = portfolio::PfCfg { seed: g("seed").map_or(1, |x| x.parse().unwrap()), unit: g("unit").map_or(3.0, |x| x.parse().unwrap()), ngcap: g("ngcap").map_or(500_000, |x| x.parse().unwrap()), tl: g("tl").map_or(0.0, |x| x.parse().unwrap()), threads: g("threads").map_or(2, |x| x.parse().unwrap()), arms: vec![0, 1, 2], orient: g("orient").map(|x| x.parse().unwrap()) };
        if let Some(a) = g("arms") { pc.arms = a.split(',').map(|y| y.parse().unwrap()).collect(); }
        let o = portfolio::run(&inst, &pc);
        let mut extra = String::new();
        if o.verdict == "FOUND" {
            let out = g("tiling").unwrap_or_else(|| format!("{}.pf.found.txt", path));
            write_tiling(&inst, &o.tgt.unwrap(), &o.tiles, &out);
            let mut tl = verify::load(&out); let rep = verify::verify(&mut tl);
            extra = format!(" tiling={} exact_verify={}", out, if rep.ok() { "VERIFIED" } else { "FAILED" });
        }
        let sd = &inst.spec.sides;
        println!("bte-portfolio ({},{},{}) N={} seed={} threads={} unit_secs={} orientations={} verdict={} winner_orient={} winner_arm={} slices={} calls={} nogoods={} secs={:.1}{}{}",
            sd[0], sd[1], sd[2], inst.n, pc.seed, pc.threads, pc.unit, o.norient, o.verdict, o.orient_desc, ["lex","band","mrv-la1","lex-shuffle"][match o.arm { 0 => 0, 1 => 1, 3 => 3, _ => 2 }], o.slices, o.calls, o.nogoods, o.secs,
            if o.verdict == "NO_TILING" { " (complete exhaustive search of one orientation)" } else { "" }, extra);
        return;
    }
    if args.iter().any(|a| a == "macro") { macros::cli(&inst, &opts, &flags, &path); return; }
    let mut cfg = Cfg::default();
    cfg.order = match g("order").as_deref() { Some("lex") => Order::Lex, Some(s) if s.starts_with("band:") => Order::Band(s[5..].parse().unwrap()), _ => Order::Mrv };
    if let Some(x) = g("la") { cfg.la = x.parse().unwrap(); }
    if let Some(x) = g("cbj") { cfg.cbj = x == "1"; }
    if let Some(x) = g("cap") { cfg.cap = x.parse().unwrap(); }
    if let Some(x) = g("tl") { cfg.tl = x.parse().unwrap(); }
    if let Some(x) = g("ng") { cfg.ng = x == "1"; }
    if let Some(x) = g("ngcap") { cfg.ngcap = x.parse().unwrap(); }
    if let Some(x) = g("restart") { cfg.restart_unit = x.parse().unwrap(); }
    if let Some(x) = g("stall") { cfg.stall_ticks = x.parse().unwrap(); }
    if let Some(x) = g("tick") { cfg.tick = x.parse().unwrap(); }
    if let Some(x) = g("seed") { cfg.seed = x.parse().unwrap(); }
    if let Some(x) = g("report") { cfg.report_secs = x.parse().unwrap(); }
    if let Some(x) = g("sweep") { let w: Vec<i64> = x.split(',').map(|y| y.parse().unwrap()).collect(); cfg.sweep = Some((w[0], w[1])); }
    if let Some(x) = g("tb") { cfg.tb0 = x.parse::<u64>().unwrap() | 1; }
    if let Some(x) = g("pmode") { cfg.pmode = x; }
    if let Some(x) = g("rootslots") { cfg.mirror_slots = Some(x.split(',').map(|y| y.parse().unwrap()).collect()); }
    cfg.sym = flags.contains(&"sym".to_string());
    cfg.wallgap_on = flags.contains(&"wallgap".to_string());
    cfg.notree = flags.contains(&"notree".to_string()) || g("tree").is_none() || cfg.sym || cfg.wallgap_on;
    cfg.selfcheck = flags.contains(&"selfcheck".to_string());
    cfg.perturb = !flags.contains(&"noperturb".to_string());
    let order_name = g("order").unwrap_or("mrv".into());
    let mut s = S::new(&inst, cfg.clone());
    s.progpath = g("progress");
    if let Some(ck) = g("ck") { assert!(cfg.notree, "--ck needs verdict mode (no --tree)"); if s.load_ck(&ck) { eprintln!("checkpoint loaded: {} nogoods, calls={}", s.nogoods.len(), s.calls); } s.ck = Some(ck); }
    let t0 = std::time::Instant::now();
    let (r, verdict) = s.run();
    let secs = s.secs_prev + t0.elapsed().as_secs_f64();
    let mut extra = String::new();
    if let (Some(x), Some(path), false) = (r.as_ref(), g("tree"), cfg.notree) { let c = s.write_tree(&x.2, &path); extra = format!(" TREE={} CERT={}", x.0, c); }
    if verdict == "FOUND" {
        let mut o = format!("# {} tiles, each with sides ({},{},{}); target ({}, {}*sqrt({})), ({}, {}*sqrt({})), ({}, {}*sqrt({})); each line: X0 Y0 X1 Y1 X2 Y2, a vertex is the point (X, Y*sqrt({})); found by bonfioli_tiling_engine (exact)\n",
            s.found_tiles.len(), inst.spec.sides[0], inst.spec.sides[1], inst.spec.sides[2],
            inst.target.v[0].x, inst.target.v[0].y, inst.spec.dd, inst.target.v[1].x, inst.target.v[1].y, inst.spec.dd, inst.target.v[2].x, inst.target.v[2].y, inst.spec.dd, inst.spec.dd);
        for t in &s.found_tiles { o.push_str(&format!("{} {} {} {} {} {}\n", t[0].x, t[0].y, t[1].x, t[1].y, t[2].x, t[2].y)); }
        let out = g("tiling").unwrap_or_else(|| format!("{}.found.txt", path));
        std::fs::write(&out, &o).unwrap();
        let mut tl = verify::load(&out); let rep = verify::verify(&mut tl);
        extra = format!(" tiling={} exact_verify={}", out, if rep.ok() { "VERIFIED" } else { "FAILED" });
    }
    let sd = &inst.spec.sides; let tl = &inst.target.len;
    println!("bte ({},{},{}) in ({},{},{}) N={} order={} la={} cbj={} calls={} nodes={} jumps={} restarts={} stall={} luby={} nogoods={} hits={} verdict={} secs={:.1}{}{}{}",
        sd[0], sd[1], sd[2], tl[0], tl[1], tl[2], inst.n, order_name, s.cfg.la, s.cfg.cbj as u8, s.calls, s.nodes_total, s.jumps, s.restarts, s.stall_restarts, s.luby_restarts, s.nogoods.len(), s.ng_hits, verdict, secs, extra, format!("{}{}", if s.cfg.wallgap_on { format!(" wallgap_kills={}", s.wallgap_kills) } else { String::new() }, if s.cfg.sym { format!(" sym_skips={}", s.sym_skips) } else { String::new() }), if s.cfg.selfcheck { format!(" selfchecked_nodes={}", s.selfchecked) } else { String::new() });
    if let Some(ck) = &s.ck { if verdict != "TIMEOUT" { let _ = std::fs::remove_file(ck); } else { s.save_ck_pub(ck); } }
}
