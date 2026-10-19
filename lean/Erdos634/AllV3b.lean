/-
AllV3b.lean -- aggregator for the modules added after `AllV3` in release v3.0.  Does NOT import `Erdos634.All`; no search certificate
`Refl.M*` in the import closure.  Build through `code/lakeone_at.sh` (modules one at a time).  Contents:
* `AllChain`        -- the chain (winding-number) lemma and the placement of the six-piece template of Theorem W (Draft/Chain*);
* `AllSplusThick`   -- the thick regime, no-tiling rung e+1: `W_M(e,f)` has no tiling when e >= 2, M < f, M e >= f, M (f-e) <= e+1;
* `AllSplusR2`      -- Theorem R2 (rung e+2): ARITHMETIC HALF and a CONDITIONAL corollary only (the geometric core `R2Count` is NOT in Lean);
* `CollarFam2`      -- 966 g^2 and 2485 g^2 are tile counts for every g >= 2;
* `AllS4Ext`        -- the S+ kill composed into the exclusion chain: `no_dissection_412`; `NSQMMainZETWD3W270`: `no_dissection_270`.
-/
import Erdos634.Draft.AllChain
import Erdos634.Draft.AllSplusThick
import Erdos634.Draft.AllSplusR2
import Erdos634.Draft.CollarFam2
import Erdos634.Draft.AllS4Ext
import Erdos634.Draft.NSQMMainZETWD3W270
