import Erdos634.Refl.DataE120

/-! Refl/NegE120.lean -- non-vacuity negative controls for the GapE120 certificate (kernel-checked, `decide +kernel`):
    perturbed trees make the check return `false`.  (i) every edge-blocked node (`hb = (true,1)`, target edge 1)
    sent to edge 2 -- shows the new blocked kind is load-bearing and sensitive; (ii) every overlap witness shifted by
    +100; (iii) first Farkas multiplier of each first BSP bumped; (iv) top tree with an incomplete `known` list. -/

set_option maxRecDepth 100000
open Refl

def Node.flipEdge : Nat → Node → Node
  | 0, n => n
  | f + 1, n => { n with hb := if n.hb.base && n.hb.m == 1 then { n.hb with m := 2 } else n.hb,
                          children := n.children.map (Node.flipEdge f) }

def Node.shiftOvl : Nat → Node → Node
  | 0, n => n
  | f + 1, n => { n with
      kills := n.kills.map (fun k => match k with | .ovl m w => .ovl m ⟨w.x + 100 * w.w, w.y, w.w⟩ | k => k),
      children := n.children.map (Node.shiftOvl f) }

def Bsp.bump : Bsp → Bsp
  | .inf (m :: ms) => .inf ((m + 1) :: ms)
  | b => b
def Node.bumpT1 : Nat → Node → Node
  | 0, n => n
  | f + 1, n => { n with t1 := n.t1.bump, children := n.children.map (Node.bumpT1 f) }

-- the unperturbed chunks pass (RunE120); perturbed ones fail
theorem neg_edge_0 : checkNodeE instE120 400 chunkCfgE0 (Node.flipEdge 60 chunkE0) = false := by decide +kernel
theorem neg_edge_8 : checkNodeE instE120 400 chunkCfgE8 (Node.flipEdge 60 chunkE8) = false := by decide +kernel
theorem neg_edge_21 : checkNodeE instE120 400 chunkCfgE21 (Node.flipEdge 60 chunkE21) = false := by decide +kernel
theorem neg_ovl_1 : checkNodeE instE120 400 chunkCfgE1 (Node.shiftOvl 60 chunkE1) = false := by decide +kernel
theorem neg_ovl_10 : checkNodeE instE120 400 chunkCfgE10 (Node.shiftOvl 60 chunkE10) = false := by decide +kernel
theorem neg_bsp_19 : checkNodeE instE120 400 chunkCfgE19 (Node.bumpT1 60 chunkE19) = false := by decide +kernel
theorem neg_bsp_20 : checkNodeE instE120 400 chunkCfgE20 (Node.bumpT1 60 chunkE20) = false := by decide +kernel
-- the top tree with an incomplete list of known configurations
theorem neg_top_empty : instE120.checkAllR [] 400 treeE120 = false := by decide +kernel
theorem neg_top_partial : instE120.checkAllR (knownE120.drop 1) 400 treeE120 = false := by decide +kernel
-- a wrong configuration for a chunk
theorem neg_cfg : checkNodeE instE120 400 chunkCfgE1 chunkE0 = false := by decide +kernel
#print axioms neg_edge_0
#print axioms neg_top_partial
