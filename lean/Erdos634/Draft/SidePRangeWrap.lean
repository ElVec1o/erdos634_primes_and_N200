import Erdos634.SideWalk
import Erdos634.SidePRange

/-!
# Assembly of the corner-side range: wrapper

A corner tile laying `c` on the base
lays `a` on the side; that side's `a`-count `P'` is positive; quantization gives `P'=fp`,
so `1 ≤ p ≤ (f−1)/e`.

**What this file provides**: the assembly theorem `side_p_range_of_walk` that, given:
- The abstract walk setup hypotheses (dischargeable from `wallFun`/`dirFun` for any target)
- Two witnesses `p0` (model-0/a edge on the wall) and `p2` (model-2/c edge on the wall)
- Natural-number model side lengths (`ha`, `hb`, `hc`) and target side length (`hL`)
- Coprimality/size hypotheses

derives `∃ p, 1 ≤ p ∧ p ≤ (f - 1) / e`.

The two witnesses are the responsibility of the caller:
- `p0` (a-side witness) comes from the corner tile's forced a-edge on the side chain
- `p2` (c-side witness) comes from `GammaTrap.congruentDissection_gammatrap`

0 sorry, standard axioms.
-/

namespace Erdos634.Draft.SidePRangeWrap

open Erdos634.Geometry Erdos634.Placement Erdos634.TilePlacement Erdos634.WallEndpoints

/-- **Assembly for lem:ccornerside**.  Given the walk setup plus two witnesses for the a-count
and c-count positivity, derives the parameter bound `1 ≤ p ≤ (f-1)/e`. -/
theorem side_p_range_of_walk
    {N : ℕ} (D : CongruentDissection N)
    (g : Plane →ᵃ[ℝ] ℝ) (c : ℝ)
    (dir : Plane →ₗ[ℝ] ℝ)
    (hker : ∀ v : Plane, g.linear v = 0 → dir v = 0 → v = 0)
    (hwall : ∀ y ∈ D.target.carrier, g y ≤ c)
    (a b : Plane) (hab : a ≠ b) (hdirab : dir a ≤ dir b)
    (hbase : segment ℝ a b ⊆ frontier D.target.carrier)
    (hline : ∀ y ∈ segment ℝ a b, g y = c)
    (hface : ∀ y ∈ D.target.carrier, g y = c → y ∈ segment ℝ a b)
    (hthird : ∀ p ∈ Erdos634.BaseChain.wallList D.toDissection g c,
      g ((D.tile p.1).pts (p.2 + 2)) < c)
    (hiso : ∀ p q : Plane, g p = c → g q = c → dist p q = |dir p - dir q|)
    (hscalene : sideOpp D.model 0 ≠ sideOpp D.model 1 ∧ sideOpp D.model 0 ≠ sideOpp D.model 2 ∧
      sideOpp D.model 1 ≠ sideOpp D.model 2)
    (hN : 0 < N)
    -- a-side witness (from the corner tile's forced a-edge)
    (p0 : Fin N × Fin 3) (hp0 : p0 ∈ Erdos634.BaseChain.wallList D.toDissection g c)
    (hp0len : dist ((D.tile p0.1).pts p0.2) ((D.tile p0.1).pts (p0.2 + 1)) = sideOpp D.model 0)
    -- c-side witness (from the γ-trap)
    (p2 : Fin N × Fin 3) (hp2 : p2 ∈ Erdos634.BaseChain.wallList D.toDissection g c)
    (hp2len : dist ((D.tile p2.1).pts p2.2) ((D.tile p2.1).pts (p2.2 + 1)) = sideOpp D.model 2)
    -- natural-number model side lengths
    (e0 f0 b0 : ℕ) (he0 : 1 ≤ e0) (hef0 : e0 < f0)
    (hcop : Nat.Coprime e0 f0) (hb0 : b0 + e0 * e0 = f0 * f0)
    (ha : sideOpp D.model 0 = ((e0 * f0 : ℕ) : ℝ))
    (hbm : sideOpp D.model 1 = ((b0 : ℕ) : ℝ))
    (hcm : sideOpp D.model 2 = ((f0 * f0 : ℕ) : ℝ))
    (hL : dist a b = ((f0 * f0 * f0 : ℕ) : ℝ)) :
    ∃ p, 1 ≤ p ∧ p ≤ (f0 - 1) / e0 := by
  -- Step 1: get Pc, Qc, Rc in ℕ with 1 ≤ Pc, 1 ≤ Rc, and the real walk equation
  obtain ⟨Pc, Qc, Rc, hPc, hRc, heq⟩ := Erdos634.SideWalk.side_walk_pos02_of_dissection D g c dir
    hker hwall a b hab hdirab hbase hline hface hthird hiso hscalene hN p0 hp0 hp0len p2 hp2 hp2len
  -- Step 2: cast the real walk to ℕ
  have hwalk : Pc * (e0 * f0) + Qc * b0 + Rc * (f0 * f0) = f0 * f0 * f0 := by
    have hreal : (Pc : ℝ) * (e0 * f0) + (Qc : ℝ) * b0 + (Rc : ℝ) * (f0 * f0) = f0 * f0 * f0 := by
      rw [ha, hbm, hcm] at heq
      rw [hL] at heq
      push_cast at heq ⊢
      linarith
    exact_mod_cast hreal
  -- Step 3: apply side_p_range
  obtain ⟨p, _, hp1, hp2'⟩ := side_p_range hcop hef0 b0 hb0 hwalk hRc he0 (by omega)
  exact ⟨p, hp1, hp2'⟩

#print axioms side_p_range_of_walk

end Erdos634.Draft.SidePRangeWrap
