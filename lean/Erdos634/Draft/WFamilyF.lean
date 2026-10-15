-- The family theorem for general f, e = 1.
--
-- Results:
--   * W version (from `WAddF.WClosed_add`):  WClosed f m1 -> WClosed f m2 -> WClosed f (m1+m2),
--     hence closure under every positive N-combination of seeds (`W_comb`), i.e. if W_a and W_b tile,
--     then W_n tiles (by (2f²-1)n² tiles) for all n = x a + y b, x+y >= 1.
--   * Delta via W (`WtoDeltaF.delta_of_W`):  WClosed m1 -> WClosed m2 -> DeltaF (m1+m2),
--     and WClosed seeds -> DeltaF n for all positive combinations n.
-- Not proved here: `DeltaF m1 -> DeltaF m2 -> DeltaF (m1+m2)`.  Delta_{m1+m2} = Delta_{m1} U P U Delta_{m2}
--   with P an m1 x m2 grid of the parallelogram P_1 (thm:addlaw).  W cannot be recovered from Delta
--   (there is no Delta -> W map).
-- No base case: no `WClosed f hf m` is exhibited for any f in this frame.  At f = 2 the certified
--   seeds (WSeed.seed28/63) live in the 8x-larger frame `WFrame.Phi` with model `MW`; transport to
--   `WFrameF.Phi 2` / `MF 2` needs a homothety map on RTiling (only isometries are available).
--   Every theorem below is therefore conditional on a hypothesis that is not witnessed in this frame.
import Erdos634.Draft.WtoDeltaF

open scoped Classical
open Erdos634.Geometry
open Erdos634.Draft.CollarParam (RTiling.cast RTiling.castN)

namespace Erdos634.Draft.WFamilyF
open Erdos634.Draft.WAddF Erdos634.Draft.WtoDeltaF Erdos634.Draft.RegionTiling

/-- `Delta_m` admits a tiling by `(3f²-1)m²` copies of `MF f`. -/
def DeltaF (f : ℕ) (hf : 2 ≤ f) (m : ℕ) : Prop :=
  ∃ hm : 1 ≤ m, Nonempty (RTiling (DeltaTri f hf m hm).carrier
    (Erdos634.Draft.WBrickF.MF (f : ℝ) (Erdos634.Draft.WPgramF.hF f hf)) ((3 * f ^ 2 - 1) * m ^ 2))

/-- **L10 (W version).** -/
theorem W_family (f : ℕ) (hf : 2 ≤ f) {m₁ m₂ : ℕ} (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂)
    (H1 : WClosed f hf m₁) (H2 : WClosed f hf m₂) : WClosed f hf (m₁ + m₂) :=
  WClosed_add f hf h1 h2 H1 H2

/-- Multiples of a seed. -/
theorem W_mul (f : ℕ) (hf : 2 ≤ f) {a : ℕ} (ha : 1 ≤ a) (H : WClosed f hf a) :
    ∀ k : ℕ, 1 ≤ k → WClosed f hf (k * a) := by
  intro k hk
  induction k, hk using Nat.le_induction with
  | base => simpa using H
  | succ k hk ih =>
    have := W_family f hf (by nlinarith) ha ih H
    rwa [show (k + 1) * a = k * a + a by ring]

/-- Positive combinations of two seeds. -/
theorem W_comb (f : ℕ) (hf : 2 ≤ f) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (Ha : WClosed f hf a) (Hb : WClosed f hf b) (x y : ℕ) (hxy : 1 ≤ x + y) :
    WClosed f hf (x * a + y * b) := by
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have hy : 1 ≤ y := by omega
    simpa using W_mul f hf hb Hb y hy
  · rcases Nat.eq_zero_or_pos y with rfl | hy
    · simpa using W_mul f hf ha Ha x hx
    · exact W_family f hf (by nlinarith) (by nlinarith) (W_mul f hf ha Ha x hx) (W_mul f hf hb Hb y hy)

/-- **Delta via W.** -/
theorem delta_of_W' (f : ℕ) (hf : 2 ≤ f) {m : ℕ} (hm : 1 ≤ m) (H : WClosed f hf m) : DeltaF f hf m :=
  ⟨hm, delta_of_W f hf m hm H⟩

/-- Delta_{m1+m2} from W_{m1}, W_{m2} (mixed hypotheses; NOT `Delta -> Delta -> Delta`). -/
theorem delta_add_of_W (f : ℕ) (hf : 2 ≤ f) {m₁ m₂ : ℕ} (h1 : 1 ≤ m₁) (h2 : 1 ≤ m₂)
    (H1 : WClosed f hf m₁) (H2 : WClosed f hf m₂) : DeltaF f hf (m₁ + m₂) :=
  delta_of_W' f hf (by omega) (W_family f hf h1 h2 H1 H2)

/-- Delta_n for every positive combination of two W-seeds. -/
theorem delta_comb_of_W (f : ℕ) (hf : 2 ≤ f) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (Ha : WClosed f hf a) (Hb : WClosed f hf b) (x y : ℕ) (hxy : 1 ≤ x + y) :
    DeltaF f hf (x * a + y * b) := by
  refine delta_of_W' f hf ?_ (W_comb f hf ha hb Ha Hb x y hxy)
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · have : 1 ≤ y := by omega
    nlinarith
  · nlinarith

end Erdos634.Draft.WFamilyF

#print axioms Erdos634.Draft.WFamilyF.W_family
#print axioms Erdos634.Draft.WFamilyF.W_comb
#print axioms Erdos634.Draft.WFamilyF.delta_add_of_W
#print axioms Erdos634.Draft.WFamilyF.delta_comb_of_W
