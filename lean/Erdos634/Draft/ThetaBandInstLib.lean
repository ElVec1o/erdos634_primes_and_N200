-- Draft/ThetaBandInstLib.lean -- instances of Theorem B (`thetaTiled_band`): decidable hypothesis bundle and the two instantiation lemmas.
-- INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.  No sorry, no native_decide.
/-
`BandCond` is the conjunction of the hypotheses of `ThetaNotch.thetaTiled_band` (module `ThetaOddEBand`) and of `N = b t^2`; it is decidable, so each
instance `TileCount N` is `tcB .. (by decide)`.  `tcHub` gives `TileCount (b (b + f^2))` (the hub value `alpha_1`) from a band instance at `t = f`
through the existing hub gluing `ThetaNotch.alphaTiled_of_thetaTiled` (`ThetaTiled e f b (g f) -> AlphaTiled e f b g`, here `g = 1`).
Credit: Theorem B is the AI assistant's (RESULT.md S2); the notch is the project's (Bonfioli); the hub gluing is Beeson's (arXiv:1206.2229 Cor. 8) and Paliy's.
INTERNAL BUILD ONLY, UNAUDITED beyond internal checks.
-/
import Erdos634.Draft.ThetaOddEBand
import Erdos634.Draft.ThetaNotch4Glue
import Erdos634.Draft.TileCountFamilies

namespace Erdos634.Draft.ThetaBandInst
open Erdos634.Draft.ThetaUnit (ThetaTiled)
open Erdos634.Draft.ThetaNotch (thetaTiled_band alphaTiled_of_thetaTiled)
open Erdos634.Draft.TileCountFamilies (TileCount)

def BandCond (e f n M k s x r m N : ℕ) : Prop :=
  1 ≤ e ∧ e < f ∧ 1 ≤ n ∧ e ≤ (f - e) * n ∧ f * n ≤ e * M ∧ 0 < k ∧ k < s ∧ s < M + k ∧ e + (f - e) * k ≤ (f - e) * s ∧
  e * n + s * f ≤ (M + k) * f ∧ e ∣ M + k - s ∧
  e * (k * (f * f - e * e)) = e * (e * n * f) + (x * (e * f) + r * (f * f - e * e) + m * (f * f)) ∧ ¬ f ∣ e * M ∧
  N = (f * f - e * e) * (M + k) * (M + k)

instance (e f n M k s x r m N : ℕ) : Decidable (BandCond e f n M k s x r m N) := by unfold BandCond; infer_instance

theorem ttB (e f n M k s x r m N : ℕ) (h : BandCond e f n M k s x r m N) : ThetaTiled e f (f * f - e * e) (M + k) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, -⟩ := h
  exact thetaTiled_band e f n M k s x r m h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13

theorem tcB (e f n M k s x r m N : ℕ) (h : BandCond e f n M k s x r m N) : TileCount N := by
  have hN := h.2.2.2.2.2.2.2.2.2.2.2.2.2
  obtain ⟨D, -, -⟩ := ttB e f n M k s x r m N h
  rw [hN]; exact ⟨D⟩

/-- the hub value `alpha_1 = b (b + f^2)` from a band instance at `t = f` -/
theorem tcHub (e f n M k s x r m aN : ℕ) (h : BandCond e f n M k s x r m ((f * f - e * e) * (M + k) * (M + k)))
    (hf : M + k = f) (haN : aN = (f * f - e * e) * ((f * f - e * e) + f * f) * 1 * 1) : TileCount aN := by
  have hee : e * e ≤ f * f := Nat.mul_self_le_mul_self h.2.1.le
  have hT := ttB e f n M k s x r m _ h
  rw [hf] at hT
  have hb : f * f = e * e + (f * f - e * e) := by omega
  obtain ⟨D, -, -⟩ := alphaTiled_of_thetaTiled e f (f * f - e * e) 1 h.1 h.2.1 hb le_rfl (by rw [one_mul]; exact hT)
  rw [haN]; exact ⟨D⟩

end Erdos634.Draft.ThetaBandInst
