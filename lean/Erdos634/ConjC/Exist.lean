/-
ConjC/Exist.lean -- **the existence half of Conjecture C, unconditionally**: every `N` in `ConjCBase` is a tile count.

    theorem conjC_existence {N : ℕ} : ConjCBase N → TileCount N

Each family case cites an existing formal construction (see `ConjC.Defs` for the exact ranges):
F0 `TileCountFamilies` (Snover–Waiveris–Williams, Laczkovich); F1T the new count lemma `ConjC.BetaCount` on
`Residue.wTilable_ge` / `CollarG.beta_lift_real` (Paliy, seed Beeson); F1W `Residue.wTilable_ge` (Paliy);
F2 `S2All.s2_family_all` (Paliy's five-piece layout); F3a/F3b `F4All`, `PRevAll`, `F3All`, `PF3All`, `PF2All` (Paliy; Harries
for the 88 instance); F3c `ZhangProps.zhang_five` and F3d `EqSemigroup`, `Iso357Semigroup` (Zhang, arXiv:2512.22696;
seeds Paliy, Herdt); F4 `R84/R88/R143/R189TilingBridge` (Harries 88, Beeson); F5 `T<N>` (our template engine `bto`,
Laczkovich-type macro-dissections); F6 `HerdtFamily` (Herdt's 1125 template, uniformized by us); `k²` closure
`TileCountFamilies.tileCount_scale`.

This is NOT progress on the prime case or on the NO side of C: it only collects the proved constructions under one
statement.  Composite-N bookkeeping.  UNAUDITED.  No sorry.
-/
import Erdos634.ConjC.Defs
import Erdos634.ConjC.BetaCount
import Erdos634.Draft.TileCountFamilies
import Erdos634.Draft.S2All
import Erdos634.Draft.F4All
import Erdos634.Draft.F3All
import Erdos634.Draft.PRevAll
import Erdos634.Draft.PF2All
import Erdos634.Draft.PF3All
import Erdos634.Draft.ZhangProps
import Erdos634.Draft.EqSemigroup
import Erdos634.Draft.Iso357Semigroup
import Erdos634.R84TilingBridge
import Erdos634.R88TilingBridge
import Erdos634.R143TilingBridge
import Erdos634.R189TilingBridge
import Erdos634.Draft.T11625
import Erdos634.Draft.T66960
import Erdos634.Draft.T119040
import Erdos634.Draft.T121765
import Erdos634.Draft.T167865
import Erdos634.Draft.T186000
import Erdos634.Draft.T364560
import Erdos634.Draft.T603750
import Erdos634.Draft.HerdtFamily
import Erdos634.Draft.CollarUp

namespace Erdos634.ConjC.Exist
open Erdos634.ConjC Erdos634.Draft.TileCountFamilies

/-- every core is a tile count -/
theorem core_tileCount {n : ℕ} (h : ConjCCore n) : TileCount n := by
  rcases h with h | h | h | h | h | h | h | h | h | h | h | h
  · -- F0a
    rcases h with rfl | ⟨x, y, hx, hy, rfl⟩
    · exact tileCount_one
    · exact tileCount_two_squares x y hx hy
  · -- F0b
    rcases h with rfl | rfl
    · simpa using tileCount_three_sq (k := 1) one_pos
    · simpa using tileCount_six_sq (k := 1) one_pos
  · -- F1T
    obtain ⟨e, f, M, he, hef, hco, hM, rfl⟩ := h
    exact BetaCount.tileCount_beta_ge e f he hef hco M hM
  · -- F1W
    obtain ⟨e, f, M, he, hef, hco, hM, rfl⟩ := h
    obtain ⟨D, -⟩ := Erdos634.Draft.Residue.wTilable_ge e f he hef hco M hM
    exact ⟨D⟩
  · -- F2
    obtain ⟨p, q, hp, hpq, rfl⟩ := h
    exact Erdos634.Draft.S2All.s2_family_all p q hp hpq
  · -- F3a
    rcases h with ⟨a, b, c, ha, hab, hc, rfl⟩ | ⟨a, b, c, hb, hab, hc, ⟨A, B, s, hS⟩, rfl⟩
    · exact Erdos634.Draft.F4All.f4_family a b c ha hab hc
    · exact Erdos634.Draft.PRevAll.prev_family a b c hb hab hc A B s hS
  · -- F3b
    rcases h with ⟨a, b, c, ha, hab, hc, rfl⟩ | ⟨a, b, c, hb, hab, h2, hc, rfl⟩ |
      ⟨a, b, c, hb, hab, hc, ⟨A, B, s, hS⟩, rfl⟩
    · exact Erdos634.Draft.F3All.f3_family a b c ha hab hc
    · exact Erdos634.Draft.PF3All.pf3_family a b c hb hab h2 hc
    · exact Erdos634.Draft.PF2All.pf2_family a b c hb hab hc A B s hS
  · -- F3c
    obtain ⟨a, b, c, t0, m, ha, hb, hc, h0, hm, hN⟩ := h
    have Z := Erdos634.Draft.ZhangProps.zhang_five a b c t0 m ha hb hc h0 hm
    rcases hN with rfl | rfl | rfl | rfl | rfl
    · exact Z.1
    · exact Z.2.1
    · exact Z.2.2.1
    · exact Z.2.2.2.1
    · exact Z.2.2.2.2
  · -- F3d
    obtain ⟨m, hm, hm0, rfl | rfl⟩ := h
    · exact Erdos634.Draft.EqSemigroup.eq357_semigroup hm hm0
    · exact Erdos634.Draft.Iso357Semigroup.iso357_semigroup hm hm0
  · -- F4
    rcases h with rfl | rfl | rfl | rfl
    · exact Erdos634.R84TilingBridge.r84_nonempty_congruentDissection
    · exact Erdos634.R88TilingBridge.r88_nonempty_congruentDissection
    · exact Erdos634.R143TilingBridge.r143_nonempty_congruentDissection
    · exact Erdos634.R189TilingBridge.r189_nonempty_congruentDissection
  · -- F5
    rcases h with ⟨f, g, hf, hg, rfl⟩ | ⟨g, hg, rfl⟩ | rfl | rfl | rfl | rfl | rfl
    · exact Erdos634.Draft.CollarUp.tileCount_e1_up f g hf hg
    · rw [← mul_assoc]; exact Erdos634.Draft.CollarFam.tileCount_966_sq g hg
    · exact Erdos634.Draft.T66960.tileCount_66960
    · exact Erdos634.Draft.T119040.tileCount_119040
    · exact Erdos634.Draft.T167865.tileCount_167865
    · exact Erdos634.Draft.T186000.tileCount_186000
    · exact Erdos634.Draft.T364560.tileCount_364560
  · -- F6
    rcases h with rfl | rfl | rfl | ⟨u, v, b, τ, D, a1, n1, a2, n2, hu, huv, hv2, hτ, hD, ha1, hn1, ha2, hn2,
      hb, hE1, hE2, rfl⟩
    · exact Erdos634.Draft.HerdtFamily.tileCount_1125
    · exact Erdos634.Draft.HerdtFamily.tileCount_19600
    · exact Erdos634.Draft.HerdtFamily.tileCount_130977
    · exact Erdos634.Draft.HerdtFamily.herdt_family u v b τ D a1 n1 a2 n2 hu huv hv2 hτ hD ha1 hn1 ha2 hn2
        hb hE1 hE2

/-- **The existence half of Conjecture C** (unconditional): every `N` in `ConjCBase` is a tile count. -/
theorem conjC_existence {N : ℕ} (h : ConjCBase N) : TileCount N := by
  obtain ⟨k, n, hk, hn, rfl⟩ := h
  exact tileCount_scale (core_tileCount hn) hk

/-! ## Non-vacuity: concrete members -/

theorem conjCBase_143 : ConjCBase 143 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inl (Or.inr (Or.inr (Or.inl rfl))))

theorem conjCBase_11625 : ConjCBase 11625 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl (Or.inl ⟨4, 5, by norm_num, by norm_num, by norm_num⟩))

/-- F1T at `(e, f, M) = (1, 2, 3)`: `9 · 11 = 99`, a value NOT a multiple-of-`f` scale (new count lemma used). -/
theorem conjCBase_99 : ConjCBase 99 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inl ⟨1, 2, 3, le_rfl, by norm_num, by norm_num, by norm_num, by norm_num⟩)

theorem tileCount_99 : TileCount 99 := conjC_existence conjCBase_99

/-- F1W at `(1, 2, 2)`: `7 · 4 = 28`. -/
theorem conjCBase_28 : ConjCBase 28 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨1, 2, 2, le_rfl, by norm_num, by norm_num, le_rfl, by norm_num⟩)

/-- F2 at `(p, q) = (1, 2)`: `7 · 11 = 77`. -/
theorem conjCBase_77 : ConjCBase 77 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨1, 2, by norm_num, by norm_num, by norm_num⟩)

/-- F3d at `m = 4`: `33 · 16 = 528`. -/
theorem conjCBase_528 : ConjCBase 528 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl
    ⟨4, AddSubmonoid.subset_closure (by simp), by norm_num, Or.inr (by norm_num)⟩)

/-- F6: `1125` (Herdt), and the `k²` closure: `4 · 1125 = 4500`. -/
theorem conjCBase_4500 : ConjCBase 4500 :=
  ⟨2, 1125, by norm_num, Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inr (Or.inl rfl), by norm_num⟩

/-- F5 (e = 1 collar up-set), `f = 4, g = 6`: `465 · 36 = 16740`. -/
theorem conjCBase_16740 : ConjCBase 16740 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl (Or.inl ⟨4, 6, by norm_num, by norm_num, by norm_num⟩))

/-- F5, `f = 6, g = 8`: `2485 · 64 = 159040`. -/
theorem conjCBase_159040 : ConjCBase 159040 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl (Or.inl ⟨6, 8, by norm_num, by norm_num, by norm_num⟩))

/-- F5, `f = 2, g = 3`: `21 · 9 = 189`. -/
theorem conjCBase_189_F5 : ConjCBase 189 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl (Or.inl ⟨2, 3, by norm_num, by norm_num, by norm_num⟩))

/-- F5, row (2,5) tail: `966 · 25² = 603750`. -/
theorem conjCBase_603750 : ConjCBase 603750 :=
  conjCBase_of_core (Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <|
    Or.inr <| Or.inl (Or.inr (Or.inl ⟨25, le_rfl, by norm_num⟩)))

end Erdos634.ConjC.Exist
