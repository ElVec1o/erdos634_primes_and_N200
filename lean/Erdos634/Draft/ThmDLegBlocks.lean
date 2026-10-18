import Mathlib.Tactic
import Erdos634.Draft.ThmDGeoStop
import Erdos634.Draft.ThmDInterior

/-!
Credit: the method (rigidity window, Lemmas 30-34, row induction, Theorem 37) is adapted from M. Beeson and G. Rosu, 'Tiling a triangle into a prime number of congruent triangles' (preprint, 16 Oct 2026); the transfer to the tile with gamma = 2 alpha (fan lemma at straight points, windows u and v, Lemma K) is ours.

# Theorem D' (ThmDGeo, item (4)/(5)): blocks of a positioned leg at an arbitrary index  

`Brk S W f` : the breakpoints `f` of a positioned base leg with word `W` (`legseq` read in the frame `Q = (0,0)`, `B = (L,0)`).
`blk_cp` / `blk_cm` : a block of `n` consecutive `c>` (`c<`) edges at ANY index gives `UTT D u v 1 (f a * L) i 0` (resp. `UTT D u v (-1) (f b * L) i 0`),
the interior-start analogue of `hrun_start` / `hrun_end`.  `cp_stop` / `cm_stop` : the stop data `hVnv`, `hstop` of `lemma33_interior`.
-/

namespace Erdos634.Draft.ThmDRun

open Erdos634.Geometry Erdos634.CertCoord Erdos634.Draft.SideRun Erdos634.Draft.APrimeLegBuild
  Erdos634.Draft.APrimeSeat1 Erdos634.Draft.APrimeLeg Erdos634.MarchSlots Set

variable {N : ℕ} {D : CongruentDissection N} {u v : ℕ} {α β γ L ax ay : ℝ}

theorem lpT_base (u v ε x ξ : ℝ) : lpT u v ε x ξ 0 = mkPt (x + ε * (ξ * (u * v))) 0 := by
  unfold lpT; exact mkPt_congr (by ring) (by ring)

structure Brk (S : SetupT D u v α β γ L ax ay) (W : List OE) (f : ℕ → ℝ) : Prop where
  f0 : f 0 = 0
  fl : f W.length = 1
  step : ∀ idx (h : idx < W.length), ∃ (t' : Fin N) (j k : Fin 3), j ≠ k ∧
      (D.tile t').pts j = mkPt (f idx * L) 0 ∧ (D.tile t').pts k = mkPt (f (idx + 1) * L) 0 ∧
      (D.tile t').localAngle ((D.tile t').pts j) = angVal α (W[idx]'h).l ∧
      (D.tile t').localAngle ((D.tile t').pts k) = angVal α (W[idx]'h).r ∧
      (f (idx + 1) - f idx) * L = Erdos634.Draft.ThmD.wlen D.model (W[idx]'h)

theorem brk_of_leg (S : SetupT D u v α β γ L ax ay) {r : List (LegStep N)} {t : Fin N} {e : OE}
    (hRL : RealLeg D.toDissection α t e r)
    (hLP : LegPos D.toDissection D.model (mkPt 0 0) (mkPt L 0) t e 0 r)
    (hLE : LegEnd D.toDissection α (mkPt L 0) t e r)
    (hang : (D.tile t).localAngle (mkPt 0 0) = angVal α e.l) :
    ∃ f : ℕ → ℝ, Brk S (legEdges e r) f := by
  have hL := S.hL
  have hd : dist (mkPt 0 0) (mkPt L 0) = L := by
    have := Erdos634.MarchInduction.dist_mkPt_base 0 L hL.le
    simpa using this
  obtain ⟨f, hf0, hfl, hfi⟩ := legseq D.toDissection D.model α (mkPt 0 0) (mkPt L 0) r t e 0 hRL hLP hLE
    (by rw [AffineMap.lineMap_apply_zero]; exact hang)
  refine ⟨f, ⟨hf0, hfl, fun idx h => ?_⟩⟩
  obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, hw⟩ := hfi idx h
  refine ⟨t', j, k, hjk, ?_, ?_, hjang, hkang, ?_⟩
  · rw [hj, lineMap_base]
  · rw [hk, lineMap_base]
  · rw [← hw, hd]

namespace Brk

variable {S : SetupT D u v α β γ L ax ay} {W : List OE} {f : ℕ → ℝ}

theorem lt_succ (hB : Brk S W f) {idx : ℕ} (h : idx < W.length) : f idx < f (idx + 1) := by
  obtain ⟨t', j, k, -, -, -, -, -, hw⟩ := hB.step idx h
  have hp := wlen_pos S (W[idx]'h)
  have hL := S.hL
  rw [← hw] at hp
  by_contra hnot
  push Not at hnot
  nlinarith

theorem le_of_le (hB : Brk S W f) {i : ℕ} : ∀ k : ℕ, i + k ≤ W.length → f i ≤ f (i + k) := by
  intro k
  induction k with
  | zero => intro _; simp
  | succ k ih =>
    intro h
    have := hB.lt_succ (idx := i + k) (by omega)
    have := ih (by omega)
    rw [show i + (k + 1) = i + k + 1 by ring]
    linarith

theorem lt_of_lt (hB : Brk S W f) {i j : ℕ} (hij : i < j) (hj : j ≤ W.length) : f i < f j := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hij
  have h1 := hB.le_of_le (i := i + 1) k (by omega)
  have h2 := hB.lt_succ (idx := i) (by omega)
  have e : i + 1 + k = i + k + 1 := by ring
  rw [e] at h1
  exact lt_of_lt_of_le h2 h1

theorem nonneg (hB : Brk S W f) {i : ℕ} (hi : i ≤ W.length) : 0 ≤ f i := by
  have := hB.le_of_le (i := 0) i (by omega)
  simpa [hB.f0] using this

theorem le_one (hB : Brk S W f) {i : ℕ} (hi : i ≤ W.length) : f i ≤ 1 := by
  have := hB.le_of_le (i := i) (W.length - i) (by omega)
  rw [show i + (W.length - i) = W.length by omega, hB.fl] at this
  exact this

end Brk

theorem blk_cp (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {a n : ℕ}
    (han : a + n ≤ W.length) (hcp : ∀ j < n, W[a + j]? = some OE.cp) :
    (∀ j ≤ n, f (a + j) = f a + (j : ℝ) * ((u : ℝ) * v / L)) ∧
    ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) 1 (f a * L) (i : ℝ) 0 := by
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  have hget : ∀ j (hj : j < n), W[a + j]'(by omega) = OE.cp := by
    intro j hj
    have := hcp j hj
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  have hpos : ∀ j, j ≤ n → f (a + j) = f a + (j : ℝ) * ((u : ℝ) * v / L) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨t', j', k', -, -, -, -, -, hw⟩ := hB.step (a + j) (by omega)
      rw [hget j (by omega), wlen_cp_eq S OE.cp rfl] at hw
      have := ih (by omega)
      rw [show a + (j + 1) = a + j + 1 by ring]
      push_cast
      field_simp at this ⊢
      nlinarith
  refine ⟨hpos, ?_⟩
  refine hrun_of_tiles S (by norm_num) ?_
  intro i hi
  obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, -⟩ := hB.step (a + i) (by omega)
  rw [hget i hi] at hjang hkang
  refine ⟨t', j, k, hjk, ?_, ?_, ?_, ?_⟩
  · rw [hj, lpT_base, hpos i hi.le]
    congr 1; field_simp
  · rw [hk, lpT_base, show a + i + 1 = a + (i + 1) by ring, hpos (i + 1) hi]
    congr 1; push_cast; field_simp
  · rw [hjang]; simp [OE.l, angVal]
  · rw [hkang, S.hβ]; simp [OE.r, angVal]

theorem blk_cm (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {b n : ℕ}
    (hb : b ≤ W.length) (hn : n ≤ b) (hcm : ∀ j < n, W[b - 1 - j]? = some OE.cm) :
    (∀ j ≤ n, f (b - j) = f b - (j : ℝ) * ((u : ℝ) * v / L)) ∧
    ∀ i : ℕ, i < n → UTT D (u : ℝ) (v : ℝ) (-1) (f b * L) (i : ℝ) 0 := by
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  have hget : ∀ j (hj : j < n), W[b - 1 - j]'(by omega) = OE.cm := by
    intro j hj
    have := hcm j hj
    rw [List.getElem?_eq_getElem (by omega)] at this
    exact Option.some.inj this
  have hpos : ∀ j, j ≤ n → f (b - j) = f b - (j : ℝ) * ((u : ℝ) * v / L) := by
    intro j
    induction j with
    | zero => intro _; simp
    | succ j ih =>
      intro hj
      obtain ⟨t', j', k', -, -, -, -, -, hw⟩ := hB.step (b - 1 - j) (by omega)
      rw [hget j (by omega), wlen_cp_eq S OE.cm rfl] at hw
      have e1 : b - 1 - j + 1 = b - j := by omega
      have e2 : b - (j + 1) = b - 1 - j := by omega
      rw [e1] at hw
      rw [e2]
      have := ih (by omega)
      push_cast
      field_simp at this ⊢
      nlinarith
  refine ⟨hpos, ?_⟩
  refine hrun_of_tiles S (by norm_num) ?_
  intro i hi
  obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, -⟩ := hB.step (b - 1 - i) (by omega)
  rw [hget i hi] at hjang hkang
  have e1 : b - 1 - i + 1 = b - i := by omega
  rw [e1] at hk
  have p1 := hpos i hi.le
  have p2 := hpos (i + 1) hi
  have e2 : b - (i + 1) = b - 1 - i := by omega
  rw [e2] at p2
  refine ⟨t', k, j, hjk.symm, ?_, ?_, ?_, ?_⟩
  · rw [hk, p1, lpT_base]
    congr 1; push_cast; field_simp; ring
  · rw [hj, p2, lpT_base]
    congr 1; push_cast; field_simp; ring
  · rw [hkang]; simp [OE.r, angVal]
  · rw [hjang, S.hβ]; simp [OE.l, angVal]

#print axioms brk_of_leg
#print axioms blk_cp
#print axioms blk_cm
/-- the stop data of a `c>` block at the index `a`, length `n ≥ 1`: the next edge starts with `γ`, or the block reaches `B` -/
theorem cp_stop (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {a n : ℕ}
    (hn1 : 1 ≤ n) (han : a + n ≤ W.length) (hcp : ∀ j < n, W[a + j]? = some OE.cp)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : a + n = W.length ∨ ∃ o, W[a + n]? = some o ∧ o.l = Ang.ga) :
    ((∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧
        (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∉ Set.range D.target.pts) ∧
    (lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0) = γ) := by
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  obtain ⟨hpos, -⟩ := blk_cp S hB han hcp
  have hV : lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 = mkPt (f (a + n) * L) 0 := by
    rw [lpT_base, hpos n le_rfl]
    congr 1; field_simp
  rcases hstop with hall | ⟨o, ho, hol⟩
  · have hfl : f (a + n) = 1 := by rw [hall]; exact hB.fl
    have hVB : lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∈ Set.range D.target.pts := by
      refine ⟨1, ?_⟩
      rw [hV, hfl, (target_pts01 S).2.1]; simp
    refine ⟨?_, Or.inl hVB⟩
    rintro ⟨t', k, m, -, hk, -, -, hang⟩
    exact absurd hang (by
      have := hnoγ t' k (by rw [hk]; exact hVB)
      simpa [hk] using this)
  · have hlt : a + n < W.length := by
      by_contra h
      rw [List.getElem?_eq_none (by omega)] at ho
      exact absurd ho (by simp)
    have hgeto : W[a + n]'hlt = o := by
      rw [List.getElem?_eq_getElem hlt] at ho
      exact Option.some.inj ho
    obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, hw⟩ := hB.step (a + n) hlt
    rw [hgeto] at hjang
    have hvn : lpT (u : ℝ) (v : ℝ) 1 (f a * L) (n : ℝ) 0 ∉ Set.range D.target.pts := by
      rw [hV]
      have h1 : f 0 < f (a + n) := hB.lt_of_lt (by omega) (by omega)
      have h2 : f (a + n) < f (a + n + 1) := hB.lt_succ hlt
      have h3 : f (a + n + 1) ≤ 1 := hB.le_one (by omega)
      rw [hB.f0] at h1
      exact base_vertex_not S (by positivity) (by nlinarith)
    refine ⟨fun _ => hvn, Or.inr ⟨t', j, k, hjk, ?_, ?_, ?_, ?_⟩⟩
    · rw [hV]; exact hj
    · rw [hk, mkPt_one]
    · rw [hV, ← hj]; exact (D.tile t').indep.injective.ne hjk.symm
    · rw [hV, ← hj, hjang, hol, S.hγ]; simp [angVal]

/-- the stop data of a `c<` block ending at the index `b` (exclusive), length `n ≥ 1`: the edge before it ends with `γ`, or the block starts at `Q` -/
theorem cm_stop (S : SetupT D u v α β γ L ax ay) {W : List OE} {f : ℕ → ℝ} (hB : Brk S W f) {b n : ℕ}
    (hn1 : 1 ≤ n) (hb : b ≤ W.length) (hn : n ≤ b) (hcm : ∀ j < n, W[b - 1 - j]? = some OE.cm)
    (hnoγ : ∀ (t : Fin N) (k : Fin 3), (D.tile t).pts k ∈ Set.range D.target.pts →
      (D.tile t).localAngle ((D.tile t).pts k) ≠ γ)
    (hstop : n = b ∨ (n < b ∧ ∃ o, W[b - 1 - n]? = some o ∧ o.r = Ang.ga)) :
    ((∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧
        (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0) = γ) →
      lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∉ Set.range D.target.pts) ∧
    (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∈ Set.range D.target.pts ∨
      ∃ (t' : Fin N) (k m : Fin 3), k ≠ m ∧ (D.tile t').pts k = lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∧
        (D.tile t').pts m 1 = 0 ∧ (D.tile t').pts m ≠ lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∧
        (D.tile t').localAngle (lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0) = γ) := by
  have hL := S.hL
  have hLne : L ≠ 0 := hL.ne'
  obtain ⟨hpos, -⟩ := blk_cm S hB hb hn hcm
  have hV : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 = mkPt (f (b - n) * L) 0 := by
    rw [lpT_base, hpos n le_rfl]
    congr 1; field_simp; ring
  rcases hstop with hall | ⟨hnb, o, ho, hor⟩
  · have hf0 : f (b - n) = 0 := by rw [← hall, Nat.sub_self]; exact hB.f0
    have hVB : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∈ Set.range D.target.pts := by
      refine ⟨0, ?_⟩
      rw [hV, hf0, (target_pts01 S).1]; simp
    refine ⟨?_, Or.inl hVB⟩
    rintro ⟨t', k, m, -, hk, -, -, hang⟩
    exact absurd hang (by
      have := hnoγ t' k (by rw [hk]; exact hVB)
      simpa [hk] using this)
  · have hlt : b - 1 - n < W.length := by omega
    have hgeto : W[b - 1 - n]'hlt = o := by
      rw [List.getElem?_eq_getElem hlt] at ho
      exact Option.some.inj ho
    obtain ⟨t', j, k, hjk, hj, hk, hjang, hkang, hw⟩ := hB.step (b - 1 - n) hlt
    rw [hgeto] at hkang
    have e1 : b - 1 - n + 1 = b - n := by omega
    rw [e1] at hk
    have hvn : lpT (u : ℝ) (v : ℝ) (-1) (f b * L) (n : ℝ) 0 ∉ Set.range D.target.pts := by
      rw [hV]
      have h1 : f (b - 1 - n) < f (b - n) := by
        have := hB.lt_succ (idx := b - 1 - n) hlt
        rwa [e1] at this
      have h2 : f 0 ≤ f (b - 1 - n) := hB.le_of_le (i := 0) (b - 1 - n) (by omega) |> fun h => by simpa using h
      have h3 : f (b - n) < f b := hB.lt_of_lt (by omega) hb
      have h4 : f b ≤ 1 := hB.le_one hb
      rw [hB.f0] at h2
      exact base_vertex_not S (by nlinarith) (by nlinarith)
    refine ⟨fun _ => hvn, Or.inr ⟨t', k, j, hjk.symm, ?_, ?_, ?_, ?_⟩⟩
    · rw [hV]; exact hk
    · rw [hj, mkPt_one]
    · rw [hV, ← hk]; exact (D.tile t').indep.injective.ne hjk
    · rw [hV, ← hk, hkang, hor, S.hγ]; simp [angVal]

#print axioms cp_stop
#print axioms cm_stop

end Erdos634.Draft.ThmDRun
