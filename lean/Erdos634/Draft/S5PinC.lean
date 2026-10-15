/-
Draft/S5PinC.lean -- a side between two corners `α + β` carries at least two `c`-edges.

* `collision`: the apex `G` of a tile cannot be straddled from the far side of BOTH of its upper edges (two tiles through
  `G` along different lines, plus the tile's own corner at `G`, exceed `2π`).
* `no_single_c`: a side of the target between two corners `α + β` does not carry exactly one `c`-edge
  (`apex_straddled` from each end, then `collision`).
* `base_two_c`: the walk equation of such a side with `R ≥ 2`.

Hypotheses are those of `Ctx` (tile angles `α, β, γ = 2α + β`, `3α + 2β = π`, `α/π` irrational; `a`, `b` not words of
two or more tile sides).  No sorry, no native_decide.
-/
import Erdos634.Draft.S5PinB

open scoped Classical
open Erdos634.Geometry Erdos634.TilePlacement Erdos634.Placement Erdos634.GLI Erdos634.BaseChain
  Erdos634.SideWall Erdos634.Draft.TraceCovering Erdos634.OrientBridge Erdos634.ChainInstance Set

namespace Erdos634.Draft.S5Pin

variable {N : ℕ}

/-- **Collision at the apex.** -/
theorem collision (D : Dissection N) (i : Fin N) (kW kE kG : Fin 3) (hWE : kW ≠ kE) (hWG : kW ≠ kG)
    (hEG : kE ≠ kG) (hpos : 0 < (D.tile i).localAngle ((D.tile i).pts kG))
    (h1 : Straddled D ((D.tile i).basis.coord kE).linear (-((D.tile i).basis.coord kE 0)) ((D.tile i).pts kG))
    (h2 : Straddled D ((D.tile i).basis.coord kW).linear (-((D.tile i).basis.coord kW 0)) ((D.tile i).pts kG)) :
    False := by
  obtain ⟨e1, he1, hG1⟩ := h1
  obtain ⟨e2, he2, hG2⟩ := h2
  obtain ⟨-, -, hall1⟩ := Dissection.mem_lineChain.mp he1
  obtain ⟨p2, q2, hall2⟩ := Dissection.mem_lineChain.mp he2
  have hc1 : ∀ m, (D.tile i).basis.coord kE ((D.tile e1.1).pts m) ≤ 0 := by
    intro m
    have := hall1 m
    rw [aff_apply ((D.tile i).basis.coord kE)]
    linarith
  have hc2 : ∀ m, (D.tile i).basis.coord kW ((D.tile e2.1).pts m) ≤ 0 := by
    intro m
    have := hall2 m
    rw [aff_apply ((D.tile i).basis.coord kW)]
    linarith
  have hne1 : e1.1 ≠ i := by
    intro h
    have := hc1 kE
    rw [h, Erdos634.Draft.NearBaseVertex.coord_self] at this
    linarith
  have hne2 : e2.1 ≠ i := by
    intro h
    have := hc2 kW
    rw [h, Erdos634.Draft.NearBaseVertex.coord_self] at this
    linarith
  have hπ1 : (D.tile e1.1).localAngle ((D.tile i).pts kG) = Real.pi := by
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile e1.1) (e1.2 + 2)
    rw [(fin3_shift e1.2).2.1, (fin3_shift e1.2).2.2.1]
    exact hG1
  have hπ2 : (D.tile e2.1).localAngle ((D.tile i).pts kG) = Real.pi := by
    apply Erdos634.RouteOne.openSegment_localAngle_pi (D.tile e2.1) (e2.2 + 2)
    rw [(fin3_shift e2.2).2.1, (fin3_shift e2.2).2.2.1]
    exact hG2
  have hne12 : e1.1 ≠ e2.1 := by
    intro h
    obtain ⟨s, t, hs, ht, -, hco⟩ := coord_openSegment (D.tile i) kE hG2
    have hGE : (D.tile i).basis.coord kE ((D.tile i).pts kG) = 0 :=
      Erdos634.Draft.NearBaseVertex.coord_other (D.tile i) hEG
    have ha : (D.tile i).basis.coord kE ((D.tile e2.1).pts e2.2) ≤ 0 := by rw [← h]; exact hc1 _
    have hb : (D.tile i).basis.coord kE ((D.tile e2.1).pts (e2.2 + 1)) ≤ 0 := by rw [← h]; exact hc1 _
    rw [hGE] at hco
    have ha0 : (D.tile i).basis.coord kE ((D.tile e2.1).pts e2.2) = 0 := by
      by_contra hne
      have hlt : (D.tile i).basis.coord kE ((D.tile e2.1).pts e2.2) < 0 := lt_of_le_of_ne ha hne
      have h3 := mul_neg_of_pos_of_neg hs hlt
      have h4 := mul_nonpos_of_nonneg_of_nonpos ht.le hb
      linarith
    have hb0 : (D.tile i).basis.coord kE ((D.tile e2.1).pts (e2.2 + 1)) = 0 := by
      by_contra hne
      have hlt : (D.tile i).basis.coord kE ((D.tile e2.1).pts (e2.2 + 1)) < 0 := lt_of_le_of_ne hb hne
      have h3 := mul_neg_of_pos_of_neg ht hlt
      have h4 := mul_nonpos_of_nonneg_of_nonpos hs.le ha
      linarith
    have hp2 : (D.tile i).basis.coord kW ((D.tile e2.1).pts e2.2) = 0 := by
      rw [aff_apply ((D.tile i).basis.coord kW)]; linarith
    have hq2 : (D.tile i).basis.coord kW ((D.tile e2.1).pts (e2.2 + 1)) = 0 := by
      rw [aff_apply ((D.tile i).basis.coord kW)]; linarith
    have hP : (D.tile e2.1).pts e2.2 = (D.tile i).pts kG := by
      apply eq_vertex_of_coords
      intro jj hjj
      rcases fin3_cover kW kE kG hWE hWG hEG jj with rfl | rfl | rfl
      · exact hp2
      · exact ha0
      · exact absurd rfl hjj
    have hQ : (D.tile e2.1).pts (e2.2 + 1) = (D.tile i).pts kG := by
      apply eq_vertex_of_coords
      intro jj hjj
      rcases fin3_cover kW kE kG hWE hWG hEG jj with rfl | rfl | rfl
      · exact hq2
      · exact hb0
      · exact absurd rfl hjj
    exact (fin3_ne e2.2).1 ((D.tile e2.1).indep.injective (hP.trans hQ.symm))
  have hsum := D.sum_localAngle_eq ((D.tile i).pts kG)
  have hle := localAngle_le_two_pi D.target ((D.tile i).pts kG)
  have htriple : (D.tile e1.1).localAngle ((D.tile i).pts kG) + (D.tile i).localAngle ((D.tile i).pts kG)
      + (D.tile e2.1).localAngle ((D.tile i).pts kG) ≤ ∑ m, (D.tile m).localAngle ((D.tile i).pts kG) := by
    have hsub : ({e1.1, i, e2.1} : Finset (Fin N)) ⊆ Finset.univ := Finset.subset_univ _
    have hle' : ∑ m ∈ ({e1.1, i, e2.1} : Finset (Fin N)), (D.tile m).localAngle ((D.tile i).pts kG)
        ≤ ∑ m, (D.tile m).localAngle ((D.tile i).pts kG) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun m _ _ => (D.tile m).localAngle_nonneg _)
    rw [Finset.sum_insert (by simp [hne1, hne12]), Finset.sum_insert (by simp [hne2.symm]),
      Finset.sum_singleton] at hle'
    linarith
  rw [hπ1, hπ2, hsum] at htriple
  linarith [Real.pi_pos]

/-- **Lemma C**: a side between two corners `α + β` does not carry exactly one `c`-edge. -/
theorem no_single_c {D : CongruentDissection N} {α β γ a b c : ℝ} (hN : 0 < N) (X : Ctx D α β γ a b c)
    (k : Fin 3)
    (hc0 : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α + β)
    (hc1 : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1)) (D.target.pts (k + 1 + 2)) = α + β)
    (p : Fin N × Fin 3) (hp : p ∈ wallList D.toDissection (wallFun D.target k) 0) (hpc : elen D p = c)
    (huniq : ∀ q ∈ wallList D.toDissection (wallFun D.target k) 0, elen D q = c → q = p) : False := by
  obtain ⟨E1, n1, Ch1⟩ := (Wall.fwd D.toDissection k).exists_chain hN
  obtain ⟨E2, n2, Ch2⟩ := (Wall.bwd D.toDissection k).exists_chain hN
  obtain ⟨j1, hj1, hE1⟩ := Ch1.surj p hp
  obtain ⟨j2, hj2, hE2⟩ := Ch2.surj p hp
  have hf1 : ∀ m, m < j1 → elen D (E1 m) ≠ c := by
    intro m hm hcm
    have h1 := huniq (E1 m) (Ch1.mem m (by omega)) hcm
    have h2 := Ch1.inj m j1 (by omega) hj1 (h1.trans hE1.symm)
    omega
  have hf2 : ∀ m, m < j2 → elen D (E2 m) ≠ c := by
    intro m hm hcm
    have h1 := huniq (E2 m) (Ch2.mem m (by omega)) hcm
    have h2 := Ch2.inj m j2 (by omega) hj2 (h1.trans hE2.symm)
    omega
  have hk := fin3_ne k
  obtain ⟨kW1, kE1, hcase1, hkW1, hS1⟩ := apex_straddled X (Wall.fwd D.toDissection k) Ch1 k (k + 1) (k + 2)
    hk.1 hk.2.1 hk.2.2 rfl rfl (fun _ => rfl) hc0 hj1 (by rw [hE1]; exact hpc) hf1
  obtain ⟨kW2, kE2, hcase2, hkW2, hS2⟩ := apex_straddled X (Wall.bwd D.toDissection k) Ch2 (k + 1) k (k + 2)
    hk.1.symm hk.2.2 hk.2.1 rfl rfl (fun _ => rfl) hc1 hj2 (by rw [hE2]; exact hpc) hf2
  have hnd1 := Ch1.nondeg j1 hj1
  rw [hE1] at hcase1 hkW1 hS1 hnd1
  rw [hE2] at hcase2 hkW2 hS2
  -- the two west ends are different vertices of the tile
  have hWne : kW1 ≠ kW2 := by
    intro heq
    have hA : (Wall.fwd D.toDissection k).dir ((D.tile p.1).pts kW1)
        = edgePos D.toDissection (Wall.fwd D.toDissection k).dir p := by
      rw [hkW1]; exact dir_edgeWest _ _ _
    have hB : (Wall.bwd D.toDissection k).dir ((D.tile p.1).pts kW1)
        = edgePos D.toDissection (Wall.bwd D.toDissection k).dir p := by
      rw [heq, hkW2]; exact dir_edgeWest _ _ _
    have hneg : ∀ y, (Wall.bwd D.toDissection k).dir y = -((Wall.fwd D.toDissection k).dir y) := fun _ => rfl
    simp only [edgePos, edgeEnd, hneg] at hA hB hnd1
    rw [min_neg_neg] at hB
    have hB' := neg_injective hB
    rw [hA] at hB'
    linarith
  have hpos : 0 < (D.tile p.1).localAngle ((D.tile p.1).pts (p.2 + 2)) := by
    have hlen : dist ((D.tile p.1).pts (p.2 + 2 + 1)) ((D.tile p.1).pts (p.2 + 2 + 2)) = c := by
      rw [(fin3_shift p.2).2.1, (fin3_shift p.2).2.2.1]; exact hpc
    rcases X.opp_of_angle p.1 (p.2 + 2) with ⟨h, -⟩ | ⟨h, -⟩ | ⟨h, -⟩
    · rw [h]; exact X.hA.hα
    · rw [h]; exact X.hA.hβ
    · rw [h]; exact X.gpos
  have hp2 := fin3_ne p.2
  rcases hcase1 with ⟨a1, b1⟩ | ⟨a1, b1⟩ <;> rcases hcase2 with ⟨a2, b2⟩ | ⟨a2, b2⟩
  · exact hWne (a1.trans a2.symm)
  · rw [b1] at hS1; rw [b2] at hS2
    exact collision D.toDissection p.1 p.2 (p.2 + 1) (p.2 + 2) hp2.1 hp2.2.1 hp2.2.2 hpos hS1 hS2
  · rw [b1] at hS1; rw [b2] at hS2
    exact collision D.toDissection p.1 (p.2 + 1) p.2 (p.2 + 2) hp2.1.symm hp2.2.2 hp2.2.1 hpos hS1 hS2
  · exact hWne (a1.trans a2.symm)

/-- **Theorem 2 (i)**: the walk equation of a side between two corners `α + β`, with at least two `c`-edges. -/
theorem base_two_c {D : CongruentDissection N} {α β γ a b c : ℝ} (hN : 0 < N) (X : Ctx D α β γ a b c)
    (k : Fin 3)
    (hc0 : cornerAngle (D.target.pts (k + 1)) (D.target.pts k) (D.target.pts (k + 2)) = α + β)
    (hc1 : cornerAngle (D.target.pts (k + 1 + 1)) (D.target.pts (k + 1)) (D.target.pts (k + 1 + 2)) = α + β) :
    ∃ P Q R : ℕ, 2 ≤ R ∧ dist (D.target.pts k) (D.target.pts (k + 1)) = P * a + Q * b + R * c := by
  obtain ⟨⟨hαβ, hαγ, hαπ, hα0, hβγ, hβπ, hβ0, hγπ, hγ0, hπ0⟩, -⟩ := Erdos634.CornerPara.angleFacts X.hA
  have hα := X.hA.hα
  have hβ := X.hA.hβ
  obtain ⟨E, n, Ch⟩ := (Wall.fwd D.toDissection k).exists_chain hN
  obtain ⟨x, y, -, hsum⟩ := sum_abc (Finset.range n) (fun m => elen D (E m)) a b c
    (fun m _ => X.len_cases _ _)
  -- the side length is the sum of the chain's edge lengths
  have hside : dist (D.target.pts k) (D.target.pts (k + 1)) = ∑ m ∈ Finset.range n, elen D (E m) := by
    have h1 := Ch.sum_len
    have h2 : ∑ m ∈ Finset.range n, elen D (E m)
        = ∑ m ∈ Finset.range n, (edgeEnd D.toDissection (Wall.fwd D.toDissection k).dir (E m)
          - edgePos D.toDissection (Wall.fwd D.toDissection k).dir (E m)) :=
      Finset.sum_congr rfl (fun m hm => Ch.dist_eq (Finset.mem_range.mp hm))
    have h3 := (Wall.fwd D.toDissection k).hiso (Wall.fwd D.toDissection k).a (Wall.fwd D.toDissection k).b
      ((Wall.fwd D.toDissection k).hline _ (left_mem_segment ℝ _ _))
      ((Wall.fwd D.toDissection k).hline _ (right_mem_segment ℝ _ _))
    have h4 := (Wall.fwd D.toDissection k).dir_lt
    rw [abs_of_neg (by linarith)] at h3
    rw [h2, h1]
    have h5 : dist (D.target.pts k) (D.target.pts (k + 1))
        = dist (Wall.fwd D.toDissection k).a (Wall.fwd D.toDissection k).b := rfl
    rw [h5, h3]; ring
  by_cases hz : 2 ≤ ((Finset.range n).filter (fun m => elen D (E m) = c)).card
  · exact ⟨x, y, _, hz, by rw [hside, hsum]⟩
  · exfalso
    -- the trap gives one `c`-edge; with fewer than two it is the only one
    obtain ⟨p0, hp0, hp0len⟩ := Erdos634.Geometry.Dissection.congruentDissection_gammatrap_lt hN D α β γ hαβ hαγ
      hαπ hα0 hβγ hβπ hβ0 hγπ hγ0 hπ0 X.hA.hγdef X.hA.hrel X.hA.hirr X.scalene X.hα' X.hβ' X.hγ' k
      (Wall.fwd D.toDissection k).dir (Wall.fwd D.toDissection k).hker (Wall.fwd D.toDissection k).hdirab
      (Wall.fwd D.toDissection k).hthird (by rw [hc0, X.hA.hγdef]; linarith)
      (by rw [hc1, X.hA.hγdef]; linarith)
    have hp0c : elen D p0 = c := by rw [← X.hs2]; exact hp0len
    obtain ⟨j0, hj0, hEj0⟩ := Ch.surj p0 hp0
    have hj0mem : j0 ∈ (Finset.range n).filter (fun m => elen D (E m) = c) := by
      rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hj0, by rw [hEj0]; exact hp0c⟩
    have hcard1 : ((Finset.range n).filter (fun m => elen D (E m) = c)).card ≤ 1 := by omega
    refine no_single_c hN X k hc0 hc1 p0 hp0 hp0c ?_
    intro q hq hqc
    obtain ⟨m, hm, hEm⟩ := Ch.surj q hq
    have hmmem : m ∈ (Finset.range n).filter (fun m => elen D (E m) = c) := by
      rw [Finset.mem_filter, Finset.mem_range]; exact ⟨hm, by rw [hEm]; exact hqc⟩
    have := Finset.card_le_one.mp hcard1 m hmmem j0 hj0mem
    rw [← hEm, this, hEj0]

end Erdos634.Draft.S5Pin

#print axioms Erdos634.Draft.S5Pin.collision
#print axioms Erdos634.Draft.S5Pin.no_single_c
#print axioms Erdos634.Draft.S5Pin.base_two_c
