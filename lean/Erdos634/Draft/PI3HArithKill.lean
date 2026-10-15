/-
Draft/PI3HArithKill.lean -- the arithmetic side of the strip kills and the level + T2 kills, by kernel `decide`.

`strip_kill_list`  : over the window, the pairs satisfying `stripDead` (exact integer predicate (I) + interval (II'))
                     are exactly those of N = 609, 2145, 6693.
`level_kill_list`  : the pairs with `levelKill` but not `stripDead` are exactly those of N = 285, 3315, 3621, 4047,
                     4503, 6555, 9483;  `level_stats_*` give the counts (U, #geom-dead, #level-dead, 0 alive, 0 ambiguous).
`pairKill_list`    : the window N all of whose (single) uncovered x-type pairs are killed: the ten N.
`excluded_*`       : with the FULL pair table (`pairs`, `pairCovered`): nine N (all but 2145) have NO uncovered pair.
`not_killed_2145`  : N = 2145: the x-type pair (165,39) is strip-killed, but the pair (143,45), D = 1024 = 32^2 a SQUARE, is covered by
                     NOTHING in this layer: `uncoveredPairs 2145 = [(143,45)]`, `excluded 2145 = false`.
Controls: N = 255 alive; N = 1440 (D square, even) not excluded; wrong predicates (`r s < 4N`, `r s < 16N`) give DIFFERENT strip lists; the
non-strict `<=` variant of (I) gives the SAME list (no equality case in the window); `levelDead`-only kills nothing.

On the window every strip-dead pair is also `levelKill` (all its odd levels are geometrically dead), so
the `levelKill` list is the full ten; the strip lemma only differs in the hypotheses it needs (an unbalanced chain, no level/coset).
This is the arithmetic side only: soundness of the `Int` interval layer w.r.t. reals is NOT proved here.
No sorry, no native_decide.
-/
import Erdos634.Draft.PI3HArithWindow

namespace Erdos634.Draft.PI3H

/-! ### Strip kills -/

theorem strip_kill_list :
    windowList.filter (fun N => (xList N).all fun x => stripDead N x) = [609, 2145, 6693] := by decide +kernel

theorem strip_609 : stripDead 609 7 = true := by decide +kernel
theorem strip_2145 : stripDead 2145 13 = true := by decide +kernel
theorem strip_6693 : stripDead 6693 23 = true := by decide +kernel

/-- (II') holds for ALL 52 window pairs (margin ratio >= 3.2 in the spec). -/
theorem stripII_all : windowList.all (fun N => (xList N).all fun x => stripII N (xdata N x)) = true := by decide +kernel

/-- the exact integer part (I) alone already selects the same three pairs. -/
theorem stripI_list :
    windowList.filter (fun N => (xList N).all fun x => stripI N (xdata N x)) = [609, 2145, 6693] := by decide +kernel

/-- the finest strip kill, N = 609: `r = 2N - l_kappa = 30`, `r s = 3240 < 8N = 4872`, and `D r^2 = 1728000 < 1632^2`. -/
theorem strip_609_integers :
    (2 * 609 - (xdata 609 7).lk = 30) ∧ ((xdata 609 7).s = 108) ∧ ((xdata 609 7).D = 1920) := by decide +kernel

/-! ### Level + T2 kills -/

theorem level_kill_list :
    windowList.filter (fun N => (xList N).all fun x => levelKill N x && !stripDead N x)
      = [285, 3315, 3621, 4047, 4503, 6555, 9483] := by decide +kernel

/-- every strip-dead pair is level-dead (observation). -/
theorem strip_sub_level : windowList.all (fun N => (xList N).all fun x => !stripDead N x || levelKill N x) = true := by
  decide +kernel

/-- `(U, #geometrically dead, #level dead, #alive, #ambiguous)` of the odd levels, as in the table of section 5.4. -/
def stats (N x : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ :=
  (ucap N (xdata N x), cnt 1 (codes N x), cnt 2 (codes N x), cnt 3 (codes N x), cnt 0 (codes N x))

theorem stats_285 : stats 285 5 = (40, 6, 14, 0, 0) := by decide +kernel
theorem stats_3315 : stats 3315 17 = (119, 26, 34, 0, 0) := by decide +kernel
theorem stats_3621 : stats 3621 17 = (133, 65, 2, 0, 0) := by decide +kernel
theorem stats_4047 : stats 4047 19 = (128, 21, 43, 0, 0) := by decide +kernel
theorem stats_4503 : stats 4503 19 = (147, 70, 4, 0, 0) := by decide +kernel
theorem stats_6555 : stats 6555 23 = (175, 81, 7, 0, 0) := by decide +kernel
theorem stats_9483 : stats 9483 29 = (193, 27, 70, 0, 0) := by decide +kernel

/-- the largest level cap over the window is 202 -/
theorem ucap_max : windowList.all (fun N => (xList N).all fun x => decide (ucap N (xdata N x) ≤ 202)) = true := by
  decide +kernel

/-! ### The combined list -/

theorem pairKill_list :
    windowList.filter (fun N => (xList N).all fun x => pairKill N x)
      = [285, 609, 2145, 3315, 3621, 4047, 4503, 6555, 6693, 9483] := by decide +kernel

/-- the 42 window N that stay alive (some pair neither strip- nor level-killed). -/
def aliveList : List ℕ :=
  [255, 483, 1155, 1221, 1353, 1419, 1599, 1677, 1833, 2067, 2703, 2805, 3009, 3111, 3363, 3417, 3477, 3705, 3819, 4161,
   4389, 4899, 5037, 5313, 5451, 5727, 5865, 6141, 6279, 7743, 7917, 8265, 8439, 8787, 8835, 8961, 9021, 9309, 9393,
   9579, 9831, 9951]

theorem alive_list :
    windowList.filter (fun N => !((xList N).all fun x => pairKill N x)) = aliveList := by decide +kernel

theorem alive_card : aliveList.length = 42 := by decide +kernel

/-! ### Full pair table: nine N are excluded (arithmetic side); 2145 is NOT -/

theorem excluded_nine :
    windowList.filter excluded = [285, 609, 3315, 3621, 4047, 4503, 6555, 6693, 9483] := by decide +kernel

theorem excluded_nine_card : (windowList.filter excluded).length = 9 := by rw [excluded_nine]; decide +kernel

/-- N = 2145: the x-type pair (165, 39) IS killed ... -/
theorem pair_2145_165_39 : pairCovered 2145 165 39 = true := by decide +kernel
/-- ... but the pair (143, 45) has D = 1024 = 32^2, a square, and nothing here covers it. -/
theorem not_killed_2145 :
    isSq ((143 + 45) * (143 + 45) - 16 * 2145) = true ∧ (143 + 45) * (143 + 45) - 16 * 2145 = 1024 ∧
    pairCovered 2145 143 45 = false ∧ uncoveredPairs 2145 = [(143, 45)] ∧ excluded 2145 = false := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- the other pairs of 2145 are all covered (pinned, D < 0, or Theorem T, or strip) -/
theorem pairs_2145 : (pairs 2145).length = 11 := by decide +kernel

/-! ### Controls -/

/-- N = 255 (x = 5): alive, NOT killed (level 1 is alive: code 3). -/
theorem ctl_255_alive : pairKill 255 5 = false ∧ excluded 255 = false ∧ uncoveredPairs 255 = [(51, 15)] := by
  refine ⟨?_, ?_, ?_⟩ <;> decide +kernel
theorem ctl_255_stats : stats 255 5 = (34, 0, 13, 4, 0) := by decide +kernel

/-- N = 1440 (a realised tiling, tile (5,8,7)): even, pair (120, 36) has D = 36^2: nothing covers it. -/
theorem ctl_1440 : excluded 1440 = false ∧ pairCovered 1440 120 36 = false := by
  constructor <;> decide +kernel

/-- WRONG predicate 1: `r s < 4N` instead of `r s < 8N` (drops the factor 2 of `M = (s + sqrt D)/2`). -/
def stripW4 (N : ℕ) (d : XData) : Bool := decide (d.lk ≤ 2 * N) && decide ((2 * N - d.lk) * d.s < 4 * N)
/-- WRONG predicate 2: `r s < 16N` (a looser bound). -/
def stripW16 (N : ℕ) (d : XData) : Bool := decide (d.lk ≤ 2 * N) && decide ((2 * N - d.lk) * d.s < 16 * N)

theorem wrong4_list : windowList.filter (fun N => (xList N).all fun x => stripW4 N (xdata N x)) = [2145, 6693] := by
  decide +kernel
theorem wrong16_list :
    windowList.filter (fun N => (xList N).all fun x => stripW16 N (xdata N x)) = [609, 2145, 3621, 4503, 6693] := by
  decide +kernel
theorem wrong_lists_differ :
    windowList.filter (fun N => (xList N).all fun x => stripW4 N (xdata N x)) ≠ [609, 2145, 6693] ∧
    windowList.filter (fun N => (xList N).all fun x => stripW16 N (xdata N x)) ≠ [609, 2145, 6693] := by
  constructor <;> decide +kernel

/-- the NON-STRICT (`<=`) variant of (I), as the corrected inequality of LOUD 2 would suggest: SAME list (no equality case). -/
theorem stripIle_list :
    windowList.filter (fun N => (xList N).all fun x => stripIle N (xdata N x) && stripII N (xdata N x)) = [609, 2145, 6693] := by
  decide +kernel

/-- `levelDead` alone (without the geometric branch) kills no window N: the strip kills come exactly from the geometric branch. -/
theorem levelDead_only_kills_none :
    windowList.filter (fun N => (xList N).all fun x => (codes N x).all fun c => c == 2) = [] := by decide +kernel
theorem geomDead_only_list :
    windowList.filter (fun N => (xList N).all fun x => (codes N x).all fun c => c == 1) = [609, 2145, 6693] := by
  decide +kernel

end Erdos634.Draft.PI3H

#print axioms Erdos634.Draft.PI3H.strip_kill_list
#print axioms Erdos634.Draft.PI3H.level_kill_list
#print axioms Erdos634.Draft.PI3H.pairKill_list
#print axioms Erdos634.Draft.PI3H.alive_list
#print axioms Erdos634.Draft.PI3H.excluded_nine
#print axioms Erdos634.Draft.PI3H.not_killed_2145
#print axioms Erdos634.Draft.PI3H.ctl_255_alive
#print axioms Erdos634.Draft.PI3H.wrong_lists_differ
