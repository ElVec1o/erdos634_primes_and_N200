import Erdos634.Draft.FDEDefs
import Erdos634.Draft.FDEB_ov_1
import Erdos634.Draft.FDEB_ov_2
import Erdos634.Draft.FDEB_ov_3
import Erdos634.Draft.FDEB_ov_4
import Erdos634.Draft.FDEB_re_1
import Erdos634.Draft.FDEB_re_2
import Erdos634.Draft.FDEB_re_3
import Erdos634.Draft.FDEB_re_4
import Erdos634.Draft.FDEB_ex_1
import Erdos634.Draft.FDEB_ex_2
import Erdos634.Draft.FDEB_ex_3
import Erdos634.Draft.FDEB_ex_4
import Erdos634.Draft.FDEB_un_1
import Erdos634.Draft.FDEB_un_2
import Erdos634.Draft.FDEB_un_3
import Erdos634.Draft.FDEB_un_4
/-! FDE: assembles the spectrum-table checks (original names/statements) from the 16 small block modules
`FDEB_*` plus the cheap list checks; imports no realization module. -/
namespace Erdos634.Draft.FDDSpectrumTable

theorem range201_blocks : List.range 201 = List.range' 0 51 ++ List.range' 51 50 ++ List.range' 101 50 ++ List.range' 151 50 := by
  decide +kernel

theorem no_overlap_check : ∀ N ∈ List.range 201,
    (FamB N && (decide (N ∈ exclList) || decide (N ∈ primeExcl))) = false := by
  intro N hN
  rw [range201_blocks] at hN
  simp only [List.mem_append] at hN
  rcases hN with ((h | h) | h) | h
  exacts [blk_ov_1 N h, blk_ov_2 N h, blk_ov_3 N h, blk_ov_4 N h]

/-- **The Lean-realizable values `≤ 200` are exactly the paper's 103.** -/
theorem realizable_eq_paper : realizableBelow = paperRealizable := by
  unfold realizableBelow
  rw [range201_blocks]
  simp only [List.filter_append, blk_re_1, blk_re_2, blk_re_3, blk_re_4]
  decide +kernel

/-- **Lean-excluded values `≤ 200`:** the 23 primes `≡ 3 (4)` and the 34 composites. -/
theorem excluded_below_card : excludedBelow.length = 59 := by
  unfold excludedBelow
  rw [range201_blocks]
  simp only [List.filter_append, blk_ex_1, blk_ex_2, blk_ex_3, blk_ex_4]
  decide +kernel

/-- The `unknown` values, `1 ≤ N ≤ 200`: 38 of them. -/
theorem unknown_eq :
    ((List.range 201).filter (fun N => 0 < N && !FamB N && !exclB N)) = unknownList := by
  rw [range201_blocks]
  simp only [List.filter_append, blk_un_1, blk_un_2, blk_un_3, blk_un_4]
  decide +kernel

theorem realizable_card : paperRealizable.length = 103 := by decide


/-- Paper-excluded values with NO Lean exclusion: exactly `60, 70, 76`. -/
theorem paper_excluded_missing_in_lean :
    paperExcluded.filter (fun N => !exclB N) = [56, 60, 70, 76] := by
  decide +kernel

/-- Values excluded in Lean that are not in `paperExcluded`: 17 values (`131, 167` via `theoremP_6`;
the rest per-`N` chains). -/
theorem lean_excluded_beyond_paper :
    ((List.range 201).filter (fun N => 0 < N && exclB N && !decide (N ∈ paperExcluded))) = [91, 93, 94, 95, 110, 111, 123, 129, 131, 133, 141, 152, 159, 165, 167,
          177, 183, 195] := by
  decide +kernel

theorem unknown_card : unknownList.length = 38 := by decide


/-- Controls: the `unknown` entries are the genuinely uncovered ones, and the table agrees with the
paper on the values the paper calls sporadic-open (`105, 120, 132, 154, 184`). -/
theorem status_examples :
    spectrumStatus 84 = .realizable ∧ spectrumStatus 176 = .realizable ∧
    spectrumStatus 7 = .excluded ∧ spectrumStatus 91 = .excluded ∧
    spectrumStatus 56 = .unknown ∧ spectrumStatus 60 = .unknown ∧ spectrumStatus 70 = .unknown ∧
    spectrumStatus 76 = .unknown ∧ spectrumStatus 105 = .unknown ∧ spectrumStatus 120 = .unknown ∧
    spectrumStatus 132 = .unknown ∧ spectrumStatus 154 = .unknown ∧ spectrumStatus 184 = .unknown := by
  decide +kernel

end Erdos634.Draft.FDDSpectrumTable
