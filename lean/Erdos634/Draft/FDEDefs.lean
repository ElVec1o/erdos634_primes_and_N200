import Mathlib.Tactic
/-! Definitions of the spectrum table, split out of FDDSpectrumTable so that the heavy `decide +kernel`
checks can run in modules that do not import the realization closure. -/
namespace Erdos634.Draft.FDDSpectrumTable

inductive Status | realizable | excluded | unknown
  deriving DecidableEq, Repr

def sporadic : List ℕ := [28, 44, 63, 77, 84, 88, 99, 126]

/-- The realizable families as a Boolean, with search bound `15` on the parameters (enough for
`N ≤ 200`; the soundness theorem below holds for every `N` regardless):
`k²`, `3k²`, `6k²`, `7m²`, `11m²` (`m ≥ 2`), `k²(a²+b²)`, and the ladder `k²·s`, `s` sporadic. -/
def FamB (N : ℕ) : Bool :=
  (List.range 15).any (fun k => 0 < k && (N == k * k || N == 3 * (k * k) || N == 6 * (k * k)
      || (2 ≤ k && (N == 7 * (k * k) || N == 11 * (k * k)))
      || sporadic.any (fun s => N == k * k * s)
      || (List.range 15).any (fun a => (List.range 15).any (fun b =>
          0 < a && 0 < b && N == k * k * (a * a + b * b)))))

/-- Prime exclusions: primes `p ≡ 3 (mod 4)`, `3 < p ≤ 200`. -/
def primeExcl : List ℕ := [7, 11, 19, 23, 31, 43, 47, 59, 67, 71, 79, 83, 103, 107, 127, 131, 139, 151, 163, 167, 179, 191, 199]

/-- Composite exclusions with a hypothesis-free Lean theorem. -/
def exclList : List ℕ := [14, 15, 21, 22, 30, 33, 35, 38, 39, 42, 46, 51, 55, 57, 62, 66, 69, 78, 86, 87, 91, 93, 94, 95, 110, 111, 123, 129, 133, 141, 152, 159, 165, 177, 183, 195]

/-- The table: `realizable` if a Lean realization exists, else `excluded` if a Lean exclusion exists,
else `unknown`. -/
def spectrumStatus (N : ℕ) : Status :=
  if FamB N then .realizable
  else if decide (N ∈ exclList) || decide (N ∈ primeExcl) then .excluded else .unknown

/-- The paper's 103 realizable values `≤ 200` (tex lines 2386-2391). -/
def paperRealizable : List ℕ := [1, 2, 3, 4, 5, 6, 8, 9, 10, 12, 13, 16, 17, 18, 20, 24, 25, 26, 27, 28, 29, 32, 34, 36, 37, 40, 41, 44, 45, 48, 49, 50, 52, 53, 54, 58, 61, 63, 64, 65, 68, 72, 73, 74, 75, 77, 80, 81, 82, 84, 85, 88, 89, 90, 96, 97, 98, 99, 100, 101, 104, 106, 108, 109, 112, 113, 116, 117, 121, 122, 125, 126, 128, 130, 136, 137, 144, 145, 146, 147, 148, 149, 150, 153, 157, 160, 162, 164, 169, 170, 173, 175, 176, 178, 180, 181, 185, 192, 193, 194, 196, 197, 200]

/-- The paper's 45 excluded values `≤ 200`. -/
def paperExcluded : List ℕ := [7, 11, 14, 15, 19, 21, 22, 23, 30, 31, 33, 35, 38, 39, 42, 43, 46, 47, 51, 55, 56, 57, 59, 60, 62, 66, 67, 69, 70, 71, 76, 78, 79, 83, 86, 87, 103, 107, 127, 139, 151, 163, 179, 191, 199]

/-- The values for which Lean has neither a realization nor an exclusion. -/
def unknownList : List ℕ := [56, 60, 70, 76, 92, 102, 105, 114, 115, 118, 119, 120, 124, 132, 134, 135, 138, 140, 142, 143, 154, 155, 156, 158, 161, 166, 168, 171, 172, 174, 182, 184, 186, 187, 188, 189, 190, 198]

def exclB (N : ℕ) : Bool := decide (N ∈ exclList) || decide (N ∈ primeExcl)

def realizableBelow : List ℕ := (List.range 201).filter fun N => 0 < N && FamB N
def excludedBelow : List ℕ := (List.range 201).filter fun N => 0 < N && !FamB N && exclB N

end Erdos634.Draft.FDDSpectrumTable
