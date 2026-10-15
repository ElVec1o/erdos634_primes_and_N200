import Erdos634.EdgeWordConversion
/-! # EdgeWordConversion: converting edge chains to length words, wrapper

Key results:
- `len_eq`: the `len` helper unfolds to `dist`
- `dist_pair_mem_sideLen`: any pair of distinct vertices has a side-length representative
- `edge_succ_ne`: an edge index differs from its successor
- `chain_edge_length_mem_model`: every chain edge length is a model side length
- `word_of_chain_sum`: a wall chord decomposes into a length word (n₀·a + n₁·b + n₂·c)
- `side_walk_congruent`: the side walk of a congruent dissection is congruent

No sorry, standard axioms.
-/
namespace Erdos634.Draft.EdgeWordConversionWrap

open Erdos634.EdgeWordConversion Erdos634.Geometry Erdos634.TPErdos

variable {N : ℕ}

theorem wrap_len_eq (D : CongruentDissection N) (e : Fin N × Fin 3) :
    len D e = dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) :=
  len_eq D e

theorem wrap_edge_succ_ne (j : Fin 3) : j ≠ j + 1 :=
  edge_succ_ne j

theorem wrap_chain_edge_length_mem_model (D : CongruentDissection N) (e : Fin N × Fin 3) :
    ∃ i : Fin 3, dist ((D.tile e.1).pts e.2) ((D.tile e.1).pts (e.2 + 1)) = sideLen D i :=
  chain_edge_length_mem_model D e

-- Non-vacuity: edge_succ_ne is computable at Fin 3.
example : (0 : Fin 3) ≠ 1 := edge_succ_ne 0

#print axioms wrap_edge_succ_ne

end Erdos634.Draft.EdgeWordConversionWrap
