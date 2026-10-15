import Erdos634.OrderForcing

/-!
# OrderForcing — order-forcing arithmetic: wrapper (key theorems)

Wraps the most important theorems from the large OrderForcing module:
- Partition theorems (2b, jb, jb_gen, c_sub_a, south_cover)
- Gap theorems (east_cover_gap, gap_2b_minus_c, gap_jb_minus_multiple)
- Junction/vertex analysis (straight_junction_cases, full_vertex_cases, beta/alpha_slot_unique)
- Pincer windows (pincer_window, pincer_window_four, chain_needs_small_lines)
- Arithmetic helpers (east_cover_gap, alpha_vertex_gap, cos_alpha/beta_closed)

Standard axioms, no `sorry`.
-/

namespace Erdos634.Draft.OrderForcingWrap

open Erdos634.OrderForcing

theorem of_straight_junction_cases (na nb ng : ℕ) (h1 : na + 2 * ng = 3) (h2 : nb + ng = 2) :
    (na = 3 ∧ nb = 2 ∧ ng = 0) ∨ (na = 1 ∧ nb = 1 ∧ ng = 1) :=
  straight_junction_cases na nb ng h1 h2

theorem of_full_vertex_cases (na nb ng : ℕ) (h1 : 2 * na + ng = 3 * nb) (h2 : na + 2 = 2 * nb) :
    (na = 0 ∧ nb = 1 ∧ ng = 3) ∨ (na = 2 ∧ nb = 2 ∧ ng = 2) ∨
    (na = 4 ∧ nb = 3 ∧ ng = 1) ∨ (na = 6 ∧ nb = 4 ∧ ng = 0) :=
  full_vertex_cases na nb ng h1 h2

theorem of_beta_slot_unique (na nb ng : ℕ) (h1 : na + 2 * ng = 0) (h2 : nb + ng = 1) :
    na = 0 ∧ nb = 1 ∧ ng = 0 :=
  beta_slot_unique na nb ng h1 h2

theorem of_alpha_slot_unique (na nb ng : ℕ) (h1 : na + 2 * ng = 1) (h2 : nb + ng = 0) :
    na = 1 ∧ nb = 0 ∧ ng = 0 :=
  alpha_slot_unique na nb ng h1 h2

theorem of_east_cover_gap {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - 1 - f) : False :=
  east_cover_gap hf h

theorem of_alpha_vertex_gap {f n K : ℕ} (hf : 2 ≤ f) (h : n * f + 1 = K * (f * f)) : False :=
  alpha_vertex_gap hf h

theorem of_partition_2b {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = 2 * (f * f) - 2) :
    x = 0 ∧ y = 2 ∧ z = 0 :=
  partition_2b hf h

theorem of_partition_jb {f j x y z : ℕ} (hf : 3 ≤ f) (hj1 : 1 ≤ j) (hjf : j < f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = j * (f * f - 1)) :
    x = 0 ∧ y = j ∧ z = 0 :=
  partition_jb hf hj1 hjf h

theorem of_south_cover {f x y z : ℕ} (hf : 3 ≤ f)
    (h : x * f + y * (f * f - 1) + z * (f * f) = f * f - f) :
    x = f - 1 ∧ y = 0 ∧ z = 0 :=
  south_cover hf h

theorem of_pincer_window {f bp cp : ℕ} (hf : 3 ≤ f) (hf5 : f ≤ 5)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 4) ∨ (cp < bp ∧ f + 3 - bp ≤ 4) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 4) ∨ (bp = cp + 1 ∧ cp ≤ 4) :=
  pincer_window hf hf5 hb3 hbf hc2 hcf hne

theorem of_pincer_window_four {f bp cp : ℕ} (hf : 3 ≤ f) (hf6 : f ≤ 6)
    (hb3 : 3 ≤ bp) (hbf : bp ≤ f) (hc2 : 2 ≤ cp) (hcf : cp ≤ f + 1) (hne : bp ≠ cp) :
    (bp < cp ∧ bp ≤ 5) ∨ (cp < bp ∧ f + 3 - bp ≤ 5) ∨
    (cp = bp + 1 ∧ f + 3 - cp ≤ 5) ∨ (bp = cp + 1 ∧ cp ≤ 5) :=
  pincer_window_four hf hf6 hb3 hbf hc2 hcf hne

theorem of_chain_needs_small_lines {f bp k : ℕ} (hf : 3 ≤ f) (hb3 : 3 ≤ bp) (hbf : bp ≤ f)
    (hk : k ≤ bp - 1) : k < f :=
  chain_needs_small_lines hf hb3 hbf hk

theorem of_cos_alpha_closed (f : ℤ) :
    2 * f ^ 2 * ((f ^ 2 - 1) ^ 2 + (f ^ 2) ^ 2 - f ^ 2)
      = (2 * f ^ 2 - 1) * (2 * (f ^ 2 - 1) * f ^ 2) :=
  cos_alpha_closed f

theorem of_partition_jb_gen {e f j x y z B : ℕ} (he : 1 ≤ e) (hef : e < f) (hjf : j < f)
    (hco : Nat.Coprime f (e * e)) (hB : f * f = B + e * e)
    (h : x * (e * f) + y * B + z * (f * f) = j * B) :
    x = 0 ∧ y = j ∧ z = 0 :=
  partition_jb_gen he hef hjf hco hB h

-- Non-vacuity: alpha_slot_unique
example : (1 : ℕ) = 1 ∧ 0 = 0 ∧ 0 = 0 := of_alpha_slot_unique 1 0 0 (by omega) (by omega)

#print axioms of_east_cover_gap
#print axioms of_partition_jb_gen
#print axioms of_pincer_window

end Erdos634.Draft.OrderForcingWrap
