import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem two_mul_sum_choose_le (m D : ℕ) :
    2 * (∑ i ∈ range (m + D + 1), (2 * m).choose i)
      ≤ 4 ^ m + 2 * (D + 1) * ((2 * m).choose m) := by
  have hsplit : ∑ i ∈ range (m + D + 1), (2 * m).choose i
      = (∑ i ∈ range m, (2 * m).choose i) + ∑ i ∈ Ico m (m + D + 1), (2 * m).choose i := by
    rw [← Finset.sum_range_add_sum_Ico _ (by omega : m ≤ m + D + 1)]
  have hband : ∑ i ∈ Ico m (m + D + 1), (2 * m).choose i ≤ (D + 1) * ((2 * m).choose m) := by
    calc ∑ i ∈ Ico m (m + D + 1), (2 * m).choose i
        ≤ ∑ _i ∈ Ico m (m + D + 1), (2 * m).choose m := by
          refine Finset.sum_le_sum fun i _ => ?_
          have := Nat.choose_le_middle i (2 * m)
          simpa [Nat.mul_div_cancel_left m (by norm_num : 0 < 2)] using this
      _ = (D + 1) * ((2 * m).choose m) := by
          rw [Finset.sum_const, Nat.card_Ico, smul_eq_mul]
          congr 1
          omega
  have h2 := two_mul_sum_choose_lt m
  have h3 : 2 * (D + 1) * ((2 * m).choose m) = 2 * ((D + 1) * ((2 * m).choose m)) := by ring
  omega

end CS

/-
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to be the first command, so the header above is a plain comment;
-- it is repeated below as the module docstring.)

import RequestProject.Assembly

/-!
# Razborov Smolensky
Category: Frontier Cs
Target: CS.razborov_smolensky
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The Razborov–Smolensky theorem: for distinct primes `p` and `q`, the function `MOD p` is not
in `AC⁰[q]`, i.e. it is not computed by constant depth, polynomial size circuits with
unbounded fan-in `AND`, `OR`, `NOT` and `MOD q` gates.
-/

namespace CS

open Finset

/-- The number of "rounds" used in the polynomial approximation of a circuit of size at most
`(2m + p + 2) ^ c`. -/
