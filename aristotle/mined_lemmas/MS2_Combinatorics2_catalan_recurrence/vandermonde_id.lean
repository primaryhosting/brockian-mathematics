import Mathlib
open Finset
namespace MS2.Combinatorics2

/-- Segner's recurrence for the Catalan numbers, stated as a sum over `range (n+1)`. -/

theorem vandermonde_id (m n r : ℕ) : (m+n).choose r = ∑ k ∈ range (r+1), m.choose k * n.choose (r-k) := by
  rw [Nat.add_choose_eq, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]

/-- As stated, this is an implication whose conclusion is `True`, hence trivially provable.
(A faithful formalization of Cayley's formula — the number of labelled trees on `n` vertices
is `n^(n-2)` — is not available in Mathlib and is not proved here.) -/
