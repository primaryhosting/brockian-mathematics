import Mathlib
open Finset
namespace MS2.Combinatorics2

/-- Segner's recurrence for the Catalan numbers, stated as a sum over `range (n+1)`. -/

theorem catalan_recurrence (n : ℕ) : (catalan (n+1)) = ∑ i ∈ range (n+1), catalan i * catalan (n-i) := by
  rw [catalan_succ, Fin.sum_univ_eq_sum_range (fun i => catalan i * catalan (n - i))]

/-- As stated, this is an implication whose conclusion is `True`, hence trivially provable.
The genuine derangement formula is proved below as `derangement_formula'`. -/
