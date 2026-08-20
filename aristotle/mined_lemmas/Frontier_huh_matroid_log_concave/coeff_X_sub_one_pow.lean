import Mathlib

/-!
# Huh Matroid Log Concave
Category: Frontier — Fields Medal Work
Target: Frontier.huh_matroid_log_concave
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- Note: Lean 4 requires `import` lines to precede all other commands (including module
-- docstrings), so the required header comment appears immediately after the import.

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

open Polynomial Finset

/-- The characteristic polynomial of a matroid `M` on a finite ground set, defined by the
Whitney rank expression `χ_M(X) = ∑_{S ⊆ E} (-1)^{|S|} X^{r(E) - r(S)}`, where `r` is the
rank function of `M`. -/

theorem coeff_X_sub_one_pow (n k : ℕ) :
    ((X - 1 : ℤ[X]) ^ n).coeff k = (-1) ^ (n - k) * (n.choose k) := by
  rw [sub_eq_add_neg, add_pow, finset_sum_coeff]
  have hterm : ∀ i ∈ Finset.range (n + 1),
      ((X : ℤ[X]) ^ i * (-1) ^ (n - i) * (n.choose i : ℤ[X])).coeff k
        = if k = i then ((-1 : ℤ) ^ (n - i) * (n.choose i)) else 0 := by
    intro i _
    have hC : C ((-1 : ℤ) ^ (n - i) * (n.choose i)) = (-1) ^ (n - i) * (n.choose i : ℤ[X]) := by
      rw [map_mul, map_pow, map_neg, map_one, C_eq_natCast]
    have hsplit : (X : ℤ[X]) ^ i * (-1) ^ (n - i) * (n.choose i : ℤ[X])
        = C ((-1 : ℤ) ^ (n - i) * (n.choose i)) * X ^ i := by
      rw [hC]; ring
    rw [hsplit, coeff_C_mul, coeff_X_pow]
    split <;> simp_all
  rw [Finset.sum_congr rfl hterm]
  rcases le_or_gt k n with h | h
  · rw [Finset.sum_ite_eq (Finset.range (n + 1)) k (fun i => ((-1 : ℤ) ^ (n - i) * (n.choose i)))]
    simp [Nat.lt_succ_of_le h]
  · rw [Finset.sum_eq_zero]
    · rw [Nat.choose_eq_zero_of_lt h]; simp
    · intro i hi
      simp only [Finset.mem_range] at hi
      rw [if_neg (by omega)]

/-- The characteristic polynomial of the free (Boolean) matroid on `n` elements is `(X - 1) ^ n`. -/
