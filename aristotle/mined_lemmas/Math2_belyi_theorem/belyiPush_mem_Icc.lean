import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Polynomial
open scoped IntermediateField

namespace Math2

/-- A *Belyi map* (in the genus-zero, polynomial model): a nonconstant polynomial with
rational coefficients, viewed as a morphism `ℙ¹ → ℙ¹` defined over `ℚ`, all of whose
finite critical values lie in `{0, 1}`.  Being a polynomial, such a map is totally
ramified over `∞`, so it is ramified only above `{0, 1, ∞}`. -/

theorem belyiPush_mem_Icc (m n : ℕ) {t : ℚ} (h0 : 0 ≤ t) (h1 : t ≤ 1) :
    0 ≤ (belyiPush (m + 1) (n + 1)).eval t ∧ (belyiPush (m + 1) (n + 1)).eval t ≤ 1 := by
  have hev : (belyiPush (m + 1) (n + 1)).eval t =
      ((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1))) * (t ^ (m + 1) * (1 - t) ^ (n + 1)) := by
    rw [belyiPush_eq]; simp
  refine ⟨?_, ?_⟩
  · rw [hev]
    have : (0 : ℚ) ≤ 1 - t := by linarith
    positivity
  · rw [hev]
    have hreal := push_real_le (m + 1) (n + 1) (Nat.succ_pos m) (Nat.succ_pos n) (t : ℝ)
      (by exact_mod_cast h0) (by exact_mod_cast h1)
    have hcast : ((((((m : ℚ) + 1 + ((n : ℚ) + 1)) ^ ((m + 1) + (n + 1))) /
        (((m : ℚ) + 1) ^ (m + 1) * ((n : ℚ) + 1) ^ (n + 1))) *
          (t ^ (m + 1) * (1 - t) ^ (n + 1)) : ℚ) : ℝ) ≤ 1 := by
      push_cast
      convert hreal using 3 <;> push_cast <;> ring
    exact_mod_cast hcast

/-! ### The rational case -/

/-- Any rational number in `(0,1)` is of the form `(m+1)/(m+n+2)`. -/
