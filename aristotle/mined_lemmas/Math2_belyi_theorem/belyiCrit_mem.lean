import Mathlib

/-!
# Belyi Theorem
Category: Frontier Math
Target: Math2.belyi_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

open Polynomial IntermediateField

namespace Math2

/-- A complex number is a *rational point* if it lies in the image of `ℚ`. -/

lemma belyiCrit_mem (a b : ℕ) : 0 < belyiCrit a b ∧ belyiCrit a b < 1 := by
  have h : (0:ℚ) < (a : ℚ) + b + 2 := by positivity
  rw [belyiCrit]
  refine ⟨div_pos (by positivity) h, ?_⟩
  rw [div_lt_one h]
  linarith [Nat.cast_nonneg (α := ℚ) b]

