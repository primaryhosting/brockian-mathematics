/-
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Sunflower Bound
Category: Frontier Math
Target: Math2.sunflower_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Math2

variable {α : Type*} [DecidableEq α]

/-- A family `S` of sets is a *sunflower with core `c`* if any two distinct members of `S`
intersect exactly in `c`. -/

lemma rhoLog_mono (C : ℝ) (hC : 0 ≤ C) (p k k' : ℕ) (hkk' : k' ≤ k) :
    rhoLog C p k' ≤ rhoLog C p k := by
  have h1 : Real.log ((k' : ℝ) + 1) ≤ Real.log ((k : ℝ) + 1) := by
    apply Real.log_le_log (by positivity)
    have : (k' : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkk'
    linarith
  have h2 : (0 : ℝ) ≤ C * p := by positivity
  simpa [rhoLog, mul_assoc] using mul_le_mul_of_nonneg_left h1 h2

