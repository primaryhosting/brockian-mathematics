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

lemma isIntegral_of_aeval_eq_zero {q : ℚ[X]} (hq : q ≠ 0) {c : ℂ} (h : aeval c q = 0) :
    IsIntegral ℚ c :=
  ⟨q * C (q.leadingCoeff)⁻¹, monic_mul_leadingCoeff_inv hq, by
    rw [← aeval_def, map_mul, h, zero_mul]⟩

/-- A root of a nonzero rational polynomial has degree at most the degree of that
polynomial. -/
