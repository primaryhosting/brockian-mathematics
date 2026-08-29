/-
/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/
import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace QC

open Complex

/-- A pure qubit state: a unit vector in `ℂ²`. -/

lemma conj_mul_self_of_normSq_one {z : ℂ} (hz : normSq z = 1) :
    (starRingEnd ℂ) z * z = 1 := by
  apply Complex.ext <;>
    simp [Complex.mul_re, Complex.mul_im, Complex.normSq_apply] at hz ⊢ <;> linarith [hz]

