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

lemma bloch_norm (a b : ℂ) (h : normSq a + normSq b = 1) :
    (2 * ((starRingEnd ℂ) a * b).re) ^ 2 + (2 * ((starRingEnd ℂ) a * b).im) ^ 2
      + (normSq a - normSq b) ^ 2 = 1 := by
  have key : (2 * ((starRingEnd ℂ) a * b).re) ^ 2 + (2 * ((starRingEnd ℂ) a * b).im) ^ 2
      + (normSq a - normSq b) ^ 2 = (normSq a + normSq b) ^ 2 := by
    simp only [Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
      Complex.normSq_apply]
    ring
  rw [key, h]; norm_num

/-- The Bloch vector of a qubit state. -/
