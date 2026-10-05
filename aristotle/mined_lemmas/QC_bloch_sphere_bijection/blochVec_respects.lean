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

lemma blochVec_respects : ∀ v w : Qubit, PhaseRel v w → blochVec v = blochVec w := by
  rintro ⟨⟨a, b⟩, hv⟩ ⟨⟨c, d⟩, hw⟩ ⟨z, hz, h1, h2⟩
  simp only at h1 h2
  subst h1
  subst h2
  have hzz : (starRingEnd ℂ) z * z = 1 := conj_mul_self_of_normSq_one hz
  have hprod : (starRingEnd ℂ) (z * a) * (z * b) = (starRingEnd ℂ) a * b := by
    rw [map_mul]
    linear_combination ((starRingEnd ℂ) a * b) * hzz
  have hna : normSq (z * a) = normSq a := by rw [map_mul, hz, one_mul]
  have hnb : normSq (z * b) = normSq b := by rw [map_mul, hz, one_mul]
  apply Subtype.ext
  simp only [blochVec, hprod, hna, hnb]

/-- The Bloch map on states modulo global phase. -/
