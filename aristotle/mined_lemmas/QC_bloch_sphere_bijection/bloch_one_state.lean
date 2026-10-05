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

lemma bloch_one_state :
    bloch (Quotient.mk qubitSetoid ⟨(0, 1), by simp⟩) = ⟨(0, 0, -1), by norm_num⟩ := by
  apply Subtype.ext
  simp [bloch, blochVec]

/-- The resulting explicit bijection `PureState ≃ S²`. -/
