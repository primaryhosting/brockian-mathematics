import Mathlib

/-!
# Hadamard Involutive
Category: Quantum Computing
Target: QC.hadamard_involutive
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Complex

/-- The normalization constant `1/√2` of the Hadamard gate, as a complex number. -/

lemma hc_conj : (starRingEnd ℂ) hc = hc := by
  simp [hc, Complex.conj_ofReal]

