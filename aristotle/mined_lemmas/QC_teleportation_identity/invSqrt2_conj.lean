import Mathlib

/-!
# Teleportation Identity
Category: Quantum Computing
Target: QC.teleportation_identity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC


lemma invSqrt2_conj : (starRingEnd ℂ) invSqrt2 = invSqrt2 := by
  simp [invSqrt2]

