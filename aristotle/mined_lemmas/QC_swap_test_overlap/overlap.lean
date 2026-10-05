/-
# Swap Test Overlap
Category: Quantum Computing
Target: QC.swap_test_overlap
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open ComplexConjugate

namespace QC

variable {n : Type*} [Fintype n]

/-- The overlap `⟨ψ|φ⟩` of two state vectors indexed by `n`. -/

noncomputable def overlap (psi phi : n → ℂ) : ℂ := ∑ i, conj (psi i) * phi i

/-- A state vector is normalized when the sum of the squared moduli of its
amplitudes is `1`. -/
