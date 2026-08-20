/-
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Ghz 2 Normalized
Category: Quantum Computing
Target: QC.ghz2_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2`, as a vector in the complex Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2)` (one `Fin 2` factor per qubit). -/

@[simp] lemma ghz2_apply (p : Fin 2 × Fin 2) :
    ghz2 p = if p = (0, 0) ∨ p = (1, 1) then (1 : ℂ) / Real.sqrt 2 else 0 := rfl

/-- The 2-qubit GHZ state `(|00⟩ + |11⟩)/√2` is a unit vector.

The proof rewrites the norm with `EuclideanSpace.norm_eq` (`‖x‖ = √(∑ i, ‖x i‖ ^ 2)`)
and evaluates the resulting four-term sum. -/
