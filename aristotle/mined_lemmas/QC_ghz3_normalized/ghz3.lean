import Mathlib
/-!
# Ghz 3 Normalized
Category: Quantum Computing
Target: QC.ghz3_normalized
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

/-- The 3-qubit GHZ state `(|000⟩ + |111⟩)/√2`, as a vector in the Hilbert space
`EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2)` of three qubits. -/

noncomputable def ghz3 : EuclideanSpace ℂ (Fin 2 × Fin 2 × Fin 2) :=
  WithLp.toLp 2 fun q => if q = (0, 0, 0) ∨ q = (1, 1, 1) then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

/-- `ghz3` is indeed `(|000⟩ + |111⟩)/√2`, written with the standard basis vectors. -/
