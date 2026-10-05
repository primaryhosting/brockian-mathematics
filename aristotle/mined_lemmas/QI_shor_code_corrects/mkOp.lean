import Mathlib

/-!
# Shor Code Corrects
Category: Frontier Qi
Target: QI.shor_code_corrects
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open ComplexConjugate

namespace QI

/-! ## The 9-qubit Hilbert space -/

/-- Labels for the computational basis of 9 qubits. -/
abbrev Q := Fin 9 → Bool

/-- The state space of 9 qubits, `ℂ^(2^9)` with its standard Hermitian inner product. -/
abbrev H := EuclideanSpace ℂ Q

/-- Flip the `i`-th bit of a basis label. -/

noncomputable def mkOp (co : Q → ℂ) (g : Q → Q) : H →ₗ[ℂ] H :=
  (WithLp.linearEquiv 2 ℂ (Q → ℂ)).symm.toLinearMap ∘ₗ (piOp co g) ∘ₗ
    (WithLp.linearEquiv 2 ℂ (Q → ℂ)).toLinearMap

