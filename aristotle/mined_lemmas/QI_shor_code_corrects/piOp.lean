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

def piOp (co : Q → ℂ) (g : Q → Q) : (Q → ℂ) →ₗ[ℂ] (Q → ℂ) where
  toFun v := fun b => co b * v (g b)
  map_add' u v := by funext b; simp [mul_add]
  map_smul' a v := by funext b; simp [Pi.smul_apply]; ring

/-- The same operator, transported to `H`. -/
