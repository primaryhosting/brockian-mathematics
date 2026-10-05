import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import Mathlib

/-!
# Pure State Zero Entropy
Category: Quantum Computing
Target: QC.pure_state_zero_entropy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The von Neumann entropy `S(ρ) = -Tr(ρ log ρ)` of a Hermitian matrix `ρ`, computed in the
eigenbasis: `S(ρ) = ∑ i, -λ i * log (λ i)` where the `λ i` are the (real) eigenvalues of `ρ`.
This is the standard definition of the entropy of a density matrix. -/

theorem negMulLog_eq_zero_of_sq_eq_self {x : ℝ} (hx : x ^ 2 = x) :
    Real.negMulLog x = 0 := by
  have hcases : x = 0 ∨ x = 1 := by
    have h : x * (x - 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp h with h | h
    · exact Or.inl h
    · exact Or.inr (by linarith)
  rcases hcases with h | h <;> simp [h, Real.negMulLog]

/-- **The von Neumann entropy of a pure state is zero.**
For a unit vector `ψ`, the density matrix `ρ = |ψ⟩⟨ψ|` satisfies `S(ρ) = -Tr(ρ log ρ) = 0`. -/
