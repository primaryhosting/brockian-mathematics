/-
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-!
## Uhlmann's theorem

We work with finite-dimensional quantum systems, states being described by density
matrices (positive semidefinite matrices) on `ℂ^n`.

A *purification* of a state `ρ` on `ℂ^n` by an ancilla system `ℂ^m` is a vector
`ψ : n × m → ℂ` (i.e. an element of `ℂ^n ⊗ ℂ^m`) whose reduced state on the first
factor, `Tr_2 |ψ⟩⟨ψ|`, is `ρ`.

The *fidelity* of two states is `F(ρ, σ) = Tr √(√ρ σ √ρ)`.

Uhlmann's theorem states that `F(ρ, σ)` is the maximum of `|⟨ψ, ψ₂⟩|` over all
purifications `ψ` of `ρ` and `ψ₂` of `σ` (using an ancilla of the same dimension).
-/

namespace QI

open Matrix
open scoped MatrixOrder ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The partial trace over the second (ancilla) factor of `ℂ^n ⊗ ℂ^m`. -/

theorem matrix_ext_of_mulVec {A B : Matrix n n ℂ} (h : ∀ v, A *ᵥ v = B *ᵥ v) : A = B := by
  ext i j
  have := congrFun (h (Pi.single j 1)) i
  simpa [Matrix.mulVec_single] using this

/-- `Matrix.toEuclideanLin` acts by matrix-vector multiplication. -/
