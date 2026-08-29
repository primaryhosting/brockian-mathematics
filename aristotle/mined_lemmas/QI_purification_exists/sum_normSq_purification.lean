import Mathlib

/-!
# Purification Exists
Category: Frontier Qi
Target: QI.purification_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder
open scoped MatrixOrder

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

namespace QI

open Matrix

universe u v

/-! ## Linear-algebraic preliminaries -/

/-- The inner product of two images under a matrix, expressed through `Mᴴ * M`. -/

theorem sum_normSq_purification {n m : Type*} [Fintype n] [Fintype m] {ρ : Matrix n n ℂ}
    (hρ : IsMixedState ρ) {ψ : n × m → ℂ} (hψ : IsPurification ρ ψ) :
    ∑ p : n × m, ‖ψ p‖ ^ 2 = 1 := by
  have h := sum_normSq_eq_trace_reducedState ψ
  rw [show reducedState ψ = ρ from hψ, hρ.trace_one] at h
  exact_mod_cast h

/-! ## Existence of purifications -/

/-- Every mixed state `ρ` on `n` admits a purification on `n × n`, given by the entries of the
positive semidefinite square root of `ρ`. -/
