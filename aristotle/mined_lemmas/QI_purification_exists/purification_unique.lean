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

theorem purification_unique {n m : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
    {ρ : Matrix n n ℂ} {ψ ψ' : n × m → ℂ} (hψ : IsPurification ρ ψ) (hψ' : IsPurification ρ ψ') :
    ∃ U : Matrix m m ℂ, U ∈ Matrix.unitaryGroup m ℂ ∧
      ∀ i : n, ∀ k : m, ψ' (i, k) = ∑ l : m, ψ (i, l) * U l k := by
  have hA : bipartiteMatrix ψ * (bipartiteMatrix ψ)ᴴ
      = bipartiteMatrix ψ' * (bipartiteMatrix ψ')ᴴ := by
    rw [← reducedState_eq_mul_conjTranspose, ← reducedState_eq_mul_conjTranspose,
      show reducedState ψ = ρ from hψ, show reducedState ψ' = ρ from hψ']
  obtain ⟨U, hUmem, hU⟩ :=
    exists_unitary_of_mul_conjTranspose_eq (bipartiteMatrix ψ) (bipartiteMatrix ψ') hA
  refine ⟨U, hUmem, fun i k => ?_⟩
  have := congrFun (congrFun hU i) k
  simpa [bipartiteMatrix, Matrix.mul_apply] using this

/-! ## Main theorem -/

/-- **Purification exists.** Every mixed state `ρ` on a finite-dimensional system has a
purification: a unit vector `ψ` on the doubled system whose partial trace over the ancilla
is `ρ`. Moreover any two purifications with a common ancilla are related by a unitary
transformation acting on the ancilla alone. -/
