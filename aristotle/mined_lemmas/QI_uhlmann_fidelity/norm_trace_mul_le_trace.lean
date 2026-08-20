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

theorem norm_trace_mul_le_trace (P V : Matrix n n ℂ) (hP : P.PosSemidef) (hV : Vᴴ * V = 1) :
    ‖(V * P).trace‖ ≤ P.trace.re := by
  set S := CFC.sqrt P with hS
  have hSS : S * S = P := CFC.sqrt_mul_sqrt_self P hP.nonneg
  have hSh : Sᴴ = S := (CFC.sqrt_nonneg P).posSemidef.1
  have hconj : ∀ i k, star (S k i) = S i k := by
    intro i k
    have := congrFun (congrFun hSh i) k
    simpa [Matrix.conjTranspose_apply] using this
  have key : (V * P).trace = (S * V * S).trace := by
    rw [← hSS, ← Matrix.mul_assoc, Matrix.trace_mul_comm (V * S) S, Matrix.mul_assoc]
  set x : n → n → ℂ := fun i k => S k i with hx
  have hentry : ∀ i, (S * V * S) i i = star (x i) ⬝ᵥ (V *ᵥ x i) := by
    intro i
    simp only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Pi.star_apply, hx, hconj,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  have hdiag : ∀ i, P i i = star (x i) ⬝ᵥ x i := by
    intro i
    rw [← hSS]
    simp only [Matrix.mul_apply, dotProduct, Pi.star_apply, hx, hconj]
  have hiso : ∀ i, star (V *ᵥ x i) ⬝ᵥ (V *ᵥ x i) = star (x i) ⬝ᵥ x i := by
    intro i
    rw [star_mulVec, ← dotProduct_mulVec, Matrix.mulVec_mulVec, hV, one_mulVec]
  calc ‖(V * P).trace‖ = ‖∑ i, (S * V * S) i i‖ := by rw [key, Matrix.trace]; rfl
    _ ≤ ∑ i, ‖(S * V * S) i i‖ := norm_sum_le _ _
    _ ≤ ∑ i, (star (x i) ⬝ᵥ x i).re := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [hentry i]
        exact norm_dotProduct_le _ _ (hiso i)
    _ = P.trace.re := by
        rw [Matrix.trace, Complex.re_sum]
        exact Finset.sum_congr rfl fun i _ => by rw [← hdiag i]; rfl

omit [DecidableEq n] in
/-- Two square matrices agree as soon as they act identically on all vectors. -/
