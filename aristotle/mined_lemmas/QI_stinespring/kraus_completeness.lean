import Mathlib
/-!
# Stinespring
Category: Frontier Qi
Target: QI.stinespring
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

set_option grind.warning false

namespace QI

open Matrix

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The partial trace over the second (ancilla) factor of a matrix indexed by a product. -/

lemma kraus_completeness {E : Type} [Fintype E] {Φ : Matrix n n ℂ →ₗ[ℂ] Matrix m m ℂ}
    (K : E → Matrix m n ℂ) (hK : ∀ ρ : Matrix n n ℂ, Φ ρ = ∑ e : E, K e * ρ * (K e)ᴴ)
    (hTP : IsTracePreserving Φ) :
    ∑ e : E, (K e)ᴴ * K e = 1 := by
  set A : Matrix n n ℂ := ∑ e : E, (K e)ᴴ * K e with hA
  have key : ∀ ρ : Matrix n n ℂ, (A * ρ).trace = ρ.trace := by
    intro ρ
    have h1 : (A * ρ).trace = ∑ e : E, (K e * ρ * (K e)ᴴ).trace := by
      rw [hA, Finset.sum_mul, Matrix.trace_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [Matrix.trace_mul_comm (K e * ρ) ((K e)ᴴ), ← Matrix.mul_assoc]
    rw [h1, ← Matrix.trace_sum, ← hK ρ, hTP ρ]
  ext a b
  have h := key (Matrix.single b a 1)
  have h1 : (A * Matrix.single b a (1 : ℂ)).trace = A a b := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Matrix.single_apply, ite_and,
      Finset.sum_ite_eq]
  have h2 : (Matrix.single b a (1 : ℂ)).trace = if a = b then 1 else 0 := by
    simp [Matrix.trace, Matrix.diag, Matrix.single_apply, ite_and, Finset.sum_ite_eq]
  rw [h1, h2] at h
  rw [h, Matrix.one_apply]

/-- **Stinespring dilation, isometric form**: every CPTP map is the partial trace of a
conjugation by an isometry. -/
