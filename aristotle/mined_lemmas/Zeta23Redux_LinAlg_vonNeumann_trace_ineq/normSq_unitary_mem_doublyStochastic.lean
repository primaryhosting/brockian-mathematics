/-
# Von Neumann Trace Ineq
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.vonNeumann_trace_ineq
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

set_option grind.warning false

namespace Zeta23Redux.LinAlg

open Matrix Finset

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The entrywise squared modulus of a unitary matrix is doubly stochastic. -/

lemma normSq_unitary_mem_doublyStochastic {W : Matrix n n ℂ}
    (hW : W ∈ Matrix.unitaryGroup n ℂ) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ n := by
  have h1 : W * star W = 1 := Unitary.mul_star_self_of_mem hW
  have h2 : star W * W = 1 := Unitary.star_mul_self_of_mem hW
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have hii := congrFun (congrFun h1 i) i
    rw [Matrix.mul_apply] at hii
    simp only [Matrix.star_apply, Matrix.one_apply_eq] at hii
    have h3 : ∑ j, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
      rw [← hii]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Complex.star_def, Complex.mul_conj]
    exact_mod_cast h3
  · have hjj := congrFun (congrFun h2 j) j
    rw [Matrix.mul_apply] at hjj
    simp only [Matrix.star_apply, Matrix.one_apply_eq] at hjj
    have h3 : ∑ i, ((Complex.normSq (W i j) : ℝ) : ℂ) = 1 := by
      rw [← hjj]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Complex.star_def, mul_comm, Complex.mul_conj]
    exact_mod_cast h3

/-- Rearrangement + Birkhoff: a bilinear form of two monovarying families against a doubly
stochastic matrix is bounded by the aligned sum. -/
