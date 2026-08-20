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

section Core

variable {d : ℕ}

/-- Two antitone real sequences monovary. -/

lemma normSq_mem_doublyStochastic {W : Matrix (Fin d) (Fin d) ℂ}
    (h1 : Wᴴ * W = 1) (h2 : W * Wᴴ = 1) :
    (Matrix.of fun i j => Complex.normSq (W i j)) ∈ doublyStochastic ℝ (Fin d) := by
  have key : ∀ z : ℂ, z * star z = (Complex.normSq z : ℂ) := fun z => Complex.mul_conj z
  rw [mem_doublyStochastic_iff_sum]
  refine ⟨fun i j => Complex.normSq_nonneg _, fun i => ?_, fun j => ?_⟩
  · have h := congrFun (congrFun h2 i) i
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ j, Complex.normSq (W i j) : ℝ) : ℂ) = (1 : ℂ) := by
      push_cast; rw [← h]; exact Finset.sum_congr rfl fun x _ => (key _).symm
    exact_mod_cast hc
  · have h := congrFun (congrFun h1 j) j
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply_eq] at h
    have hc : ((∑ i, Complex.normSq (W i j) : ℝ) : ℂ) = (1 : ℂ) := by
      push_cast; rw [← h]
      exact Finset.sum_congr rfl fun x _ => by rw [mul_comm]; exact (key _).symm
    exact_mod_cast hc

end Spectral

/-- **Von Neumann's trace inequality** for Hermitian complex matrices.

If `A` and `B` are Hermitian matrices of size `d`, and `mu`, `nu` list the eigenvalues of `A`
and `B` respectively (i.e. each is a permutation of the eigenvalue list), both arranged in
decreasing (antitone) order, then `Re (trace (A * B)) ≤ ∑ i, mu i * nu i`.

The proof diagonalises both matrices, reduces the trace to a bilinear form against the
doubly stochastic matrix of entrywise squared moduli of a unitary, and then applies
Birkhoff's theorem together with the rearrangement inequality. -/
