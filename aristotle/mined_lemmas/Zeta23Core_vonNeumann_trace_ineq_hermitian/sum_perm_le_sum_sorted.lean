/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

The proof follows the classical route: writing `A = U Dα U*`, `B = V Dβ V*` via the spectral
theorem, one gets `tr (A B) = ∑ j k, α j * β k * |W j k|²` for the unitary `W = U* V`.
The matrix of squared moduli of a unitary matrix is doubly stochastic, so by Birkhoff's theorem
(`exists_eq_sum_perm_of_mem_doublyStochastic`) the right-hand side is a convex combination of the
quantities `∑ j, α j * β (σ j)`, each of which is bounded by `∑ i, a i * b i` by the rearrangement
inequality (`Monovary.sum_mul_comp_perm_le_sum_mul`).
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

set_option grind.warning false

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a matrix. -/

lemma sum_perm_le_sum_sorted [LinearOrder n] {f g a b : n → ℝ} (ha : Antitone a)
    (hb : Antitone b) {sa sb : Equiv.Perm n} (hsa : a = f ∘ sa) (hsb : b = g ∘ sb)
    (σ : Equiv.Perm n) : ∑ j, f j * g (σ j) ≤ ∑ i, a i * b i := by
  have hmono : Monovary a b := by
    intro i j h
    rcases le_total i j with hij | hij
    · exact absurd (hb hij) (not_le.2 h)
    · exact ha hij
  have hf : ∀ i, f (sa i) = a i := fun i => by rw [hsa]; rfl
  have hg : ∀ k, g k = b (sb.symm k) := fun k => by rw [hsb]; simp
  have h1 : ∑ j, f j * g (σ j) = ∑ i, a i * b ((sa.trans (σ.trans sb.symm)) i) := by
    rw [← Equiv.sum_comp sa fun j => f j * g (σ j)]
    exact Finset.sum_congr rfl fun i _ => by rw [hf, hg]; rfl
  rw [h1]
  exact hmono.sum_mul_comp_perm_le_sum_mul

/-- Averaging step: a doubly stochastic average of the quantities `∑ j, f j * g (σ j)` is bounded
by any common upper bound `T` of those quantities. -/
