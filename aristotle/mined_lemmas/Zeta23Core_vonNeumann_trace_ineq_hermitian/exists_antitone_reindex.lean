/-
# Von Neumann Trace Ineq Hermitian
Category: Brockian Corpus
Target: Zeta23Core.vonNeumann_trace_ineq_hermitian
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

namespace Zeta23Core

open Matrix Finset

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The matrix of squared absolute values of the entries of a unitary matrix is doubly
stochastic. -/

lemma exists_antitone_reindex (f : n → ℝ) :
    ∃ e : Fin (Fintype.card n) ≃ n, Antitone (f ∘ e) := by
  classical
  set eqv : Fin (Fintype.card n) ≃ n := (Fintype.equivFin n).symm with heqv
  set g : Fin (Fintype.card n) → ℝ := fun i => -(f (eqv i)) with hg
  refine ⟨(Tuple.sort g).trans eqv, ?_⟩
  have hm : Monotone (g ∘ Tuple.sort g) := Tuple.monotone_sort g
  intro i j hij
  have h := hm hij
  simp only [Function.comp_apply, hg] at h ⊢
  simpa using neg_le_neg h

/-- **Von Neumann trace inequality, Hermitian case**, in the form asserting existence of the
decreasing rearrangements of the two eigenvalue families. -/
