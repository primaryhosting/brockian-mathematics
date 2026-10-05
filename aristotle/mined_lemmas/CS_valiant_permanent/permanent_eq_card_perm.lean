import Mathlib

/-!
# Valiant Permanent
Category: Frontier Cs
Target: CS.valiant_permanent
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000
set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace CS

open Finset Matrix

/-! ## Part A: the 0/1 permanent as a counting problem -/

/-- For a 0/1 matrix, the permanent counts the permutations supported on the matrix, i.e. the
perfect matchings of the associated bipartite graph (equivalently, the cycle covers of the
associated digraph). -/

theorem permanent_eq_card_perm {V : Type} [DecidableEq V] [Fintype V] (A : Matrix V V ℕ)
    (h01 : ∀ i j, A i j = 0 ∨ A i j = 1) :
    A.permanent = Nat.card {σ : Equiv.Perm V // ∀ i, A i (σ i) = 1} := by
  classical
  rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  rw [← Matrix.permanent_transpose]
  unfold Matrix.permanent
  rw [Finset.card_filter]
  refine Finset.sum_congr rfl ?_
  intro σ _
  by_cases h : ∀ i, A i (σ i) = 1
  · simp [h, Matrix.transpose_apply]
  · push_neg at h
    obtain ⟨i, hi⟩ := h
    rw [if_neg (by simpa using ⟨i, hi⟩)]
    refine Finset.prod_eq_zero (Finset.mem_univ i) ?_
    rcases h01 i (σ i) with h0 | h1
    · simpa [Matrix.transpose_apply] using h0
    · exact absurd h1 hi

/-! ## Part B: Boolean circuits, `#P`, and membership of the permanent -/

/-- Boolean circuits (formulas) over a type of input variables. -/
inductive Circuit (ι : Type) where
  | var : ι → Circuit ι
  | tru : Circuit ι
  | fls : Circuit ι
  | neg : Circuit ι → Circuit ι
  | conj : Circuit ι → Circuit ι → Circuit ι
  | disj : Circuit ι → Circuit ι → Circuit ι

namespace Circuit

variable {ι : Type}

/-- Semantics of a circuit under an assignment of its variables. -/
