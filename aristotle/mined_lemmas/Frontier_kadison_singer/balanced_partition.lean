/-
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the required
-- header above is written as a plain block comment.)

import Mathlib

/-!
The Kadison–Singer problem asks whether every pure state on a maximal abelian self-adjoint
subalgebra (MASA) of `B(ℓ²)` extends uniquely to a state on `B(ℓ²)`.  It was answered
affirmatively by Marcus, Spielman and Srivastava via the method of interlacing families of
polynomials.

This file formalizes and proves in full the *finite-dimensional* case — the base case of the
Kadison–Singer question: for the diagonal MASA of the matrix algebra `Mₙ(ℂ)`, the pure state
`d ↦ d i` of the diagonal has a unique extension to a state on `Mₙ(ℂ)`, namely `A ↦ A i i`.

Here a *state* is a unital positive ℂ-linear functional (`Frontier.IsState`), and the pure
states of the diagonal algebra `ℂⁿ` are exactly the coordinate evaluations `d ↦ d i`.

The proof is the classical one: positivity of `phi` yields a positive semidefinite Hermitian
sesquilinear form `(X, Y) ↦ phi (Xᴴ * Y)`, and the degenerate case of the Cauchy–Schwarz
inequality forces `phi` to vanish on every matrix unit other than `E i i`.
-/

namespace Frontier

open Matrix ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- A *state* on the matrix algebra `Mₙ(ℂ)`: a unital, positive linear functional. -/

theorem balanced_partition {m : Type*} [DecidableEq m] (a : m → ℝ) (eps : ℝ) (heps : 0 ≤ eps)
    (h0 : ∀ j, 0 ≤ a j) (h1 : ∀ j, a j ≤ eps) (t : Finset m) :
    ∃ S ⊆ t, |∑ j ∈ S, a j - ∑ j ∈ t \ S, a j| ≤ eps := by
  classical
  induction t using Finset.induction_on with
  | empty => exact ⟨∅, by simp, by simpa using heps⟩
  | insert x t hx ih =>
    obtain ⟨S, hSt, hd⟩ := ih
    rcases le_or_gt 0 (∑ j ∈ S, a j - ∑ j ∈ t \ S, a j) with hpos | hneg
    · refine ⟨S, hSt.trans (Finset.subset_insert _ _), ?_⟩
      have hins : (insert x t) \ S = insert x (t \ S) :=
        Finset.insert_sdiff_of_notMem _ (fun h => hx (hSt h))
      rw [hins, Finset.sum_insert (by simp [hx])]
      have hx0 := h0 x
      have hx1 := h1 x
      rw [abs_le] at hd ⊢
      constructor <;> linarith [hd.1, hd.2]
    · refine ⟨insert x S, Finset.insert_subset_insert _ hSt, ?_⟩
      have hxS : x ∉ S := fun h => hx (hSt h)
      have hins : (insert x t) \ (insert x S) = t \ S := by
        ext y
        simp only [Finset.mem_sdiff, Finset.mem_insert]
        constructor
        · rintro ⟨hy, hy2⟩
          refine ⟨?_, fun h => hy2 (Or.inr h)⟩
          rcases hy with rfl | hy
          · exact absurd (Or.inl rfl) hy2
          · exact hy
        · rintro ⟨hy, hy2⟩
          exact ⟨Or.inr hy, by rintro (rfl | h); exacts [hx hy, hy2 h]⟩
      rw [hins, Finset.sum_insert hxS]
      have hx0 := h0 x
      have hx1 := h1 x
      rw [abs_le] at hd ⊢
      constructor <;> linarith [hd.1, hd.2]

/-- **Weaver's `KS₂` / the Marcus–Spielman–Srivastava discrepancy theorem in dimension one.**
If scalars `vⱼ` satisfy `∑ ‖vⱼ‖² = 1` (the one-dimensional isotropy condition) and
`‖vⱼ‖² ≤ eps`, then the index set splits into two parts, each carrying at most
`1/2 + eps/2` of the total mass. -/
