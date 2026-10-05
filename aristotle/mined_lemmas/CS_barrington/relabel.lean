/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above uses `/- -/` rather than `/-! -/` because Lean 4 requires all `import`
-- commands to precede any module docstring.)

import Mathlib

/-!
## Barrington's theorem

We formalise Barrington's theorem, which identifies the class `NC¹` (Boolean formulas of
logarithmic depth) with the class of functions computed by *width-5 permutation branching
programs* of polynomial length.

* `CS.Formula n` are Boolean formulas in the variables `Fin n` built from `¬`, `∧`, `∨`.
  Following the usual convention for Barrington's theorem, `Formula.depth` counts the
  nesting depth of the binary gates (negations are free, since they can be pushed to the
  leaves without changing the depth).
* `CS.BProg n` is a *width-5 permutation branching program*: a list of instructions, each of
  which reads one input bit and outputs one of two permutations of `Fin 5`, depending on the
  value of that bit.  The value `BProg.eval P x` of the program on the input `x` is the
  product of the permutations selected by the instructions.

The two halves of `CS.barrington` are:

1. every formula of depth `d` is computed by a width-5 permutation branching program of
   length at most `4 ^ d`, with output the prescribed 5-cycle `σ` on accepted inputs and the
   identity on rejected inputs (this is Barrington's construction);
2. conversely, for every width-5 permutation branching program `P` of length `ℓ` and every
   target permutation `σ`, the acceptance predicate `P.eval x = σ` is computed by a formula of
   depth `O(log ℓ)` (a balanced divide-and-conquer evaluation of the product).
-/

namespace CS

open Equiv Equiv.Perm

/-- The group of permutations of five points: the "width 5" of Barrington's theorem. -/
abbrev W : Type := Equiv.Perm (Fin 5)

/-! ### Boolean formulas -/

/-- Boolean formulas over the variables `Fin n`. -/
inductive Formula (n : ℕ) where
  | var : Fin n → Formula n
  | neg : Formula n → Formula n
  | conj : Formula n → Formula n → Formula n
  | disj : Formula n → Formula n → Formula n

/-- The depth of a formula, counting binary gates only (negations are free). -/

theorem relabel {n : ℕ} {P : BProg n} {γ γ' : W} {f : (Fin n → Bool) → Bool}
    (h : ∀ x, P.eval x = if f x then γ else 1) (hc : IsConj γ γ') :
    ∃ P' : BProg n, P'.length = P.length ∧ (P ≠ [] → P' ≠ []) ∧
      ∀ x, P'.eval x = if f x then γ' else 1 := by
  rw [isConj_iff] at hc
  obtain ⟨θ, hθ⟩ := hc
  refine ⟨P.conj θ, by simp, ?_, ?_⟩
  · intro hne
    simpa [BProg.conj] using hne
  · intro x
    rw [BProg.eval_conj, h]
    cases f x <;> simp [hθ]

/-- **Barrington's construction.** Every formula of depth `d` is computed, with output any
prescribed 5-cycle `σ`, by a nonempty width-5 permutation branching program of length at
most `4 ^ d`. -/
