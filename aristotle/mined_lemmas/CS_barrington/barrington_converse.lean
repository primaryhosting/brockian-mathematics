/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Barrington's theorem

We formalise Barrington's theorem, which identifies `NC¹` (log-depth boolean formulas)
with width-`5` permutation branching programs:

* **Forward direction.** Every boolean formula of depth `d` is computed by a width-`5`
  permutation branching program of length at most `4 ^ d` (in the strong sense of
  `σ`-computation, for an arbitrary `5`-cycle `σ`).
* **Converse direction.** Every width-`5` permutation branching program of length at
  most `2 ^ k` is computed by a boolean formula of depth `O(k)` (explicitly `6 * k + 4`).

Together these say: depth-`d` formulas ↔ length-`4^d` width-`5` programs, i.e.
`NC¹` = width-`5` permutation branching programs.
-/

namespace CS

open Equiv Equiv.Perm

/-! ### Boolean formulas -/

/-- Boolean formulas in `n` variables, over the complete basis `{¬, ∧}` together with
constants.  Depth-`O(log n)` formulas are exactly `NC¹`. -/
inductive Formula (n : ℕ) where
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  deriving DecidableEq

variable {n : ℕ}

/-- The boolean function computed by a formula. -/

theorem barrington_converse (k : ℕ) (P : Program n) (σ : Perm (Fin 5))
    (hP : P.length ≤ 2 ^ k) :
    ∃ ψ : Formula n, ψ.depth ≤ 6 * k + 4 ∧ ∀ x, ((ψ.eval x = true) ↔ P.eval x = σ) := by
  obtain ⟨F, hFd, hF⟩ : ∃ F : Fin 5 → Formula n, (∀ a, (F a).depth ≤ 6 * k + 1) ∧
      ∀ a x, (((F a).eval x = true) ↔ P.eval x a = σ a) := by
    choose F h1 h2 using fun a => exists_formula_entry k P hP a (σ a)
    exact ⟨F, h1, h2⟩
  refine ⟨and5 F, ?_, ?_⟩
  · have := and5_depth hFd
    omega
  · intro x
    rw [and5_eval]
    constructor
    · intro h
      exact Equiv.ext (fun a => (hF a x).1 (h a))
    · intro h a
      exact (hF a x).2 (by rw [h])

/-! ### Barrington's theorem -/

/-- **Barrington's theorem**: `NC¹` equals width-`5` permutation branching programs.

The first component: every depth-`d` boolean formula is `σ`-computed, for any `5`-cycle `σ`,
by a width-`5` permutation branching program of length at most `4 ^ d`.

The second component: conversely, the function decided by any width-`5` permutation
branching program of length at most `2 ^ k` is computed by a boolean formula of depth
at most `6 * k + 4`, i.e. logarithmic in the length of the program.

The forward direction takes a variable index `Fin n` as data: at least one variable must
exist for a nonempty program to be writable (a program over zero variables can only
compute the constant-`false` function). -/
