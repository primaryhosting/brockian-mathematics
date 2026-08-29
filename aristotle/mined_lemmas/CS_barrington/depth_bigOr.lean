/-
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean does not permit a module docstring `/-! ... -/` before `import`; the header above is
-- reproduced verbatim as the module docstring immediately after the import.)
import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

open Equiv

/-! ## Boolean formulas (the `NC¹` side)

A `Formula n` is a fan-in-two Boolean formula over the variables `x 0, …, x (n-1)`.
Logarithmic-depth formulas are exactly (non-uniform) `NC¹`. -/

/-- Fan-in-two Boolean formulas over `n` variables. -/
inductive Formula (n : ℕ) : Type
  | const : Bool → Formula n
  | var : Fin n → Formula n
  | not : Formula n → Formula n
  | and : Formula n → Formula n → Formula n
  | or : Formula n → Formula n → Formula n

namespace Formula

variable {n : ℕ}

/-- The Boolean function computed by a formula. -/

lemma depth_bigOr (l : List (Formula n)) (D : ℕ) (h : ∀ F ∈ l, F.depth ≤ D) :
    (bigOr l).depth ≤ D + l.length := by
  induction l with
  | nil => simp [bigOr, depth]
  | cons F t ih =>
    have h1 : F.depth ≤ D := h F (by simp)
    have h2 := ih (fun G hG => h G (by simp [hG]))
    simp only [bigOr, depth, List.length_cons]
    omega

end Formula

/-! ## Width-5 permutation branching programs -/

/-- The symmetric group on five points, the "width 5" of the model. -/
abbrev Perm5 := Equiv.Perm (Fin 5)

/-- A single layer of a width-5 permutation branching program: either it queries an input
bit and applies one of two permutations, or it applies a fixed permutation. -/
inductive Instr (n : ℕ) : Type
  | query : Fin n → Perm5 → Perm5 → Instr n
  | konst : Perm5 → Instr n

namespace Instr

variable {n : ℕ}

/-- The permutation applied by a layer on a given input. -/
