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

private lemma two_add_pow4 (d₁ d₂ m : ℕ) (h₁ : d₁ ≤ m) (h₂ : d₂ ≤ m) :
    2 * ((4 : ℕ) ^ d₁ + 4 ^ d₂) ≤ 4 ^ (m + 1) := by
  have a₁ := pow4_le h₁
  have a₂ := pow4_le h₂
  have : (4 : ℕ) ^ (m + 1) = 4 * 4 ^ m := by ring
  omega

/-- **Barrington's simulation.**  Every fan-in-two Boolean formula of depth `d` is computed,
for *every* prescribed 5-cycle `σ`, by a width-5 permutation branching program with at most
`4 ^ d` layers. -/
