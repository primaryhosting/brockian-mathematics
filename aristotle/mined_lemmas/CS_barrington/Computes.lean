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

lemma Computes.congr {n : ℕ} {P : BP n} {σ : Perm5} {f g : (Fin n → Bool) → Bool}
    (h : Computes P σ f) (hfg : ∀ x, f x = g x) : Computes P σ g := by
  intro x; rw [h x, hfg x]

/-- `σ` is a 5-cycle in `S₅`. -/
