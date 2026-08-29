/-
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open Finset
open scoped Classical

namespace Phys

variable {X : Type*} [Fintype X]

/-- State visited by a path at (natural-number) time `n`, clamped to the horizon `N`. -/

lemma gibbsKernel_nonneg (t : ℕ) (x y : X) : 0 ≤ gibbsKernel β E t x y := by
  have := Real.exp_pos (-β * E (t + 1) y)
  exact div_nonneg this.le (Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le)

