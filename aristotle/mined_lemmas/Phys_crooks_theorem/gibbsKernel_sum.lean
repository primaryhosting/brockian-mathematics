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

lemma gibbsKernel_sum [Nonempty X] (t : ℕ) (x : X) : ∑ y : X, gibbsKernel β E t x y = 1 := by
  simp only [gibbsKernel]
  rw [← Finset.sum_div]
  exact div_self (Zpf_pos (β := β) (E := E) (t + 1)).ne'

/-- The heat-bath kernel satisfies detailed balance, so the hypotheses of the Crooks theorem
are non-vacuous. -/
