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

lemma Pfwd_gibbs_pos [Nonempty X] (γ : Fin (N + 1) → X) :
    0 < Pfwd β E (gibbsKernel β E) N γ := by
  refine mul_pos (div_pos (Real.exp_pos _) (Zpf_pos 0)) (Finset.prod_pos fun t _ => ?_)
  exact div_pos (Real.exp_pos _) (Zpf_pos _)

