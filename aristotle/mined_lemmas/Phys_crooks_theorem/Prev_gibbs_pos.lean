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

lemma Prev_gibbs_pos [Nonempty X] (δ : Fin (N + 1) → X) :
    0 < Prev β E (gibbsKernel β E) N δ := by
  refine mul_pos (div_pos (Real.exp_pos _) (Zpf_pos 0)) (Finset.prod_pos fun s _ => ?_)
  exact div_pos (Real.exp_pos _) (Zpf_pos _)

/-- Non-vacuity of the ratio form: for the heat-bath dynamics and any work value that is
actually realized by some trajectory, both work distributions are supported at `±w` and the
Crooks ratio `P_F(w) / P_R(-w) = exp (β (w - ΔF))` holds. -/
