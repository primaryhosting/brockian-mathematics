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

theorem crooks_theorem_ratio_gibbs [Nonempty X] (hβ : β ≠ 0) (γ₀ : Fin (N + 1) → X) :
    (∑ γ ∈ Finset.univ.filter (fun γ : Fin (N + 1) → X => Wfwd E N γ = Wfwd E N γ₀),
        Pfwd β E (gibbsKernel β E) N γ) /
      (∑ δ ∈ Finset.univ.filter (fun δ : Fin (N + 1) → X => Wrev E N δ = -Wfwd E N γ₀),
        Prev β E (gibbsKernel β E) N δ) =
      Real.exp (β * (Wfwd E N γ₀ - deltaF β E N)) := by
  refine crooks_theorem_ratio hβ gibbsKernel_detailedBalance _ (ne_of_gt ?_)
  refine Finset.sum_pos (fun δ _ => Prev_gibbs_pos δ) ⟨revPath γ₀, ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact Wrev_revPath γ₀

end

end Phys

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

