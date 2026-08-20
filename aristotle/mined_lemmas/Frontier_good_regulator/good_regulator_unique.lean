/-!
# Good Regulator
Category: Frontier Mind
Target: Frontier.good_regulator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

universe u v w

/-- A regulator `ρ : S → R` chooses, for each state `s` of the system, a regulatory action
`ρ s`.  The outcome of state `s` under action `r` is `φ s r`, and the regulator is *good*
(perfectly regulating) when the outcome is always the target value `z₀`. -/

theorem good_regulator_unique {S : Type u} {R : Type v} {Z : Type w}
    (phi : S → R → Z) (z₀ : Z)
    (huniq : ∀ s r r', phi s r = z₀ → phi s r' = z₀ → r = r')
    (rho rho' : S → R) (h : GoodRegulator phi z₀ rho) (h' : GoodRegulator phi z₀ rho') :
    rho = rho' :=
  funext fun s => huniq s (rho s) (rho' s) (h s) (h' s)

/-- Sanity check: the hypotheses of `good_regulator` are satisfiable (the theorem is not
vacuous).  Here the system has two states, the regulator must match the state, and the target
outcome `true` is achieved exactly by the matching action. -/
example : Function.Injective (id : Bool → Bool) ∧
    ∃ m : Bool → Bool, (∀ s, m (id s) = s) ∧
      ∀ (d : Bool → Bool) (s : Bool), m (id (d s)) = d (m (id s)) :=
  good_regulator (fun s r => (s == r)) true
    (fun s s' r hs hs' => by
      simp only [beq_iff_eq] at hs hs'
      exact hs.trans hs'.symm)
    id (fun s => by simp)

end Frontier

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

