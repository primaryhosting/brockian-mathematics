/-
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Nash Equilibrium Exists
Category: Frontier Mind
Target: Frontier.nash_equilibrium_exists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset

/-! ## Finite games in normal form -/

variable {ι : Type} [Fintype ι] [DecidableEq ι]
  {S : ι → Type} [∀ i, Fintype (S i)] [∀ i, DecidableEq (S i)]

/-- A probability distribution on the (finite) pure strategy set of a player. -/

theorem not_isNashEquilibrium_of_dominated :
    ¬ IsNashEquilibrium (fun (_ : Fin 1) (p : (_ : Fin 1) → Bool) => if p 0 then (1 : ℝ) else 0)
      (pureProfile (fun _ : Fin 1 => false)) := by
  intro h
  have hz := (isMixed_pureProfile (fun _ : Fin 1 => true)) 0
  have hle := h.2 0 (pureProfile (fun _ : Fin 1 => true) 0) hz
  have heq : Function.update (pureProfile (fun _ : Fin 1 => false)) 0
      (pureProfile (fun _ : Fin 1 => true) 0) = pureProfile (fun _ : Fin 1 => true) := by
    funext j
    have hj : j = 0 := Subsingleton.elim _ _
    subst hj
    simp
  rw [heq, payoff_pureProfile, payoff_pureProfile] at hle
  norm_num at hle

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

