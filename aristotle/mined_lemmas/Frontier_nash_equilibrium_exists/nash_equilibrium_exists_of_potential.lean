/-
Two player zero sum finite games: the von Neumann minimax theorem, proved
unconditionally (via the separating hyperplane theorem, without Brouwer).
This is the unconditional "base case" of Nash's theorem.
-/

import RequestProject.NashEquilibrium

/-!
# Minimax for two player zero sum finite games
-/

open scoped BigOperators

namespace Frontier

variable {m n : Type} [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n]

/-- The vector of expected payoffs to the row player against the mixed strategy `y`. -/

theorem nash_equilibrium_exists_of_potential [∀ i, Nonempty (S i)]
    (G : FiniteGame ι S) (P : ((i : ι) → S i) → ℝ)
    (hP : ∀ (i : ι) (s : (i : ι) → S i) (t : S i),
      G.payoff i (Function.update s i t) - G.payoff i s
        = P (Function.update s i t) - P s) :
    ∃ x : (i : ι) → S i → ℝ, IsNash G x := by
  obtain ⟨s, hmax⟩ := Finite.exists_max (fun σ : (i : ι) → S i => P σ)
  refine ⟨fun i => pureVec (s i), isNash_pure G ?_⟩
  intro i t
  have h1 := hP i s t
  have h2 := hmax (Function.update s i t)
  linarith

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

