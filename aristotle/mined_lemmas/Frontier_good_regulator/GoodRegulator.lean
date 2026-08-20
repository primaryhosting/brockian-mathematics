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

/-!
# The Conant–Ashby good regulator theorem

We formalize the deterministic, finite version of the theorem of Conant and Ashby:
*every good regulator of a system must be a model of that system*.

Setup: a system is a map `h : S → R → Z` sending a disturbance `s : S` and a regulatory
action `r : R` to an outcome `h s r : Z`.  A regulator is a (deterministic) map
`rho : S → R`; it is *successful* when the outcome is always the target value `z₀`.
Each disturbance `s` determines, through the system, the set `GoodActions h z₀ s` of actions
that keep the outcome on target — this is the information about the system that a regulator
could possibly need.  A *good regulator* is a successful regulator of minimal Shannon entropy
(the "simplest" successful regulator) with respect to a strictly positive weighting `p` of the
disturbances.

The theorem `Frontier.good_regulator` states that such a regulator is a **model** of the
system: its action is a function of the system's own map `s ↦ GoodActions h z₀ s`, i.e.
`rho` factors as `m ∘ (GoodActions h z₀)`.
-/

namespace Frontier

variable {S R Z : Type*} [Fintype S] [DecidableEq S] [Fintype R] [DecidableEq R]

/-- The total weight of the disturbances that the regulator `rho` maps to the state `r`. -/

def GoodRegulator (p : S → ℝ) (h : S → R → Z) (z₀ : Z) (rho : S → R) : Prop :=
  Successful h z₀ rho ∧ ∀ σ : S → R, Successful h z₀ σ → regEntropy p rho ≤ regEntropy p σ

omit [Fintype R] in
/-- Updating a regulator at one disturbance moves that disturbance's weight. -/
