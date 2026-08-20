import Mathlib

/-!
# Crooks Theorem
Category: Frontier Phys
Target: Phys.crooks_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Phys

/-- A driven microscopic system on a finite state space, observed at times
`0, 1, …, N`.

* `E k` is the energy function of the system after the `k`-th update of the
  external protocol parameter.
* `T k x y` is the probability that the thermalisation step performed while the
  energy function is `E k` takes the system from `x` to `y`.  It is assumed to
  satisfy *detailed balance* with respect to the Boltzmann weights of `E k` at
  inverse temperature `beta`.

A forward trajectory is a sequence of states `x₀, x₁, …, x_N`: the system starts
in thermal equilibrium for `E 0`, then alternately the protocol is advanced
(`E k → E (k+1)`, which costs work) and the system relaxes with the kernel
`T (k+1)`. -/
structure CrooksSystem where
  /-- the (finite, nonempty) microscopic state space -/
  S : Type
  [finS : Fintype S]
  [decS : DecidableEq S]
  [neS : Nonempty S]
  /-- number of protocol steps -/
  N : ℕ
  /-- inverse temperature -/
  beta : ℝ
  beta_pos : 0 < beta
  /-- energy function after `k` protocol updates -/
  E : ℕ → S → ℝ
  /-- thermalisation kernel used while the energy is `E k` -/
  T : ℕ → S → S → ℝ
  /-- detailed balance of `T k` with respect to the Boltzmann weights of `E k` -/
  detailed_balance : ∀ (k : ℕ) (x y : S),
    Real.exp (-beta * E k x) * T k x y = Real.exp (-beta * E k y) * T k y x

attribute [instance] CrooksSystem.finS CrooksSystem.decS CrooksSystem.neS

variable (C : CrooksSystem)

/-- Partition function of the equilibrium state with energy `E k`. -/

noncomputable def thermalSystem (S : Type) [Fintype S] [DecidableEq S] [Nonempty S]
    (N : ℕ) (beta : ℝ) (hbeta : 0 < beta) (E : ℕ → S → ℝ) : CrooksSystem where
  S := S
  N := N
  beta := beta
  beta_pos := hbeta
  E := E
  T := fun k _ y => Real.exp (-beta * E k y) / ∑ z : S, Real.exp (-beta * E k z)
  detailed_balance := by
    intro k x y
    ring

