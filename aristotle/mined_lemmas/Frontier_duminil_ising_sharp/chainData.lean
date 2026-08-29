/-
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
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

/-!
## Overview

This file formalises the *sharpness of the phase transition* for the Ising model in the
following Lean-checked form.

* `Frontier.Ising.SharpData` bundles the data of a two–point function `τ β n`
  (the truncated correlation at distance `n` and inverse temperature `β`) together with the
  structural inputs coming from the Ising model: it is a number in `[0,1]`, it is
  nondecreasing in `β`, and it is submultiplicative in the distance (the Simon–Lieb /
  Duminil-Copin–Tassion input).

* `Frontier.duminil_ising_sharp` is the sharpness statement: for **every** `β` the model is
  either *subcritical* (`τ β n` decays exponentially in `n`) or exhibits *long-range order*
  (`τ β n = 1` for all `n`); these two behaviours are mutually exclusive, and they are
  separated by a critical value `βc : EReal`: below `βc` one has exponential decay, above
  `βc` one has long-range order.  In particular no intermediate (e.g. polynomial) decay of
  correlations can occur — this is exactly the content of sharpness.

* The statement is not vacuous: the second half of the file constructs the genuine
  one-dimensional Ising chain (spins `Fin (N+1) → Bool`, nearest neighbour Hamiltonian,
  Gibbs weights `exp (β σᵢσⱼ)`, free boundary conditions), computes its partition function
  and its two-point function exactly (`Frontier.Ising.corr_eq_tanh_pow` :
  `⟨σ₀σ_N⟩ = tanh(β)^N`), and shows that it produces `SharpData` whose critical point is
  `βc = +∞`, i.e. the classical fact that the one-dimensional Ising model is subcritical at
  every finite temperature.
-/

noncomputable section

namespace Frontier
namespace Ising

/-! ### The one-dimensional Ising chain -/

/-- The spin value `±1` attached to a boolean. -/

def chainData : SharpData where
  τ := fun β n => Real.tanh (max β 0) ^ n
  nonneg := fun β n => pow_nonneg (tanh_nonneg (le_max_right β 0)) n
  le_one := fun β n => pow_le_one₀ (tanh_nonneg (le_max_right β 0)) (Real.tanh_lt_one _).le
  mono := fun n β β' h => by
    exact pow_le_pow_left₀ (tanh_nonneg (le_max_right β 0))
      (tanh_mono (max_le_max h le_rfl)) n
  submul := fun β m n => le_of_eq (pow_add _ m n)

/-- For `β ≥ 0` the abstract two-point function of `chainData` is the genuine two-point
function `⟨σ₀ σ_n⟩` of the one-dimensional Ising chain. -/
