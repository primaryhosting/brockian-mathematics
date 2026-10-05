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

lemma tanh_mono : Monotone Real.tanh := by
  intro x y h
  rw [Real.tanh_eq_sinh_div_cosh, Real.tanh_eq_sinh_div_cosh,
    div_le_div_iff₀ (Real.cosh_pos _) (Real.cosh_pos _)]
  have h1 : Real.sinh (x - y) ≤ 0 := by
    have h2 : Real.sinh (x - y) ≤ Real.sinh 0 := Real.sinh_le_sinh.2 (by linarith)
    simpa using h2
  rw [Real.sinh_sub] at h1
  linarith

/-! ### The abstract sharpness framework -/

/-- The data entering the Duminil-Copin–Tassion sharpness argument for the Ising model:
a two-point function `τ β n` at inverse temperature `β` and distance `n`, taking values in
`[0,1]`, nondecreasing in `β`, and submultiplicative in the distance (the Simon–Lieb
inequality). -/
structure SharpData where
  /-- The two-point function at inverse temperature `β` and distance `n`. -/
  τ : ℝ → ℕ → ℝ
  nonneg : ∀ β n, 0 ≤ τ β n
  le_one : ∀ β n, τ β n ≤ 1
  mono : ∀ n, Monotone fun β => τ β n
  submul : ∀ β m n, τ β (m + n) ≤ τ β m * τ β n

/-- Subcritical behaviour: the two-point function decays exponentially in the distance. -/
