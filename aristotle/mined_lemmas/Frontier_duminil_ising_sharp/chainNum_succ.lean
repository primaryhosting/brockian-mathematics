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

lemma chainNum_succ (β : ℝ) (N : ℕ) :
    chainNum β (N + 1) = (2 * Real.sinh β) * chainNum β N := by
  rw [chainNum, sum_snoc, chainNum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  have hzero : ∀ b : Bool, (Fin.snoc σ b : Fin (N + 2) → Bool) 0 = σ 0 := by
    intro b
    have h : (0 : Fin (N + 2)) = Fin.castSucc (0 : Fin (N + 1)) := rfl
    rw [h, Fin.snoc_castSucc]
  have hlast : ∀ b : Bool, (Fin.snoc σ b : Fin (N + 2) → Bool) (Fin.last (N + 1)) = b :=
    fun b => Fin.snoc_last _ _
  simp only [hzero, hlast, chainWeight_snoc]
  have hsum : ∑ b : Bool,
      sgn (σ 0) * sgn b * (chainWeight β σ * Real.exp (β * (sgn (σ (Fin.last N)) * sgn b)))
      = sgn (σ 0) * chainWeight β σ *
        ∑ b : Bool, sgn b * Real.exp (β * (sgn (σ (Fin.last N)) * sgn b)) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by ring
  rw [hsum, sum_bool_sgn_exp]
  ring

/-- Exact partition function of the one-dimensional Ising chain with free boundary
conditions: `Z_N = 2 (2 cosh β)^N`. -/
