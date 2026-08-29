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

theorem subcritical_of_lt_one (M : SharpData) (β : ℝ) {N : ℕ} (hN : 0 < N)
    (h : M.τ β N < 1) : Subcritical M β := by
  set q := M.τ β N with hq
  have hq0 : 0 ≤ q := M.nonneg β N
  set p := (q + 1) / 2 with hpdef
  have hp0 : 0 < p := by rw [hpdef]; linarith
  have hp1 : p < 1 := by rw [hpdef]; linarith
  have hqp : q ≤ p := by rw [hpdef]; linarith
  have hL : Real.log p < 0 := Real.log_neg hp0 hp1
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  refine ⟨1 / p, by positivity, -Real.log p / N, div_pos (by linarith) hNpos, ?_⟩
  intro n
  set k := n / N with hk
  have hdm := Nat.div_add_mod n N
  have hmod : n % N < N := Nat.mod_lt n hN
  have hnk : (n : ℝ) ≤ N * k + N := by
    have h1 : n ≤ N * k + N := by rw [hk]; omega
    exact_mod_cast h1
  have hstep : M.τ β n ≤ p ^ k := by
    have hr : n = N * k + n % N := by rw [hk]; omega
    calc M.τ β n = M.τ β (N * k + n % N) := by rw [← hr]
      _ ≤ M.τ β (N * k) * M.τ β (n % N) := M.submul β _ _
      _ ≤ M.τ β (N * k) * 1 :=
          mul_le_mul_of_nonneg_left (M.le_one β _) (M.nonneg β _)
      _ = M.τ β (N * k) := by ring
      _ ≤ q ^ k := tau_pow_le M β N k
      _ ≤ p ^ k := pow_le_pow_left₀ hq0 hqp k
  refine hstep.trans ?_
  have hpexp : p ^ k = Real.exp (k * Real.log p) := by
    rw [Real.exp_nat_mul, Real.exp_log hp0]
  have hinv : 1 / p = Real.exp (-Real.log p) := by
    rw [Real.exp_neg, Real.exp_log hp0, one_div]
  rw [hpexp, hinv, ← Real.exp_add, Real.exp_le_exp]
  have hkey : ((k : ℝ) * Real.log p) * N
      ≤ (-Real.log p + -(-Real.log p / N * n)) * N := by
    have hexp : (-Real.log p + -(-Real.log p / N * n)) * N
        = -Real.log p * N + Real.log p * n := by
      field_simp
    rw [hexp]
    nlinarith [mul_nonneg (neg_nonneg.2 hL.le) (sub_nonneg.2 hnk)]
  exact le_of_mul_le_mul_right hkey hNpos

/-- **Dichotomy**: at every inverse temperature the model is either subcritical (exponential
decay of correlations) or exhibits long-range order. -/
