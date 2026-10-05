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

namespace Frontier

/-!
## The Ising model on a finite chain

We set up the nearest-neighbour Ising model with free boundary conditions on the
segment `{0, 1, …, n}` and compute its two-point function exactly.  This is the
one-dimensional base case of the sharpness of the phase transition
(Duminil-Copin–Tassion): the two-point function decays exponentially at *every*
finite inverse temperature, so the critical inverse temperature is `+∞` and the
subcritical phase (exponential decay of correlations, finite susceptibility)
occupies the whole of `[0, ∞)`.
-/

namespace IsingChain

/-- The spin value attached to a Boolean: `true ↦ +1`, `false ↦ -1`. -/

theorem exponential_decay (β : ℝ) :
    ∃ c : ℝ, 0 < c ∧ ∀ n : ℕ, |corr β n| ≤ Real.exp (-(c * n)) := by
  rcases eq_or_ne (Real.tanh β) 0 with h0 | h0
  · refine ⟨1, one_pos, fun n => ?_⟩
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [corr_eq, h0]
    · rw [corr_eq, h0, zero_pow (by omega)]
      simp [Real.exp_nonneg]
  · refine ⟨-Real.log |Real.tanh β|, ?_, fun n => ?_⟩
    · have h1 : |Real.tanh β| < 1 := abs_tanh_lt_one β
      have h2 : 0 < |Real.tanh β| := abs_pos.mpr h0
      have := Real.log_neg h2 h1
      linarith
    · have h2 : 0 < |Real.tanh β| := abs_pos.mpr h0
      rw [corr_eq, abs_pow]
      rw [show -(-Real.log |Real.tanh β| * (n : ℝ)) = (n : ℝ) * Real.log |Real.tanh β| by ring,
        ← Real.log_pow, Real.exp_log (by positivity)]

/-- Correlations tend to zero: the chain has no long-range order at any finite `β`. -/
