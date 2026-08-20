import Mathlib
/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Finset

/-! ## Natural density -/

/-- The number of elements of `A` in the interval `[1, N]`. -/

lemma hasDensityZero_of_countUpTo_le {A B : Set ℕ} (c : ℝ)
    (hB : HasDensityZero B) (h : ∀ N, (countUpTo A N : ℝ) ≤ c * countUpTo B N) :
    HasDensityZero A := by
  have h0 : Filter.Tendsto (fun N : ℕ => c * ((countUpTo B N : ℝ) / N)) Filter.atTop (nhds 0) := by
    simpa using hB.const_mul c
  refine squeeze_zero' ?_ ?_ h0
  · filter_upwards [Filter.eventually_ge_atTop 1] with N _
    positivity
  · filter_upwards [Filter.eventually_ge_atTop 1] with N hN
    rw [mul_div_assoc']
    have : (0:ℝ) < N := by exact_mod_cast hN
    gcongr
    exact h N

/-- Approximation test: a set that is, up to a set of density `≤ ε`, covered by a
density-zero set for every `ε > 0`, has density zero. -/
