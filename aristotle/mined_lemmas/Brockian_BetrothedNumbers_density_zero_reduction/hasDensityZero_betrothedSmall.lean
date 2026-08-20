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

lemma hasDensityZero_betrothedSmall
    (hcore : ∀ K : ℕ, HasDensityZero {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}) :
    HasDensityZero BetrothedSmall := by
  refine hasDensityZero_of_approx (fun ε hε => ?_)
  obtain ⟨K, hK⟩ := exists_abundancy_bound ε hε
  refine ⟨{n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}, hcore K, fun N => ?_⟩
  have h1 : countUpTo BetrothedSmall N
      ≤ countUpTo ({n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}
        ∪ {n | (K : ℝ) * n < sigmaOne n}) N := countUpTo_mono (betrothedSmall_subset K) N
  have h2 := countUpTo_union_le {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n}
      {n : ℕ | (K : ℝ) * n < sigmaOne n} N
  have h3 := hK N
  have h4 : (countUpTo BetrothedSmall N : ℝ)
      ≤ (countUpTo {n | n ∈ BetrothedSmall ∧ (sigmaOne n : ℝ) ≤ K * n} N : ℝ)
        + (countUpTo {n : ℕ | (K : ℝ) * n < sigmaOne n} N : ℝ) := by
    exact_mod_cast le_trans h1 h2
  linarith

/-! ## Main reduction -/

/-- **Density zero reduction for betrothed numbers.**
Pollack's theorem that the set of betrothed (quasi-amicable) numbers has asymptotic
density zero is reduced here to its analytic core: it suffices to know, for each fixed
bound `K`, that the smaller members of betrothed pairs whose abundancy `σ(n)/n` is at
most `K` form a set of density zero.

The reduction proved here is unconditional and consists of:
* the counting injection from larger to smaller members of betrothed pairs
  (`countUpTo_large_le_small`), so that the whole problem is carried by the smaller
  members;
* the Markov/average-order bound `∑_{n ≤ N} σ(n)/n ≤ 2N` (`sum_sigmaOne_div_le`),
  giving `#{n ≤ N : σ(n) > K n} ≤ 2N/K` (`countUpTo_abundancy_le`), which removes the
  numbers of unbounded abundancy;
* the generic density-zero toolbox (`hasDensityZero_of_approx`,
  `hasDensityZero_of_countUpTo_le`). -/
