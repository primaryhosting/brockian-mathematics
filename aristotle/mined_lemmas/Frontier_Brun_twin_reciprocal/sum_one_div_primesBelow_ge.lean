import Mathlib
import RequestProject.Brun.Final

/-!
# Brun Twin Reciprocal
Category: Frontier — Prime Numbers
Target: Frontier.Brun_twin_reciprocal
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- doc comments, so the required header comment appears immediately after the imports.)

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-- **Brun's theorem**: the sum of the reciprocals of the twin primes converges.

The summand is `1/n` whenever `n` and `n + 2` are both prime, and `0` otherwise; the value of
its sum is Brun's constant.  Convergence is proved from scratch by a Brun pure sieve; see the
development in `RequestProject/Brun/`. -/

theorem sum_one_div_primesBelow_ge (N : ℕ) (hN : 3 ≤ N) :
    Real.log (Real.log N) - Real.log 2 ≤ ∑ p ∈ Nat.primesBelow N, (1 : ℝ) / p := by
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : 2 ≤ n := by omega
  have hharm : Real.log ((n:ℝ) + 1) ≤ ∑ k ∈ Icc 1 n, (1 : ℝ) / k := by
    have h := log_add_one_le_harmonic n
    have h2 : ((harmonic n : ℚ) : ℝ) = ∑ k ∈ Icc 1 n, (1 : ℝ) / k := by
      rw [harmonic_eq_sum_Icc]
      push_cast
      simp [one_div]
    rw [h2] at h
    simpa using h
  have hchain : Real.log ((n:ℝ) + 1) ≤ 2 * Real.exp (∑ p ∈ Nat.primesBelow (n+1), (1 : ℝ) / p) := by
    calc Real.log ((n:ℝ)+1) ≤ ∑ k ∈ Icc 1 n, (1 : ℝ) / k := hharm
      _ ≤ (∑ a ∈ (Icc 1 n).filter Squarefree, (1 : ℝ) / a) *
            (∑ b ∈ Icc 1 n, (1 : ℝ) / (b : ℝ) ^ 2) := harmonic_le_mul n
      _ ≤ (∏ p ∈ Nat.primesBelow (n + 1), (1 + (1 : ℝ) / p)) * 2 := by
          apply mul_le_mul (sum_squarefree_le_prod n) (sum_one_div_sq_le n)
          · positivity
          · exact le_trans (by positivity) (sum_squarefree_le_prod n)
      _ = 2 * (∏ p ∈ Nat.primesBelow (n + 1), (1 + (1 : ℝ) / p)) := by ring
      _ ≤ 2 * Real.exp (∑ p ∈ Nat.primesBelow (n+1), (1 : ℝ) / p) := by
          have := prod_one_add_le_exp (Nat.primesBelow (n+1))
          linarith
  have hlogpos : 0 < Real.log ((n:ℝ)+1) := by
    apply Real.log_pos
    have : (2:ℝ) ≤ n := by exact_mod_cast hn
    linarith
  have := Real.log_le_log (by positivity) hchain
  rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp] at this
  push_cast
  linarith

end Brun

import RequestProject.Brun.Counting

/-!
# Brun's pure sieve

Truncated inclusion–exclusion (Bonferroni) applied to the twin prime sieve.
The main result of this file, `Brun.sieve_main`, bounds the number of `n < N` such that
`n (n+2)` is coprime to all primes in a finite set `Q` of odd primes.
-/

open Finset

namespace Brun

/-- Alternating sum of binomial coefficients. -/
