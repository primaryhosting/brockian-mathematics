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

theorem card_divisible_approx (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) :
    |(#((range N).filter (fun n => ∀ p ∈ T, p ∣ n*(n+2))) : ℝ)
      - N * 2 ^ T.card / (∏ p ∈ T, p)| ≤ 2 ^ T.card := by
  classical
  rw [filter_dvd_eq_biUnion T hT N, Finset.card_biUnion (pairwiseDisjoint_pieces T hT N)]
  have hsplit : (N : ℝ) * 2 ^ T.card / (∏ p ∈ T, p)
      = ∑ U ∈ T.powerset, (N : ℝ) / (∏ p ∈ T, p) := by
    rw [Finset.sum_const, Finset.card_powerset]
    simp [nsmul_eq_mul]
    ring
  rw [hsplit, Nat.cast_sum, ← Finset.sum_sub_distrib]
  calc |∑ U ∈ T.powerset, ((#((range N).filter
          (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) : ℝ) - N / (∏ p ∈ T, p))|
      ≤ ∑ U ∈ T.powerset, |(#((range N).filter
          (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) : ℝ) - N / (∏ p ∈ T, p)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ U ∈ T.powerset, (1:ℝ) := by
        refine Finset.sum_le_sum fun U hU => piece_approx T hT N U (Finset.mem_powerset.1 hU)
    _ = 2 ^ T.card := by rw [Finset.sum_const, Finset.card_powerset]; simp

end Brun

import RequestProject.Brun.Sieve

/-!
# Analytic estimates for Brun's pure sieve

We bound the main term and the error term of `Brun.sieve_main`, obtaining
`Brun.sifted_bound`: with `S = ∑ p ∈ Q, 2/p` and `K` even with `(e+1) S ≤ K + 1`,
the number of `n < N` with `n (n+2)` coprime to all `p ∈ Q` is at most
`2 N exp (-S) + (K+1) (2 |Q| + 2) ^ K`.
-/

open Finset

namespace Brun

variable (Q : Finset ℕ)

/-- `∏ (1 - 2/p) ≤ exp (-S)`. -/
