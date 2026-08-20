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

theorem summable_twinRecip : Summable twinRecip := by
  apply summable_of_sum_range_le (c := (aa 16 : ℝ) + (∑' j, vv j) + 2 * (1 - rt)⁻¹)
    twinRecip_nonneg
  intro M
  have hM : M ≤ 2^M := Nat.le_of_lt (Nat.lt_two_pow_self)
  have h1 : ∑ n ∈ range M, twinRecip n ≤ ∑ n ∈ range (2^M), twinRecip n := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro x hx
      exact Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 hx) hM)
    · intro i _ _
      exact twinRecip_nonneg i
  have h2 : ∑ n ∈ range (2^M), twinRecip n
      = twinRecip 0 + ∑ n ∈ Ico 1 (2^M), twinRecip n := by
    have := Finset.sum_range_add_sum_Ico twinRecip (m := 1) (n := 2^M) Nat.one_le_two_pow
    rw [← this]
    simp
  have h3 : twinRecip 0 = 0 := by
    unfold twinRecip
    rw [if_neg]
    rintro ⟨h, -⟩
    exact absurd h (by norm_num)
  rw [h2, h3, zero_add, sum_Ico_dyadic] at h1
  exact h1.trans (sum_block_le M)

end Brun

import Mathlib

/-!
# Counting `n < N` with `n (n+2)` divisible by a set of odd primes

The main result is `Brun.card_divisible_approx`: for a finite set `T` of odd primes,
the number of `n < N` such that every `p ∈ T` divides `n (n+2)` differs from
`N * 2 ^ |T| / ∏ p ∈ T, p` by at most `2 ^ |T|`.
-/

open Finset

namespace Brun

section Periodic

variable (P : ℕ → Prop) [DecidablePred P]

