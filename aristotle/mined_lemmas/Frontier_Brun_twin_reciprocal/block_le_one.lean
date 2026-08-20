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

lemma block_le_one (i : ℕ) : block i ≤ 1 := by
  classical
  have h1 : ∀ n ∈ Ico (2^i) (2^(i+1)), twinRecip n ≤ (1:ℝ)/2^i := by
    intro n hn
    rw [Finset.mem_Ico] at hn
    unfold twinRecip
    split
    · apply one_div_le_one_div_of_le
      · positivity
      · exact_mod_cast hn.1
    · positivity
  calc block i ≤ ∑ _n ∈ Ico (2^i) (2^(i+1)), (1:ℝ)/2^i := Finset.sum_le_sum h1
    _ = 1 := by
        rw [Finset.sum_const, Nat.card_Ico]
        have : (2:ℕ)^(i+1) - 2^i = 2^i := by
          have : (2:ℕ)^(i+1) = 2 * 2^i := by ring
          omega
        rw [this, nsmul_eq_mul]
        field_simp
        push_cast
        ring

/-- The block index threshold for sieve parameter `j`. -/
