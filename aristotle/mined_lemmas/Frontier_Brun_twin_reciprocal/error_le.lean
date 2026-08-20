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

lemma error_le (K : ℕ) :
    ∑ T ∈ Q.powerset.filter (fun T => T.card ≤ K), (2:ℝ)^T.card
      ≤ (K+1) * (2*Q.card + 2)^K := by
  classical
  rw [sum_powerset_filter_card_real Q K (fun j => (2:ℝ)^j)]
  have hterm : ∀ j ∈ range (K+1), (Q.card.choose j : ℝ) * 2^j ≤ (2*Q.card + 2)^K := by
    intro j hj
    have hjK : j ≤ K := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have h1 : (Q.card.choose j : ℝ) ≤ (Q.card : ℝ)^j := by
      exact_mod_cast Nat.choose_le_pow Q.card j
    have h2 : (Q.card : ℝ)^j * 2^j = (2*Q.card)^j := by
      rw [← mul_pow]; ring_nf
    have h3 : ((2:ℝ)*Q.card)^j ≤ (2*Q.card + 2)^K := by
      calc ((2:ℝ)*Q.card)^j ≤ (2*Q.card + 2)^j :=
            pow_le_pow_left₀ (by positivity) (by linarith) j
        _ ≤ (2*Q.card + 2)^K := by
            apply pow_le_pow_right₀ _ hjK
            have : (0:ℝ) ≤ Q.card := by positivity
            linarith
    calc (Q.card.choose j : ℝ) * 2^j ≤ (Q.card : ℝ)^j * 2^j := by
          apply mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (2*Q.card)^j := h2
      _ ≤ (2*Q.card + 2)^K := h3
  calc ∑ j ∈ range (K+1), (Q.card.choose j : ℝ) * 2^j
      ≤ ∑ _j ∈ range (K+1), ((2*Q.card + 2)^K : ℝ) := Finset.sum_le_sum hterm
    _ = (K+1) * (2*Q.card + 2)^K := by
        rw [Finset.sum_const, Finset.card_range]
        simp [nsmul_eq_mul]

/-- **The sieve bound.** -/
