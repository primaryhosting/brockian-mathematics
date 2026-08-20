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

lemma piece_approx (T : Finset ℕ) (hT : ∀ p ∈ T, p.Prime ∧ p ≠ 2) (N : ℕ) (U : Finset ℕ)
    (hU : U ⊆ T) :
    |(#((range N).filter (fun n => (∏ p ∈ U, p) ∣ n ∧ (∏ p ∈ T \ U, p) ∣ n+2)) : ℝ)
      - N / (∏ p ∈ T, p)| ≤ 1 := by
  classical
  set a := ∏ p ∈ U, p with hha
  set b := ∏ p ∈ T \ U, p with hhb
  have hab : a * b = ∏ p ∈ T, p := by
    rw [hha, hhb, mul_comm]
    exact Finset.prod_sdiff hU
  have ha : 0 < a := Finset.prod_pos (fun p hp => (hT p (hU hp)).1.pos)
  have hb : 0 < b := Finset.prod_pos (fun p hp => (hT p (Finset.mem_sdiff.1 hp).1).1.pos)
  have hcop : Nat.Coprime a b := by
    apply Nat.Coprime.prod_left
    intro p hp
    apply Nat.Coprime.prod_right
    intro q hq
    have hne : p ≠ q := by
      rintro rfl
      exact (Finset.mem_sdiff.1 hq).2 hp
    exact (Nat.coprime_primes (hT p (hU hp)).1 (hT q (Finset.mem_sdiff.1 hq).1).1).2 hne
  rw [← hab]
  push_cast
  exact count_pair_approx a b N ha hb hcop

/-- **Main counting estimate.** For a finite set `T` of odd primes, the number of `n < N`
with `n (n+2)` divisible by every `p ∈ T` is `N * 2 ^ |T| / ∏ p ∈ T, p` up to an error of
at most `2 ^ |T|`. -/
