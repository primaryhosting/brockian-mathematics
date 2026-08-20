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

lemma bonferroni_pointwise (R : Finset ℕ) (K : ℕ) (hK : Even K) :
    (if R = ∅ then (1:ℤ) else 0)
      ≤ ∑ T ∈ R.powerset.filter (fun T => T.card ≤ K), (-1:ℤ)^T.card := by
  classical
  by_cases h : R = ∅
  · subst h
    rw [if_pos rfl, Finset.powerset_empty, Finset.filter_singleton]
    simp
  · rw [if_neg h, sum_powerset_filter_card]
    obtain ⟨s, hs⟩ : ∃ s, R.card = s + 1 := by
      refine ⟨R.card - 1, ?_⟩
      have : 0 < R.card := Finset.card_pos.2 (Finset.nonempty_iff_ne_empty.2 h)
      omega
    rw [hs, alt_sum_choose, hK.neg_one_pow]
    positivity

/-- Brun's pure sieve inequality, in integer form. -/
