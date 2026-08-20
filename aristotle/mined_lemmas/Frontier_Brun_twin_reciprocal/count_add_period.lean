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

lemma count_add_period (M : ℕ) (hper : ∀ n, P (n + M) ↔ P n) (n : ℕ) :
    #((range (n + M)).filter P) = #((range n).filter P) + #((range M).filter P) := by
  induction n with
  | zero => simp
  | succ k ih =>
    have h1 : k + 1 + M = (k + M) + 1 := by ring
    rw [h1, Finset.range_add_one, Finset.range_add_one, Finset.filter_insert, Finset.filter_insert]
    by_cases h : P k
    · have h2 : P (k + M) := (hper k).mpr h
      rw [if_pos h2, if_pos h, Finset.card_insert_of_notMem (by simp),
        Finset.card_insert_of_notMem (by simp), ih]
      omega
    · have h2 : ¬ P (k + M) := fun hc => h ((hper k).mp hc)
      rw [if_neg h2, if_neg h, ih]

