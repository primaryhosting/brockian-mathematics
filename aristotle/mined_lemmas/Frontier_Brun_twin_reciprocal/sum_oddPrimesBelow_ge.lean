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

lemma sum_oddPrimesBelow_ge (W : ℕ) (hW : 3 ≤ W) :
    2 * (Real.log (Real.log W) - Real.log 2) - 1 ≤ ∑ p ∈ oddPrimesBelow W, 2/(p:ℝ) := by
  classical
  have hmert := sum_one_div_primesBelow_ge W hW
  have hsplit : ∑ p ∈ Nat.primesBelow W, (1:ℝ)/p
      = (if 2 ∈ Nat.primesBelow W then (1:ℝ)/2 else 0) + ∑ p ∈ oddPrimesBelow W, (1:ℝ)/p := by
    by_cases h2 : 2 ∈ Nat.primesBelow W
    · rw [if_pos h2]
      have : oddPrimesBelow W = (Nat.primesBelow W).erase 2 := by
        unfold oddPrimesBelow
        ext p
        simp [Finset.mem_erase, Finset.mem_filter]
        tauto
      rw [this]
      have := Finset.add_sum_erase (Nat.primesBelow W) (fun p => (1:ℝ)/p) h2
      simpa using this.symm
    · rw [if_neg h2]
      have : oddPrimesBelow W = Nat.primesBelow W := by
        unfold oddPrimesBelow
        apply Finset.filter_true_of_mem
        intro p hp
        rintro rfl
        exact h2 hp
      rw [this, zero_add]
  have hhalf : (if 2 ∈ Nat.primesBelow W then (1:ℝ)/2 else 0) ≤ 1/2 := by
    split <;> norm_num
  have hdouble : ∑ p ∈ oddPrimesBelow W, 2/(p:ℝ) = 2 * ∑ p ∈ oddPrimesBelow W, (1:ℝ)/p := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun p _ => by ring
  rw [hdouble]
  linarith

/-- Greedy choice of a subset with prescribed sum. -/
