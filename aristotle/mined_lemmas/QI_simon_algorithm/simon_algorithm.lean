/-
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib
import RequestProject.Simon.Defs
import RequestProject.Simon.Quantum
import RequestProject.Simon.Classical
import RequestProject.Simon.Sampling
import RequestProject.Simon.Upper

/-!
# Simon Algorithm
Category: Frontier Qi
Target: QI.simon_algorithm
Statement: Simon's problem is solved with O(n) quantum queries but needs Ω(2^{n/2}) classically.
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

namespace QI

open Finset

/-- The measurement outcomes of Simon's circuit form a probability distribution. -/

theorem simon_algorithm (n : ℕ) :
    (∀ (f : BV n → BV n) (s : BV n), SimonPromise f s →
        (∑ y : BV n, simonProb f y = 1) ∧
        (∀ y : BV n, simonProb f y = if dot s y = 0 then 2 / 2 ^ n else 0)) ∧
    (∀ s : BV n,
        ((badSamples s (2 * n)).card : ℝ) / ((allSamples s (2 * n)).card : ℝ) ≤ 1 / 2 ^ n) ∧
    (∀ (s : BV n) (y : Fin (2 * n) → BV n), Determines y s →
        ∀ t : BV n, t ≠ 0 → (∀ i, dot (y i) t = 0) → t = s) ∧
    (2 ≤ n → ∀ (A : ClassicalAlg n) (m : ℕ), A.Solves m → 2 ^ ((n - 1) / 2) ≤ m) ∧
    ((∀ s : BV n, s ≠ 0 → ∃ f : BV n → BV n, SimonPromise f s) ∧
      ∃ A : ClassicalAlg n, A.Solves (2 ^ n)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f s h
    exact ⟨simonProb_sum_eq_one h, fun y => simonProb_eq h y⟩
  · intro s
    exact sampling_failure_prob s
  · intro s y h t ht hty
    exact h.unique ht hty
  · intro hn A m hA
    exact classical_query_lower_bound A m hn hA
  · intro s hs
    exact exists_simonPromise s hs
  · exact exists_classical_solver n

end QI

import RequestProject.Simon.Defs

/-!
# Recovering the period from the quantum samples

Each run of Simon's quantum circuit costs one oracle query and returns a uniformly random vector
of the hyperplane `Orth s = {y | y ⬝ s = 0}`.  Here we show that `O(n)` such samples determine `s`:
the proportion of sample tuples `y : Fin m → Orth s` that fail to pin down `s` is at most
`2ⁿ / 2ᵐ`, so `m = 2n` samples suffice to make the failure probability at most `2⁻ⁿ`.
-/

namespace QI

open Finset

/-- The hyperplane of vectors orthogonal to `s`. -/
