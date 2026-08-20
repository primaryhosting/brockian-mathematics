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

theorem classical_query_lower_bound {n : ℕ} (A : ClassicalAlg n) (m : ℕ) (hn : 2 ≤ n)
    (hA : A.Solves m) : 2 ^ ((n - 1) / 2) ≤ m := by
  have hb := classical_query_bound A m hA
  by_contra hlt
  push_neg at hlt
  set k := (n - 1) / 2 with hk
  have hmk : m + 1 ≤ 2 ^ k := hlt
  have h2k : 2 * k ≤ n - 1 := by omega
  have hkn : 2 ^ (2 * k) ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) h2k
  have hpow : 2 ^ k * 2 ^ k = 2 ^ (2 * k) := by
    rw [← pow_add]; ring_nf
  have h1 : (m + 1) * (m + 1) ≤ 2 ^ (n - 1) := by
    calc (m + 1) * (m + 1) ≤ 2 ^ k * 2 ^ k := Nat.mul_le_mul hmk hmk
      _ = 2 ^ (2 * k) := hpow
      _ ≤ 2 ^ (n - 1) := hkn
  have h2 : 2 ^ (n - 1) * 2 = 2 ^ n := by
    have hn1 : n - 1 + 1 = n := by omega
    rw [← pow_succ, hn1]
  have h3 : (4 : ℕ) ≤ 2 ^ n := by
    calc (4 : ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  nlinarith [h1, h2, h3, hb]

end QI

import RequestProject.Simon.Classical

/-!
# Non-vacuity: promise instances exist, and Simon's problem is classically solvable

To make sure that the statements of the classical model are not vacuous we check that

* for every nonzero `s` there is an oracle satisfying Simon's promise with period `s`
  (`QI.exists_simonPromise`), and
* there *is* a deterministic classical algorithm solving Simon's problem, namely the brute-force
  one querying all `2ⁿ` points (`QI.exists_classical_solver`).

Together with `QI.classical_query_lower_bound` this shows that the classical query complexity of
Simon's problem lies between `2^{(n-1)/2}` and `2ⁿ`.
-/

namespace QI

open Finset

/-- Simon's promise is satisfiable for every nonzero period. -/
