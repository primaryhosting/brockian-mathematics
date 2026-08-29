import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The statement of Chen's theorem -/

/-- `AlmostPrime2 q` says that `q` has at most two prime factors, counted with
multiplicity (i.e. `Ω(q) ≤ 2`); such a number is classically called a `P₂`.
Note that primes themselves satisfy this (`Ω = 1`). -/

theorem goldbach_base (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1000) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  have hmem : n ∈ List.range 1002 := List.mem_range.2 (by omega)
  have h := (List.all_eq_true.1 goldbach_check) n hmem
  have h4' : (decide (n < 4)) = false := by simp; omega
  have hpar : (n % 2 == 1) = false := by
    have : n % 2 = 0 := Nat.even_iff.1 he
    simp [this]
  rw [h4', hpar] at h
  simp only [Bool.false_or, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, hple, hcont⟩ := h
  refine ⟨p, n - p, primesBelow1000_prime p hp, primesBelow1000_prime _ ?_, by omega⟩
  simpa using List.mem_of_elem_eq_true hcont

/-- **Base case of Chen's theorem**, verified by kernel computation: every even number `n`
with `4 ≤ n ≤ 1000` is the sum of a prime and a `P₂` (in fact, of two primes). -/
