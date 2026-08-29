import Mathlib

/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian

/-- The list of all primes not exceeding the wheel modulus `947`. -/
def primesUpTo947 : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
    557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
    809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
    937, 941, 947]

/-- Every entry of `primesUpTo947` really is prime. -/
theorem prime_of_mem_primesUpTo947 : ∀ p ∈ primesUpTo947, Nat.Prime p := by decide

/-- The finite Goldbach search: every `n < 474` with `n ≥ 2` gives an even number `2 * n`
that splits as a sum of two entries of `primesUpTo947`. -/
theorem exists_pair_primesUpTo947 :
    ∀ n ∈ List.range 474, n < 2 ∨ ∃ p ∈ primesUpTo947, ∃ q ∈ primesUpTo947, p + q = 2 * n := by
  decide

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
Every even number `n` with `4 ≤ n ≤ 947` is a sum of two primes. -/
theorem GoldbachWheelK2_947 (n : ℕ) (hn : Even n) (h4 : 4 ≤ n) (hub : n ≤ 947) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n := by
  obtain ⟨k, hk⟩ := hn
  have hmem : k ∈ List.range 474 := List.mem_range.2 (by omega)
  rcases exists_pair_primesUpTo947 k hmem with h | ⟨p, hp, q, hq, hpq⟩
  · omega
  · exact ⟨p, q, prime_of_mem_primesUpTo947 p hp, prime_of_mem_primesUpTo947 q hq, by omega⟩

end Brockian

