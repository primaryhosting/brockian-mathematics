/-
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` before any module docstring, so the header above is a plain
-- comment and is repeated below as the module docstring.)
import Mathlib

/-!
# Goldbach Wheel K 2 631
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_631
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian

/-- The finite "wheel" of small primes used as the first summand. -/
def wheelPrimes631 : List Nat := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 41, 43, 47, 73]

private theorem wheel_chunk_0 :
    ∀ n ∈ List.range' 2 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_1 :
    ∀ n ∈ List.range' 65 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_2 :
    ∀ n ∈ List.range' 128 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_3 :
    ∀ n ∈ List.range' 191 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_4 :
    ∀ n ∈ List.range' 254 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_5 :
    ∀ n ∈ List.range' 317 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_6 :
    ∀ n ∈ List.range' 380 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_7 :
    ∀ n ∈ List.range' 443 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_8 :
    ∀ n ∈ List.range' 506 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

private theorem wheel_chunk_9 :
    ∀ n ∈ List.range' 569 63, ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  decide

/-- Every half-value `n` with `2 ≤ n ≤ 631` admits a wheel prime `p` such that `2 * n - p`
is again prime. -/
theorem wheel_631 (n : Nat) (hlo : 2 ≤ n) (hhi : n ≤ 631) :
    ∃ p ∈ wheelPrimes631, Nat.Prime p ∧ Nat.Prime (2 * n - p) := by
  by_cases c0 : n < 65
  · exact wheel_chunk_0 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c1 : n < 128
  · exact wheel_chunk_1 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c2 : n < 191
  · exact wheel_chunk_2 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c3 : n < 254
  · exact wheel_chunk_3 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c4 : n < 317
  · exact wheel_chunk_4 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c5 : n < 380
  · exact wheel_chunk_5 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c6 : n < 443
  · exact wheel_chunk_6 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c7 : n < 506
  · exact wheel_chunk_7 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c8 : n < 569
  · exact wheel_chunk_8 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  by_cases c9 : n < 632
  · exact wheel_chunk_9 n (List.mem_range'_1.2 ⟨by omega, by omega⟩)
  exact absurd hhi (by omega)

/-- **Goldbach wheel, K = 2, modulus 631.**
Every even number `n` with `4 ≤ n ≤ 2 * 631 = 1262` is a sum of two primes. -/
theorem GoldbachWheelK2_631 (n : Nat) (heven : Even n) (h4 : 4 ≤ n) (hn : n ≤ 1262) :
    ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  obtain ⟨m, rfl⟩ := heven
  obtain ⟨p, -, hp, hq⟩ := wheel_631 m (by omega) (by omega)
  refine ⟨p, 2 * m - p, hp, hq, ?_⟩
  have hne : 2 * m - p ≠ 0 := by
    intro h
    rw [h] at hq
    exact Nat.not_prime_zero hq
  omega

end Brockian

#print axioms Brockian.GoldbachWheelK2_631

