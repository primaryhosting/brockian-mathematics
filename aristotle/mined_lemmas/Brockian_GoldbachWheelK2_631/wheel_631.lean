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
