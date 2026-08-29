import Mathlib

/-!
# Goldbach Wheel K 2 727
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_727
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 4000000
set_option maxRecDepth 20000

namespace Brockian

/-- The Goldbach "wheel" statement with `K = 2` spokes at modulus `M`:
every even number `n` with `4 ≤ n ≤ 2 * M` is a sum of two primes. -/

theorem wheelPrimes_prime : ∀ p ∈ wheelPrimes, Nat.Prime p := by
  intro p hp
  rw [wheelPrimes] at hp
  rw [List.mem_append] at hp
  rw [List.mem_append] at hp
  rw [List.mem_append] at hp
  rw [List.mem_append] at hp
  rw [List.mem_append] at hp
  rw [List.mem_append] at hp
  rw [List.mem_append] at hp
  rcases hp with ((((((h | h) | h) | h) | h) | h) | h) | h
  · exact wheelChunk0_prime p h
  · exact wheelChunk1_prime p h
  · exact wheelChunk2_prime p h
  · exact wheelChunk3_prime p h
  · exact wheelChunk4_prime p h
  · exact wheelChunk5_prime p h
  · exact wheelChunk6_prime p h
  · exact wheelChunk7_prime p h

/-- The small primes used as the first summand of each Goldbach pair. -/
