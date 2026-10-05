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
def GoldbachWheelK2 (M : Nat) : Prop :=
  ∀ n : Nat, Even n → 4 ≤ n → n ≤ 2 * M →
    ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ p + q = n

private def wheelChunk0 : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113]

private lemma wheelChunk0_prime : ∀ p ∈ wheelChunk0, Nat.Prime p := by
  decide

private def wheelChunk1 : List ℕ := [127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281]

private lemma wheelChunk1_prime : ∀ p ∈ wheelChunk1, Nat.Prime p := by
  decide

private def wheelChunk2 : List ℕ := [283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463]

private lemma wheelChunk2_prime : ∀ p ∈ wheelChunk2, Nat.Prime p := by
  decide

private def wheelChunk3 : List ℕ := [467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659]

private lemma wheelChunk3_prime : ∀ p ∈ wheelChunk3, Nat.Prime p := by
  decide

private def wheelChunk4 : List ℕ := [661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863]

private lemma wheelChunk4_prime : ∀ p ∈ wheelChunk4, Nat.Prime p := by
  decide

private def wheelChunk5 : List ℕ := [877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069]

private lemma wheelChunk5_prime : ∀ p ∈ wheelChunk5, Nat.Prime p := by
  decide

private def wheelChunk6 : List ℕ := [1087, 1091, 1093, 1097, 1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217, 1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291]

private lemma wheelChunk6_prime : ∀ p ∈ wheelChunk6, Nat.Prime p := by
  decide

private def wheelChunk7 : List ℕ := [1297, 1301, 1303, 1307, 1319, 1321, 1327, 1361, 1367, 1373, 1381, 1399, 1409, 1423, 1427, 1429, 1433, 1439, 1447, 1451, 1453]

private lemma wheelChunk7_prime : ∀ p ∈ wheelChunk7, Nat.Prime p := by
  decide

/-- The list of all primes below `2 * 727 = 1454`: the wheel's spoke set. -/
def wheelPrimes : List ℕ :=
  wheelChunk0 ++ wheelChunk1 ++ wheelChunk2 ++ wheelChunk3 ++ wheelChunk4 ++ wheelChunk5 ++ wheelChunk6 ++ wheelChunk7

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
def wheelSmallPrimes : List ℕ := [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

theorem wheelSmallPrimes_prime : ∀ p ∈ wheelSmallPrimes, Nat.Prime p := by
  decide

private lemma goldbach_check :
    ∀ k ∈ Finset.range 728, 2 ≤ k →
      ∃ p ∈ wheelSmallPrimes, p ≤ 2 * k ∧ (2 * k - p) ∈ wheelPrimes := by
  decide

theorem GoldbachWheelK2_727 : GoldbachWheelK2 727 := by
  intro n hn h4 hle
  obtain ⟨k, rfl⟩ := hn
  have hk : k + k = 2 * k := by ring
  rw [hk] at h4 hle ⊢
  have hk2 : 2 ≤ k := by omega
  have hkr : k ∈ Finset.range 728 := by
    simp only [Finset.mem_range]; omega
  obtain ⟨p, hpmem, hple, hqmem⟩ := goldbach_check k hkr hk2
  exact ⟨p, 2 * k - p, wheelSmallPrimes_prime p hpmem, wheelPrimes_prime _ hqmem, by omega⟩

end Brockian

import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

