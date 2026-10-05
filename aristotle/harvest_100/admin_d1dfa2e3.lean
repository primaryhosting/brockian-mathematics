import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian

/-- The "wheel" of primes for modulus `1327`: the list of all prime numbers `p ≤ 1327`.
Note that the modulus `1327` is itself prime, so it is the last entry. -/
def wheelPrimes1327 : List Nat :=
  [   2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89,
   97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191,
   193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283,
   293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401,
   409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509,
   521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631,
   641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751,
   757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877,
   881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009,
   1013, 1019, 1021, 1031, 1033, 1039, 1049, 1051, 1061, 1063, 1069, 1087, 1091, 1093, 1097,
   1103, 1109, 1117, 1123, 1129, 1151, 1153, 1163, 1171, 1181, 1187, 1193, 1201, 1213, 1217,
   1223, 1229, 1231, 1237, 1249, 1259, 1277, 1279, 1283, 1289, 1291, 1297, 1301, 1303, 1307,
   1319, 1321, 1327]

/-- Every entry of the wheel is prime. -/
theorem wheelPrimes1327_prime : ∀ p ∈ wheelPrimes1327, Nat.Prime p := by
  intro p hp
  fin_cases hp <;> norm_num

/-- Combinatorial core: for every even `n` with `4 ≤ n ≤ 1327` there is an entry `p` of the
wheel such that `n - p` is also an entry of the wheel.  Verified by kernel evaluation. -/
set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
theorem wheel1327_core :
    ∀ n < 1328, 4 ≤ n → n % 2 = 0 → ∃ p ∈ wheelPrimes1327, (n - p) ∈ wheelPrimes1327 := by
  decide +kernel

/-- **Goldbach's conjecture, verified on the wheel of modulus 1327** (`K = 2` summands):
every even natural number `n` with `4 ≤ n ≤ 1327` is a sum of two primes. -/
theorem GoldbachWheelK2_1327 :
    ∀ n : Nat, 4 ≤ n → n ≤ 1327 → Even n → ∃ p q : Nat, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  intro n h4 hle hev
  have hlt : n < 1328 := by omega
  have hmod : n % 2 = 0 := Nat.even_iff.mp hev
  obtain ⟨p, hp, hq⟩ := wheel1327_core n hlt h4 hmod
  have hpp : Nat.Prime p := wheelPrimes1327_prime p hp
  have hqp : Nat.Prime (n - p) := wheelPrimes1327_prime (n - p) hq
  have h2 : 2 <= n - p := hqp.two_le
  exact ⟨p, n - p, hpp, hqp, by omega⟩

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

