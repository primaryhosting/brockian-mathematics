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

/-
# Oppermann Conjecture
Category: Brockian Conjecture
Target: Brockian.OppermannConjecture.OppermannConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace Brockian.OppermannConjecture

/-- Oppermann's property for `n`: there is a prime strictly between `n(n-1)` and `n²`,
and a prime strictly between `n²` and `n(n+1)`. -/
def OppermannProperty (n : ℕ) : Prop :=
  (∃ p : ℕ, Nat.Prime p ∧ n * n - n < p ∧ p < n * n) ∧
  (∃ p : ℕ, Nat.Prime p ∧ n * n < p ∧ p < n * n + n)

/-- A short-interval prime hypothesis with threshold `X`: for every `x ≥ X` there is a prime
strictly between `x` and `x + √x`. -/
def ShortIntervalPrimes (X : ℕ) : Prop :=
  ∀ x : ℕ, X ≤ x → ∃ p : ℕ, Nat.Prime p ∧ x < p ∧ p < x + Nat.sqrt x

/-- Unconditional verification of Oppermann's property for every `n` with `2 ≤ n ≤ 500`,
by exhibiting explicit primes in the two intervals. -/
lemma oppermannProperty_of_le_500 (n : ℕ) (h2 : 2 ≤ n) (h500 : n ≤ 500) :
    OppermannProperty n := by
  interval_cases n
  · exact ⟨⟨3, by norm_num, by norm_num, by norm_num⟩, ⟨5, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨7, by norm_num, by norm_num, by norm_num⟩, ⟨11, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨13, by norm_num, by norm_num, by norm_num⟩, ⟨17, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨23, by norm_num, by norm_num, by norm_num⟩, ⟨29, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨31, by norm_num, by norm_num, by norm_num⟩, ⟨37, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨43, by norm_num, by norm_num, by norm_num⟩, ⟨53, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨59, by norm_num, by norm_num, by norm_num⟩, ⟨67, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨73, by norm_num, by norm_num, by norm_num⟩, ⟨83, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨97, by norm_num, by norm_num, by norm_num⟩, ⟨101, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨113, by norm_num, by norm_num, by norm_num⟩, ⟨127, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨137, by norm_num, by norm_num, by norm_num⟩, ⟨149, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨157, by norm_num, by norm_num, by norm_num⟩, ⟨173, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨191, by norm_num, by norm_num, by norm_num⟩, ⟨197, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨211, by norm_num, by norm_num, by norm_num⟩, ⟨227, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨241, by norm_num, by norm_num, by norm_num⟩, ⟨257, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨277, by norm_num, by norm_num, by norm_num⟩, ⟨293, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨307, by norm_num, by norm_num, by norm_num⟩, ⟨331, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨347, by norm_num, by norm_num, by norm_num⟩, ⟨367, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨383, by norm_num, by norm_num, by norm_num⟩, ⟨401, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨421, by norm_num, by norm_num, by norm_num⟩, ⟨443, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨463, by norm_num, by norm_num, by norm_num⟩, ⟨487, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨509, by norm_num, by norm_num, by norm_num⟩, ⟨541, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨557, by norm_num, by norm_num, by norm_num⟩, ⟨577, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨601, by norm_num, by norm_num, by norm_num⟩, ⟨631, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨653, by norm_num, by norm_num, by norm_num⟩, ⟨677, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨709, by norm_num, by norm_num, by norm_num⟩, ⟨733, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨757, by norm_num, by norm_num, by norm_num⟩, ⟨787, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨821, by norm_num, by norm_num, by norm_num⟩, ⟨853, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨877, by norm_num, by norm_num, by norm_num⟩, ⟨907, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨937, by norm_num, by norm_num, by norm_num⟩, ⟨967, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨997, by norm_num, by norm_num, by norm_num⟩, ⟨1031, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1061, by norm_num, by norm_num, by norm_num⟩, ⟨1091, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1123, by norm_num, by norm_num, by norm_num⟩, ⟨1163, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1193, by norm_num, by norm_num, by norm_num⟩, ⟨1229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1277, by norm_num, by norm_num, by norm_num⟩, ⟨1297, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1361, by norm_num, by norm_num, by norm_num⟩, ⟨1373, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1409, by norm_num, by norm_num, by norm_num⟩, ⟨1447, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1483, by norm_num, by norm_num, by norm_num⟩, ⟨1523, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1567, by norm_num, by norm_num, by norm_num⟩, ⟨1601, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1657, by norm_num, by norm_num, by norm_num⟩, ⟨1693, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1723, by norm_num, by norm_num, by norm_num⟩, ⟨1777, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1811, by norm_num, by norm_num, by norm_num⟩, ⟨1861, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1901, by norm_num, by norm_num, by norm_num⟩, ⟨1949, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨1987, by norm_num, by norm_num, by norm_num⟩, ⟨2027, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2081, by norm_num, by norm_num, by norm_num⟩, ⟨2129, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2179, by norm_num, by norm_num, by norm_num⟩, ⟨2213, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2267, by norm_num, by norm_num, by norm_num⟩, ⟨2309, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2357, by norm_num, by norm_num, by norm_num⟩, ⟨2411, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2459, by norm_num, by norm_num, by norm_num⟩, ⟨2503, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2551, by norm_num, by norm_num, by norm_num⟩, ⟨2609, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2657, by norm_num, by norm_num, by norm_num⟩, ⟨2707, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2767, by norm_num, by norm_num, by norm_num⟩, ⟨2819, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2879, by norm_num, by norm_num, by norm_num⟩, ⟨2917, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨2971, by norm_num, by norm_num, by norm_num⟩, ⟨3037, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3083, by norm_num, by norm_num, by norm_num⟩, ⟨3137, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3203, by norm_num, by norm_num, by norm_num⟩, ⟨3251, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3307, by norm_num, by norm_num, by norm_num⟩, ⟨3371, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3433, by norm_num, by norm_num, by norm_num⟩, ⟨3491, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3541, by norm_num, by norm_num, by norm_num⟩, ⟨3607, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3671, by norm_num, by norm_num, by norm_num⟩, ⟨3727, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3793, by norm_num, by norm_num, by norm_num⟩, ⟨3847, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨3907, by norm_num, by norm_num, by norm_num⟩, ⟨3989, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4049, by norm_num, by norm_num, by norm_num⟩, ⟨4099, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4177, by norm_num, by norm_num, by norm_num⟩, ⟨4229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4297, by norm_num, by norm_num, by norm_num⟩, ⟨4357, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4423, by norm_num, by norm_num, by norm_num⟩, ⟨4493, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4561, by norm_num, by norm_num, by norm_num⟩, ⟨4637, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4703, by norm_num, by norm_num, by norm_num⟩, ⟨4783, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4831, by norm_num, by norm_num, by norm_num⟩, ⟨4903, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨4973, by norm_num, by norm_num, by norm_num⟩, ⟨5051, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨5113, by norm_num, by norm_num, by norm_num⟩, ⟨5189, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨5261, by norm_num, by norm_num, by norm_num⟩, ⟨5333, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨5407, by norm_num, by norm_num, by norm_num⟩, ⟨5477, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨5557, by norm_num, by norm_num, by norm_num⟩, ⟨5639, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨5701, by norm_num, by norm_num, by norm_num⟩, ⟨5779, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨5857, by norm_num, by norm_num, by norm_num⟩, ⟨5939, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨6007, by norm_num, by norm_num, by norm_num⟩, ⟨6089, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨6163, by norm_num, by norm_num, by norm_num⟩, ⟨6247, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨6323, by norm_num, by norm_num, by norm_num⟩, ⟨6421, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨6481, by norm_num, by norm_num, by norm_num⟩, ⟨6563, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨6653, by norm_num, by norm_num, by norm_num⟩, ⟨6733, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨6823, by norm_num, by norm_num, by norm_num⟩, ⟨6899, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨6977, by norm_num, by norm_num, by norm_num⟩, ⟨7057, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨7151, by norm_num, by norm_num, by norm_num⟩, ⟨7229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨7321, by norm_num, by norm_num, by norm_num⟩, ⟨7411, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨7487, by norm_num, by norm_num, by norm_num⟩, ⟨7573, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨7669, by norm_num, by norm_num, by norm_num⟩, ⟨7753, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨7841, by norm_num, by norm_num, by norm_num⟩, ⟨7927, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨8011, by norm_num, by norm_num, by norm_num⟩, ⟨8101, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨8191, by norm_num, by norm_num, by norm_num⟩, ⟨8287, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨8377, by norm_num, by norm_num, by norm_num⟩, ⟨8467, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨8563, by norm_num, by norm_num, by norm_num⟩, ⟨8663, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨8747, by norm_num, by norm_num, by norm_num⟩, ⟨8837, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨8933, by norm_num, by norm_num, by norm_num⟩, ⟨9029, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨9127, by norm_num, by norm_num, by norm_num⟩, ⟨9221, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨9319, by norm_num, by norm_num, by norm_num⟩, ⟨9413, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨9511, by norm_num, by norm_num, by norm_num⟩, ⟨9613, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨9719, by norm_num, by norm_num, by norm_num⟩, ⟨9803, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨9901, by norm_num, by norm_num, by norm_num⟩, ⟨10007, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨10103, by norm_num, by norm_num, by norm_num⟩, ⟨10211, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨10303, by norm_num, by norm_num, by norm_num⟩, ⟨10427, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨10513, by norm_num, by norm_num, by norm_num⟩, ⟨10613, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨10723, by norm_num, by norm_num, by norm_num⟩, ⟨10831, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨10937, by norm_num, by norm_num, by norm_num⟩, ⟨11027, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨11131, by norm_num, by norm_num, by norm_num⟩, ⟨11239, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨11351, by norm_num, by norm_num, by norm_num⟩, ⟨11467, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨11579, by norm_num, by norm_num, by norm_num⟩, ⟨11677, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨11777, by norm_num, by norm_num, by norm_num⟩, ⟨11887, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨12007, by norm_num, by norm_num, by norm_num⟩, ⟨12101, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨12211, by norm_num, by norm_num, by norm_num⟩, ⟨12323, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨12433, by norm_num, by norm_num, by norm_num⟩, ⟨12547, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨12659, by norm_num, by norm_num, by norm_num⟩, ⟨12781, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨12889, by norm_num, by norm_num, by norm_num⟩, ⟨13001, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨13121, by norm_num, by norm_num, by norm_num⟩, ⟨13229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨13367, by norm_num, by norm_num, by norm_num⟩, ⟨13457, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨13577, by norm_num, by norm_num, by norm_num⟩, ⟨13691, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨13807, by norm_num, by norm_num, by norm_num⟩, ⟨13931, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨14051, by norm_num, by norm_num, by norm_num⟩, ⟨14173, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨14281, by norm_num, by norm_num, by norm_num⟩, ⟨14401, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨14533, by norm_num, by norm_num, by norm_num⟩, ⟨14653, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨14767, by norm_num, by norm_num, by norm_num⟩, ⟨14887, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨15013, by norm_num, by norm_num, by norm_num⟩, ⟨15131, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨15259, by norm_num, by norm_num, by norm_num⟩, ⟨15377, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨15511, by norm_num, by norm_num, by norm_num⟩, ⟨15629, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨15761, by norm_num, by norm_num, by norm_num⟩, ⟨15877, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨16007, by norm_num, by norm_num, by norm_num⟩, ⟨16139, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨16267, by norm_num, by norm_num, by norm_num⟩, ⟨16411, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨16519, by norm_num, by norm_num, by norm_num⟩, ⟨16649, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨16787, by norm_num, by norm_num, by norm_num⟩, ⟨16901, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨17033, by norm_num, by norm_num, by norm_num⟩, ⟨17167, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨17293, by norm_num, by norm_num, by norm_num⟩, ⟨17431, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨17569, by norm_num, by norm_num, by norm_num⟩, ⟨17707, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨17827, by norm_num, by norm_num, by norm_num⟩, ⟨17957, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨18097, by norm_num, by norm_num, by norm_num⟩, ⟨18229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨18367, by norm_num, by norm_num, by norm_num⟩, ⟨18503, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨18637, by norm_num, by norm_num, by norm_num⟩, ⟨18773, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨18911, by norm_num, by norm_num, by norm_num⟩, ⟨19051, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨19183, by norm_num, by norm_num, by norm_num⟩, ⟨19333, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨19463, by norm_num, by norm_num, by norm_num⟩, ⟨19603, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨19751, by norm_num, by norm_num, by norm_num⟩, ⟨19889, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨20023, by norm_num, by norm_num, by norm_num⟩, ⟨20173, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨20323, by norm_num, by norm_num, by norm_num⟩, ⟨20477, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨20593, by norm_num, by norm_num, by norm_num⟩, ⟨20743, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨20887, by norm_num, by norm_num, by norm_num⟩, ⟨21031, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨21179, by norm_num, by norm_num, by norm_num⟩, ⟨21317, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨21467, by norm_num, by norm_num, by norm_num⟩, ⟨21611, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨21757, by norm_num, by norm_num, by norm_num⟩, ⟨21911, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨22063, by norm_num, by norm_num, by norm_num⟩, ⟨22229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨22367, by norm_num, by norm_num, by norm_num⟩, ⟨22501, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨22651, by norm_num, by norm_num, by norm_num⟩, ⟨22807, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨22961, by norm_num, by norm_num, by norm_num⟩, ⟨23117, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨23269, by norm_num, by norm_num, by norm_num⟩, ⟨23417, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨23563, by norm_num, by norm_num, by norm_num⟩, ⟨23719, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨23873, by norm_num, by norm_num, by norm_num⟩, ⟨24029, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨24181, by norm_num, by norm_num, by norm_num⟩, ⟨24337, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨24499, by norm_num, by norm_num, by norm_num⟩, ⟨24659, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨24809, by norm_num, by norm_num, by norm_num⟩, ⟨24967, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨25127, by norm_num, by norm_num, by norm_num⟩, ⟨25301, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨25447, by norm_num, by norm_num, by norm_num⟩, ⟨25601, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨25763, by norm_num, by norm_num, by norm_num⟩, ⟨25931, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨26083, by norm_num, by norm_num, by norm_num⟩, ⟨26249, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨26407, by norm_num, by norm_num, by norm_num⟩, ⟨26573, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨26737, by norm_num, by norm_num, by norm_num⟩, ⟨26903, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨27061, by norm_num, by norm_num, by norm_num⟩, ⟨27239, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨27397, by norm_num, by norm_num, by norm_num⟩, ⟨27581, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨27733, by norm_num, by norm_num, by norm_num⟩, ⟨27893, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨28057, by norm_num, by norm_num, by norm_num⟩, ⟨28229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨28393, by norm_num, by norm_num, by norm_num⟩, ⟨28571, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨28751, by norm_num, by norm_num, by norm_num⟩, ⟨28901, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨29077, by norm_num, by norm_num, by norm_num⟩, ⟨29243, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨29423, by norm_num, by norm_num, by norm_num⟩, ⟨29587, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨29759, by norm_num, by norm_num, by norm_num⟩, ⟨29947, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨30103, by norm_num, by norm_num, by norm_num⟩, ⟨30293, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨30467, by norm_num, by norm_num, by norm_num⟩, ⟨30631, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨30803, by norm_num, by norm_num, by norm_num⟩, ⟨30977, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨31153, by norm_num, by norm_num, by norm_num⟩, ⟨31333, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨31511, by norm_num, by norm_num, by norm_num⟩, ⟨31687, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨31873, by norm_num, by norm_num, by norm_num⟩, ⟨32051, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨32233, by norm_num, by norm_num, by norm_num⟩, ⟨32401, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨32587, by norm_num, by norm_num, by norm_num⟩, ⟨32771, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨32957, by norm_num, by norm_num, by norm_num⟩, ⟨33149, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨33311, by norm_num, by norm_num, by norm_num⟩, ⟨33493, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨33679, by norm_num, by norm_num, by norm_num⟩, ⟨33857, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨34057, by norm_num, by norm_num, by norm_num⟩, ⟨34231, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨34421, by norm_num, by norm_num, by norm_num⟩, ⟨34603, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨34807, by norm_num, by norm_num, by norm_num⟩, ⟨34981, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨35159, by norm_num, by norm_num, by norm_num⟩, ⟨35353, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨35533, by norm_num, by norm_num, by norm_num⟩, ⟨35729, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨35911, by norm_num, by norm_num, by norm_num⟩, ⟨36107, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨36293, by norm_num, by norm_num, by norm_num⟩, ⟨36493, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨36677, by norm_num, by norm_num, by norm_num⟩, ⟨36871, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨37057, by norm_num, by norm_num, by norm_num⟩, ⟨37253, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨37447, by norm_num, by norm_num, by norm_num⟩, ⟨37643, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨37831, by norm_num, by norm_num, by norm_num⟩, ⟨38039, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨38231, by norm_num, by norm_num, by norm_num⟩, ⟨38431, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨38629, by norm_num, by norm_num, by norm_num⟩, ⟨38821, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨39019, by norm_num, by norm_num, by norm_num⟩, ⟨39209, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨39409, by norm_num, by norm_num, by norm_num⟩, ⟨39607, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨39821, by norm_num, by norm_num, by norm_num⟩, ⟨40009, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨40213, by norm_num, by norm_num, by norm_num⟩, ⟨40423, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨40609, by norm_num, by norm_num, by norm_num⟩, ⟨40813, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨41011, by norm_num, by norm_num, by norm_num⟩, ⟨41213, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨41413, by norm_num, by norm_num, by norm_num⟩, ⟨41617, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨41843, by norm_num, by norm_num, by norm_num⟩, ⟨42043, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨42239, by norm_num, by norm_num, by norm_num⟩, ⟨42437, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨42643, by norm_num, by norm_num, by norm_num⟩, ⟨42853, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨43063, by norm_num, by norm_num, by norm_num⟩, ⟨43271, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨43481, by norm_num, by norm_num, by norm_num⟩, ⟨43691, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨43891, by norm_num, by norm_num, by norm_num⟩, ⟨44101, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨44351, by norm_num, by norm_num, by norm_num⟩, ⟨44531, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨44741, by norm_num, by norm_num, by norm_num⟩, ⟨44953, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨45161, by norm_num, by norm_num, by norm_num⟩, ⟨45377, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨45587, by norm_num, by norm_num, by norm_num⟩, ⟨45817, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨46021, by norm_num, by norm_num, by norm_num⟩, ⟨46229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨46441, by norm_num, by norm_num, by norm_num⟩, ⟨46663, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨46877, by norm_num, by norm_num, by norm_num⟩, ⟨47093, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨47309, by norm_num, by norm_num, by norm_num⟩, ⟨47527, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨47743, by norm_num, by norm_num, by norm_num⟩, ⟨47963, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨48187, by norm_num, by norm_num, by norm_num⟩, ⟨48407, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨48623, by norm_num, by norm_num, by norm_num⟩, ⟨48847, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨49069, by norm_num, by norm_num, by norm_num⟩, ⟨49297, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨49523, by norm_num, by norm_num, by norm_num⟩, ⟨49739, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨49957, by norm_num, by norm_num, by norm_num⟩, ⟨50177, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨50411, by norm_num, by norm_num, by norm_num⟩, ⟨50627, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨50857, by norm_num, by norm_num, by norm_num⟩, ⟨51109, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨51307, by norm_num, by norm_num, by norm_num⟩, ⟨51539, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨51767, by norm_num, by norm_num, by norm_num⟩, ⟨51991, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨52223, by norm_num, by norm_num, by norm_num⟩, ⟨52453, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨52673, by norm_num, by norm_num, by norm_num⟩, ⟨52901, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨53147, by norm_num, by norm_num, by norm_num⟩, ⟨53377, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨53593, by norm_num, by norm_num, by norm_num⟩, ⟨53831, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨54059, by norm_num, by norm_num, by norm_num⟩, ⟨54293, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨54539, by norm_num, by norm_num, by norm_num⟩, ⟨54767, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨55001, by norm_num, by norm_num, by norm_num⟩, ⟨55229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨55469, by norm_num, by norm_num, by norm_num⟩, ⟨55697, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨55933, by norm_num, by norm_num, by norm_num⟩, ⟨56171, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨56417, by norm_num, by norm_num, by norm_num⟩, ⟨56659, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨56891, by norm_num, by norm_num, by norm_num⟩, ⟨57131, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨57367, by norm_num, by norm_num, by norm_num⟩, ⟨57601, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨57847, by norm_num, by norm_num, by norm_num⟩, ⟨58099, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨58337, by norm_num, by norm_num, by norm_num⟩, ⟨58567, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨58831, by norm_num, by norm_num, by norm_num⟩, ⟨59051, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨59333, by norm_num, by norm_num, by norm_num⟩, ⟨59539, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨59791, by norm_num, by norm_num, by norm_num⟩, ⟨60029, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨60271, by norm_num, by norm_num, by norm_num⟩, ⟨60521, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨60763, by norm_num, by norm_num, by norm_num⟩, ⟨61027, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨61261, by norm_num, by norm_num, by norm_num⟩, ⟨61507, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨61757, by norm_num, by norm_num, by norm_num⟩, ⟨62003, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨62273, by norm_num, by norm_num, by norm_num⟩, ⟨62501, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨62753, by norm_num, by norm_num, by norm_num⟩, ⟨63029, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨63277, by norm_num, by norm_num, by norm_num⟩, ⟨63521, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨63761, by norm_num, by norm_num, by norm_num⟩, ⟨64013, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨64271, by norm_num, by norm_num, by norm_num⟩, ⟨64553, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨64781, by norm_num, by norm_num, by norm_num⟩, ⟨65027, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨65287, by norm_num, by norm_num, by norm_num⟩, ⟨65537, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨65809, by norm_num, by norm_num, by norm_num⟩, ⟨66067, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨66337, by norm_num, by norm_num, by norm_num⟩, ⟨66569, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨66841, by norm_num, by norm_num, by norm_num⟩, ⟨67103, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨67343, by norm_num, by norm_num, by norm_num⟩, ⟨67601, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨67867, by norm_num, by norm_num, by norm_num⟩, ⟨68141, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨68389, by norm_num, by norm_num, by norm_num⟩, ⟨68659, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨68909, by norm_num, by norm_num, by norm_num⟩, ⟨69191, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨69439, by norm_num, by norm_num, by norm_num⟩, ⟨69697, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨69991, by norm_num, by norm_num, by norm_num⟩, ⟨70229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨70501, by norm_num, by norm_num, by norm_num⟩, ⟨70769, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨71023, by norm_num, by norm_num, by norm_num⟩, ⟨71293, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨71563, by norm_num, by norm_num, by norm_num⟩, ⟨71837, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨72101, by norm_num, by norm_num, by norm_num⟩, ⟨72367, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨72643, by norm_num, by norm_num, by norm_num⟩, ⟨72901, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨73181, by norm_num, by norm_num, by norm_num⟩, ⟨73453, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨73721, by norm_num, by norm_num, by norm_num⟩, ⟨73999, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨74257, by norm_num, by norm_num, by norm_num⟩, ⟨74531, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨74821, by norm_num, by norm_num, by norm_num⟩, ⟨75079, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨75353, by norm_num, by norm_num, by norm_num⟩, ⟨75629, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨75913, by norm_num, by norm_num, by norm_num⟩, ⟨76207, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨76463, by norm_num, by norm_num, by norm_num⟩, ⟨76733, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨77017, by norm_num, by norm_num, by norm_num⟩, ⟨77291, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨77563, by norm_num, by norm_num, by norm_num⟩, ⟨77849, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨78121, by norm_num, by norm_num, by norm_num⟩, ⟨78401, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨78691, by norm_num, by norm_num, by norm_num⟩, ⟨78977, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨79259, by norm_num, by norm_num, by norm_num⟩, ⟨79531, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨79811, by norm_num, by norm_num, by norm_num⟩, ⟨80107, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨80387, by norm_num, by norm_num, by norm_num⟩, ⟨80657, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨80953, by norm_num, by norm_num, by norm_num⟩, ⟨81233, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨81517, by norm_num, by norm_num, by norm_num⟩, ⟨81799, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨82129, by norm_num, by norm_num, by norm_num⟩, ⟨82373, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨82657, by norm_num, by norm_num, by norm_num⟩, ⟨82963, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨83233, by norm_num, by norm_num, by norm_num⟩, ⟨83537, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨83813, by norm_num, by norm_num, by norm_num⟩, ⟨84121, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨84391, by norm_num, by norm_num, by norm_num⟩, ⟨84691, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨84977, by norm_num, by norm_num, by norm_num⟩, ⟨85297, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨85571, by norm_num, by norm_num, by norm_num⟩, ⟨85853, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨86143, by norm_num, by norm_num, by norm_num⟩, ⟨86441, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨86743, by norm_num, by norm_num, by norm_num⟩, ⟨87037, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨87323, by norm_num, by norm_num, by norm_num⟩, ⟨87623, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨87917, by norm_num, by norm_num, by norm_num⟩, ⟨88211, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨88513, by norm_num, by norm_num, by norm_num⟩, ⟨88807, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨89107, by norm_num, by norm_num, by norm_num⟩, ⟨89413, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨89753, by norm_num, by norm_num, by norm_num⟩, ⟨90001, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨90313, by norm_num, by norm_num, by norm_num⟩, ⟨90617, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨90907, by norm_num, by norm_num, by norm_num⟩, ⟨91229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨91513, by norm_num, by norm_num, by norm_num⟩, ⟨91811, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨92119, by norm_num, by norm_num, by norm_num⟩, ⟨92419, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨92723, by norm_num, by norm_num, by norm_num⟩, ⟨93047, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨93337, by norm_num, by norm_num, by norm_num⟩, ⟨93637, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨93949, by norm_num, by norm_num, by norm_num⟩, ⟨94253, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨94559, by norm_num, by norm_num, by norm_num⟩, ⟨94873, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨95177, by norm_num, by norm_num, by norm_num⟩, ⟨95483, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨95791, by norm_num, by norm_num, by norm_num⟩, ⟨96137, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨96419, by norm_num, by norm_num, by norm_num⟩, ⟨96731, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨97039, by norm_num, by norm_num, by norm_num⟩, ⟨97367, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨97673, by norm_num, by norm_num, by norm_num⟩, ⟨97973, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨98297, by norm_num, by norm_num, by norm_num⟩, ⟨98597, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨98911, by norm_num, by norm_num, by norm_num⟩, ⟨99233, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨99551, by norm_num, by norm_num, by norm_num⟩, ⟨99859, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨100183, by norm_num, by norm_num, by norm_num⟩, ⟨100493, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨100811, by norm_num, by norm_num, by norm_num⟩, ⟨101141, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨101449, by norm_num, by norm_num, by norm_num⟩, ⟨101771, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨102101, by norm_num, by norm_num, by norm_num⟩, ⟨102407, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨102761, by norm_num, by norm_num, by norm_num⟩, ⟨103043, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨103387, by norm_num, by norm_num, by norm_num⟩, ⟨103687, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨104009, by norm_num, by norm_num, by norm_num⟩, ⟨104347, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨104659, by norm_num, by norm_num, by norm_num⟩, ⟨104987, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨105319, by norm_num, by norm_num, by norm_num⟩, ⟨105649, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨105953, by norm_num, by norm_num, by norm_num⟩, ⟨106277, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨106619, by norm_num, by norm_num, by norm_num⟩, ⟨106937, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨107269, by norm_num, by norm_num, by norm_num⟩, ⟨107599, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨107923, by norm_num, by norm_num, by norm_num⟩, ⟨108247, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨108571, by norm_num, by norm_num, by norm_num⟩, ⟨108907, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨109253, by norm_num, by norm_num, by norm_num⟩, ⟨109567, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨109897, by norm_num, by norm_num, by norm_num⟩, ⟨110233, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨110557, by norm_num, by norm_num, by norm_num⟩, ⟨110899, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨111227, by norm_num, by norm_num, by norm_num⟩, ⟨111577, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨111893, by norm_num, by norm_num, by norm_num⟩, ⟨112237, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨112571, by norm_num, by norm_num, by norm_num⟩, ⟨112901, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨113233, by norm_num, by norm_num, by norm_num⟩, ⟨113591, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨113909, by norm_num, by norm_num, by norm_num⟩, ⟨114259, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨114593, by norm_num, by norm_num, by norm_num⟩, ⟨114941, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨115279, by norm_num, by norm_num, by norm_num⟩, ⟨115601, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨115963, by norm_num, by norm_num, by norm_num⟩, ⟨116293, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨116639, by norm_num, by norm_num, by norm_num⟩, ⟨116969, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨117307, by norm_num, by norm_num, by norm_num⟩, ⟨117659, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨118033, by norm_num, by norm_num, by norm_num⟩, ⟨118343, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨118681, by norm_num, by norm_num, by norm_num⟩, ⟨119027, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨119389, by norm_num, by norm_num, by norm_num⟩, ⟨119723, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨120067, by norm_num, by norm_num, by norm_num⟩, ⟨120413, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨120763, by norm_num, by norm_num, by norm_num⟩, ⟨121123, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨121453, by norm_num, by norm_num, by norm_num⟩, ⟨121843, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨122167, by norm_num, by norm_num, by norm_num⟩, ⟨122501, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨122861, by norm_num, by norm_num, by norm_num⟩, ⟨123203, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨123553, by norm_num, by norm_num, by norm_num⟩, ⟨123911, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨124277, by norm_num, by norm_num, by norm_num⟩, ⟨124633, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨124979, by norm_num, by norm_num, by norm_num⟩, ⟨125329, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨125683, by norm_num, by norm_num, by norm_num⟩, ⟨126031, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨126397, by norm_num, by norm_num, by norm_num⟩, ⟨126739, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨127103, by norm_num, by norm_num, by norm_num⟩, ⟨127453, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨127807, by norm_num, by norm_num, by norm_num⟩, ⟨128173, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨128549, by norm_num, by norm_num, by norm_num⟩, ⟨128903, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨129263, by norm_num, by norm_num, by norm_num⟩, ⟨129607, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨129967, by norm_num, by norm_num, by norm_num⟩, ⟨130337, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨130687, by norm_num, by norm_num, by norm_num⟩, ⟨131059, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨131413, by norm_num, by norm_num, by norm_num⟩, ⟨131771, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨132137, by norm_num, by norm_num, by norm_num⟩, ⟨132499, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨132863, by norm_num, by norm_num, by norm_num⟩, ⟨133241, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨133597, by norm_num, by norm_num, by norm_num⟩, ⟨133963, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨134327, by norm_num, by norm_num, by norm_num⟩, ⟨134699, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨135059, by norm_num, by norm_num, by norm_num⟩, ⟨135427, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨135799, by norm_num, by norm_num, by norm_num⟩, ⟨136163, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨136531, by norm_num, by norm_num, by norm_num⟩, ⟨136943, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨137273, by norm_num, by norm_num, by norm_num⟩, ⟨137653, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨138041, by norm_num, by norm_num, by norm_num⟩, ⟨138389, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨138763, by norm_num, by norm_num, by norm_num⟩, ⟨139133, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨139511, by norm_num, by norm_num, by norm_num⟩, ⟨139883, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨140263, by norm_num, by norm_num, by norm_num⟩, ⟨140627, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨141023, by norm_num, by norm_num, by norm_num⟩, ⟨141397, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨141761, by norm_num, by norm_num, by norm_num⟩, ⟨142151, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨142529, by norm_num, by norm_num, by norm_num⟩, ⟨142897, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨143263, by norm_num, by norm_num, by norm_num⟩, ⟨143651, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨144031, by norm_num, by norm_num, by norm_num⟩, ⟨144407, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨144791, by norm_num, by norm_num, by norm_num⟩, ⟨145177, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨145543, by norm_num, by norm_num, by norm_num⟩, ⟨145931, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨146309, by norm_num, by norm_num, by norm_num⟩, ⟨146701, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨147073, by norm_num, by norm_num, by norm_num⟩, ⟨147457, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨147853, by norm_num, by norm_num, by norm_num⟩, ⟨148229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨148627, by norm_num, by norm_num, by norm_num⟩, ⟨148997, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨149393, by norm_num, by norm_num, by norm_num⟩, ⟨149771, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨150169, by norm_num, by norm_num, by norm_num⟩, ⟨150551, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨150959, by norm_num, by norm_num, by norm_num⟩, ⟨151337, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨151717, by norm_num, by norm_num, by norm_num⟩, ⟨152111, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨152501, by norm_num, by norm_num, by norm_num⟩, ⟨152897, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨153277, by norm_num, by norm_num, by norm_num⟩, ⟨153689, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨154057, by norm_num, by norm_num, by norm_num⟩, ⟨154459, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨154849, by norm_num, by norm_num, by norm_num⟩, ⟨155251, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨155653, by norm_num, by norm_num, by norm_num⟩, ⟨156041, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨156421, by norm_num, by norm_num, by norm_num⟩, ⟨156817, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨157217, by norm_num, by norm_num, by norm_num⟩, ⟨157627, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨158009, by norm_num, by norm_num, by norm_num⟩, ⟨158407, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨158803, by norm_num, by norm_num, by norm_num⟩, ⟨159209, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨159617, by norm_num, by norm_num, by norm_num⟩, ⟨160001, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨160403, by norm_num, by norm_num, by norm_num⟩, ⟨160807, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨161221, by norm_num, by norm_num, by norm_num⟩, ⟨161611, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨162007, by norm_num, by norm_num, by norm_num⟩, ⟨162413, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨162821, by norm_num, by norm_num, by norm_num⟩, ⟨163223, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨163621, by norm_num, by norm_num, by norm_num⟩, ⟨164039, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨164431, by norm_num, by norm_num, by norm_num⟩, ⟨164837, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨165247, by norm_num, by norm_num, by norm_num⟩, ⟨165653, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨166063, by norm_num, by norm_num, by norm_num⟩, ⟨166471, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨166909, by norm_num, by norm_num, by norm_num⟩, ⟨167309, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨167711, by norm_num, by norm_num, by norm_num⟩, ⟨168109, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨168523, by norm_num, by norm_num, by norm_num⟩, ⟨168937, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨169339, by norm_num, by norm_num, by norm_num⟩, ⟨169751, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨170167, by norm_num, by norm_num, by norm_num⟩, ⟨170579, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨171007, by norm_num, by norm_num, by norm_num⟩, ⟨171401, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨171811, by norm_num, by norm_num, by norm_num⟩, ⟨172243, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨172643, by norm_num, by norm_num, by norm_num⟩, ⟨173059, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨173473, by norm_num, by norm_num, by norm_num⟩, ⟨173891, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨174311, by norm_num, by norm_num, by norm_num⟩, ⟨174737, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨175211, by norm_num, by norm_num, by norm_num⟩, ⟨175573, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨175991, by norm_num, by norm_num, by norm_num⟩, ⟨176401, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨176849, by norm_num, by norm_num, by norm_num⟩, ⟨177257, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨177677, by norm_num, by norm_num, by norm_num⟩, ⟨178091, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨178513, by norm_num, by norm_num, by norm_num⟩, ⟨178931, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨179357, by norm_num, by norm_num, by norm_num⟩, ⟨179779, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨180211, by norm_num, by norm_num, by norm_num⟩, ⟨180629, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨181061, by norm_num, by norm_num, by norm_num⟩, ⟨181499, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨181903, by norm_num, by norm_num, by norm_num⟩, ⟨182333, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨182773, by norm_num, by norm_num, by norm_num⟩, ⟨183191, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨183637, by norm_num, by norm_num, by norm_num⟩, ⟨184043, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨184477, by norm_num, by norm_num, by norm_num⟩, ⟨184901, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨185359, by norm_num, by norm_num, by norm_num⟩, ⟨185767, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨186211, by norm_num, by norm_num, by norm_num⟩, ⟨186629, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨187067, by norm_num, by norm_num, by norm_num⟩, ⟨187507, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨187927, by norm_num, by norm_num, by norm_num⟩, ⟨188359, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨188791, by norm_num, by norm_num, by norm_num⟩, ⟨189229, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨189661, by norm_num, by norm_num, by norm_num⟩, ⟨190097, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨190537, by norm_num, by norm_num, by norm_num⟩, ⟨190979, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨191413, by norm_num, by norm_num, by norm_num⟩, ⟨191861, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨192307, by norm_num, by norm_num, by norm_num⟩, ⟨192737, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨193163, by norm_num, by norm_num, by norm_num⟩, ⟨193601, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨194057, by norm_num, by norm_num, by norm_num⟩, ⟨194483, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨194933, by norm_num, by norm_num, by norm_num⟩, ⟨195389, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨195809, by norm_num, by norm_num, by norm_num⟩, ⟨196271, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨196699, by norm_num, by norm_num, by norm_num⟩, ⟨197137, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨197597, by norm_num, by norm_num, by norm_num⟩, ⟨198031, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨198479, by norm_num, by norm_num, by norm_num⟩, ⟨198929, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨199373, by norm_num, by norm_num, by norm_num⟩, ⟨199811, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨200257, by norm_num, by norm_num, by norm_num⟩, ⟨200713, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨201163, by norm_num, by norm_num, by norm_num⟩, ⟨201611, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨202061, by norm_num, by norm_num, by norm_num⟩, ⟨202519, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨202967, by norm_num, by norm_num, by norm_num⟩, ⟨203417, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨203857, by norm_num, by norm_num, by norm_num⟩, ⟨204311, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨204781, by norm_num, by norm_num, by norm_num⟩, ⟨205211, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨205663, by norm_num, by norm_num, by norm_num⟩, ⟨206123, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨206593, by norm_num, by norm_num, by norm_num⟩, ⟨207029, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨207481, by norm_num, by norm_num, by norm_num⟩, ⟨207941, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨208393, by norm_num, by norm_num, by norm_num⟩, ⟨208877, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨209311, by norm_num, by norm_num, by norm_num⟩, ⟨209767, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨210229, by norm_num, by norm_num, by norm_num⟩, ⟨210709, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨211151, by norm_num, by norm_num, by norm_num⟩, ⟨211619, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨212081, by norm_num, by norm_num, by norm_num⟩, ⟨212557, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨212987, by norm_num, by norm_num, by norm_num⟩, ⟨213449, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨213919, by norm_num, by norm_num, by norm_num⟩, ⟨214373, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨214849, by norm_num, by norm_num, by norm_num⟩, ⟨215297, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨215767, by norm_num, by norm_num, by norm_num⟩, ⟨216233, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨216703, by norm_num, by norm_num, by norm_num⟩, ⟨217157, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨217643, by norm_num, by norm_num, by norm_num⟩, ⟨218107, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨218579, by norm_num, by norm_num, by norm_num⟩, ⟨219031, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨219503, by norm_num, by norm_num, by norm_num⟩, ⟨219971, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨220447, by norm_num, by norm_num, by norm_num⟩, ⟨220901, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨221393, by norm_num, by norm_num, by norm_num⟩, ⟨221849, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨222317, by norm_num, by norm_num, by norm_num⟩, ⟨222787, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨223259, by norm_num, by norm_num, by norm_num⟩, ⟨223747, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨224209, by norm_num, by norm_num, by norm_num⟩, ⟨224677, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨225157, by norm_num, by norm_num, by norm_num⟩, ⟨225629, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨226103, by norm_num, by norm_num, by norm_num⟩, ⟨226601, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨227053, by norm_num, by norm_num, by norm_num⟩, ⟨227531, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨228013, by norm_num, by norm_num, by norm_num⟩, ⟨228509, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨228983, by norm_num, by norm_num, by norm_num⟩, ⟨229459, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨229937, by norm_num, by norm_num, by norm_num⟩, ⟨230431, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨230891, by norm_num, by norm_num, by norm_num⟩, ⟨231367, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨231859, by norm_num, by norm_num, by norm_num⟩, ⟨232333, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨232811, by norm_num, by norm_num, by norm_num⟩, ⟨233293, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨233777, by norm_num, by norm_num, by norm_num⟩, ⟨234259, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨234743, by norm_num, by norm_num, by norm_num⟩, ⟨235231, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨235723, by norm_num, by norm_num, by norm_num⟩, ⟨236207, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨236699, by norm_num, by norm_num, by norm_num⟩, ⟨237173, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨237673, by norm_num, by norm_num, by norm_num⟩, ⟨238151, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨238639, by norm_num, by norm_num, by norm_num⟩, ⟨239137, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨239611, by norm_num, by norm_num, by norm_num⟩, ⟨240101, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨240599, by norm_num, by norm_num, by norm_num⟩, ⟨241093, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨241589, by norm_num, by norm_num, by norm_num⟩, ⟨242069, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨242591, by norm_num, by norm_num, by norm_num⟩, ⟨243073, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨243553, by norm_num, by norm_num, by norm_num⟩, ⟨244043, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨244547, by norm_num, by norm_num, by norm_num⟩, ⟨245029, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨245521, by norm_num, by norm_num, by norm_num⟩, ⟨246017, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨246523, by norm_num, by norm_num, by norm_num⟩, ⟨247031, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨247519, by norm_num, by norm_num, by norm_num⟩, ⟨248021, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨248509, by norm_num, by norm_num, by norm_num⟩, ⟨249017, by norm_num, by norm_num, by norm_num⟩⟩
  · exact ⟨⟨249503, by norm_num, by norm_num, by norm_num⟩, ⟨250007, by norm_num, by norm_num, by norm_num⟩⟩

/-- Under the short-interval prime hypothesis with threshold `X`, Oppermann's property holds
for every `n ≥ 2` with `X ≤ n`. -/
lemma oppermannProperty_of_shortIntervalPrimes (X : ℕ) (hX : ShortIntervalPrimes X) (n : ℕ)
    (h2 : 2 ≤ n) (hn : X ≤ n) : OppermannProperty n := by
  have hnn : n + n ≤ n * n := by nlinarith
  constructor
  · obtain ⟨p, hp, h1, h2⟩ := hX (n * n - n) (le_trans hn (by omega))
    refine ⟨p, hp, h1, ?_⟩
    have hs : Nat.sqrt (n * n - n) ≤ n :=
      le_of_le_of_eq (Nat.sqrt_le_sqrt (Nat.sub_le _ _)) (Nat.sqrt_eq n)
    omega
  · obtain ⟨p, hp, h1, h2⟩ := hX (n * n) (le_trans hn (by omega))
    rw [Nat.sqrt_eq] at h2
    exact ⟨p, hp, h1, h2⟩

/-- **Oppermann's conjecture, conditionally on a short-interval prime hypothesis.**

If there is a threshold `X ≤ 501` beyond which every interval `(x, x + √x)` contains a prime,
then Oppermann's conjecture holds in full: for every `n ≥ 2` there is a prime strictly between
`n(n-1)` and `n²`, and a prime strictly between `n²` and `n(n+1)`.

The range `n ≤ 500` is verified unconditionally (`oppermannProperty_of_le_500`); the hypothesis
is used only for `n > 500`. -/
theorem OppermannConjecture (X : ℕ) (hX : ShortIntervalPrimes X) (hX501 : X ≤ 501) (n : ℕ)
    (h2 : 2 ≤ n) : OppermannProperty n := by
  by_cases h : n ≤ 500
  · exact oppermannProperty_of_le_500 n h2 h
  · exact oppermannProperty_of_shortIntervalPrimes X hX n h2 (by omega)

/-! ### An equivalent formulation in terms of the prime counting function -/

lemma count_lt_count_iff {p : ℕ → Prop} [DecidablePred p] {a b : ℕ} (hab : a ≤ b) :
    Nat.count p a < Nat.count p b ↔ ∃ k, a ≤ k ∧ k < b ∧ p k := by
  induction b, hab using Nat.le_induction with
  | base => simp; omega
  | succ b hb ih =>
    rw [Nat.count_succ]
    constructor
    · intro h
      by_cases hpb : p b
      · exact ⟨b, hb, by omega, hpb⟩
      · rw [if_neg hpb] at h
        obtain ⟨k, hk1, hk2, hk3⟩ := ih.mp (by omega)
        exact ⟨k, hk1, by omega, hk3⟩
    · rintro ⟨k, hk1, hk2, hk3⟩
      rcases eq_or_lt_of_le (Nat.lt_succ_iff.mp hk2) with rfl | hlt
      · rw [if_pos hk3]
        have := Nat.count_monotone p hb
        omega
      · have := ih.mpr ⟨k, hk1, hlt, hk3⟩
        split <;> omega

lemma not_prime_mul_self {n : ℕ} (h2 : 2 ≤ n) : ¬ Nat.Prime (n * n) := by
  intro hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp n ⟨n, rfl⟩) with h | h <;> nlinarith

lemma not_prime_mul_succ {n : ℕ} (h2 : 2 ≤ n) : ¬ Nat.Prime (n * n + n) := by
  intro hp
  rcases (Nat.Prime.eq_one_or_self_of_dvd hp n ⟨n + 1, by ring⟩) with h | h <;> nlinarith

/-- Oppermann's property is equivalent to the classical statement
`π(n² - n) < π(n²) < π(n² + n)` in terms of the prime counting function. -/
theorem oppermannProperty_iff_primeCounting (n : ℕ) (h2 : 2 ≤ n) :
    OppermannProperty n ↔
      Nat.primeCounting (n * n - n) < Nat.primeCounting (n * n) ∧
        Nat.primeCounting (n * n) < Nat.primeCounting (n * n + n) := by
  have hnn : n + n ≤ n * n := by nlinarith
  have e₁ : Nat.primeCounting (n * n - n) < Nat.primeCounting (n * n) ↔
      ∃ k, n * n - n + 1 ≤ k ∧ k < n * n + 1 ∧ Nat.Prime k := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using
      count_lt_count_iff (p := Nat.Prime) (a := n * n - n + 1) (b := n * n + 1) (by omega)
  have e₂ : Nat.primeCounting (n * n) < Nat.primeCounting (n * n + n) ↔
      ∃ k, n * n + 1 ≤ k ∧ k < n * n + n + 1 ∧ Nat.Prime k := by
    simpa [Nat.primeCounting, Nat.primeCounting'] using
      count_lt_count_iff (p := Nat.Prime) (a := n * n + 1) (b := n * n + n + 1) (by omega)
  rw [OppermannProperty, e₁, e₂]
  constructor
  · rintro ⟨⟨p, hp, hp1, hp2⟩, ⟨q, hq, hq1, hq2⟩⟩
    exact ⟨⟨p, by omega, by omega, hp⟩, ⟨q, by omega, by omega, hq⟩⟩
  · rintro ⟨⟨p, hp1, hp2, hp⟩, ⟨q, hq1, hq2, hq⟩⟩
    refine ⟨⟨p, hp, by omega, ?_⟩, ⟨q, hq, by omega, ?_⟩⟩
    · rcases Nat.lt_or_ge p (n * n) with h | h
      · exact h
      · have : p = n * n := by omega
        exact absurd (this ▸ hp) (not_prime_mul_self h2)
    · rcases Nat.lt_or_ge q (n * n + n) with h | h
      · exact h
      · have : q = n * n + n := by omega
        exact absurd (this ▸ hq) (not_prime_mul_succ h2)

end Brockian.OppermannConjecture

