/-!
# Goldbach Wheel K 2 1153
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1153
Verified: AXLE cloud (Lean 4.32.0, Mathlib), axiom-clean
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Nat
open scoped Classical

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Brockian

/-- The new wheel modulus: the prime `1153`. -/
abbrev wheelModulus : ℕ := 1153

lemma wheelModulus_prime : Nat.Prime wheelModulus := by
  norm_num [wheelModulus]

instance : Fact (Nat.Prime 1153) := ⟨by norm_num⟩

/-- The `K = 2` Goldbach wheel at modulus `M`: the set of residues `r` modulo `M` that are
admissible as the residue of one summand in a representation `n = a + b`, i.e. both `r` and
`n - r` are units modulo `M` (as must be the case when `a` and `b` are primes not dividing
`M`). -/
noncomputable def goldbachWheelSet (M : ℕ) [NeZero M] (n : ZMod M) : Finset (ZMod M) :=
  Finset.univ.filter (fun r => IsUnit r ∧ IsUnit (n - r))

lemma mem_goldbachWheelSet {M : ℕ} [NeZero M] {n r : ZMod M} :
    r ∈ goldbachWheelSet M n ↔ IsUnit r ∧ IsUnit (n - r) := by
  simp [goldbachWheelSet]

/-- Over a prime modulus the wheel set is the complement of `{0, n}`. -/
lemma goldbachWheelSet_prime (p : ℕ) [Fact (Nat.Prime p)] (n : ZMod p) :
    goldbachWheelSet p n = Finset.univ \ ({0, n} : Finset (ZMod p)) := by
  ext r
  simp only [mem_goldbachWheelSet, Finset.mem_sdiff, Finset.mem_univ, true_and,
    Finset.mem_insert, Finset.mem_singleton, isUnit_iff_ne_zero, sub_ne_zero, not_or]
  tauto

/-- Size of the `K = 2` Goldbach wheel at a prime modulus `p`: it has `p - 1` elements when
`p ∣ n` and `p - 2` elements otherwise. -/
theorem card_goldbachWheelSet_prime (p : ℕ) [Fact (Nat.Prime p)] (n : ZMod p) :
    (goldbachWheelSet p n).card = if n = 0 then p - 1 else p - 2 := by
  have hp : Fintype.card (ZMod p) = p := ZMod.card p
  rw [goldbachWheelSet_prime, Finset.card_sdiff_of_subset (Finset.subset_univ _),
    Finset.card_univ, hp]
  by_cases h : n = 0
  · subst h
    simp
  · rw [Finset.card_insert_of_notMem (by simpa [eq_comm] using h), Finset.card_singleton,
      if_neg h]

/-- **The `K = 2` Goldbach wheel at the new wheel modulus `1153`.**
Exactly `1151` of the `1153` residue classes modulo `1153` are admissible for a Goldbach
splitting `n = a + b`, except in the single case `1153 ∣ n`, where `1152` classes are
admissible. -/
theorem GoldbachWheelK2_1153 (n : ZMod wheelModulus) :
    (goldbachWheelSet wheelModulus n).card = if n = 0 then 1152 else 1151 :=
  card_goldbachWheelSet_prime 1153 n

/-- The wheel at modulus `1153` is nonempty at every residue. -/
theorem goldbachWheelK2_1153_nonempty (n : ZMod wheelModulus) :
    (goldbachWheelSet wheelModulus n).Nonempty := by
  rw [← Finset.card_pos, GoldbachWheelK2_1153]
  split <;> norm_num

/-- The wheel really is a constraint satisfied by Goldbach representations: if an even number
`n` is a sum of two primes `a` and `b`, neither of which is the wheel modulus `1153`, then the
residue of `a` lies in the `K = 2` Goldbach wheel of `n` at `1153`. -/
theorem goldbachWheelK2_1153_of_sum_primes {n a b : ℕ} (hab : n = a + b)
    (ha : a.Prime) (hb : b.Prime) (ha' : a ≠ 1153) (hb' : b ≠ 1153) :
    (a : ZMod wheelModulus) ∈ goldbachWheelSet wheelModulus (n : ZMod wheelModulus) := by
  have hp : Nat.Prime 1153 := by norm_num
  have key : ∀ c : ℕ, c.Prime → c ≠ 1153 → (c : ZMod 1153) ≠ 0 := by
    intro c hc hc'
    rw [Ne, ZMod.natCast_eq_zero_iff]
    intro hdvd
    exact hc' (((Nat.prime_dvd_prime_iff_eq hp hc).mp hdvd).symm)
  rw [mem_goldbachWheelSet]
  refine ⟨?_, ?_⟩
  · simpa [isUnit_iff_ne_zero] using key a ha ha'
  · have : ((n : ZMod wheelModulus) - (a : ZMod wheelModulus)) = (b : ZMod wheelModulus) := by
      subst hab; push_cast; ring
    rw [this]
    simpa [isUnit_iff_ne_zero] using key b hb hb'

end Brockian


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

