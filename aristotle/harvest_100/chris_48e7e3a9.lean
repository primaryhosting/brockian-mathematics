/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `IsPrimitiveRootMod a p` says that the integer `a` is a primitive root modulo `p`,
i.e. the residue of `a` generates the multiplicative group `(ZMod p)ˣ`, which for a
prime `p` amounts to the multiplicative order of `a` modulo `p` being `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- The set of primes for which `a` is a primitive root. -/
def artinPrimes (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
def ArtinPrimitiveRootConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (artinPrimes a).Infinite

/-! ### The hypotheses of the conjecture are necessary -/

/-- A perfect square is never a primitive root modulo an odd prime: it is a quadratic
residue, so its order divides `(p-1)/2`. -/
theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : 2 < p) : ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  intro h
  have hodd : Odd p := hp.odd_of_ne_two (by omega)
  obtain ⟨k, hk⟩ := hodd
  have hk1 : 1 ≤ k := by omega
  set x : ZMod p := (b : ZMod p) with hx
  have hcast : ((b * b : ℤ) : ZMod p) = x ^ 2 := by push_cast [hx]; ring
  rw [hcast] at h
  by_cases hx0 : x = 0
  · rw [hx0] at h
    simp at h
    omega
  · have hxp : x ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one hx0
    have h2k : p - 1 = 2 * k := by omega
    have : (x ^ 2) ^ k = 1 := by
      rw [← pow_mul, ← h2k]; exact hxp
    have hdvd : orderOf (x ^ 2) ∣ k := orderOf_dvd_of_pow_eq_one this
    have hle : orderOf (x ^ 2) ≤ k := Nat.le_of_dvd (by omega) hdvd
    rw [h] at hle
    omega

/-- `-1` is never a primitive root modulo a prime `p > 3`: its order is at most `2`. -/
theorem not_isPrimitiveRootMod_neg_one {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  intro h
  have hsq : ((-1 : ℤ) : ZMod p) ^ 2 = 1 := by push_cast; ring
  have hdvd : orderOf (((-1 : ℤ) : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hle : orderOf (((-1 : ℤ) : ZMod p)) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  rw [h] at hle
  omega

/-- If `a` is a perfect square, the set of primes for which it is a primitive root is
contained in `{2}`, hence finite: Artin's hypothesis `¬ IsSquare a` cannot be dropped. -/
theorem artinPrimes_subset_of_isSquare {a : ℤ} (ha : IsSquare a) : artinPrimes a ⊆ {2} := by
  intro p hp
  obtain ⟨hprime, hroot⟩ := hp
  by_contra hne
  exact not_isPrimitiveRootMod_of_isSquare ha hprime
    (lt_of_le_of_ne hprime.two_le (fun h => hne h.symm)) hroot

theorem artinPrimes_finite_of_isSquare {a : ℤ} (ha : IsSquare a) : (artinPrimes a).Finite :=
  Set.Finite.subset (Set.finite_singleton 2) (artinPrimes_subset_of_isSquare ha)

/-- For `a = -1` the set of primes for which it is a primitive root is contained in
`{2, 3}`, hence finite: Artin's hypothesis `a ≠ -1` cannot be dropped. -/
theorem artinPrimes_neg_one_subset : artinPrimes (-1) ⊆ {2, 3} := by
  intro p hp
  obtain ⟨hprime, hroot⟩ := hp
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  have : 3 < p := by
    have := hprime.two_le
    omega
  exact not_isPrimitiveRootMod_neg_one hprime this hroot

theorem artinPrimes_neg_one_finite : (artinPrimes (-1)).Finite :=
  Set.Finite.subset (Set.toFinite _) artinPrimes_neg_one_subset

/-! ### Base cases: `2` is a primitive root modulo `3`, `5`, `11`, `13`, `19` -/

theorem isPrimitiveRootMod_two_three : IsPrimitiveRootMod 2 3 := by
  have : ((2 : ℤ) : ZMod 3) = (2 : ZMod 3) := by norm_num
  rw [IsPrimitiveRootMod, this, orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem isPrimitiveRootMod_two_five : IsPrimitiveRootMod 2 5 := by
  have : ((2 : ℤ) : ZMod 5) = (2 : ZMod 5) := by norm_num
  rw [IsPrimitiveRootMod, this, orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem isPrimitiveRootMod_two_eleven : IsPrimitiveRootMod 2 11 := by
  have : ((2 : ℤ) : ZMod 11) = (2 : ZMod 11) := by norm_num
  rw [IsPrimitiveRootMod, this, orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem isPrimitiveRootMod_two_thirteen : IsPrimitiveRootMod 2 13 := by
  have : ((2 : ℤ) : ZMod 13) = (2 : ZMod 13) := by norm_num
  rw [IsPrimitiveRootMod, this, orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

theorem isPrimitiveRootMod_two_nineteen : IsPrimitiveRootMod 2 19 := by
  have : ((2 : ℤ) : ZMod 19) = (2 : ZMod 19) := by norm_num
  rw [IsPrimitiveRootMod, this, orderOf_eq_iff (by norm_num)]
  exact ⟨by decide, by decide⟩

/-! ### Main statement -/

/-- **Artin's conjecture on primitive roots**, formalized as
`Frontier.ArtinPrimitiveRootConjecture`, together with what is proved here:

* the exceptional cases of the conjecture are genuinely exceptional — if `a` is a perfect
  square, resp. `a = -1`, then the set of primes having `a` as a primitive root is finite
  (contained in `{2}`, resp. `{2,3}`), so the two hypotheses of the conjecture cannot be
  dropped;
* base cases: `2` is a primitive root modulo `3`, `5`, `11`, `13` and `19`. -/
theorem artin_primitive_root :
    (ArtinPrimitiveRootConjecture ↔
        ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (artinPrimes a).Infinite) ∧
    (∀ a : ℤ, IsSquare a → (artinPrimes a).Finite) ∧
    (artinPrimes (-1)).Finite ∧
    ({3, 5, 11, 13, 19} : Set ℕ) ⊆ artinPrimes 2 := by
  refine ⟨Iff.rfl, fun a ha => artinPrimes_finite_of_isSquare ha, artinPrimes_neg_one_finite, ?_⟩
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl
  · exact ⟨by norm_num, isPrimitiveRootMod_two_three⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_five⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_eleven⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_thirteen⟩
  · exact ⟨by norm_num, isPrimitiveRootMod_two_nineteen⟩

end Frontier

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

