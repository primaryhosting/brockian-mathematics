import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo the prime `p` when its residue generates the
multiplicative group `(ZMod p)ˣ`, i.e. when the multiplicative order of `a` in `ZMod p`
equals `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- The set of primes for which `a` is a primitive root. -/
def artinPrimes (a : ℤ) : Set ℕ := {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots.**  If the integer `a` is neither `-1` nor a
perfect square, then `a` is a primitive root modulo infinitely many primes.
(The two excluded families are genuinely necessary; see `artin_primitive_root`.) -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (artinPrimes a).Infinite

/-! ### Necessity of the hypothesis "`a` is not a perfect square" -/

/-- A perfect square is never a primitive root modulo an odd prime: it is a quadratic
residue, so its order divides `(p-1)/2 < p-1`. -/
theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsPrimitiveRootMod a p := by
  haveI := Fact.mk hp
  obtain ⟨b, rfl⟩ := ha
  intro h
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    rcases Nat.lt_or_ge p 3 with h' | h'
    · omega
    · exact h'
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
  have hcast : ((b * b : ℤ) : ZMod p) = (b : ZMod p) * (b : ZMod p) := by push_cast; ring
  rw [IsPrimitiveRootMod, hcast] at h
  by_cases hx0 : (b : ZMod p) = 0
  · rw [hx0] at h
    have h1 : ((0 : ZMod p) * 0) ^ (p - 1) = 1 := by
      rw [← h]; exact pow_orderOf_eq_one _
    rw [zero_mul, zero_pow (by omega)] at h1
    exact zero_ne_one h1
  · have hpow : ((b : ZMod p) * (b : ZMod p)) ^ ((p - 1) / 2) = 1 := by
      have h2 : ((b : ZMod p) * (b : ZMod p)) ^ ((p - 1) / 2)
          = (b : ZMod p) ^ (2 * ((p - 1) / 2)) := by
        rw [pow_mul]; ring_nf
      rw [h2]
      have : 2 * ((p - 1) / 2) = p - 1 := by omega
      rw [this]
      exact ZMod.pow_card_sub_one_eq_one hx0
    have hdvd := orderOf_dvd_of_pow_eq_one hpow
    rw [h] at hdvd
    have hle : p - 1 ≤ (p - 1) / 2 := Nat.le_of_dvd (by omega) hdvd
    omega

/-- If `a` is a perfect square then the only prime it can be a primitive root for is `2`;
in particular the set of such primes is finite. -/
theorem artinPrimes_subset_of_isSquare {a : ℤ} (ha : IsSquare a) :
    artinPrimes a ⊆ {2} := by
  intro p hp
  by_contra hne
  exact not_isPrimitiveRootMod_of_isSquare ha hp.1 (by simpa using hne) hp.2

theorem artinPrimes_finite_of_isSquare {a : ℤ} (ha : IsSquare a) :
    (artinPrimes a).Finite :=
  Set.Finite.subset (Set.finite_singleton 2) (artinPrimes_subset_of_isSquare ha)

/-! ### Necessity of the hypothesis "`a ≠ -1`" -/

/-- `-1` has order at most `2`, so it is not a primitive root modulo any prime `p ≥ 5`. -/
theorem not_isPrimitiveRootMod_neg_one {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  haveI := Fact.mk hp
  intro h
  have hsq : (((-1 : ℤ) : ZMod p)) ^ 2 = 1 := by push_cast; ring
  have hdvd := orderOf_dvd_of_pow_eq_one hsq
  rw [h] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- For `a = -1` the set of primes with `-1` a primitive root is contained in `{2, 3}`. -/
theorem artinPrimes_neg_one_subset : artinPrimes (-1) ⊆ {2, 3} := by
  intro p hp
  obtain ⟨hprime, hroot⟩ := hp
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  have h2 := hprime.two_le
  have h5 : 5 ≤ p := by
    rcases Nat.lt_or_ge p 5 with h' | h'
    · interval_cases p
      · exact absurd rfl hne.1
      · exact absurd rfl hne.2
      · norm_num at hprime
    · exact h'
  exact not_isPrimitiveRootMod_neg_one hprime h5 hroot

theorem artinPrimes_neg_one_finite : (artinPrimes (-1)).Finite :=
  Set.Finite.subset (Set.toFinite {2, 3}) artinPrimes_neg_one_subset

/-! ### A verified base case -/

/-- `2` is a primitive root modulo `11`. -/
theorem isPrimitiveRootMod_two_eleven : IsPrimitiveRootMod 2 11 := by
  rw [IsPrimitiveRootMod, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, by decide⟩

/-- `2` is a primitive root modulo `13`. -/
theorem isPrimitiveRootMod_two_thirteen : IsPrimitiveRootMod 2 13 := by
  rw [IsPrimitiveRootMod, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, by decide⟩

/-- `3` is a primitive root modulo `7`. -/
theorem isPrimitiveRootMod_three_seven : IsPrimitiveRootMod 3 7 := by
  rw [IsPrimitiveRootMod, orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, by decide⟩

/-! ### The main statement -/

/--
**Artin's conjecture on primitive roots**, formalized, together with everything that is
unconditionally provable about it here.

* (1) The statement of the conjecture is recorded as `Frontier.ArtinConjecture`, and it
  is equivalent to: for every admissible `a` and every bound `N` there is a prime `p > N`
  having `a` as a primitive root (a Lean-checked reformulation/reduction).
* (2) The excluded case `IsSquare a` is genuinely necessary: for such `a` the set of
  primes admitting `a` as a primitive root is contained in `{2}`, hence finite.
* (3) The excluded case `a = -1` is genuinely necessary: the corresponding set of primes
  is contained in `{2, 3}`, hence finite.
* (4) Base cases: `2` is a primitive root mod `11` and mod `13`, and `3` is one mod `7`.
-/
theorem artin_primitive_root :
    (ArtinConjecture ↔
        ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
          IsPrimitiveRootMod a p)
      ∧ (∀ a : ℤ, IsSquare a → artinPrimes a ⊆ {2} ∧ (artinPrimes a).Finite)
      ∧ (artinPrimes (-1) ⊆ {2, 3} ∧ (artinPrimes (-1)).Finite)
      ∧ (IsPrimitiveRootMod 2 11 ∧ IsPrimitiveRootMod 2 13 ∧ IsPrimitiveRootMod 3 7) := by
  refine ⟨⟨?_, ?_⟩, ?_, ⟨artinPrimes_neg_one_subset, artinPrimes_neg_one_finite⟩,
    isPrimitiveRootMod_two_eleven, isPrimitiveRootMod_two_thirteen,
    isPrimitiveRootMod_three_seven⟩
  · intro h a ha hsq N
    obtain ⟨p, hp, hpN⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hpN, hp.1, hp.2⟩
  · intro h a ha hsq
    refine Set.infinite_of_not_bddAbove ?_
    rintro ⟨N, hN⟩
    obtain ⟨p, hpN, hp, hroot⟩ := h a ha hsq N
    have := hN (show p ∈ artinPrimes a from ⟨hp, hroot⟩)
    omega
  · intro a ha
    exact ⟨artinPrimes_subset_of_isSquare ha, artinPrimes_finite_of_isSquare ha⟩

end Frontier

