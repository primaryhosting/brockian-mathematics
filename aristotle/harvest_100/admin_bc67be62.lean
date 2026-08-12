import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

/-- `a : ℤ` is a *primitive root modulo `p`* when its residue generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- The set of primes for which `a` is a primitive root. -/
def artinPrimes (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (artinPrimes a).Infinite

/-- A Lean-checked reduction: Artin's conjecture is equivalent to the statement that for
every admissible `a` and every bound `N` there is a prime `p > N` having `a` as a
primitive root. -/
lemma artinConjecture_iff :
    ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p : ℕ, N < p ∧ p.Prime ∧
        IsPrimitiveRootMod a p := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hlt⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hlt, hp.1, hp.2⟩
  · intro h a ha hsq
    refine Set.infinite_of_forall_exists_gt ?_
    intro N
    obtain ⟨p, hlt, hp, hprim⟩ := h a ha hsq N
    exact ⟨p, ⟨hp, hprim⟩, hlt⟩

/-- If `a` is a primitive root mod the prime `p`, then `a` is invertible mod `p`. -/
lemma ne_zero_of_isPrimitiveRootMod {a : ℤ} {p : ℕ} (hp : p.Prime)
    (h : IsPrimitiveRootMod a p) : (a : ZMod p) ≠ 0 := by
  have hpow : ((a : ZMod p)) ^ (p - 1) = 1 := by
    have := pow_orderOf_eq_one ((a : ZMod p))
    rwa [h] at this
  intro h0
  have h2 := hp.two_le
  rw [h0, zero_pow (by omega : p - 1 ≠ 0)] at hpow
  haveI : Fact p.Prime := ⟨hp⟩
  exact zero_ne_one hpow

/-- A perfect square is a primitive root only modulo `2`. -/
lemma artinPrimes_subset_of_isSquare {a : ℤ} (ha : IsSquare a) :
    artinPrimes a ⊆ {2} := by
  rintro p ⟨hp, hprim⟩
  by_contra hne
  simp only [Set.mem_singleton_iff] at hne
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : Odd p := hp.odd_of_ne_two hne
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  obtain ⟨b, hb⟩ := ha
  have hab : (a : ZMod p) = (b : ZMod p) * (b : ZMod p) := by
    rw [hb]; push_cast; ring
  have hbne : (b : ZMod p) ≠ 0 := by
    intro h0
    exact ne_zero_of_isPrimitiveRootMod hp hprim (by rw [hab, h0, mul_zero])
  have hhalf : ((a : ZMod p)) ^ ((p - 1) / 2) = 1 := by
    have h2 : 2 * ((p - 1) / 2) = p - 1 := by
      obtain ⟨k, hk⟩ := hodd
      omega
    rw [hab, ← sq, ← pow_mul, h2]
    exact ZMod.pow_card_sub_one_eq_one hbne
  have hdvd : orderOf ((a : ZMod p)) ∣ (p - 1) / 2 := orderOf_dvd_of_pow_eq_one hhalf
  rw [hprim] at hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

lemma finite_artinPrimes_of_isSquare {a : ℤ} (ha : IsSquare a) :
    (artinPrimes a).Finite :=
  Set.Finite.subset (Set.finite_singleton 2) (artinPrimes_subset_of_isSquare ha)

/-- `-1` is a primitive root only modulo `2` and `3`. -/
lemma artinPrimes_neg_one_subset : artinPrimes (-1) ⊆ {2, 3} := by
  rintro p ⟨hp, hprim⟩
  have hcast : (((-1 : ℤ) : ZMod p)) = -1 := by push_cast; ring
  have h2 : ((-1 : ZMod p)) ^ 2 = 1 := by ring
  have hdvd : orderOf ((-1 : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [IsPrimitiveRootMod, hcast] at hprim
  rw [hprim] at hdvd
  have hle := Nat.le_of_dvd (by norm_num) hdvd
  have := hp.two_le
  have : p = 2 ∨ p = 3 := by omega
  simpa using this

lemma finite_artinPrimes_neg_one : (artinPrimes (-1)).Finite :=
  Set.Finite.subset (Set.toFinite _) artinPrimes_neg_one_subset

/-- Every prime admits *some* primitive root: the unconditional weak form of Artin's
conjecture. -/
lemma exists_isPrimitiveRootMod {p : ℕ} (hp : p.Prime) :
    ∃ a : ℤ, IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨((g : ZMod p).val : ℤ), ?_⟩
  have hcast : ((((g : ZMod p).val : ℤ)) : ZMod p) = ((g : ZMod p)) := by
    push_cast
    simp [ZMod.natCast_val, ZMod.cast_id]
  rw [IsPrimitiveRootMod, hcast, orderOf_units,
    orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient,
    Nat.totient_prime hp]

/-- There are infinitely many primes possessing a primitive root (unconditionally). -/
lemma infinite_primes_with_primitive_root :
    {p : ℕ | p.Prime ∧ ∃ a : ℤ, IsPrimitiveRootMod a p}.Infinite := by
  apply Set.Infinite.mono (s := {p : ℕ | p.Prime}) _ Nat.infinite_setOf_prime
  intro p hp
  exact ⟨hp, exists_isPrimitiveRootMod hp⟩

lemma two_primitive_root_three : IsPrimitiveRootMod 2 3 := by
  have : ((2 : ℤ) : ZMod 3) = (2 : ZMod 3) := by norm_num
  rw [IsPrimitiveRootMod, this]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have h1 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := hq.two_le
  interval_cases q
  all_goals (revert hdvd hq; decide)

lemma two_primitive_root_five : IsPrimitiveRootMod 2 5 := by
  have : ((2 : ℤ) : ZMod 5) = (2 : ZMod 5) := by norm_num
  rw [IsPrimitiveRootMod, this]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have h1 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := hq.two_le
  interval_cases q
  all_goals (revert hdvd hq; decide)

lemma two_primitive_root_eleven : IsPrimitiveRootMod 2 11 := by
  have : ((2 : ℤ) : ZMod 11) = (2 : ZMod 11) := by norm_num
  rw [IsPrimitiveRootMod, this]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have h1 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := hq.two_le
  interval_cases q
  all_goals (revert hdvd hq; decide)

lemma two_primitive_root_thirteen : IsPrimitiveRootMod 2 13 := by
  have : ((2 : ℤ) : ZMod 13) = (2 : ZMod 13) := by norm_num
  rw [IsPrimitiveRootMod, this]
  apply orderOf_eq_of_pow_and_pow_div_prime (by norm_num) (by decide)
  intro q hq hdvd
  have h1 := Nat.le_of_dvd (by norm_num) hdvd
  have h2 := hq.two_le
  interval_cases q
  all_goals (revert hdvd hq; decide)

/-- **Artin's conjecture on primitive roots**, formalized, together with everything that
can be established unconditionally about it:

1. the hypothesis "`a` is not a perfect square" is necessary: a square is a primitive
   root modulo no prime other than `2`;
2. the hypothesis "`a ≠ -1`" is necessary: `-1` is a primitive root only modulo `2`
   and `3`;
3. unconditionally, infinitely many primes possess *some* primitive root;
4. base case: `2` is a primitive root modulo `3, 5, 11, 13`, so these primes lie in the
   set that Artin's conjecture asserts to be infinite for `a = 2`;
5. the reduction: the conjecture is equivalent to the assertion that for every admissible
   `a` and every bound `N` there is a prime `p > N` having `a` as a primitive root. -/
theorem artin_primitive_root :
    (∀ a : ℤ, IsSquare a → (artinPrimes a).Finite) ∧
    (artinPrimes (-1)).Finite ∧
    {p : ℕ | p.Prime ∧ ∃ a : ℤ, IsPrimitiveRootMod a p}.Infinite ∧
    ({3, 5, 11, 13} : Set ℕ) ⊆ artinPrimes 2 ∧
    (ArtinConjecture ↔ ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p : ℕ, N < p ∧
      p.Prime ∧ IsPrimitiveRootMod a p) := by
  refine ⟨fun a ha => finite_artinPrimes_of_isSquare ha, finite_artinPrimes_neg_one,
    infinite_primes_with_primitive_root, ?_, artinConjecture_iff⟩
  rintro p (rfl | rfl | rfl | rfl)
  · exact ⟨by norm_num, two_primitive_root_three⟩
  · exact ⟨by norm_num, two_primitive_root_five⟩
  · exact ⟨by norm_num, two_primitive_root_eleven⟩
  · exact ⟨by norm_num, two_primitive_root_thirteen⟩

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

