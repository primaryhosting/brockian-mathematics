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

set_option grind.warning false

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when its residue class generates the
multiplicative group of `ZMod p`, i.e. when it has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither a
perfect square nor `-1` is a primitive root modulo infinitely many primes.

(This is an open problem; it is stated here as a `Prop`, not proved.) -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, ¬ IsSquare a → a ≠ -1 →
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Infinite

/-- The first exclusion in Artin's conjecture is necessary: a perfect square is never a
primitive root modulo an odd prime, since its order divides `(p - 1)/2`. -/
lemma sq_not_primitiveRoot (a : ℤ) (ha : IsSquare a) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  intro h
  rw [IsPrimitiveRootMod, show (((b * b : ℤ) : ZMod p)) = (b : ZMod p) ^ 2 by push_cast; ring] at h
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hp3 : 3 ≤ p := by
    obtain ⟨k, hk⟩ := hodd
    have := hp.two_le
    omega
  have hb : ((b : ZMod p)) ≠ 0 := by
    intro hb0
    rw [hb0] at h
    simp only [ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, orderOf_zero] at h
    omega
  have key : ((b : ZMod p) ^ 2) ^ ((p - 1) / 2) = 1 := by
    rw [← pow_mul, show 2 * ((p - 1) / 2) = p - 1 by obtain ⟨k, hk⟩ := hodd; omega]
    exact ZMod.pow_card_sub_one_eq_one hb
  have hdvd := orderOf_dvd_of_pow_eq_one key
  rw [h] at hdvd
  have := Nat.le_of_dvd (by omega) hdvd
  omega

/-- The second exclusion in Artin's conjecture is necessary: `-1` has order `2`, hence is
not a primitive root modulo any prime `p > 3`. -/
lemma neg_one_not_primitiveRoot (p : ℕ) (hp : p.Prime) (hp3 : 3 < p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have key : (((-1 : ℤ) : ZMod p)) ^ 2 = 1 := by push_cast; ring
  have hdvd := orderOf_dvd_of_pow_eq_one key
  rw [IsPrimitiveRootMod] at h
  rw [h] at hdvd
  have := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- A base case: `2` is a primitive root modulo `5`. -/
lemma two_primitiveRoot_five : IsPrimitiveRootMod 2 5 := by
  have h4 : ((2 : ℤ) : ZMod 5) ^ 4 = 1 := by decide
  have hd := orderOf_dvd_of_pow_eq_one h4
  have h2 : ¬ (orderOf ((2 : ℤ) : ZMod 5) ∣ 2) := by
    intro hh
    exact absurd (orderOf_dvd_iff_pow_eq_one.mp hh) (by decide)
  have hle : orderOf ((2 : ℤ) : ZMod 5) ≤ 4 := Nat.le_of_dvd (by norm_num) hd
  rw [IsPrimitiveRootMod]
  generalize orderOf ((2 : ℤ) : ZMod 5) = n at *
  interval_cases n <;> simp_all

/-- Primitive roots exist modulo every prime: the unit group of `ZMod p` is cyclic. -/
lemma exists_primitiveRootMod (p : ℕ) (hp : p.Prime) : ∃ a : ℤ, IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := (ZMod p)ˣ)
  refine ⟨((g : ZMod p).val : ℤ), ?_⟩
  have hcast : ((((g : ZMod p).val : ℤ)) : ZMod p) = ((g : ZMod p)) := by
    push_cast [ZMod.natCast_val, ZMod.cast_id]
    rfl
  rw [IsPrimitiveRootMod, hcast, orderOf_units,
    orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_eq_fintype_card,
    ZMod.card_units_eq_totient, Nat.totient_prime hp]

/-- For a perfect square `a`, the set of primes having `a` as a primitive root is contained
in `{2}`, hence finite: Artin's conjecture genuinely fails for such `a`. -/
lemma finite_primes_primitiveRoot_of_isSquare (a : ℤ) (ha : IsSquare a) :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Finite := by
  refine Set.Finite.subset (Set.finite_singleton 2) ?_
  rintro p ⟨hp, hpr⟩
  by_contra hne
  exact sq_not_primitiveRoot a ha p hp hne hpr

/-- The set of primes having `-1` as a primitive root is contained in `{2, 3}`, hence
finite: Artin's conjecture genuinely fails for `a = -1`. -/
lemma finite_primes_primitiveRoot_neg_one :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod (-1) p}.Finite := by
  refine Set.Finite.subset (Set.toFinite ({2, 3} : Set ℕ)) ?_
  rintro p ⟨hp, hpr⟩
  have hp3 : ¬ 3 < p := fun h => neg_one_not_primitiveRoot p hp h hpr
  have := hp.two_le
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
  interval_cases p
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- **Artin's primitive root conjecture: statement, necessity of its hypotheses, and a
base case.**

`Frontier.ArtinConjecture` states the (open) conjecture. This theorem records the
Lean-checked reduction accompanying it:

* both exclusions in the conjecture are necessary — a perfect square is never a primitive
  root modulo an odd prime, and `-1` is never a primitive root modulo a prime `p > 3`, so
  for those `a` the corresponding set of primes is *finite*, not infinite;
* primitive roots do exist modulo every prime;
* the base case `2` is a primitive root modulo `5`. -/
theorem artin_primitive_root :
    (∀ a : ℤ, IsSquare a → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsPrimitiveRootMod a p) ∧
      (∀ p : ℕ, p.Prime → 3 < p → ¬ IsPrimitiveRootMod (-1) p) ∧
      (∀ a : ℤ, IsSquare a → {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Finite) ∧
      {p : ℕ | p.Prime ∧ IsPrimitiveRootMod (-1) p}.Finite ∧
      (∀ p : ℕ, p.Prime → ∃ a : ℤ, IsPrimitiveRootMod a p) ∧
      IsPrimitiveRootMod 2 5 :=
  ⟨sq_not_primitiveRoot, neg_one_not_primitiveRoot, finite_primes_primitiveRoot_of_isSquare,
    finite_primes_primitiveRoot_neg_one, exists_primitiveRootMod, two_primitiveRoot_five⟩

end Frontier

