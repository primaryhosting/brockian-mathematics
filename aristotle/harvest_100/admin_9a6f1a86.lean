/-
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Frontier

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` has
multiplicative order exactly `p - 1`, i.e. it generates the group `(ZMod p)ˣ`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- **Artin's conjecture on primitive roots.**  If an integer `a` is neither `-1`
nor a perfect square, then `a` is a primitive root modulo infinitely many primes.
(This is an open problem; it is only *stated* here.) -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a →
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Infinite

/-- If `a` is a perfect square then it is a quadratic residue mod every prime,
so its order divides `(p-1)/2`; hence it is never a primitive root mod an odd prime. -/
theorem not_isPrimitiveRootMod_of_isSquare {a : ℤ} (ha : IsSquare a) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) : ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, rfl⟩ := ha
  intro h
  set x : ZMod p := ((b * b : ℤ) : ZMod p) with hx
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpow : x ^ (p - 1) = 1 := by
    have := pow_orderOf_eq_one x
    rwa [h] at this
  have hb : ((b : ZMod p)) ≠ 0 := by
    intro hb0
    apply (one_ne_zero (α := ZMod p))
    rw [← hpow, hx]
    push_cast
    have hne : p - 1 ≠ 0 := by omega
    rw [hb0]
    simp [hne]
  -- write `p - 1 = 2 * q`
  obtain ⟨q, hq⟩ : ∃ q, p - 1 = 2 * q := by
    have hodd : Odd p := hp.odd_of_ne_two hp2
    obtain ⟨k, hk⟩ := hodd
    exact ⟨k, by omega⟩
  have hq0 : 0 < q := by omega
  have hxq : x ^ q = 1 := by
    have hbb : x = (b : ZMod p) ^ 2 := by rw [hx]; push_cast; ring
    rw [hbb, ← pow_mul]
    have : 2 * q = p - 1 := hq.symm
    rw [this]
    exact ZMod.pow_card_sub_one_eq_one hb
  have hdvd : orderOf x ∣ q := orderOf_dvd_of_pow_eq_one hxq
  have hle : orderOf x ≤ q := Nat.le_of_dvd hq0 hdvd
  rw [h] at hle
  omega

/-- `-1` is a primitive root only modulo `2` and `3`: for `p > 3` its order is at most `2`. -/
theorem not_isPrimitiveRootMod_neg_one {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ IsPrimitiveRootMod (-1) p := by
  haveI : Fact p.Prime := ⟨hp⟩
  intro h
  have hsq : (((-1 : ℤ) : ZMod p)) ^ 2 = 1 := by push_cast; ring
  have hdvd : orderOf (((-1 : ℤ) : ZMod p)) ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
  have hle : orderOf (((-1 : ℤ) : ZMod p)) ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  rw [h] at hle
  omega

/-- The exceptional set for a perfect square: at most the prime `2`. -/
theorem isSquare_primes_subset {a : ℤ} (ha : IsSquare a) :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p} ⊆ {2} := by
  intro p hp
  by_contra hne
  exact not_isPrimitiveRootMod_of_isSquare ha hp.1 (by simpa using hne) hp.2

/-- The exceptional set for `-1`: at most the primes `2` and `3`. -/
theorem neg_one_primes_subset :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod (-1) p} ⊆ {2, 3} := by
  intro p hp
  by_contra hne
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hne
  have h2 := hp.1.two_le
  exact not_isPrimitiveRootMod_neg_one hp.1 (by omega) hp.2

/-- Both exceptional cases of Artin's conjecture give a *finite* set of primes,
so the hypotheses `a ≠ -1` and `¬ IsSquare a` are necessary. -/
theorem artin_exceptions_finite {a : ℤ} (ha : IsSquare a ∨ a = -1) :
    {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Finite := by
  rcases ha with ha | rfl
  · exact Set.Finite.subset (Set.finite_singleton 2) (isSquare_primes_subset ha)
  · exact Set.Finite.subset (Set.toFinite _) neg_one_primes_subset

/-- Base case: `2` is a primitive root modulo `3`, `5`, `11`, `13`, `19` and `29`. -/
theorem two_isPrimitiveRootMod_examples :
    IsPrimitiveRootMod 2 3 ∧ IsPrimitiveRootMod 2 5 ∧ IsPrimitiveRootMod 2 11 ∧
      IsPrimitiveRootMod 2 13 ∧ IsPrimitiveRootMod 2 19 ∧ IsPrimitiveRootMod 2 29 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    · show orderOf _ = _
      norm_num
      rw [orderOf_eq_iff (by norm_num)]
      exact ⟨by decide, by decide⟩

/-- Artin's conjecture is equivalent to: for each admissible `a` the primes having `a`
as a primitive root are unbounded. -/
theorem artin_conjecture_iff_unbounded :
    ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p > N, p.Prime ∧ IsPrimitiveRootMod a p := by
  constructor
  · intro h a ha hsq N
    obtain ⟨p, hp, hpN⟩ := (h a ha hsq).exists_gt N
    exact ⟨p, hpN, hp⟩
  · intro h a ha hsq
    apply Set.infinite_of_not_bddAbove
    rintro ⟨N, hN⟩
    obtain ⟨p, hpN, hp⟩ := h a ha hsq N
    exact absurd (hN hp) (by omega)

/--
**Artin's conjecture on primitive roots**, together with the Lean-checked content
we can supply unconditionally:

1. the conjecture as a formal statement (`ArtinConjecture`), reduced to the equivalent
   statement that the primes with `a` as a primitive root are unbounded;
2. the excluded cases really are excluded — if `a` is a perfect square or `a = -1`,
   then `a` is a primitive root for only finitely many primes, so the hypotheses of
   the conjecture are necessary;
3. base cases: `2` is a primitive root modulo `3, 5, 11, 13, 19, 29`.
-/
theorem artin_primitive_root :
    (ArtinConjecture ↔
      ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → ∀ N : ℕ, ∃ p > N, p.Prime ∧ IsPrimitiveRootMod a p) ∧
    (∀ a : ℤ, (IsSquare a ∨ a = -1) →
      {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}.Finite) ∧
    (IsPrimitiveRootMod 2 3 ∧ IsPrimitiveRootMod 2 5 ∧ IsPrimitiveRootMod 2 11 ∧
      IsPrimitiveRootMod 2 13 ∧ IsPrimitiveRootMod 2 19 ∧ IsPrimitiveRootMod 2 29) :=
  ⟨artin_conjecture_iff_unbounded, fun _ ha => artin_exceptions_finite ha,
    two_isPrimitiveRootMod_examples⟩

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

