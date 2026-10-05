import Mathlib

/-!
# Artin Primitive Root
Category: Frontier — Prime Numbers
Target: Frontier.artin_primitive_root
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` lines to precede every other command, including module
-- docstrings, so the header block above sits immediately after the single import.)

namespace Frontier

/-! ## Definitions -/

/-- `a : ℤ` is a *primitive root* modulo `p` when the residue of `a` generates the
multiplicative group of `ZMod p`, i.e. it has multiplicative order `p - 1`. -/
def IsPrimitiveRootMod (a : ℤ) (p : ℕ) : Prop :=
  orderOf ((a : ZMod p)) = p - 1

/-- The set of primes modulo which `a` is a primitive root. -/
def artinPrimeSet (a : ℤ) : Set ℕ :=
  {p : ℕ | p.Prime ∧ IsPrimitiveRootMod a p}

/-- **Artin's conjecture on primitive roots**: every integer `a` which is neither `-1`
nor a perfect square is a primitive root modulo infinitely many primes. -/
def ArtinConjecture : Prop :=
  ∀ a : ℤ, a ≠ -1 → ¬ IsSquare a → (artinPrimeSet a).Infinite

/-! ## The definition really says "generates the multiplicative group" -/

/-- Sanity check on the formalization: for a prime `p`, having order `p - 1` is equivalent to
being a nonzero residue whose powers exhaust all nonzero residues. -/
theorem isPrimitiveRootMod_iff (a : ℤ) (p : ℕ) (hp : p.Prime) :
    IsPrimitiveRootMod a p ↔
      ((a : ZMod p) ≠ 0 ∧ ∀ x : ZMod p, x ≠ 0 → ∃ k : ℕ, ((a : ZMod p)) ^ k = x) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [IsPrimitiveRootMod]
  constructor
  · intro hord
    have hne : ((a : ZMod p)) ≠ 0 := by
      intro h
      have h1 := pow_orderOf_eq_one ((a : ZMod p))
      rw [h] at h1 hord
      rw [hord, zero_pow (by have := hp.two_le; omega)] at h1
      exact zero_ne_one h1
    refine ⟨hne, fun x hx => ?_⟩
    obtain ⟨u, hu⟩ := hne.isUnit
    obtain ⟨v, hv⟩ := hx.isUnit
    have hcard : orderOf u = Nat.card (ZMod p)ˣ := by
      rw [Nat.card_eq_fintype_card, ZMod.card_units p, ← hord, ← hu, orderOf_units]
    have htop : Subgroup.zpowers u = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [Nat.card_zpowers, hcard])
    have hvv : v ∈ Subgroup.zpowers u := htop ▸ Subgroup.mem_top v
    rw [← mem_powers_iff_mem_zpowers] at hvv
    obtain ⟨k, hk⟩ := hvv
    exact ⟨k, by rw [← hu, ← hv, ← hk]; push_cast; ring⟩
  · rintro ⟨hne, hgen⟩
    obtain ⟨u, hu⟩ := hne.isUnit
    have hall : ∀ v : (ZMod p)ˣ, v ∈ Submonoid.powers u := by
      intro v
      obtain ⟨k, hk⟩ := hgen (v : ZMod p) v.ne_zero
      exact ⟨k, Units.ext (by rw [Units.val_pow_eq_pow_val, hu, hk])⟩
    have hcard := orderOf_eq_card_of_forall_mem_powers hall
    rw [← orderOf_units, hu] at hcard
    rw [hcard, Nat.card_eq_fintype_card, ZMod.card_units p]

/-! ## The Lean-checked reduction: the excluded cases are genuinely exceptional -/

/-- If `a = -1` or `a` is a perfect square, then `a` is not a primitive root modulo any
prime `p > 3`. -/
theorem not_isPrimitiveRootMod_of_exceptional
    (a : ℤ) (p : ℕ) (hp : p.Prime) (h3 : 3 < p) (ha : a = -1 ∨ IsSquare a) :
    ¬ IsPrimitiveRootMod a p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hodd : p % 2 = 1 := Nat.odd_iff.mp (hp.odd_of_ne_two (by omega))
  intro hord
  rw [IsPrimitiveRootMod] at hord
  rcases ha with rfl | ⟨b, rfl⟩
  · -- `-1` has order at most `2`, so it can only be a primitive root when `p - 1 ≤ 2`.
    have h2 : (((-1 : ℤ)) : ZMod p) ^ 2 = 1 := by push_cast; ring
    have hle : orderOf (((-1 : ℤ)) : ZMod p) ≤ 2 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one h2)
    omega
  · by_cases hb : ((b : ℤ) : ZMod p) = 0
    · -- a square of a multiple of `p` is `0`, which has no finite order.
      have hz : (((b * b : ℤ)) : ZMod p) = 0 := by push_cast at hb ⊢; rw [hb]; ring
      have h1 : (((b * b : ℤ)) : ZMod p) ^ orderOf (((b * b : ℤ)) : ZMod p) = 1 :=
        pow_orderOf_eq_one _
      rw [hz] at h1 hord
      rw [hord, zero_pow (by omega)] at h1
      exact zero_ne_one h1
    · -- a nonzero square has order dividing `(p - 1) / 2`, by Fermat's little theorem.
      set m := (p - 1) / 2 with hm
      have hpm : 2 * m = p - 1 := by omega
      have hpow : (((b * b : ℤ)) : ZMod p) ^ m = 1 := by
        have hrw : (((b * b : ℤ)) : ZMod p) ^ m = ((b : ℤ) : ZMod p) ^ (2 * m) := by
          push_cast; ring
        rw [hrw, hpm]
        exact ZMod.pow_card_sub_one_eq_one hb
      have hle : orderOf (((b * b : ℤ)) : ZMod p) ≤ m :=
        Nat.le_of_dvd (by omega) (orderOf_dvd_of_pow_eq_one hpow)
      omega

/-- **Lean-checked reduction for Artin's conjecture.**
The excluded cases in Artin's conjecture are genuinely exceptional: if `a = -1` or `a` is a
perfect square, then `a` is a primitive root modulo only finitely many primes (in fact only
possibly `p = 2` or `p = 3`).  Equivalently, the hypotheses `a ≠ -1` and `¬ IsSquare a` in
`Frontier.ArtinConjecture` cannot be dropped. -/
theorem artin_primitive_root (a : ℤ) (ha : a = -1 ∨ IsSquare a) :
    (artinPrimeSet a).Finite := by
  apply Set.Finite.subset (Set.finite_Iic 3)
  intro p hp
  simp only [artinPrimeSet, Set.mem_setOf_eq] at hp
  by_contra hlt
  simp only [Set.mem_Iic, not_le] at hlt
  exact not_isPrimitiveRootMod_of_exceptional a p hp.1 hlt ha hp.2

/-! ## Concrete computations -/

/-- A convenient criterion for computing multiplicative orders in concrete monoids. -/
theorem orderOf_eq_of_pow_eq_one {M : Type*} [Monoid M] {x : M} {n : ℕ} (hn : 0 < n)
    (h : x ^ n = 1) (h' : ∀ k, 0 < k → k < n → x ^ k ≠ 1) : orderOf x = n := by
  have hdvd : orderOf x ∣ n := orderOf_dvd_of_pow_eq_one h
  have hpos : 0 < orderOf x := by
    rcases Nat.eq_zero_or_pos (orderOf x) with h0 | h0
    · rw [h0] at hdvd
      omega
    · exact h0
  have hle : orderOf x ≤ n := Nat.le_of_dvd hn hdvd
  rcases eq_or_lt_of_le hle with heq | hlt
  · exact heq
  · exact absurd (pow_orderOf_eq_one x) (h' _ hpos hlt)

/-- A concrete base case: `2` is a primitive root modulo `5`. -/
theorem isPrimitiveRootMod_two_five : IsPrimitiveRootMod 2 5 := by
  show orderOf (((2 : ℤ)) : ZMod 5) = 4
  refine orderOf_eq_of_pow_eq_one (by norm_num) (by decide) ?_
  intro k hk hk4
  interval_cases k <;> decide

/-- `-1` is a primitive root modulo `3`. -/
theorem isPrimitiveRootMod_neg_one_three : IsPrimitiveRootMod (-1) 3 := by
  show orderOf (((-1 : ℤ)) : ZMod 3) = 2
  refine orderOf_eq_of_pow_eq_one (by norm_num) (by decide) ?_
  intro k hk hk2
  interval_cases k <;> decide

/-- `-1` is a primitive root modulo `2` (trivially, as `-1 ≡ 1` and the group is trivial). -/
theorem isPrimitiveRootMod_neg_one_two : IsPrimitiveRootMod (-1) 2 := by
  show orderOf (((-1 : ℤ)) : ZMod 2) = 1
  have h : (((-1 : ℤ)) : ZMod 2) = 1 := by decide
  rw [h, orderOf_one]

/-- The exceptional set for `a = -1` computed exactly: `-1` is a primitive root modulo `p`
precisely for `p = 2` and `p = 3`. -/
theorem artinPrimeSet_neg_one : artinPrimeSet (-1) = {2, 3} := by
  ext p
  simp only [artinPrimeSet, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨hp, hroot⟩
    have hle : p ≤ 3 := by
      by_contra hlt
      exact not_isPrimitiveRootMod_of_exceptional (-1) p hp (by omega) (Or.inl rfl) hroot
    have h2 := hp.two_le
    interval_cases p
    · exact Or.inl rfl
    · exact absurd hp (by norm_num)
  · rintro (rfl | rfl)
    · exact ⟨by norm_num, isPrimitiveRootMod_neg_one_two⟩
    · exact ⟨by norm_num, isPrimitiveRootMod_neg_one_three⟩

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

