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

namespace Brockian

/-- The *wheel* at modulus `M` is the set of residue classes modulo `M` that are coprime to `M`,
i.e. the units of `ZMod M`.

`M` is a *Goldbach wheel modulus of order 2* when the wheel is a `2`-fold additive basis of
`ZMod M`: every residue class modulo `M` is a sum of two classes lying on the wheel.

This is exactly the local (mod `M`) condition one has to check before a modulus `M` can be
used as a wheel in a two-prime (Goldbach-type) sieve: if `n` is a sum of two primes not dividing
`M`, then its class mod `M` must be a sum of two units. -/
def IsGoldbachWheelModulusK2 (M : ℕ) : Prop :=
  ∀ r : ZMod M, ∃ a b : ZMod M, IsUnit a ∧ IsUnit b ∧ a + b = r

/-- Any prime modulus `p` with `p ≠ 2` is a Goldbach wheel modulus of order 2. -/
theorem isGoldbachWheelModulusK2_of_prime {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) :
    IsGoldbachWheelModulusK2 p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : (1 : ZMod p) ≠ 0 := one_ne_zero
  have h2' : (2 : ZMod p) ≠ 0 := by
    have hcast : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hdvd
      exact h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp hdvd)
    simpa using hcast
  intro r
  by_cases h : r = 1
  · refine ⟨2, -1, isUnit_iff_ne_zero.mpr h2', isUnit_iff_ne_zero.mpr (neg_ne_zero.mpr h1), ?_⟩
    rw [h]; ring
  · refine ⟨1, r - 1, isUnit_one, ?_, by ring⟩
    exact isUnit_iff_ne_zero.mpr fun hc => h (sub_eq_zero.mp hc)

/-- **New wheel modulus.** `1153` is a Goldbach wheel modulus of order `2`: every residue class
modulo `1153` is the sum of two residue classes coprime to `1153`. -/
theorem GoldbachWheelK2_1153 : IsGoldbachWheelModulusK2 1153 :=
  isGoldbachWheelModulusK2_of_prime (by norm_num) (by norm_num)

/-- Concrete `ℕ`-level form of the wheel property at `1153`: every natural number is congruent
modulo `1153` to a sum `a + b` with `a` and `b` both coprime to `1153`. -/
theorem goldbachWheelK2_1153_nat (n : ℕ) :
    ∃ a b : ℕ, Nat.Coprime a 1153 ∧ Nat.Coprime b 1153 ∧ (a + b) % 1153 = n % 1153 := by
  obtain ⟨a, b, ha, hb, hab⟩ := GoldbachWheelK2_1153 (n : ZMod 1153)
  refine ⟨a.val, b.val, ?_, ?_, ?_⟩
  · rw [← ZMod.isUnit_iff_coprime]
    simpa using ha
  · rw [← ZMod.isUnit_iff_coprime]
    simpa using hb
  · have hc : ((a.val + b.val : ℕ) : ZMod 1153) = (n : ZMod 1153) := by
      push_cast [ZMod.natCast_val, ZMod.cast_id]
      exact hab
    exact (ZMod.natCast_eq_natCast_iff' _ _ _).mp hc

/-- For a prime modulus `p`, every residue class has at least `p - 2` representations as an
ordered sum of two classes coprime to `p`. -/
theorem card_wheel_representations_ge {p : ℕ} [Fact p.Prime] [NeZero p] (r : ZMod p) :
    p - 2 ≤ (Finset.univ.filter
      fun q : ZMod p × ZMod p => IsUnit q.1 ∧ IsUnit q.2 ∧ q.1 + q.2 = r).card := by
  have hcard : p - 2 ≤ (Finset.univ \ ({0, r} : Finset (ZMod p))).card := by
    have h1 : (Finset.univ : Finset (ZMod p)).card = p := by
      rw [Finset.card_univ, ZMod.card]
    have h2 : ({0, r} : Finset (ZMod p)).card ≤ 2 :=
      (Finset.card_insert_le _ _).trans (by simp)
    have h3 := Finset.card_sdiff_add_card_eq_card (Finset.subset_univ ({0, r} : Finset (ZMod p)))
    omega
  refine le_trans hcard (Finset.card_le_card_of_injOn (fun a => (a, r - a)) ?_ ?_)
  · intro a ha
    have ha' := Finset.mem_sdiff.mp (Finset.mem_coe.mp ha)
    have ha1 : a ≠ 0 := fun h => ha'.2 (by simp [h])
    have ha2 : a ≠ r := fun h => ha'.2 (by simp [h])
    refine Finset.mem_coe.mpr <| Finset.mem_filter.mpr ⟨Finset.mem_univ _,
      isUnit_iff_ne_zero.mpr ha1, isUnit_iff_ne_zero.mpr (sub_ne_zero.mpr (Ne.symm ha2)), ?_⟩
    exact add_sub_cancel a r
  · intro a _ b _ hab
    exact congrArg Prod.fst hab

/-- `1153` is prime, recorded as an instance so that `ZMod 1153` is available as a field. -/
instance fact_prime_1153 : Fact (Nat.Prime 1153) := ⟨by norm_num⟩

/-- Quantitative form of the wheel property at `1153`: every residue class modulo `1153` has at
least `1151` representations as an ordered sum of two classes coprime to `1153`. -/
theorem goldbachWheelK2_1153_card (r : ZMod 1153) :
    1151 ≤ (Finset.univ.filter
      fun q : ZMod 1153 × ZMod 1153 => IsUnit q.1 ∧ IsUnit q.2 ∧ q.1 + q.2 = r).card := by
  have h := card_wheel_representations_ge (p := 1153) r
  have e : (1153 : ℕ) - 2 = 1151 := by norm_num
  rwa [e] at h

end Brockian

