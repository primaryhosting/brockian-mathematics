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
