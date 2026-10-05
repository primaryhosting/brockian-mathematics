import Mathlib
/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

section Basic

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The inner derivation (adjoint action) `ad H x = H * x - x * H`. -/

lemma ad_loc
    (loc_mono : ∀ {p q p' q' : ℤ} {x : A}, p' ≤ p → q ≤ q' → loc p q x → loc p' q' x)
    (loc_comm : ∀ {p q p' q' : ℤ} {x y : A}, q < p' → loc p q x → loc p' q' y → x * y = y * x)
    (loc_zero : ∀ p q : ℤ, loc p q 0)
    (loc_add : ∀ {p q : ℤ} {x y : A}, loc p q x → loc p q y → loc p q (x + y))
    (loc_neg : ∀ {p q : ℤ} {x : A}, loc p q x → loc p q (-x))
    (loc_mul : ∀ {p q : ℤ} {x y : A}, loc p q x → loc p q y → loc p q (x * y))
    (Λ : Finset ℤ) (hh : ℤ → A) (H : A) (hH : H = ∑ z ∈ Λ, hh z)
    (hhloc : ∀ z ∈ Λ, loc z (z + 1) (hh z))
    {p q : ℤ} {x : A} (hx : loc p q x) :
    loc (p - 1) (q + 1) (ad H x) := by
  have hsplit : ad H x = ∑ z ∈ Λ, ad (hh z) x := by
    simp only [ad, hH, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  rw [hsplit]
  refine Finset.sum_induction _ (loc (p - 1) (q + 1)) (fun u v hu hv => loc_add hu hv)
    (loc_zero _ _) (fun z hz => ?_)
  rcases lt_or_ge (z + 1) p with hlt | hge
  · have hc : hh z * x = x * hh z := loc_comm hlt (hhloc z hz) hx
    simp [ad, hc, loc_zero]
  · rcases lt_or_ge q z with hgt | hle
    · have hc : x * hh z = hh z * x := loc_comm hgt hx (hhloc z hz)
      simp [ad, hc, loc_zero]
    · have h1 : loc (p - 1) (q + 1) (hh z) := loc_mono (by omega) (by omega) (hhloc z hz)
      have h2 : loc (p - 1) (q + 1) x := loc_mono (by omega) (by omega) hx
      have he : ad (hh z) x = hh z * x + -(x * hh z) := by rw [ad, sub_eq_add_neg]
      rw [he]
      exact loc_add (loc_mul h1 h2) (loc_neg (loc_mul h2 h1))

omit [NormedAlgebra ℝ A] in
/-- Support growth after `n` steps of the derivation: the support of `(ad H)^[n] x`
is contained in the `n`-neighbourhood of the support of `x`. -/
