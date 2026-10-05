/-!
# Chinese Remainder
Category: Pure Mathematics
Target: Math.chinese_remainder
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped Function

namespace Math

variable {ι : Type*} [Fintype ι] (n : ι → ℕ)

/-- The canonical ring homomorphism `ZMod (∏ i, n i) →+* Π i, ZMod (n i)`, given componentwise
by reduction modulo `n i`. -/
def crtHom : ZMod (∏ i, n i) →+* ∀ i, ZMod (n i) :=
  Pi.ringHom fun i =>
    ZMod.castHom (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) (ZMod (n i))

@[simp] lemma crtHom_intCast (a : ℤ) (i : ι) : crtHom n (a : ZMod (∏ i, n i)) i = (a : ZMod (n i)) :=
  map_intCast (ZMod.castHom (Finset.dvd_prod_of_mem n (Finset.mem_univ i)) (ZMod (n i))) a

/-- Injectivity of the canonical map: an integer divisible by each pairwise-coprime `n i` is
divisible by their product. -/
theorem crtHom_injective (h : Pairwise (Nat.Coprime on n)) : Function.Injective (crtHom n) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨a, rfl⟩ := ZMod.intCast_surjective x
  have hdvd : ∀ i, ((n i : ℤ)) ∣ a := by
    intro i
    rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    have := congrFun hx i
    simpa using this
  have hco : Pairwise (IsCoprime on fun i => (n i : ℤ)) := by
    intro i j hij
    exact Int.isCoprime_iff_gcd_eq_one.mpr (by simpa [Int.gcd_natCast_natCast] using h hij)
  have : ((∏ i, n i : ℕ) : ℤ) ∣ a := by
    rw [Nat.cast_prod]
    exact Fintype.prod_dvd_of_coprime hco hdvd
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd]
  exact this

section Surjective

private lemma castHom_ringEquivCongr {m N : ℕ} (hmN : m = N) (hdvd : m ∣ N) (x : ZMod m) :
    ZMod.castHom hdvd (ZMod m) (ZMod.ringEquivCongr hmN x) = x := by
  subst hmN
  rw [ZMod.ringEquivCongr_refl_apply]
  have : hdvd = dvd_rfl := rfl
  subst this
  simp [ZMod.castHom_self]

/-- Surjectivity in the degenerate case where one of the moduli is zero (then all the others
are `1`, by coprimality, and the product is `0`). -/
private lemma crtHom_surjective_of_zero (h : Pairwise (Nat.Coprime on n)) {i₀ : ι}
    (hi₀ : n i₀ = 0) : Function.Surjective (crtHom n) := by
  have hone : ∀ j, j ≠ i₀ → n j = 1 := by
    intro j hj
    have := h (Ne.symm hj)
    rw [Function.onFun, hi₀, Nat.coprime_zero_left] at this
    exact this
  have hN : ∏ i, n i = 0 := Finset.prod_eq_zero (Finset.mem_univ i₀) hi₀
  intro f
  refine ⟨ZMod.ringEquivCongr (hi₀.trans hN.symm) (f i₀), ?_⟩
  funext j
  by_cases hj : j = i₀
  · subst hj
    exact castHom_ringEquivCongr _ _ _
  · have : Subsingleton (ZMod (n j)) := by
      rw [hone j hj]; infer_instance
    exact Subsingleton.elim _ _

theorem crtHom_surjective (h : Pairwise (Nat.Coprime on n)) : Function.Surjective (crtHom n) := by
  by_cases hz : ∃ i, n i = 0
  · obtain ⟨i₀, hi₀⟩ := hz
    exact crtHom_surjective_of_zero n h hi₀
  · push_neg at hz
    have : ∀ i, NeZero (n i) := fun i => ⟨hz i⟩
    have hNz : NeZero (∏ i, n i) := ⟨Finset.prod_ne_zero_iff.mpr fun i _ => hz i⟩
    have hcard : Fintype.card (ZMod (∏ i, n i)) = Fintype.card (∀ i, ZMod (n i)) := by
      rw [ZMod.card, Fintype.card_pi]
      exact Finset.prod_congr rfl fun i _ => (ZMod.card (n i)).symm
    exact ((Fintype.bijective_iff_injective_and_card _).mpr
      ⟨crtHom_injective n h, hcard⟩).surjective

end Surjective

theorem crtHom_bijective (h : Pairwise (Nat.Coprime on n)) : Function.Bijective (crtHom n) :=
  ⟨crtHom_injective n h, crtHom_surjective n h⟩

/-- **Chinese Remainder Theorem.** For a finite family of pairwise coprime natural numbers `n i`,
the canonical reduction map gives a ring isomorphism `ZMod (∏ i, n i) ≃+* Π i, ZMod (n i)`. -/
theorem chinese_remainder (h : Pairwise (Nat.Coprime on n)) :
    ∃ e : ZMod (∏ i, n i) ≃+* ∀ i, ZMod (n i), ⇑e = ⇑(crtHom n) :=
  ⟨RingEquiv.ofBijective (crtHom n) (crtHom_bijective n h), rfl⟩

end Math

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

