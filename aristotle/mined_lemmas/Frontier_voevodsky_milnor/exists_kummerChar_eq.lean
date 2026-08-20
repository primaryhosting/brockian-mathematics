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

import Mathlib

/-!
# Mod-2 Milnor K-theory of a field

`K^M_n(F)/2` is the abelian group (a `ZMod 2`-vector space) presented by generators the
symbols `{a₁, …, aₙ}` with `aᵢ ∈ Fˣ`, subject to
* multilinearity `{…, a·b, …} = {…, a, …} + {…, b, …}`, and
* the Steinberg relation `{…, a, …, 1 - a, …} = 0`.

Since the coefficients are taken in `ZMod 2` this is exactly Milnor K-theory modulo `2`.

## Main definitions

* `Frontier.milnorRelations F n` : the set of defining relations.
* `Frontier.KMilnorMod2 F n` : the group `K^M_n(F)/2`.
* `Frontier.symbol F v` : the symbol `{v 0, …, v (n-1)}`.

## Main results

* `Frontier.kMilnorMod2ZeroEquiv` : `K^M_0(F)/2 ≃ ℤ/2`.
* `Frontier.exists_symbol_eq_one` : in degree one, every element is a single symbol.
-/

namespace Frontier

variable (F : Type) [Field F]

/-- The defining relations of `K^M_n(F)/2`: multilinearity in each slot and the Steinberg
relation `{…, a, …, 1 - a, …} = 0`. -/

lemma exists_kummerChar_eq (hF : (2 : F) ≠ 0) (chi : GalGroup F → ZMod 2)
    (hchi : chi ∈ contChars (GalGroup F)) :
    ∃ a : Fˣ, (kummerChar a : GalGroup F → ZMod 2) = chi := by
  obtain ⟨hcont, hhom⟩ := hchi
  by_cases hzero : chi = 0
  · exact ⟨1, by rw [kummerChar_one hF, hzero]⟩
  obtain ⟨s0, hs0⟩ : ∃ σ : GalGroup F, chi σ = 1 := by
    by_contra hcon
    push_neg at hcon
    exact hzero (funext fun σ => by
      by_contra hne
      exact hcon σ (zmod_two_eq_one_of_ne_zero hne))
  set H := charKernel chi hhom with hH
  have hHopen : IsOpen (H : Set (GalGroup F)) := by
    have hpre : (H : Set (GalGroup F)) = chi ⁻¹' {0} := rfl
    rw [hpre]
    exact hcont.isOpen_preimage _ (isOpen_discrete _)
  have hHclosed : IsClosed (H : Set (GalGroup F)) := Subgroup.isClosed_of_isOpen H hHopen
  have hfixsub : (IntermediateField.fixedField H).fixingSubgroup = H :=
    InfiniteGalois.fixingSubgroup_fixedField
      (⟨H, hHclosed⟩ : ClosedSubgroup (GalGroup F))
  have hs0H : s0 ∉ H := by
    rw [hH, mem_charKernel, hs0]
    decide
  obtain ⟨x, hxL, hxne⟩ : ∃ x ∈ IntermediateField.fixedField H, s0 x ≠ x := by
    by_contra hcon
    push_neg at hcon
    exact hs0H (hfixsub ▸ (IntermediateField.mem_fixingSubgroup_iff _ s0).2 hcon)
  set y : SeparableClosure F := x - s0 x with hy
  have hyne : y ≠ 0 := sub_ne_zero.2 (fun h => hxne h.symm)
  -- every element of `H` fixes `y`
  have hHy : ∀ h ∈ H, h y = y := by
    intro h hh
    have hx' : h x = x := (IntermediateField.mem_fixedField_iff _ x).1 hxL h hh
    have hconj : s0⁻¹ * h * s0 ∈ H := by
      rw [hH, mem_charKernel] at hh ⊢
      have h1 := hhom (s0⁻¹ * h) s0
      have h2 := hhom s0⁻¹ h
      have h3 := hhom s0 s0⁻¹
      rw [mul_inv_cancel] at h3
      have h4 : chi 1 = 0 := by
        have h5 := hhom 1 1
        rw [mul_one] at h5
        exact (left_eq_add.mp h5)
      rw [h4] at h3
      have hinv : chi s0⁻¹ = 1 := by
        rw [hs0] at h3
        revert h3
        generalize chi s0⁻¹ = u
        revert u
        decide
      rw [h1, h2, hh, hinv, hs0]
      decide
    have hs0x : h (s0 x) = s0 x := by
      have heq : h * s0 = s0 * (s0⁻¹ * h * s0) := by group
      calc h (s0 x) = (h * s0) x := (AlgEquiv.mul_apply h s0 x).symm
        _ = (s0 * (s0⁻¹ * h * s0)) x := by rw [heq]
        _ = s0 ((s0⁻¹ * h * s0) x) := AlgEquiv.mul_apply _ _ _
        _ = s0 x := by
            rw [(IntermediateField.mem_fixedField_iff _ x).1 hxL _ hconj]
    rw [hy, map_sub, hx', hs0x]
  -- `s0` negates `y`
  have hs0sq : s0 * s0 ∈ H := by
    rw [hH, mem_charKernel, hhom, hs0]
    decide
  have hs0y : s0 y = -y := by
    have h1 : s0 (s0 x) = x := by
      have := (IntermediateField.mem_fixedField_iff _ x).1 hxL _ hs0sq
      simpa [AlgEquiv.mul_apply] using this
    rw [hy, map_sub, h1]
    ring
  -- elements outside `H` negate `y`
  have hout : ∀ τ : GalGroup F, τ ∉ H → τ y = -y := by
    intro τ hτ
    have hτ1 : chi τ = 1 := zmod_two_eq_one_of_ne_zero (by simpa [hH] using hτ)
    have hmem : s0⁻¹ * τ ∈ H := by
      rw [hH, mem_charKernel, hhom]
      have h3 := hhom s0 s0⁻¹
      rw [mul_inv_cancel] at h3
      have h4 : chi 1 = 0 := by
        have h5 := hhom 1 1
        rw [mul_one] at h5
        exact (left_eq_add.mp h5)
      rw [h4] at h3
      have hinv : chi s0⁻¹ = 1 := by
        rw [hs0] at h3
        revert h3
        generalize chi s0⁻¹ = u
        revert u
        decide
      rw [hinv, hτ1]
      decide
    have heq : s0 * (s0⁻¹ * τ) = τ := by group
    calc τ y = (s0 * (s0⁻¹ * τ)) y := by rw [heq]
      _ = s0 ((s0⁻¹ * τ) y) := AlgEquiv.mul_apply _ _ _
      _ = s0 y := by rw [hHy _ hmem]
      _ = -y := hs0y
  -- `y ^ 2` lies in `F`
  have hyfix : ∀ τ : GalGroup F, τ (y * y) = y * y := by
    intro τ
    by_cases hτ : τ ∈ H
    · rw [map_mul, hHy τ hτ]
    · rw [map_mul, hout τ hτ]
      ring
  obtain ⟨c, hc⟩ : y * y ∈ Set.range (algebraMap F (SeparableClosure F)) :=
    (InfiniteGalois.mem_range_algebraMap_iff_fixed _).2 hyfix
  have hcne : c ≠ 0 := by
    intro hz
    rw [hz, map_zero] at hc
    exact (mul_ne_zero hyne hyne) hc.symm
  refine ⟨Units.mk0 c hcne, ?_⟩
  set a : Fˣ := Units.mk0 c hcne with ha
  have hasq : (sqrtIn a : SeparableClosure F) ^ 2 = y * y := by
    rw [sqrtIn_sq hF, ha]
    simpa using hc
  have halpha : (sqrtIn a : SeparableClosure F) = y ∨ sqrtIn a = -y := by
    have h2 : (sqrtIn a - y) * (sqrtIn a + y) = (0 : SeparableClosure F) := by
      linear_combination hasq
    rcases mul_eq_zero.1 h2 with h | h
    · exact Or.inl (sub_eq_zero.1 h)
    · exact Or.inr (eq_neg_of_add_eq_zero_left h)
  funext τ
  refine zmod_two_eq_of_iff ?_
  rw [kummerChar_eq_zero_iff]
  constructor
  · intro hfix
    by_contra hτ
    have hτH : τ ∉ H := by simpa [hH] using hτ
    have hneg : τ y = -y := hout τ hτH
    have : τ y = y := by
      rcases halpha with h | h
      · rwa [h] at hfix
      · rw [h, map_neg, neg_inj] at hfix
        exact hfix
    rw [hneg] at this
    exact neg_ne_self hF hyne this
  · intro hτ
    have hτH : τ ∈ H := by simpa [hH] using hτ
    have hyy : τ y = y := hHy τ hτH
    rcases halpha with h | h
    · rw [h]; exact hyy
    · rw [h, map_neg, hyy]

end Frontier

import Mathlib
import RequestProject.Frontier.ContinuousCohomology
import RequestProject.Frontier.MilnorK
import RequestProject.Frontier.Kummer

/-!
# Voevodsky Milnor
Category: Frontier — Fields Medal Work
Target: Frontier.voevodsky_milnor
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The Milnor conjecture

The Milnor conjecture, proved by Voevodsky, states that for a field `F` of characteristic
`≠ 2` the norm residue homomorphism

`K^M_n(F)/2 ⟶ Hⁿ(Gal(F^sep/F), ℤ/2)`,   `{a₁,…,aₙ} ↦ χ_{a₁} ∪ ⋯ ∪ χ_{aₙ}`

is an isomorphism for every `n`.  Here `K^M_*(F)/2` is mod-2 Milnor K-theory
(`Frontier.KMilnorMod2`) and `Hⁿ(-, ℤ/2)` is continuous (Galois) cochain cohomology
(`Frontier.contCohomology`).

This file formalises the statement, and proves it in the degrees where it does not
require Voevodsky's machinery:

* degree `0`: both sides are canonically `ℤ/2` (`Frontier.normResidueZeroEquiv`);
* degree `1`: this is Kummer theory; the norm residue map `a ↦ (σ ↦ σ(√a)/√a)` is
  constructed in `Frontier.normResidueOne` and proved bijective.

A (weak, group-theoretic) form of the general statement, which is Voevodsky's theorem, is
recorded as `Frontier.MilnorConjecture`; it is *not* proved here.

## Mathlib inputs

Mathlib contains neither Milnor K-theory nor Galois cohomology, so both sides of the norm
residue map are constructed here.  The main Mathlib results used are:
`groupCohomology.inhomogeneousCochains.d_comp_d` (the cochain differential squares to zero),
`IsSepClosed.exists_pow_nat_eq` (square roots exist in a separably closed field),
`IntermediateField.fixingSubgroup_isOpen` (openness in the Krull topology),
`InfiniteGalois.fixingSubgroup_fixedField` and `InfiniteGalois.mem_range_algebraMap_iff_fixed`
(the infinite Galois correspondence).
-/

set_option synthInstance.maxHeartbeats 1000000
set_option maxHeartbeats 1000000

namespace Frontier

variable {F : Type} [Field F]

attribute [local instance] Classical.propDecidable

/-- The degree-one norm residue map on the free module of degree-one symbols:
`a ↦ (σ ↦ σ(√a)/√a)`, with values in the continuous characters of `Gal(F^sep/F)`. -/
