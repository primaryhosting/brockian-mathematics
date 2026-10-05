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
# AKS core: the introspective-numbers argument

This file contains the mathematical heart of the Agrawal–Kayal–Saxena primality test.
-/

namespace AKS

open Polynomial

section Introspective

variable {p : ℕ} [hp : Fact p.Prime]

/-- `m` is *introspective* for the polynomial `f` (with respect to `r`-th roots of unity in the
field `F` of characteristic `p`) if `f(y)^m = f(y^m)` for every `r`-th root of unity `y ∈ F`. -/

lemma finset_eq_of_prod_eq {A : Finset ℕ} {t : ℕ} {I : Set ℕ} {T : Finset F}
    (hζ : ζ ^ r = 1)
    (hcard : A.card < t)
    (hinj : ∀ a ∈ A, ∀ b ∈ A, (a : ZMod p) = (b : ZMod p) → a = b)
    (hI : ∀ m ∈ I, ∀ a ∈ A, Introspective F r m (X + C (a : ZMod p)))
    (hT : t ≤ T.card) (hTI : ∀ y ∈ T, ∃ m ∈ I, y = ζ ^ m)
    {S₁ S₂ : Finset ℕ} (h₁ : S₁ ⊆ A) (h₂ : S₂ ⊆ A)
    (heq : (∏ a ∈ S₁, (ζ + (a : F))) = ∏ a ∈ S₂, (ζ + (a : F))) : S₁ = S₂ := by
  classical
  set f₁ : (ZMod p)[X] := ∏ a ∈ S₁, (X + C (a : ZMod p)) with hf₁
  set f₂ : (ZMod p)[X] := ∏ a ∈ S₂, (X + C (a : ZMod p)) with hf₂
  have haeval : ∀ (S : Finset ℕ) (y : F),
      aeval y (∏ a ∈ S, (X + C (a : ZMod p))) = ∏ a ∈ S, (y + (a : F)) := by
    intro S y
    rw [map_prod]
    refine Finset.prod_congr rfl fun a _ => ?_
    simp [map_natCast]
  have hintro : ∀ m ∈ I, ∀ (S : Finset ℕ), S ⊆ A →
      Introspective F r m (∏ a ∈ S, (X + C (a : ZMod p))) := by
    intro m hm S hS
    exact Introspective.prod S _ fun a ha => hI m hm a (hS ha)
  have hbase : aeval ζ f₁ = aeval ζ f₂ := by
    rw [hf₁, hf₂, haeval S₁ ζ, haeval S₂ ζ]; exact heq
  have hroots : ∀ y ∈ T, aeval y f₁ = aeval y f₂ := by
    intro y hy
    obtain ⟨m, hm, rfl⟩ := hTI y hy
    rw [← (hintro m hm S₁ h₁) ζ hζ, ← (hintro m hm S₂ h₂) ζ hζ, ← hf₁, ← hf₂, hbase]
  have hpoly : f₁ = f₂ := by
    by_contra hne
    have hd : f₁ - f₂ ≠ 0 := sub_ne_zero.mpr hne
    set g : F[X] := (f₁ - f₂).map (algebraMap (ZMod p) F) with hg
    have hg0 : g ≠ 0 := by
      rw [hg]
      exact (Polynomial.map_ne_zero_iff (FaithfulSMul.algebraMap_injective (ZMod p) F)).mpr hd
    have hsub : T.val ⊆ g.roots := by
      intro y hy
      have hyT : y ∈ T := hy
      rw [Polynomial.mem_roots hg0, Polynomial.IsRoot, hg, Polynomial.eval_map,
        ← Polynomial.aeval_def, map_sub, hroots y hyT, sub_self]
    have h1 : T.card ≤ g.natDegree := Polynomial.card_le_degree_of_subset_roots hsub
    have h2 : g.natDegree ≤ (f₁ - f₂).natDegree := Polynomial.natDegree_map_le
    have h3 : (f₁ - f₂).natDegree < t := by
      refine lt_of_le_of_lt (le_trans (Polynomial.natDegree_sub_le _ _) ?_) hcard
      apply max_le
      · exact le_trans (by rw [hf₁]; exact natDegree_prod_X_add_C_le S₁) (Finset.card_le_card h₁)
      · exact le_trans (by rw [hf₂]; exact natDegree_prod_X_add_C_le S₂) (Finset.card_le_card h₂)
    omega
  exact finset_eq_of_prod_X_add_C_eq hinj h₁ h₂ hpoly

omit [Algebra (ZMod p) F] [CharP F p] hp in
/-- A finset all of whose elements satisfy `x ^ m₁ = x ^ m₂` (with `m₂ < m₁`) has at most `m₁`
elements. -/
