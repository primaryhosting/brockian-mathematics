import Mathlib

/-!
# Abstract machinery for paradoxical decompositions

This file develops the general theory needed for the Banach–Tarski paradox, on top of
Mathlib's `Equidecomp` (equidecompositions for a group action).
-/

open Set Function Pointwise

namespace BT

variable {X G H : Type*} [Nonempty X] [Group G] [MulAction G X]

/-- Build an equidecomposition out of a function which is a bijection from `A` to `B` and
moves every point of `A` by an element of a fixed finite set of group elements. -/

theorem paradoxical_of_free (φ : FreeGroup (Fin 2) →* G) (A : Set X)
    (hinv : ∀ w : FreeGroup (Fin 2), (φ w) • A ⊆ A)
    (hfree : ∀ x ∈ A, ∀ w : FreeGroup (Fin 2), (φ w) • x = x → w = 1) :
    Paradoxical G A := by
  classical
  have hmem : ∀ (w : FreeGroup (Fin 2)) (x : X), x ∈ A → φ w • x ∈ A :=
    fun w x hx => hinv w ⟨x, hx, rfl⟩
  let s : Setoid X := ⟨fun x y => ∃ w : FreeGroup (Fin 2), φ w • x = y,
    ⟨fun x => ⟨1, by simp⟩,
     fun ⟨w, hw⟩ => ⟨w⁻¹, by rw [← hw, ← mul_smul, ← map_mul]; simp⟩,
     fun ⟨w, hw⟩ ⟨v, hv⟩ => ⟨v * w, by rw [map_mul, mul_smul, hw, hv]⟩⟩⟩
  set rep : X → X := fun x => (Quotient.mk s x).out with hrepdef
  have hrep : ∀ x : X, ∃ w : FreeGroup (Fin 2), φ w • rep x = x :=
    fun x => Quotient.mk_out (s := s) x
  have hrep_eq : ∀ x y : X, (∃ w : FreeGroup (Fin 2), φ w • x = y) → rep x = rep y := by
    intro x y h
    have hq : Quotient.mk s x = Quotient.mk s y := Quotient.sound h
    rw [hrepdef]; simp only [hq]
  set ω : X → FreeGroup (Fin 2) := fun x => (hrep x).choose with hωdef
  have hω : ∀ x, φ (ω x) • rep x = x := fun x => (hrep x).choose_spec
  have hrepA : ∀ x ∈ A, rep x ∈ A := by
    intro x hx
    have h1 : φ ((ω x)⁻¹) • x = rep x := by
      rw [map_inv, inv_smul_eq_iff]; exact (hω x).symm
    rw [← h1]
    exact hmem _ _ hx
  have huniq : ∀ x ∈ A, ∀ w, φ w • rep x = x → w = ω x := by
    intro x hx w hw
    have h1 : φ ((ω x)⁻¹ * w) • rep x = rep x := by
      rw [map_mul, mul_smul, hw, map_inv, inv_smul_eq_iff]
      exact (hω x).symm
    exact (inv_mul_eq_one.mp (hfree _ (hrepA x hx) _ h1)).symm
  have hequiv : ∀ x ∈ A, ∀ u : FreeGroup (Fin 2), ω (φ u • x) = u * ω x := by
    intro x hx u
    have h1 : rep (φ u • x) = rep x := (hrep_eq x (φ u • x) ⟨u, rfl⟩).symm
    refine (huniq _ (hmem u x hx) (u * ω x) ?_).symm
    rw [h1, map_mul, mul_smul, hω x]
  -- the four pieces
  set S : Fin 2 × Bool → Set X := fun v => {x | x ∈ A ∧ ω x ∈ FreeGroup.startsWith v} with hSdef
  have hSA : ∀ v, S v ⊆ A := fun v x hx => hx.1
  have main : ∀ i : Fin 2, ∃ f : Equidecomp X G,
      f.source = S (i, true) ∪ S (i, false) ∧ f.target = A := by
    intro i
    set a : FreeGroup (Fin 2) := FreeGroup.of i with hadef
    have hne : ∀ g : FreeGroup (Fin 2), g ∈ FreeGroup.startsWith (i, false) →
        g ∉ FreeGroup.startsWith (i, true) := by
      intro g hg hg'
      exact (FreeGroup.startsWith.disjoint_iff_ne.mpr (by simp)).notMem_of_mem_left hg hg'
    refine ⟨mkEquidecomp
      (fun x => if ω x ∈ FreeGroup.startsWith (i, false) then φ a • x else x)
      (S (i, true) ∪ S (i, false)) A {1, φ a} ?_ ?_, rfl, rfl⟩
    · intro x _
      by_cases h : ω x ∈ FreeGroup.startsWith (i, false)
      · exact ⟨φ a, by simp, by simp [h]⟩
      · exact ⟨1, by simp, by simp [h]⟩
    · have hsrcA : S (i, true) ∪ S (i, false) ⊆ A := union_subset (hSA _) (hSA _)
      refine ⟨?_, ?_, ?_⟩
      · intro x hx
        by_cases h : ω x ∈ FreeGroup.startsWith (i, false)
        · simpa [h] using hmem a x (hsrcA hx)
        · simpa [h] using hsrcA hx
      · intro x hx y hy hxy
        by_cases hx' : ω x ∈ FreeGroup.startsWith (i, false) <;>
          by_cases hy' : ω y ∈ FreeGroup.startsWith (i, false) <;>
          simp only [hx', hy', if_true, if_false] at hxy
        · exact MulAction.injective (φ a) hxy
        · exfalso
          have hyt : ω y ∈ FreeGroup.startsWith (i, true) :=
            (hy.resolve_right (fun hc => hy' hc.2)).2
          have : ω y = a * ω x := by rw [← hxy]; exact hequiv x (hsrcA hx) a
          exact mul_notMem_startsWith hx' (this ▸ hyt)
        · exfalso
          have hxt : ω x ∈ FreeGroup.startsWith (i, true) :=
            (hx.resolve_right (fun hc => hx' hc.2)).2
          have : ω x = a * ω y := by rw [hxy]; exact hequiv y (hsrcA hy) a
          exact mul_notMem_startsWith hy' (this ▸ hxt)
        · exact hxy
      · intro y hy
        by_cases h : ω y ∈ FreeGroup.startsWith (i, true)
        · refine ⟨y, Or.inl ⟨hy, h⟩, ?_⟩
          have hnot : ω y ∉ FreeGroup.startsWith (i, false) := fun hc => hne _ hc h
          simp [hnot]
        · refine ⟨φ a⁻¹ • y, Or.inr ⟨hmem _ _ hy, ?_⟩, ?_⟩
          · rw [hequiv y hy a⁻¹]
            exact inv_mul_mem_startsWith h
          · have hmem' : ω (φ a⁻¹ • y) ∈ FreeGroup.startsWith (i, false) := by
              rw [hequiv y hy a⁻¹]; exact inv_mul_mem_startsWith h
            simp only [hmem', if_true]
            rw [← mul_smul, ← map_mul, mul_inv_cancel, map_one, one_smul]
  obtain ⟨f, hf1, hf2⟩ := main 0
  obtain ⟨g, hg1, hg2⟩ := main 1
  refine ⟨f, g, by rw [hf1]; exact union_subset (hSA _) (hSA _),
    by rw [hg1]; exact union_subset (hSA _) (hSA _), ?_, hf2, hg2⟩
  rw [hf1, hg1]
  simp only [Set.disjoint_left, mem_union]
  rintro x (hx | hx) (hy | hy) <;>
    exact (FreeGroup.startsWith.disjoint_iff_ne.mpr (by simp)).notMem_of_mem_left hx.2 hy.2

end BT

import RequestProject.Abstract
import RequestProject.Space

/-!
# Radial extension

A paradoxical decomposition of a subset of the unit sphere extends radially to a paradoxical
decomposition of the corresponding punctured cone in the unit ball.
-/

open Matrix Set Function

namespace BT

/-- The unit sphere of `ℝ³`. -/
