import Mathlib

/-!
# Arithmetic core for the freeness of two rotations of `SO(3)`

We consider the two rotations of `ℝ³`

```
σ = 1/3 * ![![1, -2√2, 0], ![2√2, 1, 0], ![0,0,3]]      (rotation about the z-axis)
τ = 1/3 * ![![3, 0, 0], ![0, 1, -2√2], ![0, 2√2, 1]]    (rotation about the x-axis)
```

both by the angle `arccos (1/3)`.  Applying a word of length `n` in `σ^{±1}, τ^{±1}` to the
vector `(1, 0, 1)` produces a vector of the form `3⁻ⁿ • (a, b√2, c)` with `a b c : ℤ`.
This file contains the purely arithmetic heart of the matter: for a nonempty *reduced* word,
the middle coordinate `b` is not divisible by `3`; in particular it is nonzero.
-/

namespace BanachTarski

/-- A letter: the first component selects the generator (`false` = `σ`, `true` = `τ`),
the second component is the sign of the exponent (`true` = `+1`). -/
abbrev Ltr := Bool × Bool

/-- The action of a letter on the integer triple `(a, b, c)` representing the vector
`3⁻ⁿ • (a, b√2, c)`; the factor `3⁻¹` is not recorded here. -/

def EqDecomp (G : Subgroup (Equiv.Perm X)) (A B : Set X) : Prop :=
  ∃ (ι : Type) (_ : Finite ι) (P : ι → Set X) (g : ι → Equiv.Perm X),
    (∀ i, g i ∈ G) ∧
    Pairwise (Disjoint on P) ∧ (⋃ i, P i) = A ∧
    Pairwise (Disjoint on fun i => g i '' P i) ∧ (⋃ i, g i '' P i) = B

/-- A set `E` is `G`-paradoxical if it has two disjoint subsets each equidecomposable to `E`. -/

def Paradoxical (G : Subgroup (Equiv.Perm X)) (E : Set X) : Prop :=
  ∃ A B : Set X, A ⊆ E ∧ B ⊆ E ∧ Disjoint A B ∧ EqDecomp G A E ∧ EqDecomp G B E

namespace EqDecomp

variable {G H : Subgroup (Equiv.Perm X)} {A B C : Set X}

theorem mono (h : G ≤ H) (hAB : EqDecomp G A B) : EqDecomp H A B := by
  obtain ⟨ι, hι, P, g, hg, h1, h2, h3, h4⟩ := hAB
  exact ⟨ι, hι, P, g, fun i => h (hg i), h1, h2, h3, h4⟩

theorem symm (hAB : EqDecomp G A B) : EqDecomp G B A := by
  obtain ⟨ι, hι, P, g, hg, h1, h2, h3, h4⟩ := hAB
  refine ⟨ι, hι, fun i => g i '' P i, fun i => (g i)⁻¹, fun i => inv_mem (hg i), h3, h4, ?_, ?_⟩
  · intro i j hij
    have : ∀ k, (g k)⁻¹ '' (g k '' P k) = P k := by
      intro k
      rw [← Set.image_comp]
      simp
    simpa [Function.onFun, this] using h1 hij
  · have : ∀ k, (g k)⁻¹ '' (g k '' P k) = P k := by
      intro k
      rw [← Set.image_comp]
      simp
    simpa [this] using h2

theorem trans (hAB : EqDecomp G A B) (hBC : EqDecomp G B C) : EqDecomp G A C := by
  obtain ⟨ι, hι, P, g, hg, hP, hPA, hgP, hgPB⟩ := hAB
  obtain ⟨κ, hκ, Q, h, hh, hQ, hQB, hhQ, hhQC⟩ := hBC
  refine ⟨ι × κ, inferInstance, fun p => P p.1 ∩ (g p.1) ⁻¹' Q p.2,
    fun p => h p.2 * g p.1, fun p => mul_mem (hh p.2) (hg p.1), ?_, ?_, ?_, ?_⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    simp only [Function.onFun]
    by_cases hi : i = i'
    · subst hi
      have hjj : j ≠ j' := by
        intro hj; exact hne (by simp [hj])
      have := hQ hjj
      simp only [Function.onFun] at this
      apply Disjoint.mono inter_subset_right inter_subset_right
      exact Set.disjoint_preimage _ this
    · exact Disjoint.mono inter_subset_left inter_subset_left (hP hi)
  · rw [← hPA]
    apply Set.Subset.antisymm
    · exact iUnion_subset fun p => (inter_subset_left).trans (subset_iUnion _ p.1)
    · refine iUnion_subset fun i => ?_
      intro x hx
      have hgx : g i x ∈ B := by
        rw [← hgPB]
        exact mem_iUnion.2 ⟨i, ⟨x, hx, rfl⟩⟩
      rw [← hQB] at hgx
      obtain ⟨_, ⟨j, rfl⟩, hj⟩ := hgx
      exact mem_iUnion.2 ⟨(i, j), hx, hj⟩
  · rintro ⟨i, j⟩ ⟨i', j'⟩ hne
    simp only [Function.onFun]
    have himg : ∀ (i : ι) (j : κ), (h j * g i) '' (P i ∩ (g i) ⁻¹' Q j)
        = h j '' ((g i '' P i) ∩ Q j) := by
      intro i j
      rw [Equiv.Perm.coe_mul, Set.image_comp]
      congr 1
      rw [Set.image_inter (g i).injective, Set.image_preimage_eq _ (g i).surjective]
    rw [himg, himg]
    by_cases hj : j = j'
    · subst hj
      have hii : i ≠ i' := by
        intro hi; exact hne (by simp [hi])
      apply Set.disjoint_image_of_injective (h j).injective
      have := hgP hii
      simp only [Function.onFun] at this
      exact Disjoint.mono inter_subset_left inter_subset_left this
    · have := hhQ hj
      simp only [Function.onFun] at this
      exact Disjoint.mono (Set.image_mono inter_subset_right)
        (Set.image_mono inter_subset_right) this
  · have himg : ∀ (i : ι) (j : κ), (h j * g i) '' (P i ∩ (g i) ⁻¹' Q j)
        = h j '' ((g i '' P i) ∩ Q j) := by
      intro i j
      rw [Equiv.Perm.coe_mul, Set.image_comp]
      congr 1
      rw [Set.image_inter (g i).injective, Set.image_preimage_eq _ (g i).surjective]
    rw [← hhQC]
    apply Set.Subset.antisymm
    · refine iUnion_subset fun p => ?_
      rw [himg]
      exact (Set.image_mono inter_subset_right).trans (subset_iUnion _ p.2)
    · refine iUnion_subset fun j => ?_
      rintro _ ⟨y, hy, rfl⟩
      have hyB : y ∈ B := by rw [← hQB]; exact mem_iUnion.2 ⟨j, hy⟩
      rw [← hgPB] at hyB
      obtain ⟨_, ⟨i, rfl⟩, hi⟩ := hyB
      refine mem_iUnion.2 ⟨(i, j), ?_⟩
      rw [himg]
      exact ⟨y, ⟨hi, hy⟩, rfl⟩

/-- Equidecomposability of unions of two disjoint pairs of sets. -/

theorem congr {A' B' : Set X} (h : EqDecomp G A B) (hA : A = A') (hB : B = B') :
    EqDecomp G A' B' := hA ▸ hB ▸ h

end EqDecomp

/-- Transport a paradoxical decomposition along an equidecomposability. -/

theorem Paradoxical.of_eqDecomp {G : Subgroup (Equiv.Perm X)} {E F : Set X}
    (hE : Paradoxical G E) (hEF : EqDecomp G E F) : Paradoxical G F := by
  obtain ⟨A, B, hA, hB, hAB, hAE, hBE⟩ := hE
  obtain ⟨ι, hι, P, g, hg, hP, hPE, hgP, hgPF⟩ := hEF
  -- the bijection given by `hEF` maps `A` and `B` to disjoint subsets of `F`
  classical
  set f : X → X := fun x => if h : ∃ i, x ∈ P i then g h.choose x else x with hf
  have hfmem : ∀ (S : Set X), S ⊆ E → EqDecomp G S (f '' S) := by
    intro S hS
    refine ⟨ι, hι, fun i => P i ∩ S, g, hg, ?_, ?_, ?_, ?_⟩
    · intro i j hij
      exact Disjoint.mono inter_subset_left inter_subset_left (hP hij)
    · rw [← Set.iUnion_inter, hPE, Set.inter_eq_right.2 hS]
    · intro i j hij
      exact Disjoint.mono (Set.image_mono inter_subset_left) (Set.image_mono inter_subset_left)
        (hgP hij)
    · apply Set.Subset.antisymm
      · rintro x hx
        obtain ⟨_, ⟨i, rfl⟩, y, ⟨hyP, hyS⟩, rfl⟩ := hx
        refine ⟨y, hyS, ?_⟩
        have hex : ∃ i, y ∈ P i := ⟨i, hyP⟩
        simp only [hf, dif_pos hex]
        have : hex.choose = i := by
          by_contra hne
          exact (hP hne).le_bot ⟨hex.choose_spec, hyP⟩
        rw [this]
      · rintro _ ⟨y, hyS, rfl⟩
        have hex : ∃ i, y ∈ P i := by
          have : y ∈ E := hS hyS
          rw [← hPE] at this
          exact mem_iUnion.1 this
        simp only [hf, dif_pos hex]
        exact mem_iUnion.2 ⟨hex.choose, ⟨y, ⟨hex.choose_spec, hyS⟩, rfl⟩⟩
  have hinj : Set.InjOn f E := by
    intro x hx y hy hxy
    have hex : ∃ i, x ∈ P i := by rw [← hPE] at hx; exact mem_iUnion.1 hx
    have hey : ∃ i, y ∈ P i := by rw [← hPE] at hy; exact mem_iUnion.1 hy
    simp only [hf, dif_pos hex, dif_pos hey] at hxy
    by_cases hij : hex.choose = hey.choose
    · rw [hij] at hxy
      exact (g hey.choose).injective hxy
    · exfalso
      have h1 : g hex.choose x ∈ g hex.choose '' P hex.choose := ⟨x, hex.choose_spec, rfl⟩
      have h2 : g hey.choose y ∈ g hey.choose '' P hey.choose := ⟨y, hey.choose_spec, rfl⟩
      rw [hxy] at h1
      exact (hgP hij).le_bot ⟨h1, h2⟩
  refine ⟨f '' A, f '' B, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hgPF]
    have := hfmem A hA
    obtain ⟨-, -, -, -, -, -, -, -, hUnion⟩ := this
    rw [← hUnion]
    exact iUnion_mono fun i => Set.image_mono inter_subset_left
  · rw [← hgPF]
    have := hfmem B hB
    obtain ⟨-, -, -, -, -, -, -, -, hUnion⟩ := this
    rw [← hUnion]
    exact iUnion_mono fun i => Set.image_mono inter_subset_left
  · rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [mem_inter_iff, mem_image, mem_empty_iff_false, iff_false]
    rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, hba⟩⟩
    have := hinj (hB hb) (hA ha) hba
    subst this
    exact hAB.le_bot ⟨ha, hb⟩
  · exact ((hfmem A hA).symm.trans hAE).trans hEF
  · exact ((hfmem B hB).symm.trans hBE).trans hEF

end BanachTarski

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
