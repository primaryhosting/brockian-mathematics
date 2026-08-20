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

/-!
# Sperner's lemma

Every Sperner colouring of a triangulated simplex has an odd number of rainbow cells.
-/

namespace Math

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- The number of cells of `T` containing the face `F`. -/

theorem isSpernerTriangulation_std (N : ℕ) (k : ℕ) (hk : k ≤ N) :
    IsSpernerTriangulation (V := Fin (N + 1)) (fun i => (i : ℕ)) (fun i => {(i : ℕ)}) k
      {stdFace N k} := by
  induction k with
  | zero =>
      refine ⟨0, ?_, rfl⟩
      congr 1
      ext i
      simp only [stdFace, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton,
        Fin.ext_iff, Fin.val_zero]
      omega
  | succ k ih =>
      have hk' : k ≤ N := by omega
      refine ⟨?_, ?_, ?_, ?_⟩
      · intro σ hσ
        rw [Finset.mem_singleton] at hσ
        subst hσ
        exact card_stdFace N (k + 1) hk
      · intro σ hσ v hv
        rw [Finset.mem_singleton] at hσ
        subst hσ
        rw [mem_stdFace] at hv
        refine ⟨Finset.mem_singleton_self _, ?_⟩
        rw [Finset.singleton_subset_iff, Finset.mem_range]
        omega
      · intro F hF hcard _
        obtain ⟨σ, hσ, hFσ⟩ := hF
        rw [Finset.mem_singleton] at hσ
        subst hσ
        have hns : ¬ stdFace N (k + 1) ⊆ F := by
          intro hsub
          have h1 := Finset.card_le_card hsub
          rw [card_stdFace N (k + 1) hk, hcard] at h1
          omega
        obtain ⟨j, hj, hjF⟩ := Finset.not_subset.1 hns
        refine ⟨(j : ℕ), mem_stdFace.1 hj, ?_⟩
        intro v hv hmem
        rw [Finset.mem_singleton] at hmem
        exact hjF (by rwa [Fin.ext hmem.symm] at hv)
      · have hbd : bdry (fun i : Fin (N + 1) => ({(i : ℕ)} : Finset ℕ)) k {stdFace N (k + 1)}
            = {stdFace N k} := by
          ext F
          simp only [bdry, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton]
          constructor
          · rintro ⟨hcard, hcar, -⟩
            have hsub : F ⊆ stdFace N k := by
              intro v hv
              have h1 := hcar v hv
              rw [Finset.singleton_subset_iff, Finset.mem_range] at h1
              exact mem_stdFace.2 h1
            exact Finset.eq_of_subset_of_card_le hsub (by rw [card_stdFace N k hk', hcard])
          · rintro rfl
            refine ⟨card_stdFace N k hk', ?_, ?_⟩
            · intro v hv
              rw [mem_stdFace] at hv
              rw [Finset.singleton_subset_iff, Finset.mem_range]
              omega
            · have h1 : cellMult {stdFace N (k + 1)} (stdFace N k) = 1 := by
                unfold cellMult
                rw [Finset.filter_singleton, if_pos (stdFace_mono N k)]
                simp
              rw [h1]
              exact odd_one
        rw [hbd]
        exact ih hk'

/-- A segment `A B` coloured `0, 1`, subdivided by a midpoint coloured `0`. -/
