import Mathlib

/-!
# Auxiliary lemmas

Small facts about lists, about `x ^ (q-1)` in characteristic `q`, and a counting lemma about
subsets with a prescribed weight modulo `q`.
-/

namespace CS

open Finset

/-! ### Lists indexed by `Fin l.length` -/


theorem popCount_ext {n : ℕ} (a : ℕ) (x : Cube n) :
    popCount (n + a) (ext (fun i => decide (i < n + a)) x) = wt x + a := by
  classical
  unfold popCount
  have hsplit : Finset.range (n + a) = Finset.range n ∪ Finset.Ico n (n + a) := by
    simp only [Finset.range_eq_Ico]
    exact (Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)).symm
  have hdisj : Disjoint ((Finset.range n).filter
      (fun i => ext (fun i => decide (i < n + a)) x i = true))
      ((Finset.Ico n (n + a)).filter (fun i => ext (fun i => decide (i < n + a)) x i = true)) := by
    refine Finset.disjoint_left.2 fun i hi hi' => ?_
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico] at hi hi'
    omega
  rw [hsplit, Finset.filter_union, Finset.card_union_of_disjoint hdisj]
  have h2 : (Finset.Ico n (n + a)).filter
      (fun i => ext (fun i => decide (i < n + a)) x i = true) = Finset.Ico n (n + a) := by
    refine Finset.filter_true_of_mem fun i hi => ?_
    simp only [Finset.mem_Ico] at hi
    have : ¬ (i < n) := by omega
    simp [ext, this]
    omega
  have h1 : (Finset.range n).filter (fun i => ext (fun i => decide (i < n + a)) x i = true)
      = Finset.image (Fin.val) (univ.filter (fun j : Fin n => x j = true)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨hi, h⟩
      refine ⟨⟨i, hi⟩, ?_, rfl⟩
      simpa [ext, hi] using h
    · rintro ⟨j, hj, rfl⟩
      exact ⟨j.2, by simpa [ext, j.2] using hj⟩
  rw [h1, h2, Finset.card_image_of_injective _ Fin.val_injective, Nat.card_Ico]
  simp [wt]

/-! ### The full product of `ζ ^ (x i)` -/

variable {F : Type*} [Field F]

