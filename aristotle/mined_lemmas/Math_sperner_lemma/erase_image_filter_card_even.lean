import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math

/-! ## Auxiliary counting lemmas -/

/-- Parity translated into `ZMod 2`. -/

lemma erase_image_filter_card_even {V α : Type*} [DecidableEq V] [DecidableEq α]
    (σ : Finset V) (f : V → α) (J : Finset α) (i₀ : α) (hi₀ : i₀ ∈ J)
    (hcard : σ.card = J.card) (hsub : σ.image f ⊆ J) (hne : σ.image f ≠ J) :
    Even (σ.filter (fun v => (σ.erase v).image f = J.erase i₀)).card := by
  classical
  by_cases hcase : σ.image f = J.erase i₀
  · have hJc : J.card = (J.erase i₀).card + 1 := by
      rw [Finset.card_erase_of_mem hi₀]
      have := Finset.card_pos.mpr ⟨i₀, hi₀⟩
      omega
    obtain ⟨j₀, hj₀J, hj₀card, hother⟩ :=
      fiber_structure σ f (J.erase i₀) hcase (by rw [hcard, hJc])
    have hset : σ.filter (fun v => (σ.erase v).image f = J.erase i₀)
        = σ.filter (fun v => f v = j₀) := by
      apply Finset.filter_congr
      intro v hv
      constructor
      · intro h
        by_contra hvj
        have hfv : f v ∈ J.erase i₀ := by rw [← hcase]; exact Finset.mem_image_of_mem f hv
        have h1 := hother (f v) hfv hvj
        obtain ⟨a, ha⟩ := Finset.card_eq_one.mp h1
        have hva : v ∈ σ.filter (fun w => f w = f v) := Finset.mem_filter.mpr ⟨hv, rfl⟩
        rw [ha, Finset.mem_singleton] at hva
        have hfv2 : f v ∈ (σ.erase v).image f := by rw [h]; exact hfv
        obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hfv2
        obtain ⟨hwv, hwσ⟩ := Finset.mem_erase.mp hw
        have hwa : w ∈ σ.filter (fun u => f u = f v) := Finset.mem_filter.mpr ⟨hwσ, hfw⟩
        rw [ha, Finset.mem_singleton] at hwa
        exact hwv (hwa.trans hva.symm)
      · intro h
        obtain ⟨w, hwf, hwv⟩ := Finset.exists_mem_ne (s := σ.filter (fun w => f w = j₀))
          (by rw [hj₀card]; norm_num) v
        obtain ⟨hwσ, hfw⟩ := Finset.mem_filter.mp hwf
        apply Finset.Subset.antisymm
        · intro j hj
          obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hj
          rw [← hcase]
          exact Finset.mem_image.mpr ⟨u, (Finset.mem_erase.mp hu).2, hfu⟩
        · intro j hj
          rw [← hcase] at hj
          obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hj
          by_cases huv : u = v
          · subst huv
            exact Finset.mem_image.mpr ⟨w, Finset.mem_erase.mpr ⟨hwv, hwσ⟩,
              by rw [hfw, ← h, hfu]⟩
          · exact Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, hfu⟩
    rw [hset, hj₀card]
    exact even_two
  · have hempty : σ.filter (fun v => (σ.erase v).image f = J.erase i₀) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro v hv h
      have h1 : J.erase i₀ ⊆ σ.image f := by
        rw [← h]
        exact Finset.image_subset_image (Finset.erase_subset v σ)
      by_cases hi : i₀ ∈ σ.image f
      · exact hne (Finset.Subset.antisymm hsub (by
          intro j hj
          by_cases hji : j = i₀
          · subst hji; exact hi
          · exact h1 (Finset.mem_erase.mpr ⟨hji, hj⟩)))
      · exact hcase (Finset.Subset.antisymm (by
          intro j hj
          exact Finset.mem_erase.mpr ⟨by rintro rfl; exact hi hj, hsub hj⟩) h1)
    rw [hempty]
    simp

/-! ## The combinatorial setting -/

section Sperner

variable {n : ℕ} {V : Type*} [DecidableEq V]
  (carrier : V → Finset (Fin (n + 1))) (T : Finset (Finset V)) (c : V → Fin (n + 1))

/-- The top-dimensional cells of the sub-triangulation carried by the face `F J` of the
big simplex: faces of the triangulation `T` all of whose vertices are carried inside `J`
and which have the full dimension `|J| - 1` of that face. -/
