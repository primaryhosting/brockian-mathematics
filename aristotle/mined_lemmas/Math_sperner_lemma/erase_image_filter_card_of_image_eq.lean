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

lemma erase_image_filter_card_of_image_eq {V α : Type*} [DecidableEq V] [DecidableEq α]
    (σ : Finset V) (f : V → α) (J : Finset α) (i₀ : α) (hi₀ : i₀ ∈ J)
    (hcard : σ.card = J.card) (hrb : σ.image f = J) :
    (σ.filter (fun v => (σ.erase v).image f = J.erase i₀)).card = 1 := by
  classical
  have hinj : Set.InjOn f σ := by
    apply Finset.injOn_of_card_image_eq
    rw [hrb, hcard]
  have hset : σ.filter (fun v => (σ.erase v).image f = J.erase i₀)
      = σ.filter (fun v => f v = i₀) := by
    apply Finset.filter_congr
    intro v hv
    constructor
    · intro h
      by_contra hne
      have hi : i₀ ∈ σ.image f := by rw [hrb]; exact hi₀
      obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hi
      have huv : u ≠ v := by rintro rfl; exact hne hfu
      have h2 : i₀ ∈ (σ.erase v).image f :=
        Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨huv, hu⟩, hfu⟩
      rw [h] at h2
      exact (Finset.notMem_erase i₀ J) h2
    · intro h
      apply Finset.Subset.antisymm
      · intro j hj
        obtain ⟨w, hw, hfw⟩ := Finset.mem_image.mp hj
        obtain ⟨hwv, hwσ⟩ := Finset.mem_erase.mp hw
        subst hfw
        refine Finset.mem_erase.mpr ⟨?_, ?_⟩
        · rw [← h]; intro hc; exact hwv (hinj hwσ hv hc)
        · rw [← hrb]; exact Finset.mem_image_of_mem f hwσ
      · intro j hj
        obtain ⟨hjne, hjJ⟩ := Finset.mem_erase.mp hj
        rw [← hrb] at hjJ
        obtain ⟨u, hu, hfu⟩ := Finset.mem_image.mp hjJ
        refine Finset.mem_image.mpr ⟨u, Finset.mem_erase.mpr ⟨?_, hu⟩, hfu⟩
        rintro rfl
        exact hjne (by rw [← hfu, h])
  rw [hset, Finset.card_eq_one]
  have hi : i₀ ∈ σ.image f := by rw [hrb]; exact hi₀
  obtain ⟨v, hv, hfv⟩ := Finset.mem_image.mp hi
  refine ⟨v, Finset.eq_singleton_iff_unique_mem.mpr ⟨Finset.mem_filter.mpr ⟨hv, hfv⟩, ?_⟩⟩
  intro w hw
  obtain ⟨hwσ, hfw⟩ := Finset.mem_filter.mp hw
  exact hinj hwσ hv (by rw [hfw, hfv])

/-- If `f` does not map `σ` onto `J`, the number of vertices that can be deleted from `σ`
so that the remaining colours are `J \ {i₀}` is even (in fact `0` or `2`). -/
