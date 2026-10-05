import RequestProject.Circuits
import RequestProject.LowDegree

/-!
# MOD_p is not approximable by low degree functions over a field of characteristic q

This is the second half of Smolensky's argument: if the function `x ↦ ζ^{|x|}`
(`ζ` a primitive `p`-th root of unity in a field `F` of characteristic `q`) agrees
with a function of degree `D` on a set `G` of inputs, then `G` is small.
-/

namespace CS

open Finset

open scoped Classical

variable {F : Type*} [Field F] {n : ℕ}

/-- The monomial `∏_{i ∈ S} ζ^{x_i}` in the transformed variables. -/

theorem card_subsets_dvd_le {k q : ℕ} (hq : 2 ≤ q) (b : Fin k → Bool) (i0 : Fin k)
    (hi0 : b i0 = true) :
    2 * ((univ : Finset (Finset (Fin k))).filter
      (fun S => q ∣ ((S.filter fun i => b i = true).card))).card ≤ 2 ^ k := by
  classical
  set A := (univ : Finset (Finset (Fin k))).filter
      (fun S => q ∣ ((S.filter fun i => b i = true).card)) with hA
  set psi : Finset (Fin k) → Finset (Fin k) := fun S => if i0 ∈ S then S.erase i0 else insert i0 S
    with hpsi
  have hinv : Function.Involutive psi := by
    intro S
    by_cases h : i0 ∈ S
    · simp [hpsi, h, Finset.insert_erase h]
    · simp [hpsi, h, Finset.erase_insert h]
  have hcount : ∀ S : Finset (Fin k), i0 ∈ S →
      ((S.erase i0).filter fun i => b i = true).card + 1
        = (S.filter fun i => b i = true).card := by
    intro S hS
    have h1 : ((S.erase i0).filter fun i => b i = true)
        = (S.filter fun i => b i = true).erase i0 := by
      ext j; simp [Finset.mem_erase, Finset.mem_filter]; tauto
    rw [h1, Finset.card_erase_of_mem (by simp [Finset.mem_filter, hS, hi0])]
    have : 1 ≤ (S.filter fun i => b i = true).card :=
      Finset.card_pos.2 ⟨i0, by simp [Finset.mem_filter, hS, hi0]⟩
    omega
  have hcount2 : ∀ S : Finset (Fin k), i0 ∉ S →
      ((insert i0 S).filter fun i => b i = true).card
        = (S.filter fun i => b i = true).card + 1 := by
    intro S hS
    have h1 : ((insert i0 S).filter fun i => b i = true)
        = insert i0 (S.filter fun i => b i = true) := by
      ext j
      by_cases hj : j = i0 <;> simp [Finset.mem_insert, Finset.mem_filter, hj, hi0]
    rw [h1, Finset.card_insert_of_notMem (by simp [Finset.mem_filter, hS])]
  have hdisj : Disjoint A (A.image psi) := by
    rw [Finset.disjoint_right]
    intro S hS hSA
    simp only [Finset.mem_image] at hS
    obtain ⟨T, hT, rfl⟩ := hS
    simp only [hA, Finset.mem_filter, Finset.mem_univ, true_and] at hT hSA
    by_cases h : i0 ∈ T
    · simp only [hpsi, h, if_true] at hSA
      rw [← hcount T h] at hT
      have := Nat.le_of_dvd one_pos ((Nat.dvd_add_right hSA).mp hT)
      omega
    · simp only [hpsi, h, if_false] at hSA
      rw [hcount2 T h] at hSA
      have := Nat.le_of_dvd one_pos ((Nat.dvd_add_right hT).mp hSA)
      omega
  have hcard : (A.image psi).card = A.card := Finset.card_image_of_injective _ hinv.injective
  have h2 : A.card + (A.image psi).card ≤ (univ : Finset (Finset (Fin k))).card := by
    rw [← Finset.card_union_of_disjoint hdisj]
    exact Finset.card_le_card (Finset.subset_univ _)
  rw [hcard] at h2
  simpa [Finset.card_univ, Fintype.card_finset, two_mul] using h2

/-! ### The approximation of an OR gate -/

/-- The Razborov–Smolensky approximation of an unbounded fan-in `OR` gate,
determined by a choice of `ℓ` subsets of the inputs. -/
