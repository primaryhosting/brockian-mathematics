import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma card_zero_sum_le {m : ℕ} (a : Fin m → ZMod q) {i₀ : Fin m} (h : a i₀ ≠ 0) :
    2 * ((Finset.univ : Finset (Finset (Fin m))).filter
      (fun S => ∑ i ∈ S, a i = 0)).card ≤ 2 ^ m := by
  classical
  set Z := (Finset.univ : Finset (Finset (Fin m))).filter (fun S => ∑ i ∈ S, a i = 0) with hZ
  set Z' := (Finset.univ : Finset (Finset (Fin m))).filter (fun S => ¬ (∑ i ∈ S, a i = 0))
    with hZ'
  have hsum : Z.card + Z'.card = 2 ^ m := by
    rw [hZ, hZ', Finset.card_filter_add_card_filter_not]
    simp
  have hmemZ : ∀ S : Finset (Fin m), S ∈ Z ↔ ∑ i ∈ S, a i = 0 := by
    intro S; rw [hZ, Finset.mem_filter]; simp
  have hmemZ' : ∀ S : Finset (Fin m), S ∈ Z' ↔ ¬ (∑ i ∈ S, a i = 0) := by
    intro S; rw [hZ', Finset.mem_filter]; simp
  have hle : Z.card ≤ Z'.card := by
    refine Finset.card_le_card_of_injOn
      (fun S => if i₀ ∈ S then S.erase i₀ else insert i₀ S) ?_ ?_
    · intro S hS
      have hS' : ∑ i ∈ S, a i = 0 := (hmemZ S).1 (by simpa using hS)
      have hgoal : (if i₀ ∈ S then S.erase i₀ else insert i₀ S) ∈ Z' := by
        rw [hmemZ']
        by_cases hi : i₀ ∈ S
        · rw [if_pos hi]
          intro hcon
          have h2 : ∑ i ∈ S, a i = a i₀ + ∑ i ∈ S.erase i₀, a i :=
            (Finset.add_sum_erase _ _ hi).symm
          rw [hS', hcon, add_zero] at h2
          exact h h2.symm
        · rw [if_neg hi, Finset.sum_insert hi, hS', add_zero]
          exact h
      simpa using hgoal
    · intro S _ T _ hST
      simp only at hST
      by_cases hiS : i₀ ∈ S <;> by_cases hiT : i₀ ∈ T
      · rw [if_pos hiS, if_pos hiT] at hST
        have h3 := congrArg (insert i₀) hST
        rwa [Finset.insert_erase hiS, Finset.insert_erase hiT] at h3
      · rw [if_pos hiS, if_neg hiT] at hST
        exfalso
        have h3 : i₀ ∈ insert i₀ T := Finset.mem_insert_self _ _
        rw [← hST] at h3
        exact (Finset.notMem_erase i₀ S) h3
      · rw [if_neg hiS, if_pos hiT] at hST
        exfalso
        have h3 : i₀ ∈ insert i₀ S := Finset.mem_insert_self _ _
        rw [hST] at h3
        exact (Finset.notMem_erase i₀ T) h3
      · rw [if_neg hiS, if_neg hiT] at hST
        have h1 : S = (insert i₀ S).erase i₀ := (Finset.erase_insert hiS).symm
        have h2 : T = (insert i₀ T).erase i₀ := (Finset.erase_insert hiT).symm
        rw [h1, h2, hST]
  omega

variable {n : ℕ}

/-- The value an `OR` gate should take. -/
