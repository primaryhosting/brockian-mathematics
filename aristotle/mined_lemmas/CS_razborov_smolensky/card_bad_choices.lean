import Mathlib

/-!
# Binomial estimates

The estimates on binomial coefficients needed for the counting step of the
Razborov–Smolensky theorem.
-/

namespace CS

open Finset

/-- A quantitative form of `centralBinom m ≈ 4 ^ m / √(π m)`. -/

lemma card_bad_choices {m l : ℕ} (a : Fin m → ZMod q) :
    ((Finset.univ : Finset (Fin l → Finset (Fin m))).filter
        (fun c => (if ∀ j, ∑ i ∈ c j, a i = 0 then (0 : ZMod q) else 1)
          ≠ (if ∀ i, a i = 0 then (0 : ZMod q) else 1))).card * 2 ^ l ≤ (2 ^ m) ^ l := by
  classical
  by_cases hall : ∀ i, a i = 0
  · have hempty : ((Finset.univ : Finset (Fin l → Finset (Fin m))).filter
        (fun c => (if ∀ j, ∑ i ∈ c j, a i = 0 then (0 : ZMod q) else 1)
          ≠ (if ∀ i, a i = 0 then (0 : ZMod q) else 1))) = ∅ := by
      refine Finset.filter_eq_empty_iff.2 ?_
      intro c _
      have h1 : ∀ j, ∑ i ∈ c j, a i = 0 := by
        intro j
        exact Finset.sum_eq_zero (fun i _ => hall i)
      simp [hall]
    rw [hempty]
    simp
  · push_neg at hall
    obtain ⟨i₀, hi₀⟩ := hall
    set Z := (Finset.univ : Finset (Finset (Fin m))).filter
      (fun S => ∑ i ∈ S, a i = 0) with hZ
    have hset : ((Finset.univ : Finset (Fin l → Finset (Fin m))).filter
        (fun c => (if ∀ j, ∑ i ∈ c j, a i = 0 then (0 : ZMod q) else 1)
          ≠ (if ∀ i, a i = 0 then (0 : ZMod q) else 1)))
        = Fintype.piFinset (fun _ : Fin l => Z) := by
      ext c
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fintype.mem_piFinset, hZ]
      constructor
      · intro hc j
        by_contra hcon
        apply hc
        have hnot : ¬ (∀ j, ∑ i ∈ c j, a i = 0) := by
          intro hcc
          exact hcon (by simp [hcc j])
        rw [if_neg hnot, if_neg (by push_neg; exact ⟨i₀, hi₀⟩)]
      · intro hc
        have h1 : ∀ j, ∑ i ∈ c j, a i = 0 := by
          intro j
          have := hc j
          simpa using this
        rw [if_pos h1, if_neg (by push_neg; exact ⟨i₀, hi₀⟩)]
        exact zero_ne_one
    rw [hset, Fintype.card_piFinset]
    have hZcard : 2 * Z.card ≤ 2 ^ m := card_zero_sum_le a hi₀
    calc (∏ _j : Fin l, Z.card) * 2 ^ l = (2 * Z.card) ^ l := by
          rw [Finset.prod_const]
          simp [mul_pow, mul_comm]
      _ ≤ (2 ^ m) ^ l := Nat.pow_le_pow_left hZcard l

/-- There is a choice of subsets for which the `OR` approximation has few bad inputs. -/
