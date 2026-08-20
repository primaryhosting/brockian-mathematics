/-
The classical XY model on a finite graph, and the finite-volume Mermin-Wagner bound
on its magnetization in terms of the Dirichlet energy of a spin-wave profile.
-/
import RequestProject.Core

open MeasureTheory Real

namespace Phys

noncomputable section

variable {S ι : Type} [Fintype S]

/-- The energy of the classical XY model on a finite graph whose edges are indexed by
`bonds`, with endpoints `src` and `tgt`, coupling `J` and external field `h`. -/

lemma card_shell_le {d L : ℕ} (hd : d ≤ 2) (m : ℕ) :
    (Finset.univ.filter fun x : Site d L => rad x = m).card ≤ 12 * m + 1 := by
  classical
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · -- only the centre has radius `0`
    have hsub : (Finset.univ.filter fun x : Site d L => rad x = 0) ⊆ {center d L} := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_singleton]
      funext i
      have : dist1 L (x i) ≤ 0 := by
        rw [← hx]
        exact Finset.le_sup (f := fun j => dist1 L (x j)) (Finset.mem_univ i)
      have h0 : dist1 L (x i) = 0 := Nat.le_zero.mp this
      unfold dist1 at h0
      have := (x i).isLt
      exact Fin.ext (by unfold center; simp; omega)
    calc (Finset.univ.filter fun x : Site d L => rad x = 0).card ≤ ({center d L} : Finset _).card :=
          Finset.card_le_card hsub
      _ = 1 := Finset.card_singleton _
      _ ≤ 12 * 0 + 1 := by omega
  · -- some coordinate realises the maximum
    have hsub : (Finset.univ.filter fun x : Site d L => rad x = m) ⊆
        Finset.univ.biUnion fun i : Fin d =>
          Fintype.piFinset (Function.update (fun _ => Tball L m) i (Ecrit L m)) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx
      have hne : (Finset.univ : Finset (Fin d)).Nonempty := by
        rcases Nat.eq_zero_or_pos d with rfl | hd0
        · exfalso
          have : rad x = 0 := by
            unfold rad
            simp
          omega
        · exact Finset.univ_nonempty_iff.mpr (Fin.pos_iff_nonempty.mp hd0)
      obtain ⟨i, -, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hne fun j => dist1 L (x j)
      refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ i, ?_⟩
      refine Fintype.mem_piFinset.mpr fun j => ?_
      by_cases hji : j = i
      · subst hji
        simp only [Function.update_self, Ecrit, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hi]
        exact hx
      · simp only [Function.update_of_ne hji, Tball, Finset.mem_filter, Finset.mem_univ, true_and]
        rw [← hx]
        exact Finset.le_sup (f := fun k => dist1 L (x k)) (Finset.mem_univ j)
    have hcard_each : ∀ i : Fin d,
        (Fintype.piFinset (Function.update (fun _ => Tball L m) i (Ecrit L m))).card
          ≤ 2 * (2 * m + 1) ^ (d - 1) := by
      intro i
      rw [Fintype.card_piFinset, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i),
        Function.update_self]
      have hrest : ∏ j ∈ Finset.univ.erase i,
          (Function.update (fun _ => Tball L m) i (Ecrit L m) j).card
          = ∏ _j ∈ Finset.univ.erase i, (Tball L m).card :=
        Finset.prod_congr rfl fun j hj => by
          rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
      rw [hrest, Finset.prod_const]
      have hcard : (Finset.univ.erase i : Finset (Fin d)).card = d - 1 := by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i)]
        simp
      rw [hcard]
      exact Nat.mul_le_mul (card_Ecrit L m) (Nat.pow_le_pow_left (card_Tball L m) _)
    calc (Finset.univ.filter fun x : Site d L => rad x = m).card
        ≤ ∑ _i : Fin d, 2 * (2 * m + 1) ^ (d - 1) :=
          le_trans (Finset.card_le_card hsub)
            (le_trans (Finset.card_biUnion_le) (Finset.sum_le_sum fun i _ => hcard_each i))
      _ = d * (2 * (2 * m + 1) ^ (d - 1)) := by rw [Finset.sum_const]; simp [mul_comm]
      _ ≤ 12 * m + 1 := by
          have hpow : (2 * m + 1) ^ (d - 1) ≤ 2 * m + 1 := by
            have h : (2 * m + 1) ^ (d - 1) ≤ (2 * m + 1) ^ 1 :=
              Nat.pow_le_pow_right (by omega) (by omega)
            simpa using h
          have h2 : d * (2 * (2 * m + 1) ^ (d - 1)) ≤ 2 * (2 * (2 * m + 1)) :=
            Nat.mul_le_mul hd (by omega)
          have h3 : 2 * (2 * (2 * m + 1)) ≤ 12 * m + 1 := by omega
          exact le_trans h2 h3

/-- Shell decomposition of a sum over the box. -/
