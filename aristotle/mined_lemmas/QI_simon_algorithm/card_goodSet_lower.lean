/-
`m` independent runs of Simon's algorithm, and the analysis showing that `n + 2` quantum
queries determine the hidden shift with probability at least `3/4`.
-/
import RequestProject.SimonQuantum

open scoped BigOperators
open scoped Classical
open Finset

set_option maxHeartbeats 1000000
set_option autoImplicit false

namespace QI

/-- The state of `m` independent copies of the Simon circuit (a product state, using
`m` quantum queries in total). -/

lemma card_goodSet_lower {n : ℕ} (s : Bits n) (hs : s ≠ 0) (m : ℕ) (hm : m = n + 2) :
    3 * (orth s).card ^ m ≤ 4 * (goodSet n m s).card := by
  classical
  set S : Finset (Bits n) := orth s with hS
  set P : Finset (Fin m → Bits n) := Fintype.piFinset (fun _ : Fin m => S) with hP
  have hPcard : P.card = S.card ^ m := by
    rw [hP, Fintype.card_piFinset]
    simp
  have hsub : goodSet n m s ⊆ P := by
    intro y hy
    rw [goodSet, Finset.mem_filter] at hy
    rw [hP, Fintype.mem_piFinset]
    intro i
    rw [hS, mem_orth]
    exact hy.2.1 i
  set T : Finset (Bits n) := Finset.univ.filter (fun t => t ≠ 0 ∧ t ≠ s) with hT
  set Bad : Finset (Fin m → Bits n) := P \ goodSet n m s with hBad
  have hBadsub : Bad ⊆ T.biUnion
      (fun t => Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))) := by
    intro y hy
    rw [hBad, Finset.mem_sdiff] at hy
    obtain ⟨hyP, hyG⟩ := hy
    rw [hP, Fintype.mem_piFinset] at hyP
    have hys : ∀ i, bdot (y i) s = 0 := by
      intro i
      have := hyP i
      rwa [hS, mem_orth] at this
    have : ¬ determines y s := by
      intro hd
      exact hyG (by rw [goodSet, Finset.mem_filter]; exact ⟨Finset.mem_univ _, hd⟩)
    rw [determines] at this
    push_neg at this
    obtain ⟨t, ht0, htorth, hts⟩ := this hys
    refine Finset.mem_biUnion.2 ⟨t, ?_, ?_⟩
    · rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_univ _, ht0, hts⟩
    · rw [Fintype.mem_piFinset]
      intro i
      rw [Finset.mem_filter, hS, mem_orth]
      exact ⟨hys i, htorth i⟩
  have hkey : ∀ t ∈ T, 2 ^ m * (S.filter (fun y => bdot y t = 0)).card ^ m = S.card ^ m := by
    intro t ht
    rw [hT, Finset.mem_filter] at ht
    have h2 := card_orth_inter s t hs ht.2.1 ht.2.2
    rw [← hS] at h2
    calc 2 ^ m * (S.filter (fun y => bdot y t = 0)).card ^ m
        = (2 * (S.filter (fun y => bdot y t = 0)).card) ^ m := by rw [mul_pow]
      _ = S.card ^ m := by rw [h2]
  have hTcard : T.card ≤ 2 ^ n := by
    calc T.card ≤ (Finset.univ : Finset (Bits n)).card := Finset.card_le_card (Finset.subset_univ _)
      _ = 2 ^ n := by simp
  have hBadbound : 2 ^ m * Bad.card ≤ 2 ^ n * S.card ^ m := by
    have h1 : Bad.card ≤ ∑ t ∈ T,
        (Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))).card :=
      le_trans (Finset.card_le_card hBadsub) Finset.card_biUnion_le
    have h2 : 2 ^ m * Bad.card ≤ ∑ t ∈ T, 2 ^ m *
        (Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))).card := by
      rw [← Finset.mul_sum]
      exact Nat.mul_le_mul_left _ h1
    have h3 : ∑ t ∈ T, 2 ^ m *
        (Fintype.piFinset (fun _ : Fin m => S.filter (fun y => bdot y t = 0))).card
        = ∑ t ∈ T, S.card ^ m := by
      refine Finset.sum_congr rfl ?_
      intro t ht
      rw [Fintype.card_piFinset]
      simp only [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      exact hkey t ht
    rw [h3, Finset.sum_const, smul_eq_mul] at h2
    exact le_trans h2 (Nat.mul_le_mul_right _ hTcard)
  have hpow : (2:ℕ) ^ m = 4 * 2 ^ n := by
    rw [hm]; ring
  have h4 : 4 * Bad.card ≤ S.card ^ m := by
    have := hBadbound
    rw [hpow] at this
    have hpos : 0 < (2:ℕ) ^ n := Nat.pow_pos (by norm_num)
    nlinarith [this, hpos]
  have hsplit : (goodSet n m s).card + Bad.card = S.card ^ m := by
    rw [hBad, Finset.card_sdiff_of_subset hsub, ← hPcard]
    have := Finset.card_le_card hsub
    omega
  omega

/-- **`n + 2` quantum queries suffice.**  With `n + 2` runs of the one-query Simon circuit,
the measurement outcomes determine the hidden shift with probability at least `3/4`. -/
