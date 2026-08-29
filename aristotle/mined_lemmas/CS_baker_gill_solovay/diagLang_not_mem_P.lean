/-
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib
import RequestProject.Model

/-!
# Baker Gill Solovay
Category: Frontier Cs
Target: CS.baker_gill_solovay
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace CS

/-! ## A calculus for reasoning about program execution -/

/-- `Exec O S n f` says: started with registers `σ`, the statement `S` terminates
after exactly `n σ` steps, leaving the registers in state `f σ` (and the rest of
the control stack untouched). -/

theorem diagLang_not_mem_P : diagLang Boracle ∉ PLang Boracle := by
  rintro ⟨M, k, -, hMk⟩
  obtain ⟨n, hn⟩ := enumPair_surjective (M, k)
  have hM : (enumPair n).1 = M := by rw [hn]
  have hk : (enumPair n).2 = k := by rw [hn]
  have hxlen : (stInput n).length = stLen n := stInput_length n
  have hT : stTime n = ((stInput n).length + 2) ^ k := by
    rw [hxlen]
    unfold stTime
    rw [hk]
  have hqlen : ∀ s ∈ qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n),
      s.length < (stage (n + 1)).2 := by
    intro s hs
    have hb := qList_len_bound (oracleOf (stage n).1) M (stInput n) [] (stTime n) s hs
    rw [hxlen] at hb
    rw [stage_snd_succ]
    simp only [List.length_nil, Nat.max_eq_left, Nat.zero_le, max_eq_left] at hb
    omega
  by_cases hacc : AcceptsIn (oracleOf (stage n).1) M (stInput n) [] (stTime n)
  · -- the machine accepts, so no string of length `stLen n` enters the oracle
    have hfst : (stage (n + 1)).1 = (stage n).1 := by
      rw [stage_fst_succ, hM, if_pos hacc]
    have hagree : ∀ s ∈ qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n),
        oracleOf (stage n).1 s = Boracle s := by
      intro s hs
      rw [Bool.eq_iff_iff, oracleOf_apply, Boracle_agrees (n + 1) s (hqlen s hs), hfst]
    have haccB : AcceptsIn Boracle M (stInput n) [] (stTime n) := (AcceptsIn_congr hagree).1 hacc
    have hmem : stInput n ∈ diagLang Boracle := by
      rw [hMk (stInput n), ← hT]
      exact haccB
    obtain ⟨z, hz, hzB⟩ := hmem
    rw [hxlen] at hz
    rw [Boracle_true_iff] at hzB
    obtain ⟨m, hm⟩ := hzB
    have hzin : z ∈ (stage n).1 ∨ (stage (n + 1)).2 ≤ z.length := by
      rcases Nat.lt_or_ge m (n + 1) with h | h
      · left
        have : z ∈ (stage (n + 1)).1 := stage_fst_mono (by omega) hm
        rwa [hfst] at this
      · rcases stage_mem_later h z hm with h1 | h1
        · left; rwa [hfst] at h1
        · right; exact h1
    rcases hzin with h1 | h1
    · have h2 := stage_len_lt n z h1
      have h3 := stage_snd_le_stLen n
      omega
    · rw [stage_snd_succ] at h1
      have := stTime_pos n
      omega
  · -- the machine rejects, so a fresh string of length `stLen n` enters the oracle
    have hQ : (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)).length
        < 2 ^ (stLen n) := by
      have h1 := qList_length (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)
      have h2 : stTime n < 2 ^ (stLen n) := chooseLen_big (stage n).2 (enumPair n).2
      omega
    have hzspec := freshStr_spec (stLen n)
      (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)) hQ
    have hfst : (stage (n + 1)).1 = insert (freshStr (stLen n)
        (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n))) (stage n).1 := by
      rw [stage_fst_succ, hM, if_neg hacc]
    have hagree : ∀ s ∈ qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n),
        oracleOf (stage n).1 s = Boracle s := by
      intro s hs
      have hne : s ≠ freshStr (stLen n)
          (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)) := by
        intro h
        exact hzspec.2 (h ▸ hs)
      rw [Bool.eq_iff_iff, oracleOf_apply, Boracle_agrees (n + 1) s (hqlen s hs), hfst,
        Finset.mem_insert]
      constructor
      · exact fun h => Or.inr h
      · rintro (h | h)
        · exact absurd h hne
        · exact h
    have hnB : ¬ AcceptsIn Boracle M (stInput n) [] (stTime n) := fun h =>
      hacc ((AcceptsIn_congr hagree).2 h)
    have hmem : stInput n ∈ diagLang Boracle := by
      refine ⟨freshStr (stLen n)
        (qList (oracleOf (stage n).1) (init M (stInput n) []) (stTime n)), ?_, ?_⟩
      · rw [hxlen, hzspec.1]
      · rw [Boracle_true_iff]
        exact ⟨n + 1, by rw [hfst]; exact Finset.mem_insert_self _ _⟩
    rw [hMk (stInput n), ← hT] at hmem
    exact hnB hmem

/-- There is an oracle relative to which `P` and `NP` differ. -/
