import RequestProject.Counting

/-!
# Soundness of the counting machine

We define an invariant of the states of the counting machine which is satisfied by the
initial state and preserved by every transition, and which guarantees, in the accepting
phase, that no accepting vertex is reachable.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable (G : Data) (x : List Bool)

/-- The invariant of the inner loop: the vertices counted so far form a set `S` of vertices
`< u` reachable in `i` steps, and the flag correctly records whether one of them witnesses
the reachability of `v` in `i+1` steps. -/

lemma inv_step {s t : Aux G.N} (hstep : stepA G s x[G.pos (s.w : ℕ)]? t) (hs : Inv G x s) :
    Inv G x t := by
  classical
  rcases hstep with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  -- T1 : O → I
  · obtain ⟨hph, hv, hph', h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [Inv_O hph] at hs
    obtain ⟨hi, hr, _, hcnt⟩ := hs
    rw [Inv_I hph', h1, h2, h3, h4, h5, h6, h7]
    exact ⟨hi, hr, hv, hcnt, by omega, ⟨∅, by simp, by simp, by simp, by simp⟩⟩
  -- T2 : O → O (next round)
  · obtain ⟨hph, hvN, hiN, hph', h1, h2, h3, h4⟩ := h
    rw [Inv_O hph] at hs
    obtain ⟨_, _, _, hcnt⟩ := hs
    rw [Inv_O hph', h1, h2, h3, h4]
    refine ⟨by omega, ?_, by omega, by rw [cnt_zero_index]⟩
    rw [hcnt, hvN]
  -- T3 : O → F
  · obtain ⟨hph, hiN, hph', h1, h2, h3⟩ := h
    rw [Inv_O hph] at hs
    obtain ⟨_, hr, _, _⟩ := hs
    rw [Inv_F hph', h1, h2, h3]
    exact ⟨by rw [hr, hiN], by omega, ⟨∅, by simp, by simp, by simp⟩⟩
  -- T4 : I → I (skip)
  · obtain ⟨hph, hu, hph', h1, h2, h3, h4, h5, h6, h7⟩ := h
    rw [Inv_I hph] at hs
    obtain ⟨hi, hr, hv, hcnt, _, S, hS1, hS2, hS3, hS4⟩ := hs
    rw [Inv_I hph', h1, h2, h3, h4, h5, h6, h7]
    exact ⟨hi, hr, hv, hcnt, by omega,
      ⟨S, fun y hy => ⟨by have := (hS1 y hy).1; omega, (hS1 y hy).2⟩, hS2, hS3, hS4⟩⟩
  -- T5 : I → W
  · obtain ⟨hph, hu, hph', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    rw [Inv_I hph] at hs
    obtain ⟨hi, hr, hv, hcnt, _, hin⟩ := hs
    rw [Inv_W hph', h1, h2, h3, h4, h5, h6, h7, h8, h9]
    exact ⟨hi, hr, hv, hcnt, hu, hin, by omega, Rch_start⟩
  -- T6 : W → W (edge)
  · obtain ⟨hph, hd, hph', h1, h2, h3, h4, h5, h6, h7, h8, hedge⟩ := h
    rw [Inv_W hph] at hs
    obtain ⟨hi, hr, hv, hcnt, hu, hin, hdi, hw⟩ := hs
    rw [Inv_W hph', h1, h2, h3, h4, h5, h6, h7, h8]
    exact ⟨hi, hr, hv, hcnt, hu, hin, by omega, Rch_step hw hedge⟩
  -- T7 : W → W (stay)
  · obtain ⟨hph, hd, hph', h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := h
    rw [Inv_W hph] at hs
    obtain ⟨hi, hr, hv, hcnt, hu, hin, hdi, hw⟩ := hs
    rw [Inv_W hph', h1, h2, h3, h4, h5, h6, h7, h8, h9]
    exact ⟨hi, hr, hv, hcnt, hu, hin, by omega, Rch_succ_of hw⟩
  -- T8 : W → I (the path arrived, count and test)
  · obtain ⟨hph, hwu, hph', h1, h2, h3, h4, h5, h6, hflag⟩ := h
    rw [Inv_W hph] at hs
    obtain ⟨hi, hr, hv, hcnt, hu, ⟨S, hS1, hS2, hS3, hS4⟩, hdi, hw⟩ := hs
    have hRu : G.Rch x (s.i : ℕ) (s.u : ℕ) := by
      rw [← hwu]; exact Rch_mono hdi hw
    have hnotmem : (s.u : ℕ) ∉ S := fun hmem => by have := (hS1 _ hmem).1; omega
    rw [Inv_I hph', h1, h2, h3, h4, h5, h6]
    refine ⟨hi, hr, hv, hcnt, by omega, insert (s.u : ℕ) S, ?_, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact ⟨by omega, hRu⟩
      · exact ⟨by have := (hS1 y hy).1; omega, (hS1 y hy).2⟩
    · rw [Finset.card_insert_of_notMem hnotmem, hS2]
    · intro htf
      rcases hflag.1 htf with hf | huv | hE
      · exact hS3 hf
      · exact Rch_succ_of (huv ▸ hRu)
      · refine Rch_step hRu ?_
        rw [hwu] at hE
        exact hE
    · intro htf y hy
      have hnot : ¬ (s.flag = true ∨ (s.u : ℕ) = (s.v : ℕ) ∨
          G.Ed x[G.pos (s.w : ℕ)]? (s.u : ℕ) (s.v : ℕ)) := by
        intro hc
        rw [hflag.2 hc] at htf
        exact Bool.noConfusion htf
      push_neg at hnot
      obtain ⟨hfalse, huv, hE⟩ := hnot
      rw [hwu] at hE
      rcases Finset.mem_insert.1 hy with rfl | hy
      · rintro (hc | hc)
        · exact huv hc
        · exact hE hc
      · exact hS4 (by simpa using hfalse) y hy
  -- T9 : I → O (inner loop finished)
  · obtain ⟨hph, huN, hcr, hph', h1, h2, h3, h4⟩ := h
    rw [Inv_I hph] at hs
    obtain ⟨hi, hr, hv, hcnt, _, ⟨S, hS1, hS2, hS3, hS4⟩⟩ := hs
    have hSeq : S = RSet G x (s.i : ℕ) := by
      refine eq_RSet_of_card G x (fun y hy => (hS1 y hy).2) ?_
      rw [hS2, hcr, hr]
    have hflagiff : (s.flag = true) ↔ G.Rch x ((s.i : ℕ) + 1) (s.v : ℕ) := by
      constructor
      · exact hS3
      · intro hreach
        by_contra hfalse
        have hf : s.flag = false := by
          cases hb : s.flag with
          | false => rfl
          | true => exact absurd hb hfalse
        rcases hreach with hy | ⟨y, hy, hedge⟩
        · exact hS4 hf (s.v : ℕ) (by rw [hSeq]; exact (mem_RSet G x).2 hy) (Or.inl rfl)
        · exact hS4 hf y (by rw [hSeq]; exact (mem_RSet G x).2 hy) (Or.inr hedge)
    rw [Inv_O hph', h1, h2, h3, h4]
    refine ⟨hi, hr, by omega, ?_⟩
    rw [cnt_succ_index, ← hcnt]
    congr 1
    by_cases hb : s.flag = true
    · rw [if_pos (hflagiff.1 hb), if_pos hb]
    · have hb' : s.flag = false := by cases hbb : s.flag with
        | false => rfl
        | true => exact absurd hbb hb
      rw [if_neg (fun hc => hb (hflagiff.2 hc)), if_neg (by simp [hb'])]
  -- T10 : F → F (skip)
  · obtain ⟨hph, hu, hph', h1, h2, h3⟩ := h
    rw [Inv_F hph] at hs
    obtain ⟨hr, _, S, hS1, hS2, hS3⟩ := hs
    rw [Inv_F hph', h1, h2, h3]
    exact ⟨hr, by omega, S, fun y hy => ⟨by have := (hS1 y hy).1; omega, (hS1 y hy).2⟩, hS2, hS3⟩
  -- T11 : F → WF
  · obtain ⟨hph, hu, hph', h1, h2, h3, h4, h5⟩ := h
    rw [Inv_F hph] at hs
    obtain ⟨hr, _, hfin⟩ := hs
    rw [Inv_WF hph', h1, h2, h3, h4, h5]
    exact ⟨hr, hu, hfin, by omega, Rch_start⟩
  -- T12 : WF → WF (edge)
  · obtain ⟨hph, hd, hph', h1, h2, h3, h4, hedge⟩ := h
    rw [Inv_WF hph] at hs
    obtain ⟨hr, hu, hfin, hdN, hw⟩ := hs
    rw [Inv_WF hph', h1, h2, h3, h4]
    exact ⟨hr, hu, hfin, by omega, Rch_step hw hedge⟩
  -- T13 : WF → WF (stay)
  · obtain ⟨hph, hd, hph', h1, h2, h3, h4, h5⟩ := h
    rw [Inv_WF hph] at hs
    obtain ⟨hr, hu, hfin, hdN, hw⟩ := hs
    rw [Inv_WF hph', h1, h2, h3, h4, h5]
    exact ⟨hr, hu, hfin, by omega, Rch_succ_of hw⟩
  -- T14 : WF → F (the path arrived at a non accepting vertex)
  · obtain ⟨hph, hwu, hacc, hph', h1, h2, h3⟩ := h
    rw [Inv_WF hph] at hs
    obtain ⟨hr, hu, ⟨S, hS1, hS2, hS3⟩, hdN, hw⟩ := hs
    have hRu : G.Rch x G.N (s.u : ℕ) := by rw [← hwu]; exact Rch_mono hdN hw
    have hnotmem : (s.u : ℕ) ∉ S := fun hmem => by have := (hS1 _ hmem).1; omega
    rw [Inv_F hph', h1, h2, h3]
    refine ⟨hr, by omega, insert (s.u : ℕ) S, ?_, ?_, ?_⟩
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact ⟨by omega, hRu⟩
      · exact ⟨by have := (hS1 y hy).1; omega, (hS1 y hy).2⟩
    · rw [Finset.card_insert_of_notMem hnotmem, hS2]
    · intro y hy
      rcases Finset.mem_insert.1 hy with rfl | hy
      · exact hacc
      · exact hS3 y hy
  -- T15 : F → A
  · obtain ⟨hph, huN, hcr, hph'⟩ := h
    rw [Inv_F hph] at hs
    obtain ⟨hr, _, S, hS1, hS2, hS3⟩ := hs
    have hSeq : S = RSet G x G.N :=
      eq_RSet_of_card G x (fun y hy => (hS1 y hy).2) (by rw [hS2, hcr, hr])
    rw [Inv_A hph']
    rintro ⟨q, hq, hqr⟩
    exact hS3 q (by rw [hSeq]; exact (mem_RSet G x).2 hqr) hq

/-- The invariant is preserved along runs of the counting machine. -/
