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
def InnerOK (i u c v : ℕ) (flag : Bool) : Prop :=
  ∃ S : Finset ℕ, (∀ y ∈ S, y < u ∧ G.Rch x i y) ∧ S.card = c ∧
    (flag = true → G.Rch x (i + 1) v) ∧
    (flag = false → ∀ y ∈ S, ¬ (y = v ∨ G.edg x y v))

/-- The invariant of the final loop: the vertices counted so far form a set `S` of reachable
vertices `< u`, none of which is accepting. -/
def FinalOK (u c : ℕ) : Prop :=
  ∃ S : Finset ℕ, (∀ y ∈ S, y < u ∧ G.Rch x G.N y) ∧ S.card = c ∧ ∀ y ∈ S, ¬ G.accV y

/-- Invariant of the outer loop. -/
def InvO (i r v cnt : ℕ) : Prop :=
  i ≤ G.N ∧ r = G.cnt x i G.N ∧ v ≤ G.N ∧ cnt = G.cnt x (i + 1) v

/-- Invariant of the inner loop. -/
def InvI (i r v cnt u c : ℕ) (flag : Bool) : Prop :=
  i ≤ G.N ∧ r = G.cnt x i G.N ∧ v < G.N ∧ cnt = G.cnt x (i + 1) v ∧ u ≤ G.N ∧
    InnerOK G x i u c v flag

/-- Invariant of the path verification inside the inner loop. -/
def InvW (i r v cnt u c : ℕ) (flag : Bool) (w d : ℕ) : Prop :=
  i ≤ G.N ∧ r = G.cnt x i G.N ∧ v < G.N ∧ cnt = G.cnt x (i + 1) v ∧ u < G.N ∧
    InnerOK G x i u c v flag ∧ d ≤ i ∧ G.Rch x d w

/-- Invariant of the final loop. -/
def InvF (r u c : ℕ) : Prop :=
  r = G.cnt x G.N G.N ∧ u ≤ G.N ∧ FinalOK G x u c

/-- Invariant of the path verification inside the final loop. -/
def InvWF (r u c w d : ℕ) : Prop :=
  r = G.cnt x G.N G.N ∧ u < G.N ∧ FinalOK G x u c ∧ d ≤ G.N ∧ G.Rch x d w

/-- Invariant of the accepting phase: no accepting vertex is reachable. -/
def InvA : Prop := ¬ ∃ q, G.accV q ∧ G.Rch x G.N q

/-- The invariant of the counting machine. -/
def Inv (s : Aux G.N) : Prop :=
  match s.ph with
  | Phase.O => InvO G x (s.i : ℕ) (s.r : ℕ) (s.v : ℕ) (s.cnt : ℕ)
  | Phase.I => InvI G x (s.i : ℕ) (s.r : ℕ) (s.v : ℕ) (s.cnt : ℕ) (s.u : ℕ) (s.c : ℕ) s.flag
  | Phase.W =>
      InvW G x (s.i : ℕ) (s.r : ℕ) (s.v : ℕ) (s.cnt : ℕ) (s.u : ℕ) (s.c : ℕ) s.flag
        (s.w : ℕ) (s.d : ℕ)
  | Phase.F => InvF G x (s.r : ℕ) (s.u : ℕ) (s.c : ℕ)
  | Phase.WF => InvWF G x (s.r : ℕ) (s.u : ℕ) (s.c : ℕ) (s.w : ℕ) (s.d : ℕ)
  | Phase.A => InvA G x

variable {G x}

lemma Inv_O {s : Aux G.N} (h : s.ph = Phase.O) :
    Inv G x s ↔ InvO G x (s.i : ℕ) (s.r : ℕ) (s.v : ℕ) (s.cnt : ℕ) := by
  unfold Inv; rw [h]

lemma Inv_I {s : Aux G.N} (h : s.ph = Phase.I) :
    Inv G x s ↔ InvI G x (s.i : ℕ) (s.r : ℕ) (s.v : ℕ) (s.cnt : ℕ) (s.u : ℕ) (s.c : ℕ) s.flag := by
  unfold Inv; rw [h]

lemma Inv_W {s : Aux G.N} (h : s.ph = Phase.W) :
    Inv G x s ↔ InvW G x (s.i : ℕ) (s.r : ℕ) (s.v : ℕ) (s.cnt : ℕ) (s.u : ℕ) (s.c : ℕ) s.flag
      (s.w : ℕ) (s.d : ℕ) := by
  unfold Inv; rw [h]

lemma Inv_F {s : Aux G.N} (h : s.ph = Phase.F) :
    Inv G x s ↔ InvF G x (s.r : ℕ) (s.u : ℕ) (s.c : ℕ) := by
  unfold Inv; rw [h]

lemma Inv_WF {s : Aux G.N} (h : s.ph = Phase.WF) :
    Inv G x s ↔ InvWF G x (s.r : ℕ) (s.u : ℕ) (s.c : ℕ) (s.w : ℕ) (s.d : ℕ) := by
  unfold Inv; rw [h]

lemma Inv_A {s : Aux G.N} (h : s.ph = Phase.A) : Inv G x s ↔ InvA G x := by
  unfold Inv; rw [h]

variable (G x)

/-- The set of all vertices reachable in at most `i` steps. -/
noncomputable def RSet (i : ℕ) : Finset ℕ := (Finset.range G.N).filter (fun v => G.Rch x i v)

lemma mem_RSet {i y : ℕ} : y ∈ RSet G x i ↔ G.Rch x i y := by
  unfold RSet
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨fun h => h.2, fun h => ⟨Rch_lt h, h⟩⟩

lemma card_RSet (i : ℕ) : (RSet G x i).card = G.cnt x i G.N := rfl

/-- A set of `G.cnt x i G.N` vertices reachable in `i` steps is the set of *all* vertices
reachable in `i` steps.  This is the heart of the inductive counting argument. -/
lemma eq_RSet_of_card {i : ℕ} {S : Finset ℕ} (hS : ∀ y ∈ S, G.Rch x i y)
    (hcard : S.card = G.cnt x i G.N) : S = RSet G x i := by
  refine Finset.eq_of_subset_of_card_le (fun y hy => (mem_RSet G x).2 (hS y hy)) ?_
  rw [card_RSet, hcard]

variable {G x}

lemma inv_start : Inv G x (startA G) := by
  rw [Inv_O (by rfl)]
  refine ⟨by simp [startA, mkO], ?_, by simp [startA, mkO], ?_⟩
  · have h1 : ((startA G).r : ℕ) = 1 := by
      simp [startA, mkO, fv_val (show (1 : ℕ) ≤ G.N + 1 by omega)]
    have h2 : ((startA G).i : ℕ) = 0 := by simp [startA, mkO]
    rw [h1, h2, cnt_zero_eq]
  · have h1 : ((startA G).cnt : ℕ) = 0 := by simp [startA, mkO]
    have h2 : ((startA G).v : ℕ) = 0 := by simp [startA, mkO]
    rw [h1, h2, cnt_zero_index]

/-- The invariant is preserved by every transition of the counting machine. -/
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
lemma inv_reachable {s t : Aux G.N}
    (h : Relation.ReflTransGen ((machine G).edge x) s t) (hs : Inv G x s) : Inv G x t := by
  induction h with
  | refl => exact hs
  | tail _ hstep ih => exact inv_step hstep ih

/-- Soundness: if the counting machine accepts `x`, then no accepting vertex of the
configuration graph is reachable. -/
theorem machine_sound (h : (machine G).Accepts x) : ¬ ∃ q, G.accV q ∧ G.Reachable x q := by
  obtain ⟨q, hq, hpath⟩ := h
  have hinv : Inv G x q := inv_reachable hpath inv_start
  rw [Inv_A hq] at hinv
  rintro ⟨p, hp, hpr⟩
  exact hinv ⟨p, hp, (Rch_iff_reachable p).2 hpr⟩

end IS
end CS

import RequestProject.Reach

/-!
# The inductive counting machine

Given a configuration graph (vertices `< N`, start vertex `st0`, edge relation `Ed`,
accepting vertices `accV`) we build a nondeterministic branching program which accepts an
input `x` **iff** no accepting vertex is reachable in the configuration graph on `x`.

The program implements the Immerman--Szelepcsényi inductive counting algorithm.
-/

open scoped Classical

namespace CS
namespace IS

/-- The phases of the counting machine. -/
inductive Phase
  /-- Outer loop: computing the set reachable in `i+1` steps. -/
  | O
  /-- Inner loop: enumerating the vertices reachable in `i` steps. -/
  | I
  /-- Verifying a guessed path (inside the inner loop). -/
  | W
  /-- Final loop: enumerating the reachable vertices and checking none accepts. -/
  | F
  /-- Verifying a guessed path (inside the final loop). -/
  | WF
  /-- The accepting phase. -/
  | A
  deriving DecidableEq

instance : Fintype Phase :=
  ⟨{Phase.O, Phase.I, Phase.W, Phase.F, Phase.WF, Phase.A}, by intro p; cases p <;> decide⟩

lemma card_Phase : Fintype.card Phase = 6 := rfl

/-- A state of the counting machine: a phase together with a bounded number of counters,
each of which is at most `N + 1`. -/
structure Aux (N : ℕ) where
  /-- current phase -/
  ph : Phase
  /-- round number -/
  i : Fin (N + 2)
  /-- the (verified) number of vertices reachable in at most `i` steps -/
  r : Fin (N + 2)
  /-- outer loop variable -/
  v : Fin (N + 2)
  /-- number of vertices `< v` reachable in at most `i+1` steps -/
  cnt : Fin (N + 2)
  /-- inner loop variable -/
  u : Fin (N + 2)
  /-- number of vertices found so far in the inner loop -/
  c : Fin (N + 2)
  /-- current vertex of the guessed path -/
  w : Fin (N + 2)
  /-- length of the guessed path so far -/
  d : Fin (N + 2)
  /-- has a witness for `v` been found? -/
  flag : Bool

/-- Encoding of states, used only to bound their number. -/
def Aux.enc {N : ℕ} (s : Aux N) :
    Phase × Bool × Fin (N + 2) × Fin (N + 2) × Fin (N + 2) × Fin (N + 2) × Fin (N + 2) ×
      Fin (N + 2) × Fin (N + 2) × Fin (N + 2) :=
  (s.ph, s.flag, s.i, s.r, s.v, s.cnt, s.u, s.c, s.w, s.d)

lemma Aux.enc_injective {N : ℕ} : Function.Injective (Aux.enc (N := N)) := by
  rintro ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10⟩ ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10⟩ h
  simp only [Aux.enc, Prod.mk.injEq] at h
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩ := h
  subst h1; subst h2; subst h3; subst h4; subst h5; subst h6; subst h7; subst h8; subst h9
  subst h10; rfl

noncomputable instance {N : ℕ} : Fintype (Aux N) := Fintype.ofInjective _ Aux.enc_injective

lemma card_Aux_le (N : ℕ) : Fintype.card (Aux N) ≤ 12 * (N + 2) ^ 8 := by
  have h := Fintype.card_le_of_injective _ (Aux.enc_injective (N := N))
  refine le_trans h (le_of_eq ?_)
  simp [Fintype.card_prod, card_Phase]
  ring

/-- Turning a natural number into a counter (values are always `≤ N + 1` in practice). -/
def fv (N k : ℕ) : Fin (N + 2) := ⟨min k (N + 1), by omega⟩

@[simp] lemma fv_val {N k : ℕ} (h : k ≤ N + 1) : ((fv N k : Fin (N + 2)) : ℕ) = k := by
  simp [fv, Nat.min_eq_left h]

section Machine

variable (G : Data)

/-- The transition relation of the counting machine. -/
def stepA (s : Aux G.N) (b : Option Bool) (t : Aux G.N) : Prop :=
  -- T1: enter the inner loop for the vertex `v`
  (s.ph = Phase.O ∧ (s.v : ℕ) < G.N ∧ t.ph = Phase.I ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = 0 ∧ (t.c : ℕ) = 0 ∧ t.flag = false)
  ∨ -- T2: the round `i` is finished; start round `i+1`
  (s.ph = Phase.O ∧ (s.v : ℕ) = G.N ∧ (s.i : ℕ) < G.N ∧ t.ph = Phase.O ∧
      (t.i : ℕ) = (s.i : ℕ) + 1 ∧ (t.r : ℕ) = (s.cnt : ℕ) ∧ (t.v : ℕ) = 0 ∧ (t.cnt : ℕ) = 0)
  ∨ -- T3: all rounds are finished; enter the final loop
  (s.ph = Phase.O ∧ (s.i : ℕ) = G.N ∧ t.ph = Phase.F ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = 0 ∧ (t.c : ℕ) = 0)
  ∨ -- T4: skip the vertex `u` in the inner loop
  (s.ph = Phase.I ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.I ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag)
  ∨ -- T5: claim that `u` is reachable in `i` steps and start guessing a path
  (s.ph = Phase.I ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.W ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag ∧
      (t.w : ℕ) = G.st0 ∧ (t.d : ℕ) = 0)
  ∨ -- T6: follow an edge of the guessed path
  (s.ph = Phase.W ∧ (s.d : ℕ) < (s.i : ℕ) ∧ t.ph = Phase.W ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag ∧
      (t.d : ℕ) = (s.d : ℕ) + 1 ∧ G.Ed b (s.w : ℕ) (t.w : ℕ))
  ∨ -- T7: stay where we are (a shorter path is also a path)
  (s.ph = Phase.W ∧ (s.d : ℕ) < (s.i : ℕ) ∧ t.ph = Phase.W ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ t.flag = s.flag ∧
      (t.d : ℕ) = (s.d : ℕ) + 1 ∧ (t.w : ℕ) = (s.w : ℕ))
  ∨ -- T8: the path reached `u`; count it and test whether it witnesses `v`
  (s.ph = Phase.W ∧ (s.w : ℕ) = (s.u : ℕ) ∧ t.ph = Phase.I ∧ (t.i : ℕ) = (s.i : ℕ) ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) ∧ (t.cnt : ℕ) = (s.cnt : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ) + 1 ∧
      (t.flag = true ↔ (s.flag = true ∨ (s.u : ℕ) = (s.v : ℕ) ∨ G.Ed b (s.u : ℕ) (s.v : ℕ))))
  ∨ -- T9: the inner loop is finished and all vertices were counted
  (s.ph = Phase.I ∧ (s.u : ℕ) = G.N ∧ (s.c : ℕ) = (s.r : ℕ) ∧ t.ph = Phase.O ∧
      (t.i : ℕ) = (s.i : ℕ) ∧ (t.r : ℕ) = (s.r : ℕ) ∧ (t.v : ℕ) = (s.v : ℕ) + 1 ∧
      (t.cnt : ℕ) = (s.cnt : ℕ) + (if s.flag then 1 else 0))
  ∨ -- T10: skip `u` in the final loop
  (s.ph = Phase.F ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.F ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ))
  ∨ -- T11: claim that `u` is reachable and start guessing a path
  (s.ph = Phase.F ∧ (s.u : ℕ) < G.N ∧ t.ph = Phase.WF ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ (t.w : ℕ) = G.st0 ∧ (t.d : ℕ) = 0)
  ∨ -- T12: follow an edge of the guessed path
  (s.ph = Phase.WF ∧ (s.d : ℕ) < G.N ∧ t.ph = Phase.WF ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ (t.d : ℕ) = (s.d : ℕ) + 1 ∧
      G.Ed b (s.w : ℕ) (t.w : ℕ))
  ∨ -- T13: stay where we are
  (s.ph = Phase.WF ∧ (s.d : ℕ) < G.N ∧ t.ph = Phase.WF ∧ (t.r : ℕ) = (s.r : ℕ) ∧
      (t.u : ℕ) = (s.u : ℕ) ∧ (t.c : ℕ) = (s.c : ℕ) ∧ (t.d : ℕ) = (s.d : ℕ) + 1 ∧
      (t.w : ℕ) = (s.w : ℕ))
  ∨ -- T14: the path reached `u`, which is not accepting; count it
  (s.ph = Phase.WF ∧ (s.w : ℕ) = (s.u : ℕ) ∧ ¬ G.accV (s.u : ℕ) ∧ t.ph = Phase.F ∧
      (t.r : ℕ) = (s.r : ℕ) ∧ (t.u : ℕ) = (s.u : ℕ) + 1 ∧ (t.c : ℕ) = (s.c : ℕ) + 1)
  ∨ -- T15: all reachable vertices have been seen and none of them accepts
  (s.ph = Phase.F ∧ (s.u : ℕ) = G.N ∧ (s.c : ℕ) = (s.r : ℕ) ∧ t.ph = Phase.A)

/-- A state in the outer loop. -/
def mkO (i r v cnt : ℕ) : Aux G.N :=
  { ph := Phase.O, i := fv G.N i, r := fv G.N r, v := fv G.N v, cnt := fv G.N cnt,
    u := fv G.N 0, c := fv G.N 0, w := fv G.N G.st0, d := fv G.N 0, flag := false }

/-- A state in the inner loop. -/
def mkI (i r v cnt u c : ℕ) (flag : Bool) : Aux G.N :=
  { ph := Phase.I, i := fv G.N i, r := fv G.N r, v := fv G.N v, cnt := fv G.N cnt,
    u := fv G.N u, c := fv G.N c, w := fv G.N G.st0, d := fv G.N 0, flag := flag }

/-- A state verifying a guessed path inside the inner loop. -/
def mkW (i r v cnt u c : ℕ) (flag : Bool) (w d : ℕ) : Aux G.N :=
  { ph := Phase.W, i := fv G.N i, r := fv G.N r, v := fv G.N v, cnt := fv G.N cnt,
    u := fv G.N u, c := fv G.N c, w := fv G.N w, d := fv G.N d, flag := flag }

/-- A state in the final loop. -/
def mkF (r u c : ℕ) : Aux G.N :=
  { ph := Phase.F, i := fv G.N 0, r := fv G.N r, v := fv G.N 0, cnt := fv G.N 0,
    u := fv G.N u, c := fv G.N c, w := fv G.N G.st0, d := fv G.N 0, flag := false }

/-- A state verifying a guessed path inside the final loop. -/
def mkWF (r u c w d : ℕ) : Aux G.N :=
  { ph := Phase.WF, i := fv G.N 0, r := fv G.N r, v := fv G.N 0, cnt := fv G.N 0,
    u := fv G.N u, c := fv G.N c, w := fv G.N w, d := fv G.N d, flag := false }

/-- The accepting state. -/
def mkA : Aux G.N :=
  { ph := Phase.A, i := fv G.N 0, r := fv G.N 0, v := fv G.N 0, cnt := fv G.N 0,
    u := fv G.N 0, c := fv G.N 0, w := fv G.N G.st0, d := fv G.N 0, flag := false }

/-- The initial state of the counting machine. -/
def startA : Aux G.N := mkO G 0 1 0 0

/-- The counting machine associated with a configuration graph. -/
noncomputable def machine : NBP where
  State := Aux G.N
  fintypeState := inferInstance
  read s := G.pos (s.w : ℕ)
  step := stepA G
  start := startA G
  acc s := s.ph = Phase.A

@[simp] lemma machine_size : (machine G).size = Fintype.card (Aux G.N) := rfl

end Machine

end IS
end CS

import Mathlib

/-!
# The machine model : polynomial size nondeterministic branching programs

This file sets up the computational model used to state `NL = coNL`.

A *nondeterministic branching program* (`CS.NBP`) has a finite set of states.  Each state
carries a position `read` of the input tape; a transition out of a state may depend on the
input only through the symbol found at that position (`none` if the position is beyond the
end of the input).  A word is accepted if some accepting state is reachable from the start
state.

The class `CS.NL` consists of the languages `L ⊆ List Bool` for which there is a family of
such programs, one for each input length, of size polynomial in the input length, accepting
exactly the words of `L`.  This is the standard (non-uniform) characterisation of
nondeterministic logarithmic space: a nondeterministic machine using space `s(n)` has
`2^{O(s(n))}` configurations, and the configuration graph is exactly a nondeterministic
branching program of that size.
-/

open scoped Classical

namespace CS

/-- A nondeterministic branching program: a finite state set, a position of the input tape
read at each state, a nondeterministic transition relation depending on the symbol read,
a start state and a set of accepting states. -/
structure NBP where
  /-- The (finite) set of states. -/
  State : Type
  /-- Finiteness of the state set. -/
  fintypeState : Fintype State
  /-- The input position which is read at a given state. -/
  read : State → ℕ
  /-- The transition relation: `step q b q'` says that from `q`, having read the symbol `b`,
  the program may move to `q'`. -/
  step : State → Option Bool → State → Prop
  /-- The initial state. -/
  start : State
  /-- The accepting states. -/
  acc : State → Prop

attribute [instance] NBP.fintypeState

/-- The size of a branching program is its number of states. -/
def NBP.size (M : NBP) : ℕ := Fintype.card M.State

/-- The configuration graph of `M` on the input `x`. -/
def NBP.edge (M : NBP) (x : List Bool) (q q' : M.State) : Prop :=
  M.step q x[M.read q]? q'

/-- `M` accepts `x` if some accepting state is reachable from the start state in the
configuration graph of `M` on `x`. -/
def NBP.Accepts (M : NBP) (x : List Bool) : Prop :=
  ∃ q, M.acc q ∧ Relation.ReflTransGen (M.edge x) M.start q

/-- The class `NL`: languages decided by a polynomial size family of nondeterministic
branching programs. -/
def NL (L : Set (List Bool)) : Prop :=
  ∃ (M : ℕ → NBP) (c k : ℕ), (∀ n, (M n).size ≤ c * (n + 1) ^ k) ∧
    ∀ x : List Bool, (x ∈ L ↔ (M x.length).Accepts x)

/-- The class `coNL`: complements of languages in `NL`. -/
def coNL (L : Set (List Bool)) : Prop := NL Lᶜ

end CS

import RequestProject.Soundness

/-!
# Completeness of the counting machine

If no accepting vertex of the configuration graph is reachable, then the counting machine
has an accepting run.  This is the direction which uses the actual inductive counting
algorithm: in the run we guess, for each round `i`, the set of vertices reachable in at
most `i` steps together with the certifying paths, and we check the guesses against the
previously computed cardinality.
-/

open scoped Classical

namespace CS
namespace IS

open Data

variable {G : Data} {x : List Bool}

/-- Runs of the counting machine. -/
abbrev MR (G : Data) (x : List Bool) (s t : Aux G.N) : Prop :=
  Relation.ReflTransGen ((machine G).edge x) s t

/-- Discharges the arithmetic side conditions about the fields of the states. -/
macro "mkfin" : tactic =>
  `(tactic| first
      | rfl
      | (simp only [mkO, mkI, mkW, mkF, mkWF, mkA, fv]; try omega))

lemma edge_iff {s t : Aux G.N} :
    (machine G).edge x s t ↔ stepA G s x[G.pos (s.w : ℕ)]? t := Iff.rfl

/-- Has a witness for `v` been found among the vertices `< u`? -/
noncomputable def flagOf (G : Data) (x : List Bool) (i u v : ℕ) : Bool :=
  decide (∃ y, y < u ∧ G.Rch x i y ∧ (y = v ∨ G.edg x y v))

@[simp] lemma flagOf_zero (i v : ℕ) : flagOf G x i 0 v = false := by
  simp [flagOf]

lemma flagOf_succ_of_not {i u v : ℕ} (h : ¬ G.Rch x i u) :
    flagOf G x i (u + 1) v = flagOf G x i u v := by
  unfold flagOf
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, hy, hy2, hy3⟩
    rcases Nat.lt_or_ge y u with h' | h'
    · exact ⟨y, h', hy2, hy3⟩
    · have : y = u := by omega
      exact absurd (this ▸ hy2) h
  · rintro ⟨y, hy, hy2, hy3⟩
    exact ⟨y, by omega, hy2, hy3⟩

lemma flagOf_succ_of {i u v : ℕ} (h : G.Rch x i u) :
    flagOf G x i (u + 1) v = (flagOf G x i u v || decide (u = v ∨ G.edg x u v)) := by
  unfold flagOf
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq, Bool.or_eq_true]
  constructor
  · rintro ⟨y, hy, hy2, hy3⟩
    rcases Nat.lt_or_ge y u with h' | h'
    · exact Or.inl ⟨y, h', hy2, hy3⟩
    · have hyu : y = u := by omega
      subst hyu
      exact Or.inr hy3
  · rintro (⟨y, hy, hy2, hy3⟩ | hc)
    · exact ⟨y, by omega, hy2, hy3⟩
    · exact ⟨u, by omega, h, hc⟩

lemma flagOf_N {i v : ℕ} : flagOf G x i G.N v = decide (G.Rch x (i + 1) v) := by
  unfold flagOf
  rw [Bool.eq_iff_iff]
  simp only [decide_eq_true_eq]
  constructor
  · rintro ⟨y, _, hy2, hy3 | hy3⟩
    · exact Rch_succ_of (hy3 ▸ hy2)
    · exact Rch_step hy2 hy3
  · rintro (hv | ⟨y, hy, he⟩)
    · exact ⟨v, Rch_lt hv, hv, Or.inl rfl⟩
    · exact ⟨y, Rch_lt hy, hy, Or.inr he⟩

section Fields

variable (G)

@[simp] lemma mkO_ph (i r v cnt : ℕ) : (mkO G i r v cnt).ph = Phase.O := rfl
@[simp] lemma mkI_ph (i r v cnt u c : ℕ) (f : Bool) : (mkI G i r v cnt u c f).ph = Phase.I := rfl
@[simp] lemma mkW_ph (i r v cnt u c : ℕ) (f : Bool) (w d : ℕ) :
    (mkW G i r v cnt u c f w d).ph = Phase.W := rfl
@[simp] lemma mkF_ph (r u c : ℕ) : (mkF G r u c).ph = Phase.F := rfl
@[simp] lemma mkWF_ph (r u c w d : ℕ) : (mkWF G r u c w d).ph = Phase.WF := rfl
@[simp] lemma mkA_ph : (mkA G).ph = Phase.A := rfl

end Fields

/-- Values of the fields of the states are the expected ones (all our values are `≤ N+1`). -/
lemma fv_eq {k : ℕ} (h : k ≤ G.N + 1) : ((fv G.N k : Fin (G.N + 2)) : ℕ) = k := fv_val h

/-- A guessed path can be followed by the machine inside the inner loop. -/
lemma walk_reach (i r v cnt u c : ℕ) (flag : Bool) (hi : i ≤ G.N) :
    ∀ d w, d ≤ i → G.Rch x d w →
      MR G x (mkW G i r v cnt u c flag G.st0 0) (mkW G i r v cnt u c flag w d) := by
  intro d
  induction d with
  | zero =>
      intro w _ hw
      rw [Rch_zero] at hw
      subst hw
      exact Relation.ReflTransGen.refl
  | succ d ih =>
      intro w hd hw
      rcases hw with hw | ⟨y, hy, hedge⟩
      · -- stay where we are
        refine Relation.ReflTransGen.tail (ih w (by omega) hw) ?_
        rw [edge_iff]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, rfl⟩))))))
        · mkfin
        · mkfin
      · -- follow an edge
        have hyN : y < G.N := Rch_lt hy
        have hwN : w < G.N := (G.hEd _ _ _ hedge).2
        refine Relation.ReflTransGen.tail (ih y (by omega) hy) ?_
        rw [edge_iff]
        have hwy : ((mkW G i r v cnt u c flag y d).w : ℕ) = y := by
          simp only [mkW, fv]; omega
        rw [hwy]
        refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩)))))
        · mkfin
        · mkfin
        · have h1 : ((mkW G i r v cnt u c flag y d).w : ℕ) = y := by
            simp only [mkW, fv]; omega
          have h2 : ((mkW G i r v cnt u c flag w (d + 1)).w : ℕ) = w := by
            simp only [mkW, fv]; omega
          rw [h1, h2]
          exact hedge

/-- One iteration of the inner loop, when the vertex `u` is claimed (and is) reachable. -/
lemma claim_reach {i r v cnt u c : ℕ} {flag : Bool} (hi : i ≤ G.N) (hu : u < G.N) (hc : c ≤ G.N)
    (hv : v < G.N) (hru : G.Rch x i u) :
    MR G x (mkI G i r v cnt u c flag)
      (mkI G i r v cnt (u + 1) (c + 1) (flag || decide (u = v ∨ G.edg x u v))) := by
  have hst0 := G.hst0
  have step1 : (machine G).edge x (mkI G i r v cnt u c flag)
      (mkW G i r v cnt u c flag G.st0 0) := by
    rw [edge_iff]
    refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩))))
    · mkfin
    · mkfin
    · mkfin
  have step2 : MR G x (mkW G i r v cnt u c flag G.st0 0) (mkW G i r v cnt u c flag u i) :=
    walk_reach i r v cnt u c flag hi i u le_rfl hru
  refine Relation.ReflTransGen.tail (Relation.ReflTransGen.trans
    (Relation.ReflTransGen.single step1) step2) ?_
  rw [edge_iff]
  have hwu : ((mkW G i r v cnt u c flag u i).w : ℕ) = u := by simp only [mkW, fv]; omega
  rw [hwu]
  refine Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
    ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩)))))))
  · mkfin
  · mkfin
  · mkfin
  · have h1 : ((mkW G i r v cnt u c flag u i).u : ℕ) = u := by simp only [mkW, fv]; omega
    have h2 : ((mkW G i r v cnt u c flag u i).v : ℕ) = v := by simp only [mkW, fv]; omega
    rw [h1, h2]
    simp only [mkW, mkI, Bool.or_eq_true, decide_eq_true_eq]
    exact Iff.rfl

/-- The inner loop: starting at the vertex `u` with a correct count, the machine reaches the
outer loop state for the next vertex `v+1`. -/
lemma inner_reach {i r v cnt : ℕ} (hi : i ≤ G.N) (hr : r = G.cnt x i G.N) (hv : v < G.N)
    (hcnt : cnt = G.cnt x (i + 1) v) :
    ∀ k u, u + k = G.N →
      MR G x (mkI G i r v cnt u (G.cnt x i u) (flagOf G x i u v))
        (mkO G i r (v + 1) (G.cnt x (i + 1) (v + 1))) := by
  intro k
  induction k with
  | zero =>
      intro u hu
      have huN : u = G.N := by omega
      subst huN
      have hb : G.cnt x (i + 1) (v + 1) ≤ G.N := le_trans (cnt_le _ _) (by omega)
      have hb2 : G.cnt x (i + 1) v ≤ G.N := le_trans (cnt_le _ _) (by omega)
      have hb3 : G.cnt x i u ≤ G.N := cnt_le _ _
      refine Relation.ReflTransGen.single ?_
      rw [edge_iff]
      refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, ?_, rfl, rfl, rfl, ?_, ?_⟩
      · mkfin
      · mkfin
      · mkfin
      · have h1 : G.cnt x (i + 1) (v + 1)
            = G.cnt x (i + 1) v + (if G.Rch x (i + 1) v then 1 else 0) := cnt_succ_index _ _
        simp only [mkI, mkO, fv, flagOf_N, decide_eq_true_eq]
        by_cases hP : G.Rch x (i + 1) v
        · rw [if_pos hP] at h1 ⊢
          omega
        · rw [if_neg hP] at h1 ⊢
          omega
  | succ k ih =>
      intro u hu
      have huN : u < G.N := by omega
      have hcu : G.cnt x i u ≤ G.N := cnt_le _ _
      by_cases hru : G.Rch x i u
      · have hcs : G.cnt x i (u + 1) = G.cnt x i u + 1 := by
          rw [cnt_succ_index, if_pos hru]
        have hfs : flagOf G x i (u + 1) v
            = (flagOf G x i u v || decide (u = v ∨ G.edg x u v)) := flagOf_succ_of hru
        refine Relation.ReflTransGen.trans (claim_reach hi huN hcu hv hru) ?_
        rw [← hcs, ← hfs]
        exact ih (u + 1) (by omega)
      · have hcs : G.cnt x i (u + 1) = G.cnt x i u := by rw [cnt_succ_index, if_neg hru]
        have hfs : flagOf G x i (u + 1) v = flagOf G x i u v := flagOf_succ_of_not hru
        have hstep : (machine G).edge x (mkI G i r v cnt u (G.cnt x i u) (flagOf G x i u v))
            (mkI G i r v cnt (u + 1) (G.cnt x i u) (flagOf G x i u v)) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl⟩
          · mkfin
          · mkfin
        refine Relation.ReflTransGen.head hstep ?_
        rw [← hcs, ← hfs]
        exact ih (u + 1) (by omega)

/-- The outer loop: one full round of the counting algorithm. -/
lemma outer_reach {i r : ℕ} (hi : i ≤ G.N) (hr : r = G.cnt x i G.N) :
    ∀ k v, v + k = G.N →
      MR G x (mkO G i r v (G.cnt x (i + 1) v)) (mkO G i r G.N (G.cnt x (i + 1) G.N)) := by
  intro k
  induction k with
  | zero =>
      intro v hv
      have : v = G.N := by omega
      subst this
      exact Relation.ReflTransGen.refl
  | succ k ih =>
      intro v hv
      have hvN : v < G.N := by omega
      have hb : G.cnt x (i + 1) v ≤ G.N := le_trans (cnt_le _ _) (by omega)
      have hstep : (machine G).edge x (mkO G i r v (G.cnt x (i + 1) v))
          (mkI G i r v (G.cnt x (i + 1) v) 0 0 false) := by
        rw [edge_iff]
        refine Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, rfl, ?_, ?_, rfl⟩
        · mkfin
        · mkfin
        · mkfin
      refine Relation.ReflTransGen.head hstep ?_
      have hstart : mkI G i r v (G.cnt x (i + 1) v) 0 0 false
          = mkI G i r v (G.cnt x (i + 1) v) 0 (G.cnt x i 0) (flagOf G x i 0 v) := by
        rw [cnt_zero_index, flagOf_zero]
      rw [hstart]
      exact Relation.ReflTransGen.trans (inner_reach hi hr hvN rfl G.N 0 (by omega))
        (ih (v + 1) (by omega))

/-- All the rounds of the counting algorithm. -/
lemma round_reach : ∀ m i, i + m = G.N →
    MR G x (mkO G i (G.cnt x i G.N) 0 0) (mkO G G.N (G.cnt x G.N G.N) 0 0) := by
  intro m
  induction m with
  | zero =>
      intro i hi
      have : i = G.N := by omega
      subst this
      exact Relation.ReflTransGen.refl
  | succ m ih =>
      intro i hi
      have hiN : i < G.N := by omega
      have hb : G.cnt x (i + 1) G.N ≤ G.N := cnt_le _ _
      have hb2 : G.cnt x i G.N ≤ G.N := cnt_le _ _
      have h1 : MR G x (mkO G i (G.cnt x i G.N) 0 0)
          (mkO G i (G.cnt x i G.N) G.N (G.cnt x (i + 1) G.N)) := by
        have h := outer_reach (G := G) (x := x) (i := i) (r := G.cnt x i G.N) (by omega) rfl
          G.N 0 (by omega)
        rwa [cnt_zero_index] at h
      have hstep : (machine G).edge x (mkO G i (G.cnt x i G.N) G.N (G.cnt x (i + 1) G.N))
          (mkO G (i + 1) (G.cnt x (i + 1) G.N) 0 0) := by
        rw [edge_iff]
        refine Or.inr <| Or.inl ⟨rfl, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
        · mkfin
        · mkfin
        · mkfin
        · mkfin
        · mkfin
        · mkfin
      exact Relation.ReflTransGen.trans h1
        (Relation.ReflTransGen.head hstep (ih (i + 1) (by omega)))

/-- A guessed path can be followed by the machine inside the final loop. -/
lemma walkF_reach (r u c : ℕ) :
    ∀ d w, d ≤ G.N → G.Rch x d w → MR G x (mkWF G r u c G.st0 0) (mkWF G r u c w d) := by
  intro d
  induction d with
  | zero =>
      intro w _ hw
      rw [Rch_zero] at hw
      subst hw
      exact Relation.ReflTransGen.refl
  | succ d ih =>
      intro w hd hw
      rcases hw with hw | ⟨y, hy, hedge⟩
      · refine Relation.ReflTransGen.tail (ih w (by omega) hw) ?_
        rw [edge_iff]
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, rfl⟩
        · mkfin
        · mkfin
      · have hyN : y < G.N := Rch_lt hy
        have hwN : w < G.N := (G.hEd _ _ _ hedge).2
        refine Relation.ReflTransGen.tail (ih y (by omega) hy) ?_
        rw [edge_iff]
        have hwy : ((mkWF G r u c y d).w : ℕ) = y := by mkfin
        rw [hwy]
        refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
        · mkfin
        · mkfin
        · have h1 : ((mkWF G r u c y d).w : ℕ) = y := by mkfin
          have h2 : ((mkWF G r u c w (d + 1)).w : ℕ) = w := by mkfin
          rw [h1, h2]
          exact hedge

/-- The final loop: enumerate all reachable vertices, check that none of them accepts, and
accept. -/
lemma final_reach (hnoacc : ¬ ∃ q, G.accV q ∧ G.Rch x G.N q) {r : ℕ}
    (hr : r = G.cnt x G.N G.N) :
    ∀ k u, u + k = G.N → MR G x (mkF G r u (G.cnt x G.N u)) (mkA G) := by
  intro k
  induction k with
  | zero =>
      intro u hu
      have huN : u = G.N := by omega
      subst huN
      have hb : G.cnt x u u ≤ G.N := cnt_le _ _
      refine Relation.ReflTransGen.single ?_
      rw [edge_iff]
      refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| ⟨rfl, ?_, ?_, rfl⟩
      · mkfin
      · mkfin
  | succ k ih =>
      intro u hu
      have huN : u < G.N := by omega
      have hcu : G.cnt x G.N u ≤ G.N := le_trans (cnt_le _ _) (by omega)
      by_cases hru : G.Rch x G.N u
      · have hacc : ¬ G.accV u := fun hc => hnoacc ⟨u, hc, hru⟩
        have hcs : G.cnt x G.N (u + 1) = G.cnt x G.N u + 1 := by
          rw [cnt_succ_index, if_pos hru]
        have hst0 := G.hst0
        have step1 : (machine G).edge x (mkF G r u (G.cnt x G.N u))
            (mkWF G r u (G.cnt x G.N u) G.st0 0) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, rfl, rfl, ?_, ?_⟩
          · mkfin
          · mkfin
          · mkfin
        have step2 : MR G x (mkWF G r u (G.cnt x G.N u) G.st0 0)
            (mkWF G r u (G.cnt x G.N u) u G.N) := walkF_reach r u _ G.N u le_rfl hru
        have step3 : (machine G).edge x (mkWF G r u (G.cnt x G.N u) u G.N)
            (mkF G r (u + 1) (G.cnt x G.N u + 1)) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, ?_, rfl, rfl, ?_, ?_⟩
          · mkfin
          · have h1 : ((mkWF G r u (G.cnt x G.N u) u G.N).u : ℕ) = u := by mkfin
            rw [h1]
            exact hacc
          · mkfin
          · mkfin
        refine Relation.ReflTransGen.trans (Relation.ReflTransGen.single step1)
          (Relation.ReflTransGen.trans step2 (Relation.ReflTransGen.head step3 ?_))
        rw [← hcs]
        exact ih (u + 1) (by omega)
      · have hcs : G.cnt x G.N (u + 1) = G.cnt x G.N u := by rw [cnt_succ_index, if_neg hru]
        have hstep : (machine G).edge x (mkF G r u (G.cnt x G.N u))
            (mkF G r (u + 1) (G.cnt x G.N u)) := by
          rw [edge_iff]
          refine Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, rfl, ?_, rfl⟩
          · mkfin
          · mkfin
        refine Relation.ReflTransGen.head hstep ?_
        rw [← hcs]
        exact ih (u + 1) (by omega)

/-- Completeness: if no accepting vertex is reachable, the counting machine accepts. -/
theorem machine_complete (hnoacc : ¬ ∃ q, G.accV q ∧ G.Reachable x q) :
    (machine G).Accepts x := by
  have hn : ¬ ∃ q, G.accV q ∧ G.Rch x G.N q := by
    rintro ⟨q, hq, hqr⟩
    exact hnoacc ⟨q, hq, (Rch_iff_reachable q).1 hqr⟩
  refine ⟨mkA G, rfl, ?_⟩
  show MR G x (startA G) (mkA G)
  have hb : G.cnt x G.N G.N ≤ G.N := cnt_le _ _
  have h0 : startA G = mkO G 0 (G.cnt x 0 G.N) 0 0 := by
    rw [cnt_zero_eq]; rfl
  rw [h0]
  refine Relation.ReflTransGen.trans (round_reach G.N 0 (by omega)) ?_
  have hstep : (machine G).edge x (mkO G G.N (G.cnt x G.N G.N) 0 0)
      (mkF G (G.cnt x G.N G.N) 0 0) := by
    rw [edge_iff]
    refine Or.inr <| Or.inr <| Or.inl ⟨rfl, ?_, rfl, ?_, ?_, ?_⟩
    · mkfin
    · mkfin
    · mkfin
    · mkfin
  refine Relation.ReflTransGen.head hstep ?_
  have h1 : mkF G (G.cnt x G.N G.N) 0 0 = mkF G (G.cnt x G.N G.N) 0 (G.cnt x G.N 0) := by
    rw [cnt_zero_index]
  rw [h1]
  exact final_reach hn rfl G.N 0 (by omega)

end IS
end CS

import RequestProject.Model

/-!
# Bounded reachability in a configuration graph

We work with an abstract configuration graph whose vertices are the natural numbers
`< N` (packaged in the structure `CS.IS.Data`).  `Ed b u v` says that there is an edge from
`u` to `v` when the symbol read at `u` is `b`; the symbol actually read is the one at input
position `pos u`.

`G.Rch x i v` says that `v` is reachable from the start vertex `st0` in at most `i` steps.
The main result of this file is `Data.Rch_iff_reachable`: reachability is the same thing as
reachability in at most `N` steps.
-/

open scoped Classical

namespace CS
namespace IS

/-- An (input dependent) configuration graph on the vertex set `{0, …, N-1}`. -/
structure Data where
  /-- number of vertices -/
  N : ℕ
  /-- the start vertex -/
  st0 : ℕ
  /-- the input position read at a vertex -/
  pos : ℕ → ℕ
  /-- the edge relation, depending on the symbol read at the source vertex -/
  Ed : Option Bool → ℕ → ℕ → Prop
  /-- the accepting vertices -/
  accV : ℕ → Prop
  /-- the start vertex is a vertex -/
  hst0 : st0 < N
  /-- edges only connect vertices -/
  hEd : ∀ b u v, Ed b u v → u < N ∧ v < N

namespace Data

variable (G : Data) (x : List Bool)

/-- The edge relation of the configuration graph on input `x`. -/
def edg (u v : ℕ) : Prop := G.Ed x[G.pos u]? u v

/-- `G.Rch x i v`: the vertex `v` is reachable from `G.st0` in at most `i` steps. -/
def Rch (G : Data) (x : List Bool) : ℕ → ℕ → Prop
  | 0, v => v = G.st0
  | (i + 1), v => Rch G x i v ∨ ∃ u, Rch G x i u ∧ G.edg x u v

/-- Reachability in the configuration graph. -/
def Reachable (v : ℕ) : Prop := Relation.ReflTransGen (G.edg x) G.st0 v

variable {G x}

lemma Rch_zero {v : ℕ} : G.Rch x 0 v ↔ v = G.st0 := Iff.rfl

lemma Rch_succ {i v : ℕ} :
    G.Rch x (i + 1) v ↔ G.Rch x i v ∨ ∃ u, G.Rch x i u ∧ G.edg x u v := Iff.rfl

lemma Rch_succ_of {i v : ℕ} (h : G.Rch x i v) : G.Rch x (i + 1) v := Or.inl h

lemma Rch_mono {i j v : ℕ} (hij : i ≤ j) (h : G.Rch x i v) : G.Rch x j v := by
  induction j with
  | zero =>
      have hi : i = 0 := by omega
      subst hi; exact h
  | succ j ih =>
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · exact Rch_succ_of (ih (by omega))
      · have : i = j + 1 := by omega
        subst this; exact h

lemma Rch_start : G.Rch x 0 G.st0 := rfl

lemma Rch_step {i u v : ℕ} (h : G.Rch x i u) (he : G.edg x u v) : G.Rch x (i + 1) v :=
  Or.inr ⟨u, h, he⟩

/-- Every reachable vertex is a genuine vertex. -/
lemma Rch_lt : ∀ {i v : ℕ}, G.Rch x i v → v < G.N := by
  intro i
  induction i with
  | zero => intro v hv; rw [Rch_zero] at hv; have := G.hst0; omega
  | succ i ih =>
      intro v hv
      rcases hv with hv | ⟨u, _, he⟩
      · exact ih hv
      · exact (G.hEd _ _ _ he).2

variable (G x)

/-- The number of vertices `< k` reachable in at most `i` steps. -/
noncomputable def cnt (i k : ℕ) : ℕ :=
  ((Finset.range k).filter (fun v => G.Rch x i v)).card

variable {G x}

@[simp] lemma cnt_zero_index (i : ℕ) : G.cnt x i 0 = 0 := by simp [cnt]

lemma cnt_succ_index (i k : ℕ) :
    G.cnt x i (k + 1) = G.cnt x i k + (if G.Rch x i k then 1 else 0) := by
  classical
  unfold cnt
  rw [Finset.range_add_one, Finset.filter_insert]
  by_cases h : G.Rch x i k
  · simp [h, Finset.card_insert_of_notMem]
  · simp [h]

/-- If reachability in `i+1` steps coincides with reachability in `i` steps, it stays so. -/
lemma Rch_stab (i : ℕ) (h : ∀ v, G.Rch x (i + 1) v → G.Rch x i v) :
    ∀ j v, i ≤ j → G.Rch x j v → G.Rch x i v := by
  intro j
  induction j with
  | zero => intro v hij hv; interval_cases i; exact hv
  | succ j ih =>
      intro v hij hv
      rcases Nat.lt_or_ge i (j + 1) with h' | h'
      · have hij' : i ≤ j := by omega
        rcases hv with hv | ⟨u, hu, he⟩
        · exact ih v hij' hv
        · exact h v (Rch_step (ih u hij' hu) he)
      · have : i = j + 1 := by omega
        subst this; exact hv

lemma cnt_le (i k : ℕ) : G.cnt x i k ≤ k := by
  classical
  unfold cnt
  calc ((Finset.range k).filter (fun v => G.Rch x i v)).card
      ≤ (Finset.range k).card := Finset.card_filter_le _ _
    _ = k := by simp

lemma cnt_zero_eq : G.cnt x 0 G.N = 1 := by
  classical
  unfold cnt
  have : (Finset.range G.N).filter (fun v => G.Rch x 0 v) = {G.st0} := by
    ext v
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
    constructor
    · rintro ⟨-, hv⟩; exact hv
    · rintro rfl; exact ⟨G.hst0, rfl⟩
  rw [this]; simp

lemma cnt_mono_step (i : ℕ) : G.cnt x i G.N ≤ G.cnt x (i + 1) G.N := by
  classical
  unfold cnt
  apply Finset.card_le_card
  intro v hv
  simp only [Finset.mem_filter, Finset.mem_range] at hv ⊢
  exact ⟨hv.1, Rch_succ_of hv.2⟩

lemma cnt_lt_of_not_stab (i : ℕ) (h : ¬ ∀ v, G.Rch x (i + 1) v → G.Rch x i v) :
    G.cnt x i G.N < G.cnt x (i + 1) G.N := by
  classical
  push_neg at h
  obtain ⟨v, hv1, hv2⟩ := h
  unfold cnt
  apply Finset.card_lt_card
  refine ⟨?_, ?_⟩
  · intro w hw
    simp only [Finset.mem_filter, Finset.mem_range] at hw ⊢
    exact ⟨hw.1, Rch_succ_of hw.2⟩
  · intro hsub
    have hvmem : v ∈ (Finset.range G.N).filter (fun w => G.Rch x (i + 1) w) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨Rch_lt hv1, hv1⟩
    have := hsub hvmem
    simp only [Finset.mem_filter, Finset.mem_range] at this
    exact hv2 this.2

/-- There is a stabilisation point below `N`. -/
lemma exists_stab : ∃ i < G.N, ∀ v, G.Rch x (i + 1) v → G.Rch x i v := by
  classical
  by_contra hcon
  push_neg at hcon
  have key : ∀ m, m ≤ G.N → m + 1 ≤ G.cnt x m G.N := by
    intro m
    induction m with
    | zero => intro _; rw [cnt_zero_eq]
    | succ m ih =>
        intro hm
        have h1 := ih (by omega)
        have h2 : ¬ ∀ v, G.Rch x (m + 1) v → G.Rch x m v := by
          intro hstab
          obtain ⟨v, hv1, hv2⟩ := hcon m (by omega)
          exact hv2 (hstab v hv1)
        have := cnt_lt_of_not_stab (G := G) (x := x) m h2
        omega
  have h1 := key G.N le_rfl
  have h2 := cnt_le (G := G) (x := x) G.N G.N
  omega

/-- Reachability in the configuration graph is the same as reachability in at most `N` steps. -/
lemma Rch_iff_reachable (v : ℕ) : G.Rch x G.N v ↔ G.Reachable x v := by
  constructor
  · intro h
    have key : ∀ i v, G.Rch x i v → G.Reachable x v := by
      intro i
      induction i with
      | zero => intro v hv; rw [Rch_zero] at hv; subst hv; exact Relation.ReflTransGen.refl
      | succ i ih =>
          intro v hv
          rcases hv with hv | ⟨u, hu, he⟩
          · exact ih v hv
          · exact (ih u hu).tail he
    exact key G.N v h
  · intro h
    obtain ⟨i, hi, hstab⟩ := exists_stab (G := G) (x := x)
    have key : ∀ w, G.Reachable x w → ∃ j, G.Rch x j w := by
      intro w hw
      induction hw with
      | refl => exact ⟨0, Rch_start⟩
      | tail _ he ih =>
          obtain ⟨j, hj⟩ := ih
          exact ⟨j + 1, Rch_step hj he⟩
    obtain ⟨j, hj⟩ := key v h
    rcases Nat.lt_or_ge j G.N with hjN | hjN
    · exact Rch_mono (by omega) hj
    · exact Rch_mono (by omega) (Rch_stab i hstab j v (by omega) hj)

end Data

end IS
end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

