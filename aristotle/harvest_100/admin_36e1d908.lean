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

/-
The inductive counting machine of Immerman and Szelepcsényi, as a transition system on
configurations built from a constant number of counters.

This file is part of the development of the Immerman-Szelepcsényi theorem.
-/
import RequestProject.IS.Machine

namespace CS

open NDM

/-- The control states ("program counter" values) of the inductive counting machine. -/
inductive Mode where
  /-- Outer loop: enumerate the configurations `v`, counting those reachable in `≤ i+1` steps. -/
  | outer
  /-- Verify that `v` is reachable in `≤ i+1` steps, by guessing a path. -/
  | pathA
  /-- Inner loop: enumerate all configurations reachable in `≤ i` steps in order to certify
  that `v` is *not* reachable in `≤ i+1` steps. -/
  | inner
  /-- Verify that `u` is reachable in `≤ i` steps, by guessing a path. -/
  | pathB
  /-- Final loop: enumerate all configurations reachable in `≤ n` steps, checking that none of
  them is accepting. -/
  | final
  /-- Verify that `u` is reachable in `≤ n` steps, by guessing a path. -/
  | pathC
  /-- Accepting state. -/
  | acc
  deriving DecidableEq

/-- A configuration of the inductive counting machine: a control state together with eight
counters, each of which stays `≤ n`. -/
structure Cfg where
  /-- Control state. -/
  mode : Mode
  /-- Current level of the inductive counting. -/
  i : ℕ
  /-- The number of configurations reachable in `≤ i` steps (computed at the previous level). -/
  r : ℕ
  /-- Running count of configurations reachable in `≤ i+1` steps. -/
  c : ℕ
  /-- Outer loop variable. -/
  v : ℕ
  /-- Running count in the inner loop. -/
  b : ℕ
  /-- Inner loop variable. -/
  u : ℕ
  /-- Current configuration of the guessed path. -/
  p : ℕ
  /-- Number of remaining steps of the guessed path. -/
  k : ℕ
  deriving DecidableEq

/-- Outer loop configuration. -/
def outerC (i r c v : ℕ) : Cfg := ⟨Mode.outer, i, r, c, v, 0, 0, 0, 0⟩
/-- Path guessing configuration for the outer loop. -/
def pathAC (i r c v p k : ℕ) : Cfg := ⟨Mode.pathA, i, r, c, v, 0, 0, p, k⟩
/-- Inner loop configuration. -/
def innerC (i r c v b u : ℕ) : Cfg := ⟨Mode.inner, i, r, c, v, b, u, 0, 0⟩
/-- Path guessing configuration for the inner loop. -/
def pathBC (i r c v b u p k : ℕ) : Cfg := ⟨Mode.pathB, i, r, c, v, b, u, p, k⟩
/-- Final loop configuration. -/
def finalC (r b u : ℕ) : Cfg := ⟨Mode.final, 0, r, 0, 0, b, u, 0, 0⟩
/-- Path guessing configuration for the final loop. -/
def pathCC (r b u p k : ℕ) : Cfg := ⟨Mode.pathC, 0, r, 0, 0, b, u, p, k⟩
/-- The accepting configuration. -/
def accC : Cfg := ⟨Mode.acc, 0, 0, 0, 0, 0, 0, 0, 0⟩
/-- The initial configuration. -/
def initC : Cfg := outerC 0 1 0 0

/-- One step of the inductive counting machine. -/
def Step (M : NDM) (x y : Cfg) : Prop :=
  match x with
  | ⟨Mode.outer, i, r, c, v, _, _, _, _⟩ =>
      (v = M.n ∧ i + 1 < M.n ∧ c ≤ M.n ∧ y = outerC (i + 1) c 0 0)
    ∨ (v = M.n ∧ i + 1 = M.n ∧ c ≤ M.n ∧ y = finalC c 0 0)
    ∨ (v < M.n ∧ i < M.n ∧ y = pathAC i r c v M.start (i + 1))
    ∨ (v < M.n ∧ y = innerC i r c v 0 0)
  | ⟨Mode.pathA, i, r, c, v, _, _, p, k⟩ =>
      (p = v ∧ v < M.n ∧ c < M.n ∧ y = outerC i r (c + 1) (v + 1))
    ∨ (0 < k ∧ M.E p y.p = true ∧ y = pathAC i r c v y.p (k - 1))
  | ⟨Mode.inner, i, r, c, v, b, u, _, _⟩ =>
      (u = M.n ∧ b = r ∧ v < M.n ∧ y = outerC i r c (v + 1))
    ∨ (u < M.n ∧ i ≤ M.n ∧ y = pathBC i r c v b u M.start i)
    ∨ (u < M.n ∧ y = innerC i r c v b (u + 1))
  | ⟨Mode.pathB, i, r, c, v, b, u, p, k⟩ =>
      (p = u ∧ u ≠ v ∧ M.E u v = false ∧ u < M.n ∧ b < M.n ∧
        y = innerC i r c v (b + 1) (u + 1))
    ∨ (0 < k ∧ M.E p y.p = true ∧ y = pathBC i r c v b u y.p (k - 1))
  | ⟨Mode.final, _, r, _, _, b, u, _, _⟩ =>
      (u = M.n ∧ b = r ∧ y = accC)
    ∨ (u < M.n ∧ y = pathCC r b u M.start M.n)
    ∨ (u < M.n ∧ y = finalC r b (u + 1))
  | ⟨Mode.pathC, _, r, _, _, b, u, p, k⟩ =>
      (p = u ∧ M.A u = false ∧ u < M.n ∧ b < M.n ∧ y = finalC r (b + 1) (u + 1))
    ∨ (0 < k ∧ M.E p y.p = true ∧ y = pathCC r b u y.p (k - 1))
  | ⟨Mode.acc, _, _, _, _, _, _, _, _⟩ => False

instance decStep (M : NDM) (x y : Cfg) : Decidable (Step M x y) := by
  rcases x with ⟨mode, i, r, c, v, b, u, p, k⟩
  cases mode <;> · unfold Step; infer_instance

/-- `Reaches M x` means that the inductive counting machine can go from configuration `x` to
its accepting state. -/
inductive Reaches (M : NDM) : Cfg → Prop
  | acc {x : Cfg} (h : x.mode = Mode.acc) : Reaches M x
  | step {x y : Cfg} (h : Step M x y) (h2 : Reaches M y) : Reaches M x

/-- The invariant satisfied by all configurations of the inductive counting machine that are
reachable from the initial configuration.  It expresses that the counters really do hold the
quantities they are supposed to hold. -/
def Inv (M : NDM) (x : Cfg) : Prop :=
  match x with
  | ⟨Mode.outer, i, r, c, v, _, _, _, _⟩ =>
      i < M.n ∧ v ≤ M.n ∧ r = M.Cnt i ∧ c = M.CntB (i + 1) v
  | ⟨Mode.pathA, i, r, c, v, _, _, p, k⟩ =>
      i < M.n ∧ v < M.n ∧ r = M.Cnt i ∧ c = M.CntB (i + 1) v ∧ k ≤ i + 1 ∧
        M.reachF (i + 1 - k) M.start p = true
  | ⟨Mode.inner, i, r, c, v, b, u, _, _⟩ =>
      i < M.n ∧ v < M.n ∧ r = M.Cnt i ∧ c = M.CntB (i + 1) v ∧ u ≤ M.n ∧
        b ≤ M.CntP i u (M.PvB v)
  | ⟨Mode.pathB, i, r, c, v, b, u, p, k⟩ =>
      i < M.n ∧ v < M.n ∧ r = M.Cnt i ∧ c = M.CntB (i + 1) v ∧ u < M.n ∧
        b ≤ M.CntP i u (M.PvB v) ∧ k ≤ i ∧ M.reachF (i - k) M.start p = true
  | ⟨Mode.final, _, r, _, _, b, u, _, _⟩ =>
      r = M.Cnt M.n ∧ u ≤ M.n ∧ b ≤ M.CntP M.n u M.PaB
  | ⟨Mode.pathC, _, r, _, _, b, u, p, k⟩ =>
      r = M.Cnt M.n ∧ u < M.n ∧ b ≤ M.CntP M.n u M.PaB ∧ k ≤ M.n ∧
        M.reachF (M.n - k) M.start p = true
  | ⟨Mode.acc, _, _, _, _, _, _, _, _⟩ =>
      ∀ w, M.reachF M.n M.start w = true → M.A w = false

variable {M : NDM}

lemma Inv_initC : Inv M initC := by
  refine ⟨M.hstart.trans_le' (Nat.zero_le _) |>.trans_le' (Nat.zero_le _), Nat.zero_le _, ?_, ?_⟩
  · exact (NDM.Cnt_zero (M := M)).symm
  · exact (M.CntB_zero 1).symm

/-- The key soundness step: the invariant is preserved by the transition relation. -/
lemma Inv_step {x y : Cfg} (hx : Inv M x) (hs : Step M x y) : Inv M y := by
  obtain ⟨mode, i, r, c, v, b, u, p, k⟩ := x
  cases mode
  · -- outer
    simp only [Step] at hs
    obtain ⟨hi, hv, hr, hc⟩ := hx
    rcases hs with ⟨hvn, hin, -, rfl⟩ | ⟨hvn, hin, -, rfl⟩ | ⟨hvn, hin, rfl⟩ | ⟨hvn, rfl⟩
    · refine ⟨hin, Nat.zero_le _, ?_, (M.CntB_zero _).symm⟩
      rw [hc, hvn]; rfl
    · refine ⟨?_, Nat.zero_le _, ?_⟩
      · rw [hc, hvn, hin]; rfl
      · rw [M.CntP_zero]
    · exact ⟨hi, hvn, hr, hc, le_rfl, by rw [Nat.sub_self]; exact reachF_self _ _⟩
    · exact ⟨hi, hvn, hr, hc, Nat.zero_le _, by rw [M.CntP_zero]⟩
  · -- pathA
    simp only [Step] at hs
    obtain ⟨hi, hv, hr, hc, hk, hp⟩ := hx
    rcases hs with ⟨hpv, hvn, -, rfl⟩ | ⟨hk0, he, hy⟩
    · subst hpv
      have hRv : M.reachF (i + 1) M.start p = true := reachF_mono (Nat.sub_le _ _) hp
      refine ⟨hi, by omega, hr, ?_⟩
      rw [M.CntB_succ_of_pos hRv, hc]
    · rw [hy]
      refine ⟨hi, hv, hr, hc, by omega, ?_⟩
      have hkk : i + 1 - (k - 1) = (i + 1 - k) + 1 := by omega
      rw [hkk]
      exact reachF_snoc hp he
  · -- inner
    simp only [Step] at hs
    obtain ⟨hi, hv, hr, hc, hu, hb⟩ := hx
    rcases hs with ⟨hun, hbr, hvn, rfl⟩ | ⟨hun, hin, rfl⟩ | ⟨hun, rfl⟩
    · have h1 : M.CntB i M.n ≤ M.CntP i M.n (M.PvB v) := by
        rw [hun] at hb
        calc M.CntB i M.n = M.Cnt i := rfl
          _ = r := hr.symm
          _ = b := hbr.symm
          _ ≤ _ := hb
      have hall := M.CntP_all h1
      have hnr : M.reachF (i + 1) M.start v ≠ true := by
        intro hcon
        rcases (reachF_succ_back (M := M) i M.start v).1 hcon with h | ⟨w, hw, hrw, hew⟩
        · have hthis := hall v hv h
          rw [NDM.PvB_eq_true] at hthis
          exact absurd rfl hthis.1
        · have hthis := hall w hw hrw
          rw [NDM.PvB_eq_true] at hthis
          rw [hthis.2] at hew
          exact Bool.noConfusion hew
      exact ⟨hi, by omega, hr, by rw [M.CntB_succ_of_neg hnr, hc]⟩
    · exact ⟨hi, hv, hr, hc, hun, hb, le_rfl, by rw [Nat.sub_self]; exact reachF_self _ _⟩
    · exact ⟨hi, hv, hr, hc, by omega, hb.trans (M.CntP_mono (by omega))⟩
  · -- pathB
    simp only [Step] at hs
    obtain ⟨hi, hv, hr, hc, hu, hb, hk, hp⟩ := hx
    rcases hs with ⟨hpu, hne, hE, hun, hbn, rfl⟩ | ⟨hk0, he, hy⟩
    · subst hpu
      have hRu : M.reachF i M.start p = true := reachF_mono (Nat.sub_le _ _) hp
      have hPu : M.PvB v p = true := by simp only [NDM.PvB_eq_true]; exact ⟨hne, hE⟩
      refine ⟨hi, hv, hr, hc, by omega, ?_⟩
      rw [M.CntP_succ_pos hRu hPu]
      omega
    · rw [hy]
      refine ⟨hi, hv, hr, hc, hu, hb, by omega, ?_⟩
      have hkk : i - (k - 1) = (i - k) + 1 := by omega
      rw [hkk]
      exact reachF_snoc hp he
  · -- final
    simp only [Step] at hs
    obtain ⟨hr, hu, hb⟩ := hx
    rcases hs with ⟨hun, hbr, rfl⟩ | ⟨hun, rfl⟩ | ⟨hun, rfl⟩
    · have h1 : M.CntB M.n M.n ≤ M.CntP M.n M.n M.PaB := by
        rw [hun] at hb
        calc M.CntB M.n M.n = M.Cnt M.n := rfl
          _ = r := hr.symm
          _ = b := hbr.symm
          _ ≤ _ := hb
      have hall := M.CntP_all h1
      intro w hw
      have := hall w (reachF_lt hw) hw
      simpa using this
    · exact ⟨hr, hun, hb, le_rfl, by rw [Nat.sub_self]; exact reachF_self _ _⟩
    · exact ⟨hr, by omega, hb.trans (M.CntP_mono (by omega))⟩
  · -- pathC
    simp only [Step] at hs
    obtain ⟨hr, hu, hb, hk, hp⟩ := hx
    rcases hs with ⟨hpu, hA, hun, hbn, rfl⟩ | ⟨hk0, he, hy⟩
    · subst hpu
      have hRu : M.reachF M.n M.start p = true := reachF_mono (Nat.sub_le _ _) hp
      have hPu : M.PaB p = true := by simp only [NDM.PaB_eq_true]; exact hA
      refine ⟨hr, by omega, ?_⟩
      rw [M.CntP_succ_pos hRu hPu]
      omega
    · rw [hy]
      refine ⟨hr, hu, hb, by omega, ?_⟩
      have hkk : M.n - (k - 1) = (M.n - k) + 1 := by omega
      rw [hkk]
      exact reachF_snoc hp he
  · -- acc
    exact absurd hs (by simp [Step])

/-- Soundness: if the inductive counting machine accepts, then `M` has no reachable accepting
configuration. -/
lemma Reaches_sound {x : Cfg} (h : Reaches M x) (hx : Inv M x) :
    ∀ w, M.reachF M.n M.start w = true → M.A w = false := by
  induction h with
  | @acc x hmode =>
    obtain ⟨mode, i, r, c, v, b, u, p, k⟩ := x
    cases mode
    case acc => exact hx
    all_goals simp at hmode
  | step hstep _ ih => exact ih (Inv_step hx hstep)

/-! ### Completeness: the machine accepts whenever `M` rejects -/

lemma pathA_run {i r c v : ℕ} (hv : v < M.n) (hc : c < M.n)
    (hnext : Reaches M (outerC i r (c + 1) (v + 1))) :
    ∀ (k p : ℕ), M.reachF k p v = true → Reaches M (pathAC i r c v p k) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rw [reachF_zero_iff] at hp
    subst hp
    refine Reaches.step ?_ hnext
    simp only [Step, pathAC]
    exact Or.inl ⟨trivial, hv, hc, trivial⟩
  | succ k ih =>
    intro p hp
    rw [reachF_succ_iff] at hp
    rcases hp with rfl | ⟨q, hq, he, hr⟩
    · refine Reaches.step ?_ hnext
      simp only [Step, pathAC]
      exact Or.inl ⟨trivial, hv, hc, trivial⟩
    · refine Reaches.step (y := pathAC i r c v q k) ?_ (ih q hr)
      simp only [Step, pathAC]
      exact Or.inr ⟨Nat.succ_pos k, he, rfl⟩

lemma pathB_run {i r c v b u : ℕ} (hne : u ≠ v) (hE : M.E u v = false) (hu : u < M.n)
    (hb : b < M.n) (hnext : Reaches M (innerC i r c v (b + 1) (u + 1))) :
    ∀ (k p : ℕ), M.reachF k p u = true → Reaches M (pathBC i r c v b u p k) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rw [reachF_zero_iff] at hp
    subst hp
    refine Reaches.step ?_ hnext
    simp only [Step, pathBC]
    exact Or.inl ⟨trivial, hne, hE, hu, hb, trivial⟩
  | succ k ih =>
    intro p hp
    rw [reachF_succ_iff] at hp
    rcases hp with rfl | ⟨q, hq, he, hr⟩
    · refine Reaches.step ?_ hnext
      simp only [Step, pathBC]
      exact Or.inl ⟨trivial, hne, hE, hu, hb, trivial⟩
    · refine Reaches.step (y := pathBC i r c v b u q k) ?_ (ih q hr)
      simp only [Step, pathBC]
      exact Or.inr ⟨Nat.succ_pos k, he, rfl⟩

lemma pathC_run {r b u : ℕ} (hA : M.A u = false) (hu : u < M.n) (hb : b < M.n)
    (hnext : Reaches M (finalC r (b + 1) (u + 1))) :
    ∀ (k p : ℕ), M.reachF k p u = true → Reaches M (pathCC r b u p k) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    rw [reachF_zero_iff] at hp
    subst hp
    refine Reaches.step ?_ hnext
    simp only [Step, pathCC]
    exact Or.inl ⟨trivial, hA, hu, hb, trivial⟩
  | succ k ih =>
    intro p hp
    rw [reachF_succ_iff] at hp
    rcases hp with rfl | ⟨q, hq, he, hr⟩
    · refine Reaches.step ?_ hnext
      simp only [Step, pathCC]
      exact Or.inl ⟨trivial, hA, hu, hb, trivial⟩
    · refine Reaches.step (y := pathCC r b u q k) ?_ (ih q hr)
      simp only [Step, pathCC]
      exact Or.inr ⟨Nat.succ_pos k, he, rfl⟩

lemma final_loop (hrej : ∀ w, M.reachF M.n M.start w = true → M.A w = false) :
    ∀ (d u : ℕ), u + d = M.n →
      Reaches M (finalC (M.Cnt M.n) (M.CntP M.n u M.PaB) u) := by
  intro d
  induction d with
  | zero =>
    intro u hu
    have hun : u = M.n := by omega
    subst hun
    have heq : M.CntP M.n M.n M.PaB = M.Cnt M.n :=
      M.CntP_eq_CntB (fun w _ hw => by simpa using hrej w hw)
    rw [heq]
    refine Reaches.step ?_ (Reaches.acc (x := accC) rfl)
    simp only [Step, finalC]
    exact Or.inl ⟨trivial, trivial, trivial⟩
  | succ d ih =>
    intro u hu
    have hun : u < M.n := by omega
    by_cases hR : M.reachF M.n M.start u = true
    · have hA := hrej u hR
      have hbn : M.CntP M.n u M.PaB < M.n := lt_of_le_of_lt (M.CntP_le _ _ _) hun
      have hIH := ih (u + 1) (by omega)
      rw [M.CntP_succ_pos hR (by simpa using hA)] at hIH
      refine Reaches.step
        (y := pathCC (M.Cnt M.n) (M.CntP M.n u M.PaB) u M.start M.n) ?_ ?_
      · simp only [Step, finalC]
        exact Or.inr (Or.inl ⟨hun, trivial⟩)
      · exact pathC_run hA hun hbn hIH M.n M.start hR
    · have hIH := ih (u + 1) (by omega)
      rw [M.CntP_succ_neg (fun hc => hR hc.1)] at hIH
      refine Reaches.step ?_ hIH
      simp only [Step, finalC]
      exact Or.inr (Or.inr ⟨hun, trivial⟩)

lemma inner_loop {i c v : ℕ} (hi : i < M.n) (hv : v < M.n)
    (hnr : M.reachF (i + 1) M.start v ≠ true)
    (hnext : Reaches M (outerC i (M.Cnt i) c (v + 1))) :
    ∀ (d u : ℕ), u + d = M.n →
      Reaches M (innerC i (M.Cnt i) c v (M.CntP i u (M.PvB v)) u) := by
  have hPv : ∀ w, M.reachF i M.start w = true → M.PvB v w = true := by
    intro w hw
    rw [NDM.PvB_eq_true]
    constructor
    · rintro rfl
      exact hnr (reachF_mono_one hw)
    · by_contra hc
      simp only [Bool.not_eq_false] at hc
      exact hnr (reachF_snoc hw hc)
  intro d
  induction d with
  | zero =>
    intro u hu
    have hun : u = M.n := by omega
    subst hun
    have heq : M.CntP i M.n (M.PvB v) = M.Cnt i :=
      M.CntP_eq_CntB (fun w _ hw => hPv w hw)
    rw [heq]
    refine Reaches.step ?_ hnext
    simp only [Step, innerC]
    exact Or.inl ⟨trivial, trivial, hv, trivial⟩
  | succ d ih =>
    intro u hu
    have hun : u < M.n := by omega
    by_cases hR : M.reachF i M.start u = true
    · have hP := hPv u hR
      rw [NDM.PvB_eq_true] at hP
      have hbn : M.CntP i u (M.PvB v) < M.n := lt_of_le_of_lt (M.CntP_le _ _ _) hun
      have hIH := ih (u + 1) (by omega)
      rw [M.CntP_succ_pos hR (hPv u hR)] at hIH
      refine Reaches.step
        (y := pathBC i (M.Cnt i) c v (M.CntP i u (M.PvB v)) u M.start i) ?_ ?_
      · simp only [Step, innerC]
        exact Or.inr (Or.inl ⟨hun, le_of_lt hi, trivial⟩)
      · exact pathB_run hP.1 hP.2 hun hbn hIH i M.start hR
    · have hIH := ih (u + 1) (by omega)
      rw [M.CntP_succ_neg (fun hc => hR hc.1)] at hIH
      refine Reaches.step ?_ hIH
      simp only [Step, innerC]
      exact Or.inr (Or.inr ⟨hun, trivial⟩)

lemma outer_loop {i : ℕ} (hi : i < M.n)
    (hend : Reaches M (outerC i (M.Cnt i) (M.Cnt (i + 1)) M.n)) :
    ∀ (d v : ℕ), v + d = M.n →
      Reaches M (outerC i (M.Cnt i) (M.CntB (i + 1) v) v) := by
  intro d
  induction d with
  | zero =>
    intro v hv
    have hvn : v = M.n := by omega
    subst hvn
    exact hend
  | succ d ih =>
    intro v hv
    have hvn : v < M.n := by omega
    by_cases hR : M.reachF (i + 1) M.start v = true
    · have hIH := ih (v + 1) (by omega)
      rw [M.CntB_succ_of_pos hR] at hIH
      have hcn : M.CntB (i + 1) v < M.n := lt_of_le_of_lt (M.CntB_le _ _) hvn
      refine Reaches.step
        (y := pathAC i (M.Cnt i) (M.CntB (i + 1) v) v M.start (i + 1)) ?_ ?_
      · simp only [Step, outerC]
        exact Or.inr (Or.inr (Or.inl ⟨hvn, hi, trivial⟩))
      · exact pathA_run hvn hcn hIH (i + 1) M.start hR
    · have hIH := ih (v + 1) (by omega)
      rw [M.CntB_succ_of_neg hR] at hIH
      refine Reaches.step
        (y := innerC i (M.Cnt i) (M.CntB (i + 1) v) v 0 0) ?_ ?_
      · simp only [Step, outerC]
        exact Or.inr (Or.inr (Or.inr ⟨hvn, trivial⟩))
      · have := inner_loop hi hvn hR hIH M.n 0 (by omega)
        rwa [M.CntP_zero] at this

lemma levels (hrej : ∀ w, M.reachF M.n M.start w = true → M.A w = false) :
    ∀ (d i : ℕ), i + d + 1 = M.n → Reaches M (outerC i (M.Cnt i) 0 0) := by
  intro d
  induction d with
  | zero =>
    intro i hi
    have hin : i + 1 = M.n := by omega
    have hend : Reaches M (outerC i (M.Cnt i) (M.Cnt (i + 1)) M.n) := by
      refine Reaches.step (y := finalC (M.Cnt (i + 1)) 0 0) ?_ ?_
      · simp only [Step, outerC]
        exact Or.inr (Or.inl ⟨trivial, hin, M.Cnt_le _, trivial⟩)
      · have := final_loop hrej M.n 0 (by omega)
        rw [M.CntP_zero] at this
        rw [hin]
        exact this
    have := outer_loop (by omega) hend M.n 0 (by omega)
    rwa [M.CntB_zero] at this
  | succ d ih =>
    intro i hi
    have hin : i + 1 < M.n := by omega
    have hend : Reaches M (outerC i (M.Cnt i) (M.Cnt (i + 1)) M.n) := by
      refine Reaches.step (y := outerC (i + 1) (M.Cnt (i + 1)) 0 0) ?_ (ih (i + 1) (by omega))
      simp only [Step, outerC]
      exact Or.inl ⟨trivial, hin, M.Cnt_le _, trivial⟩
    have := outer_loop (by omega) hend M.n 0 (by omega)
    rwa [M.CntB_zero] at this

/-- Correctness of the inductive counting machine: it reaches its accepting state from the
initial configuration if and only if `M` does not accept. -/
theorem reaches_initC_iff : Reaches M initC ↔ ¬ M.Accepts := by
  constructor
  · intro h ha
    rw [NDM.accepts_iff] at ha
    obtain ⟨v, hv, hav⟩ := ha
    rw [Reaches_sound h Inv_initC v hv] at hav
    exact Bool.noConfusion hav
  · intro h
    have hrej : ∀ w, M.reachF M.n M.start w = true → M.A w = false := by
      intro w hw
      by_contra hc
      exact h (NDM.accepts_iff.2 ⟨w, hw, by simpa using hc⟩)
    have hn := M.hstart
    have := levels hrej (M.n - 1) 0 (by omega)
    rw [NDM.Cnt_zero] at this
    exact this

end CS

/-
Nondeterministic machines as configuration graphs, and bounded reachability.

This file is part of the development of the Immerman-Szelepcsényi theorem.
-/
import Mathlib

namespace CS

/-- A nondeterministic machine, presented by its configuration graph on the vertex set
`{0, 1, ..., n-1}`: `start` is the initial configuration, `E` the (one step) transition
relation and `A` the set of accepting configurations.

A machine whose configuration graph has `n` vertices is a machine running in space
`O(log n)`: a configuration is described by `log n` bits. -/
structure NDM where
  /-- Number of configurations. -/
  n : ℕ
  /-- The initial configuration. -/
  start : ℕ
  /-- The initial configuration is a configuration. -/
  hstart : start < n
  /-- One-step transition relation. -/
  E : ℕ → ℕ → Bool
  /-- Accepting configurations. -/
  A : ℕ → Bool
  /-- Transitions only relate configurations. -/
  hE : ∀ u v, E u v = true → u < n ∧ v < n

namespace NDM

/-- `M.reachF t a b` is `true` iff `b` can be reached from `a` in at most `t` steps. -/
def reachF (M : NDM) : ℕ → ℕ → ℕ → Bool
  | 0, a, b => a == b
  | t + 1, a, b => (a == b) || ((List.range M.n).any fun q => M.E a q && M.reachF t q b)

/-- The machine accepts if some accepting configuration is reachable from the start. -/
def Accepts (M : NDM) : Prop :=
  ∃ v, Relation.ReflTransGen (fun a b => M.E a b = true) M.start v ∧ M.A v = true

variable {M : NDM}

@[simp] lemma reachF_zero_iff (a b : ℕ) : (M.reachF 0 a b = true) ↔ a = b := by
  simp [reachF]

lemma reachF_succ_iff (t a b : ℕ) :
    (M.reachF (t + 1) a b = true) ↔
      a = b ∨ ∃ q, q < M.n ∧ M.E a q = true ∧ M.reachF t q b = true := by
  simp [reachF, List.any_eq_true]

lemma reachF_self (t a : ℕ) : M.reachF t a a = true := by
  cases t with
  | zero => simp
  | succ t => rw [reachF_succ_iff]; exact Or.inl rfl

lemma reachF_mono_one {t a b : ℕ} (h : M.reachF t a b = true) : M.reachF (t + 1) a b = true := by
  induction t generalizing a with
  | zero =>
    rw [reachF_zero_iff] at h
    subst h
    exact reachF_self _ _
  | succ t ih =>
    rw [reachF_succ_iff] at h ⊢
    rcases h with h | ⟨q, hq, hE, hr⟩
    · exact Or.inl h
    · exact Or.inr ⟨q, hq, hE, ih hr⟩

lemma reachF_mono {t t' a b : ℕ} (htt : t ≤ t') (h : M.reachF t a b = true) :
    M.reachF t' a b = true := by
  induction t' with
  | zero =>
    have : t = 0 := by omega
    subst this; exact h
  | succ t' ih =>
    rcases Nat.lt_or_ge t (t' + 1) with h1 | h1
    · exact reachF_mono_one (ih (by omega))
    · have : t = t' + 1 := le_antisymm htt h1
      subst this; exact h

/-- Extending a path by one edge at the end. -/
lemma reachF_snoc {t a b c : ℕ} (h : M.reachF t a b = true) (he : M.E b c = true) :
    M.reachF (t + 1) a c = true := by
  induction t generalizing a with
  | zero =>
    rw [reachF_zero_iff] at h
    subst h
    rw [reachF_succ_iff]
    exact Or.inr ⟨c, (M.hE _ _ he).2, he, reachF_self _ _⟩
  | succ t ih =>
    rw [reachF_succ_iff] at h
    rcases h with h | ⟨q, hq, hE1, hr⟩
    · subst h
      rw [reachF_succ_iff]
      exact Or.inr ⟨c, (M.hE _ _ he).2, he, reachF_self _ _⟩
    · rw [reachF_succ_iff]
      exact Or.inr ⟨q, hq, hE1, ih hr⟩

/-- The "backward" characterisation of bounded reachability. -/
lemma reachF_succ_back (t a b : ℕ) :
    (M.reachF (t + 1) a b = true) ↔
      M.reachF t a b = true ∨ ∃ w, w < M.n ∧ M.reachF t a w = true ∧ M.E w b = true := by
  constructor
  · intro h
    induction t generalizing a with
    | zero =>
      rw [reachF_succ_iff] at h
      rcases h with h | ⟨q, hq, hE1, hr⟩
      · exact Or.inl (by simp [h])
      · rw [reachF_zero_iff] at hr
        subst hr
        exact Or.inr ⟨a, (M.hE _ _ hE1).1, by simp, hE1⟩
    | succ t ih =>
      rw [reachF_succ_iff] at h
      rcases h with h | ⟨q, hq, hE1, hr⟩
      · exact Or.inl (by rw [reachF_succ_iff]; exact Or.inl h)
      · rcases ih q hr with h2 | ⟨w, hw, hr2, he2⟩
        · refine Or.inl ?_
          rw [reachF_succ_iff]
          exact Or.inr ⟨q, hq, hE1, h2⟩
        · refine Or.inr ⟨w, hw, ?_, he2⟩
          rw [reachF_succ_iff]
          exact Or.inr ⟨q, hq, hE1, hr2⟩
  · rintro (h | ⟨w, hw, hr, he⟩)
    · exact reachF_mono_one h
    · exact reachF_snoc hr he

lemma reachF_lt {t b : ℕ} (h : M.reachF t M.start b = true) : b < M.n := by
  induction t with
  | zero => rw [reachF_zero_iff] at h; subst h; exact M.hstart
  | succ t ih =>
    rw [reachF_succ_back] at h
    rcases h with h | ⟨w, hw, hr, he⟩
    · exact ih h
    · exact (M.hE _ _ he).2

/-- Number of configurations `w < x` that are reachable from the start in at most `t` steps
and satisfy the extra predicate `P`. -/
def CntP (M : NDM) (t x : ℕ) (P : ℕ → Bool) : ℕ :=
  ((Finset.range x).filter (fun w => M.reachF t M.start w = true ∧ P w = true)).card

/-- Number of configurations `w < x` reachable from the start in at most `t` steps. -/
def CntB (M : NDM) (t x : ℕ) : ℕ := M.CntP t x (fun _ => true)

/-- Number of configurations reachable from the start in at most `t` steps. -/
def Cnt (M : NDM) (t : ℕ) : ℕ := M.CntB t M.n

lemma CntP_zero (t : ℕ) (P : ℕ → Bool) : M.CntP t 0 P = 0 := by simp [CntP]

lemma CntP_le (t x : ℕ) (P : ℕ → Bool) : M.CntP t x P ≤ x := by
  simpa [CntP] using (Finset.card_filter_le (Finset.range x) _).trans_eq (by simp)

lemma CntP_mono {t x y : ℕ} {P : ℕ → Bool} (h : x ≤ y) : M.CntP t x P ≤ M.CntP t y P :=
  Finset.card_le_card (Finset.filter_subset_filter _ (by simpa using h))

lemma CntP_succ_pos {t x : ℕ} {P : ℕ → Bool} (h1 : M.reachF t M.start x = true)
    (h2 : P x = true) : M.CntP t (x + 1) P = M.CntP t x P + 1 := by
  simp only [CntP, Finset.range_add_one]
  rw [Finset.filter_insert, if_pos ⟨h1, h2⟩, Finset.card_insert_of_notMem (by simp)]

lemma CntP_succ_neg {t x : ℕ} {P : ℕ → Bool}
    (h : ¬ (M.reachF t M.start x = true ∧ P x = true)) :
    M.CntP t (x + 1) P = M.CntP t x P := by
  simp only [CntP, Finset.range_add_one]
  rw [Finset.filter_insert, if_neg h]

lemma CntP_le_CntB {t x : ℕ} {P : ℕ → Bool} : M.CntP t x P ≤ M.CntB t x := by
  unfold CntP CntB
  refine Finset.card_le_card ?_
  intro a ha
  simp only [Finset.mem_filter] at ha ⊢
  exact ⟨ha.1, ha.2.1, by trivial⟩

/-- If the `P`-constrained count is as large as the unconstrained one, then `P` holds of every
reachable configuration in range. -/
lemma CntP_all {t x : ℕ} {P : ℕ → Bool} (h : M.CntB t x ≤ M.CntP t x P) :
    ∀ w, w < x → M.reachF t M.start w = true → P w = true := by
  intro w hw hr
  have hsub : (Finset.range x).filter (fun w => M.reachF t M.start w = true ∧ P w = true) ⊆
      (Finset.range x).filter
        (fun w => M.reachF t M.start w = true ∧ (fun _ => true : ℕ → Bool) w = true) := by
    intro a ha
    simp only [Finset.mem_filter] at ha ⊢
    exact ⟨ha.1, ha.2.1, by trivial⟩
  have heq := Finset.eq_of_subset_of_card_le hsub h
  have hmem : w ∈ (Finset.range x).filter
      (fun w => M.reachF t M.start w = true ∧ (fun _ => true : ℕ → Bool) w = true) := by
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨hw, hr, by trivial⟩
  rw [← heq] at hmem
  simp only [Finset.mem_filter] at hmem
  exact hmem.2.2

/-- If `P` holds of every reachable configuration in range, the constrained count agrees with
the unconstrained one. -/
lemma CntP_eq_CntB {t x : ℕ} {P : ℕ → Bool}
    (h : ∀ w, w < x → M.reachF t M.start w = true → P w = true) :
    M.CntP t x P = M.CntB t x := by
  unfold CntP CntB
  refine congrArg Finset.card (Finset.filter_congr ?_)
  intro w hw
  simp only [Finset.mem_range] at hw
  constructor
  · rintro ⟨h1, -⟩; exact ⟨h1, by trivial⟩
  · rintro ⟨h1, -⟩; exact ⟨h1, h w hw h1⟩

lemma CntB_zero (t : ℕ) : M.CntB t 0 = 0 := CntP_zero _ _

lemma CntB_le (t x : ℕ) : M.CntB t x ≤ x := CntP_le _ _ _

lemma CntB_mono {t x y : ℕ} (h : x ≤ y) : M.CntB t x ≤ M.CntB t y := CntP_mono h

lemma CntB_succ_of_pos {t x : ℕ} (h : M.reachF t M.start x = true) :
    M.CntB t (x + 1) = M.CntB t x + 1 := CntP_succ_pos h rfl

lemma CntB_succ_of_neg {t x : ℕ} (h : M.reachF t M.start x ≠ true) :
    M.CntB t (x + 1) = M.CntB t x := CntP_succ_neg (fun hc => h hc.1)

lemma Cnt_le (t : ℕ) : M.Cnt t ≤ M.n := CntB_le _ _

lemma Cnt_zero : M.Cnt 0 = 1 := by
  unfold Cnt CntB CntP
  have : ((Finset.range M.n).filter
      (fun w => M.reachF 0 M.start w = true ∧ (fun _ => true : ℕ → Bool) w = true))
      = {M.start} := by
    ext w
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton, reachF_zero_iff,
      and_true]
    constructor
    · rintro ⟨-, h⟩; exact h.symm
    · rintro rfl; exact ⟨M.hstart, rfl⟩
  rw [this]
  simp

/-- The predicate used in the inner counting loop: `w` is neither `v` nor a predecessor of `v`. -/
def PvB (M : NDM) (v : ℕ) : ℕ → Bool := fun w => !(w == v) && !(M.E w v)

/-- The predicate used in the final loop: `w` is not accepting. -/
def PaB (M : NDM) : ℕ → Bool := fun w => !(M.A w)

@[simp] lemma PvB_eq_true {v w : ℕ} : M.PvB v w = true ↔ w ≠ v ∧ M.E w v = false := by
  simp [PvB]

@[simp] lemma PaB_eq_true {w : ℕ} : M.PaB w = true ↔ M.A w = false := by
  simp [PaB]

/-! ### Stabilisation of the reachability sets -/

/-- The reachability set is stable at time `t`. -/
def Stable (M : NDM) (t : ℕ) : Prop :=
  ∀ w, M.reachF (t + 1) M.start w = M.reachF t M.start w

lemma stable_succ {t : ℕ} (h : M.Stable t) : M.Stable (t + 1) := by
  intro w
  refine Bool.eq_iff_iff.mpr ?_
  rw [reachF_succ_back]
  constructor
  · rintro (h1 | ⟨u, hu, hr, he⟩)
    · exact h1
    · rw [h u] at hr
      rw [reachF_succ_back]
      exact Or.inr ⟨u, hu, hr, he⟩
  · exact fun h1 => Or.inl h1

lemma stable_add {t : ℕ} (h : M.Stable t) :
    ∀ k w, M.reachF (t + k) M.start w = M.reachF t M.start w := by
  intro k
  induction k with
  | zero => intro w; rfl
  | succ k ih =>
    intro w
    have hs : M.Stable (t + k) := by
      clear ih
      induction k with
      | zero => exact h
      | succ k ihk => exact stable_succ ihk
    have := hs w
    rw [show t + (k + 1) = (t + k) + 1 by ring, this, ih w]

lemma exists_stable : ∃ j, j < M.n ∧ M.Stable j := by
  by_contra hcon
  push_neg at hcon
  have key : ∀ t, t ≤ M.n → t + 1 ≤ M.CntB t M.n := by
    intro t
    induction t with
    | zero => intro _; rw [← Cnt, Cnt_zero]
    | succ t ih =>
      intro ht
      have h1 : t + 1 ≤ M.CntB t M.n := ih (by omega)
      have hns : ¬ M.Stable t := hcon t (by omega)
      unfold Stable at hns
      push_neg at hns
      obtain ⟨w, hw⟩ := hns
      have hw1 : M.reachF (t + 1) M.start w = true ∧ M.reachF t M.start w ≠ true := by
        cases h2 : M.reachF t M.start w with
        | true => exact absurd (by rw [reachF_mono_one h2, h2]) hw
        | false =>
          cases h3 : M.reachF (t + 1) M.start w with
          | true => exact ⟨rfl, by simp⟩
          | false => exact absurd (by rw [h2, h3]) hw
      have hlt : M.CntB t M.n < M.CntB (t + 1) M.n := by
        unfold CntB CntP
        refine Finset.card_lt_card (Finset.ssubset_iff_of_subset ?_ |>.2 ⟨w, ?_, ?_⟩)
        · intro x hx
          simp only [Finset.mem_filter, Finset.mem_range] at hx ⊢
          exact ⟨hx.1, reachF_mono_one hx.2.1, by trivial⟩
        · simp only [Finset.mem_filter, Finset.mem_range]
          exact ⟨reachF_lt hw1.1, hw1.1, by trivial⟩
        · intro hmem
          simp only [Finset.mem_filter] at hmem
          exact hw1.2 hmem.2.1
      omega
  have h1 := key M.n le_rfl
  have h2 : M.CntB M.n M.n ≤ M.n := CntB_le _ _
  omega

/-- Every configuration reachable at all is reachable within `n` steps. -/
lemma reachF_le_n {t w : ℕ} (h : M.reachF t M.start w = true) :
    M.reachF M.n M.start w = true := by
  obtain ⟨j, hj, hst⟩ := exists_stable (M := M)
  have hjn : M.reachF M.n M.start w = M.reachF j M.start w := by
    have := stable_add hst (M.n - j) w
    rw [show j + (M.n - j) = M.n by omega] at this
    exact this
  rcases Nat.le_total t j with h1 | h1
  · rw [hjn]; exact reachF_mono h1 h
  · have := stable_add hst (t - j) w
    rw [show j + (t - j) = t by omega] at this
    rw [hjn, ← this]; exact h

lemma reachF_of_reflTransGen {v : ℕ}
    (h : Relation.ReflTransGen (fun a b => M.E a b = true) M.start v) :
    M.reachF M.n M.start v = true := by
  induction h with
  | refl => exact reachF_self _ _
  | tail hab hbc ih => exact reachF_le_n (reachF_snoc ih hbc)

lemma reflTransGen_of_reachF {t a v : ℕ} (h : M.reachF t a v = true) :
    Relation.ReflTransGen (fun a b => M.E a b = true) a v := by
  induction t generalizing a with
  | zero => rw [reachF_zero_iff] at h; subst h; exact Relation.ReflTransGen.refl
  | succ t ih =>
    rw [reachF_succ_iff] at h
    rcases h with h | ⟨q, _, he, hr⟩
    · subst h; exact Relation.ReflTransGen.refl
    · exact Relation.ReflTransGen.head he (ih hr)

/-- Acceptance is equivalent to acceptance within `n` steps. -/
lemma accepts_iff : M.Accepts ↔ ∃ v, M.reachF M.n M.start v = true ∧ M.A v = true := by
  constructor
  · rintro ⟨v, hv, ha⟩
    exact ⟨v, reachF_of_reflTransGen hv, ha⟩
  · rintro ⟨v, hv, ha⟩
    exact ⟨v, reflTransGen_of_reachF hv, ha⟩

end NDM

end CS

/-
Encoding the inductive counting machine as a nondeterministic machine of the same kind,
with a polynomially larger configuration space (i.e. with the same space bound up to a
constant factor).

This file is part of the development of the Immerman-Szelepcsényi theorem.
-/
import RequestProject.IS.Complement

namespace CS

open NDM

variable {M : NDM}

/-! ### Boundedness of the reachable configurations -/

/-- All counters of a configuration are at most `n`.  This is what makes the inductive counting
machine a machine of space `O(log n)`. -/
def Bnd (M : NDM) (x : Cfg) : Prop :=
  x.i ≤ M.n ∧ x.r ≤ M.n ∧ x.c ≤ M.n ∧ x.v ≤ M.n ∧ x.b ≤ M.n ∧ x.u ≤ M.n ∧ x.p ≤ M.n ∧
    x.k ≤ M.n

lemma Bnd_initC : Bnd M initC := by
  have := M.hstart
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [initC, outerC] <;> omega

/-- Boundedness is preserved by the transition relation. -/
lemma Bnd_step {x y : Cfg} (hx : Bnd M x) (hs : Step M x y) : Bnd M y := by
  have hs0 : M.start ≤ M.n := le_of_lt M.hstart
  obtain ⟨mode, i, r, c, v, b, u, p, k⟩ := x
  obtain ⟨hi, hr, hc, hv, hb, hu, hp, hk⟩ := hx
  simp only at hi hr hc hv hb hu hp hk
  cases mode
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ <;>
      simp only [Bnd, outerC, finalC, pathAC, innerC] <;> omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, hy⟩
    · simp only [Bnd, outerC]; omega
    · have hyp := (M.hE _ _ h2).2
      rw [hy]; simp only [Bnd, pathAC]; omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, rfl⟩ | ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ <;>
      simp only [Bnd, outerC, pathBC, innerC] <;> omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, h4, h5, rfl⟩ | ⟨h1, h2, hy⟩
    · simp only [Bnd, innerC]; omega
    · have hyp := (M.hE _ _ h2).2
      rw [hy]; simp only [Bnd, pathBC]; omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, rfl⟩ | ⟨h1, rfl⟩ | ⟨h1, rfl⟩ <;>
      simp only [Bnd, accC, pathCC, finalC] <;> omega
  · simp only [Step] at hs
    rcases hs with ⟨h1, h2, h3, h4, rfl⟩ | ⟨h1, h2, hy⟩
    · simp only [Bnd, finalC]; omega
    · have hyp := (M.hE _ _ h2).2
      rw [hy]; simp only [Bnd, pathCC]; omega
  · exact absurd hs (by simp [Step])

/-! ### Encoding configurations as natural numbers -/

/-- Little-endian base `B` encoding of a list of digits. -/
def encL (B : ℕ) : List ℕ → ℕ
  | [] => 0
  | d :: ds => d + B * encL B ds

/-- Decoding `l` base-`B` digits of a natural number. -/
def decL (B : ℕ) : ℕ → ℕ → List ℕ
  | _, 0 => []
  | a, l + 1 => (a % B) :: decL B (a / B) l

lemma decL_encL {B : ℕ} (hB : 0 < B) :
    ∀ ds : List ℕ, (∀ d ∈ ds, d < B) → decL B (encL B ds) ds.length = ds := by
  intro ds
  induction ds with
  | nil => intro _; rfl
  | cons d ds ih =>
    intro h
    have hd : d < B := h d (by simp)
    have hds : ∀ e ∈ ds, e < B := fun e he => h e (by simp [he])
    simp only [encL, List.length_cons, decL, List.cons.injEq]
    constructor
    · rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]
    · rw [Nat.add_mul_div_left _ _ hB, Nat.div_eq_of_lt hd, Nat.zero_add]
      exact ih hds

lemma encL_lt {B : ℕ} (hB : 0 < B) :
    ∀ ds : List ℕ, (∀ d ∈ ds, d < B) → encL B ds < B ^ ds.length := by
  intro ds
  induction ds with
  | nil => intro _; simpa [encL] using hB
  | cons d ds ih =>
    intro h
    have hd : d < B := h d (by simp)
    have hds : ∀ e ∈ ds, e < B := fun e he => h e (by simp [he])
    have hX : encL B ds + 1 ≤ B ^ ds.length := ih hds
    calc encL B (d :: ds) = d + B * encL B ds := rfl
      _ < B + B * encL B ds := by omega
      _ = B * (encL B ds + 1) := by ring
      _ ≤ B * B ^ ds.length := Nat.mul_le_mul_left _ hX
      _ = B ^ (d :: ds).length := by
          simp only [List.length_cons, pow_succ]
          ring

/-- Index of a control state. -/
def modeIdx : Mode → ℕ
  | Mode.outer => 0
  | Mode.pathA => 1
  | Mode.inner => 2
  | Mode.pathB => 3
  | Mode.final => 4
  | Mode.pathC => 5
  | Mode.acc => 6

/-- Control state with a given index. -/
def modeOf : ℕ → Mode
  | 0 => Mode.outer
  | 1 => Mode.pathA
  | 2 => Mode.inner
  | 3 => Mode.pathB
  | 4 => Mode.final
  | 5 => Mode.pathC
  | _ => Mode.acc

lemma modeOf_modeIdx (m : Mode) : modeOf (modeIdx m) = m := by cases m <;> rfl

lemma modeIdx_lt (m : Mode) : modeIdx m < 7 := by cases m <;> simp [modeIdx]

/-- The list of digits of a configuration. -/
def digits (x : Cfg) : List ℕ :=
  [x.k, x.p, x.u, x.b, x.v, x.c, x.r, x.i, modeIdx x.mode]

/-- The configuration with a given list of digits. -/
def ofDigits : List ℕ → Cfg
  | [k, p, u, b, v, c, r, i, m] => ⟨modeOf m, i, r, c, v, b, u, p, k⟩
  | _ => accC

lemma ofDigits_digits (x : Cfg) : ofDigits (digits x) = x := by
  obtain ⟨mode, i, r, c, v, b, u, p, k⟩ := x
  simp [digits, ofDigits, modeOf_modeIdx]

/-- Encoding of a configuration as a natural number. -/
def encCfg (M : NDM) (x : Cfg) : ℕ := encL (M.n + 8) (digits x)

/-- Decoding of a natural number as a configuration. -/
def decCfg (M : NDM) (a : ℕ) : Cfg := ofDigits (decL (M.n + 8) a 9)

lemma digits_lt {x : Cfg} (hx : Bnd M x) : ∀ d ∈ digits x, d < M.n + 8 := by
  obtain ⟨hi, hr, hc, hv, hb, hu, hp, hk⟩ := hx
  have hm := modeIdx_lt x.mode
  intro d hd
  simp only [digits, List.mem_cons, List.not_mem_nil, or_false] at hd
  rcases hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega

lemma decCfg_encCfg {x : Cfg} (hx : Bnd M x) : decCfg M (encCfg M x) = x := by
  have h9 : (digits x).length = 9 := by simp [digits]
  unfold decCfg encCfg
  rw [← h9, decL_encL (by omega) _ (digits_lt hx), ofDigits_digits]

lemma encCfg_lt {x : Cfg} (hx : Bnd M x) : encCfg M x < (M.n + 8) ^ 9 := by
  have h9 : (digits x).length = 9 := by simp [digits]
  have := encL_lt (B := M.n + 8) (by omega) (digits x) (digits_lt hx)
  rwa [h9] at this

/-! ### The complement machine -/

/-- The machine produced by the Immerman-Szelepcsényi construction: it is the inductive
counting machine for `M`, with its configurations encoded as natural numbers.  Its
configuration space has size `(n+8)^9`, i.e. it uses `O(log n)` space, a constant factor more
than `M`. -/
def complement (M : NDM) : NDM where
  n := (M.n + 8) ^ 9
  start := encCfg M initC
  hstart := encCfg_lt Bnd_initC
  E := fun a b =>
    decide (a < (M.n + 8) ^ 9) && decide (b < (M.n + 8) ^ 9) &&
      decide (Step M (decCfg M a) (decCfg M b))
  A := fun a => decide ((decCfg M a).mode = Mode.acc)
  hE := by
    intro u v h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    exact ⟨h.1.1, h.1.2⟩

@[simp] lemma complement_n : (complement M).n = (M.n + 8) ^ 9 := rfl

lemma complement_E_iff {a b : ℕ} :
    (complement M).E a b = true ↔
      a < (M.n + 8) ^ 9 ∧ b < (M.n + 8) ^ 9 ∧ Step M (decCfg M a) (decCfg M b) := by
  simp only [complement, Bool.and_eq_true, decide_eq_true_eq, and_assoc]

lemma complement_A_iff {a : ℕ} :
    (complement M).A a = true ↔ (decCfg M a).mode = Mode.acc := by
  simp [complement]

/-- Completeness of the encoded machine. -/
lemma complement_accepts_of_reaches {x : Cfg} (h : Reaches M x) :
    Bnd M x → ∃ w, Relation.ReflTransGen (fun a b => (complement M).E a b = true)
      (encCfg M x) w ∧ (complement M).A w = true := by
  induction h with
  | @acc x hmode =>
    intro hb
    refine ⟨encCfg M x, Relation.ReflTransGen.refl, ?_⟩
    rw [complement_A_iff, decCfg_encCfg hb]
    exact hmode
  | @step x y hstep _ ih =>
    intro hb
    have hby : Bnd M y := Bnd_step hb hstep
    obtain ⟨w, hw, haw⟩ := ih hby
    refine ⟨w, Relation.ReflTransGen.head ?_ hw, haw⟩
    rw [complement_E_iff, decCfg_encCfg hb, decCfg_encCfg hby]
    exact ⟨encCfg_lt hb, encCfg_lt hby, hstep⟩

/-- Soundness of the encoded machine. -/
lemma reaches_of_complement_accepts {a w : ℕ}
    (h : Relation.ReflTransGen (fun a b => (complement M).E a b = true) a w)
    (hw : (complement M).A w = true) : Reaches M (decCfg M a) := by
  induction h using Relation.ReflTransGen.head_induction_on with
  | refl => exact Reaches.acc (complement_A_iff.1 hw)
  | head hab _ ih =>
    exact Reaches.step (complement_E_iff.1 hab).2.2 ih

/-- The complement machine accepts exactly when `M` rejects. -/
theorem complement_accepts_iff (M : NDM) : (complement M).Accepts ↔ ¬ M.Accepts := by
  rw [← reaches_initC_iff]
  constructor
  · rintro ⟨w, hw, haw⟩
    have := reaches_of_complement_accepts (M := M) hw haw
    rwa [decCfg_encCfg Bnd_initC] at this
  · intro h
    exact complement_accepts_of_reaches h Bnd_initC

end CS

