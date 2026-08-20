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

def edg (u v : ℕ) : Prop := G.Ed x[G.pos u]? u v

/-- `G.Rch x i v`: the vertex `v` is reachable from `G.st0` in at most `i` steps. -/

def Rch (G : Data) (x : List Bool) : ℕ → ℕ → Prop
  | 0, v => v = G.st0
  | (i + 1), v => Rch G x i v ∨ ∃ u, Rch G x i u ∧ G.edg x u v

/-- Reachability in the configuration graph. -/

def Reachable (v : ℕ) : Prop := Relation.ReflTransGen (G.edg x) G.st0 v

variable {G x}

lemma Rch_zero {v : ℕ} : G.Rch x 0 v ↔ v = G.st0 := Iff.rfl

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
