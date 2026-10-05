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
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS
namespace IS

/-!
## The reachability sets of a finite digraph

Throughout, the digraph has vertex set `{0, 1, ..., N-1} ⊆ ℕ` and edge relation `adj`.
`R N adj s i` is the set of vertices reachable from `s` using at most `i` edges.
-/

/-- The edge relation of the digraph on vertex set `{0,...,N-1}`. -/
def Edge (N : ℕ) (adj : ℕ → ℕ → Bool) (a b : ℕ) : Prop := a < N ∧ b < N ∧ adj a b = true

/-- `R N adj s i` : the vertices reachable from `s` by a walk of length at most `i`. -/
def R (N : ℕ) (adj : ℕ → ℕ → Bool) (s : ℕ) : ℕ → Finset ℕ
  | 0 => {s}
  | i + 1 => R N adj s i ∪ (Finset.range N).filter (fun w => ∃ u ∈ R N adj s i, adj u w = true)

variable {N : ℕ} {adj : ℕ → ℕ → Bool} {s : ℕ}

theorem R_zero : R N adj s 0 = {s} := rfl

theorem R_succ (i : ℕ) :
    R N adj s (i + 1) =
      R N adj s i ∪ (Finset.range N).filter (fun w => ∃ u ∈ R N adj s i, adj u w = true) := rfl

theorem R_subset_succ (i : ℕ) : R N adj s i ⊆ R N adj s (i + 1) := by
  intro x hx
  rw [R_succ]
  exact Finset.mem_union_left _ hx

theorem R_mono {i j : ℕ} (h : i ≤ j) : R N adj s i ⊆ R N adj s j := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  clear h
  induction d with
  | zero => simp
  | succ d ih =>
    have hd : i + (d + 1) = (i + d) + 1 := by omega
    rw [hd]
    exact ih.trans (R_subset_succ _)

theorem R_subset_range (hs : s < N) (i : ℕ) : R N adj s i ⊆ Finset.range N := by
  induction i with
  | zero => intro x hx; simp only [R_zero, Finset.mem_singleton] at hx; simpa [hx] using hs
  | succ i ih =>
    intro x hx
    rw [R_succ, Finset.mem_union] at hx
    rcases hx with hx | hx
    · exact ih hx
    · exact Finset.mem_of_mem_filter _ hx

theorem mem_R_succ_of_edge {i u w : ℕ} (hu : u ∈ R N adj s i) (hw : w < N)
    (h : adj u w = true) : w ∈ R N adj s (i + 1) := by
  rw [R_succ, Finset.mem_union]
  right
  simp only [Finset.mem_filter, Finset.mem_range]
  exact ⟨hw, u, hu, h⟩

/-- If a vertex is in `R (i+1)` it is in `R i` or has a predecessor in `R i`. -/
theorem mem_R_succ_iff {i w : ℕ} :
    w ∈ R N adj s (i + 1) ↔ w ∈ R N adj s i ∨ (w < N ∧ ∃ u ∈ R N adj s i, adj u w = true) := by
  rw [R_succ, Finset.mem_union]
  simp [Finset.mem_filter, Finset.mem_range, and_comm]

/-! ### Stabilisation -/

theorem R_stable_of_eq {i : ℕ} (h : R N adj s (i + 1) = R N adj s i) (j : ℕ) :
    R N adj s (i + j) = R N adj s i := by
  induction j with
  | zero => rfl
  | succ j ih =>
    have : i + (j + 1) = (i + j) + 1 := by omega
    rw [this, R_succ, ih]
    rw [← R_succ, h]

theorem R_card_lt_of_ne {i : ℕ} (h : R N adj s (i + 1) ≠ R N adj s i) :
    (R N adj s i).card < (R N adj s (i + 1)).card :=
  Finset.card_lt_card ⟨R_subset_succ i, fun hsub => h (Finset.Subset.antisymm hsub (R_subset_succ i))⟩

theorem R_card_ge : ∀ i : ℕ, (∀ j < i, R N adj s (j + 1) ≠ R N adj s j) →
    i + 1 ≤ (R N adj s i).card := by
  intro i
  induction i with
  | zero => intro _; simp [R_zero]
  | succ i ih =>
    intro h
    have h1 : i + 1 ≤ (R N adj s i).card := ih (fun j hj => h j (by omega))
    have h2 := R_card_lt_of_ne (h i (by omega))
    omega

/-- Reachability sets stabilise by step `N`. -/
theorem R_stabilises (hs : s < N) : R N adj s (N + 1) = R N adj s N := by
  by_cases hall : ∀ j < N, R N adj s (j + 1) ≠ R N adj s j
  · exfalso
    have h1 := R_card_ge (N := N) (adj := adj) (s := s) N hall
    have h2 : (R N adj s N).card ≤ N := by
      have := Finset.card_le_card (R_subset_range (adj := adj) hs N)
      simpa using this
    omega
  · push_neg at hall
    obtain ⟨j, hjN, hj⟩ := hall
    have hstab := R_stable_of_eq hj
    have e1 : R N adj s N = R N adj s j := by
      have := hstab (N - j); rwa [Nat.add_sub_cancel' (le_of_lt hjN)] at this
    have e2 : R N adj s (N + 1) = R N adj s j := by
      have := hstab (N + 1 - j); rwa [Nat.add_sub_cancel' (by omega : j ≤ N + 1)] at this
    rw [e1, e2]

theorem R_eq_of_ge (hs : s < N) {j : ℕ} (hj : N ≤ j) : R N adj s j = R N adj s N := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  exact R_stable_of_eq (R_stabilises hs) d

/-! ### `R N` is exactly the reachable set -/

theorem mem_R_of_reachable (hs : s < N) {x : ℕ}
    (h : Relation.ReflTransGen (Edge N adj) s x) : x ∈ R N adj s N := by
  have key : ∀ y, Relation.ReflTransGen (Edge N adj) s y → ∃ i, y ∈ R N adj s i := by
    intro y hy
    induction hy with
    | refl => exact ⟨0, by simp [R_zero]⟩
    | tail hab hbc ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 1, mem_R_succ_of_edge hi hbc.2.1 hbc.2.2⟩
  obtain ⟨i, hi⟩ := key x h
  rcases Nat.lt_or_ge i N with h' | h'
  · exact R_mono (le_of_lt h') hi
  · rwa [R_eq_of_ge hs h'] at hi

theorem reachable_of_mem_R (hs : s < N) : ∀ (i x : ℕ), x ∈ R N adj s i →
    Relation.ReflTransGen (Edge N adj) s x := by
  intro i
  induction i with
  | zero => intro x hx; simp only [R_zero, Finset.mem_singleton] at hx; subst hx; exact .refl
  | succ i ih =>
    intro x hx
    rw [mem_R_succ_iff] at hx
    rcases hx with hx | ⟨hxN, u, hu, huv⟩
    · exact ih x hx
    · have hu' : u < N := by simpa using (R_subset_range hs i hu)
      exact (ih u hu).tail ⟨hu', hxN, huv⟩

theorem reachable_iff_mem_R (hs : s < N) {x : ℕ} :
    Relation.ReflTransGen (Edge N adj) s x ↔ x ∈ R N adj s N :=
  ⟨mem_R_of_reachable hs, reachable_of_mem_R hs N x⟩


/-! ### Two counting lemmas about `filter (· < v)` -/

theorem filter_lt_succ_of_mem {X : Finset ℕ} {v : ℕ} (hv : v ∈ X) :
    (X.filter (fun x => x < v + 1)).card = (X.filter (fun x => x < v)).card + 1 := by
  have h : X.filter (fun x => x < v + 1) = insert v (X.filter (fun x => x < v)) := by
    ext x
    simp only [Finset.mem_filter, Finset.mem_insert]
    constructor
    · rintro ⟨hx, hlt⟩
      rcases Nat.lt_or_ge x v with h' | h'
      · exact Or.inr ⟨hx, h'⟩
      · exact Or.inl (by omega)
    · rintro (rfl | ⟨hx, hlt⟩)
      · exact ⟨hv, by omega⟩
      · exact ⟨hx, by omega⟩
  rw [h, Finset.card_insert_of_notMem (by simp)]

theorem filter_lt_succ_of_not_mem {X : Finset ℕ} {v : ℕ} (hv : v ∉ X) :
    (X.filter (fun x => x < v + 1)).card = (X.filter (fun x => x < v)).card := by
  congr 1
  ext x
  simp only [Finset.mem_filter]
  constructor
  · rintro ⟨hx, hlt⟩
    refine ⟨hx, ?_⟩
    rcases Nat.lt_or_ge x v with h' | h'
    · exact h'
    · exact absurd (by omega : x = v) (fun h => hv (h ▸ hx))
  · rintro ⟨hx, hlt⟩; exact ⟨hx, by omega⟩

theorem filter_lt_N_eq (hs : s < N) (i : ℕ) :
    (R N adj s i).filter (fun x => x < N) = R N adj s i := by
  apply Finset.filter_true_of_mem
  intro x hx
  simpa using R_subset_range hs i hx

/-!
## The complement machine

We now describe, for a digraph `(N, adj)` with distinguished vertices `s` and `t`, a
nondeterministic machine whose configuration graph is *polynomially* larger than the digraph
itself, and which has an accepting run exactly when `t` is **not** reachable from `s`.

This is the inductive-counting construction of Immerman and Szelepcsényi.  Reading the digraph
as the configuration graph of a nondeterministic machine of space `S` (so `N = 2^{O(S)}`),
the new machine has `O(N^8)` configurations, i.e. it also runs in space `O(S)`.
-/

/-- Configurations of the complement machine.

* `outer i c v k`   : round `i`; `c = |R (i-1)|`; deciding vertex `v`; `k` vertices `< v` are in `R i`.
* `pathA i c v k p l` : verifying `v ∈ R i` by guessing a walk `s → … → p` of length `l ≤ i`.
* `inner i c v k d lb` : verifying `v ∉ R i` by enumerating `R (i-1)`; `d` elements listed so far,
  all of them `< lb`.
* `pathB i c v k d u p l` : verifying `u ∈ R (i-1)` by guessing a walk `s → … → p` of length `l`.
* `acc` : the accepting configuration. -/
inductive Cfg where
  | outer (i c v k : ℕ) : Cfg
  | pathA (i c v k p l : ℕ) : Cfg
  | inner (i c v k d lb : ℕ) : Cfg
  | pathB (i c v k d u p l : ℕ) : Cfg
  | acc : Cfg
  deriving DecidableEq, Repr

/-- The (nondeterministic) transition relation of the complement machine.  Every transition
inspects at most one entry of the adjacency matrix. -/
inductive Step (N : ℕ) (adj : ℕ → ℕ → Bool) (s t : ℕ) : Cfg → Cfg → Prop
  /-- Guess that `v ∈ R i`, and start verifying it. -/
  | startA {i c v k : ℕ} : v < N → Step N adj s t (.outer i c v k) (.pathA i c v k s 0)
  /-- Extend the guessed walk. -/
  | stepA {i c v k p p' l : ℕ} : adj p p' = true → p' < N → l + 1 ≤ i →
      Step N adj s t (.pathA i c v k p l) (.pathA i c v k p' (l + 1))
  /-- The walk arrived at `v`; record `v ∈ R i` and move on. -/
  | doneA {i c v k p l : ℕ} : p = v →
      Step N adj s t (.pathA i c v k p l) (.outer i c (v + 1) (k + 1))
  /-- Guess that `v ∉ R i`, and start enumerating `R (i-1)`. -/
  | startI {i c v k : ℕ} : v < N → Step N adj s t (.outer i c v k) (.inner i c v k 0 0)
  /-- Guess the next element `u` of `R (i-1)`, and start verifying `u ∈ R (i-1)`. -/
  | startB {i c v k d lb u : ℕ} : d < c → lb ≤ u → u < N →
      Step N adj s t (.inner i c v k d lb) (.pathB i c v k d u s 0)
  /-- Extend the guessed walk. -/
  | stepB {i c v k d u p p' l : ℕ} : adj p p' = true → p' < N → l + 1 ≤ i - 1 →
      Step N adj s t (.pathB i c v k d u p l) (.pathB i c v k d u p' (l + 1))
  /-- The walk arrived at `u`; check that `u` is not `v` and has no edge to `v`. -/
  | doneB {i c v k d u p l : ℕ} : p = u → u ≠ v → adj u v = false →
      Step N adj s t (.pathB i c v k d u p l) (.inner i c v k (d + 1) (u + 1))
  /-- All of `R (i-1)` has been enumerated, so `v ∉ R i`; move on to the next vertex. -/
  | doneI {i c v k d lb : ℕ} : d = c → i ≤ N →
      Step N adj s t (.inner i c v k d lb) (.outer i c (v + 1) k)
  /-- Round `i` is finished: `k = |R i|` becomes the count for the next round. -/
  | nextRound {i c k : ℕ} : i < N → Step N adj s t (.outer i c N k) (.outer (i + 1) k 0 0)
  /-- The last round is finished; check `t ∉ R (N+1)`. -/
  | lastRound {c k : ℕ} : Step N adj s t (.outer N c N k) (.inner (N + 1) k t 0 0 0)
  /-- All of `R N` has been enumerated and avoided `t`, so `t` is unreachable. -/
  | accept {c k d lb : ℕ} : d = c → Step N adj s t (.inner (N + 1) c t k d lb) .acc

/-- The initial configuration: round `1`, with `|R 0| = 1`. -/
def start : Cfg := .outer 1 1 0 0

/-! ### Soundness: the invariant -/

/-- The invariant satisfied by every configuration reachable from `start`. -/
def Inv (N : ℕ) (adj : ℕ → ℕ → Bool) (s t : ℕ) : Cfg → Prop
  | .outer i c v k => 1 ≤ i ∧ i ≤ N ∧ c = (R N adj s (i - 1)).card ∧ v ≤ N ∧
      k = ((R N adj s i).filter (fun x => x < v)).card
  | .pathA i c v k p l => 1 ≤ i ∧ i ≤ N ∧ c = (R N adj s (i - 1)).card ∧ v < N ∧
      k = ((R N adj s i).filter (fun x => x < v)).card ∧ p ∈ R N adj s l ∧ l ≤ i
  | .inner i c v k d lb => 1 ≤ i ∧ i ≤ N + 1 ∧ c = (R N adj s (i - 1)).card ∧
      (i ≤ N → v < N ∧ k = ((R N adj s i).filter (fun x => x < v)).card) ∧
      (N < i → v = t ∧ k = 0) ∧ lb ≤ N ∧
      ∃ S ⊆ (R N adj s (i - 1)).filter (fun x => x < lb), S.card = d ∧
        ∀ w ∈ S, w ≠ v ∧ adj w v = false
  | .pathB i c v k d u p l => 1 ≤ i ∧ i ≤ N + 1 ∧ c = (R N adj s (i - 1)).card ∧
      (i ≤ N → v < N ∧ k = ((R N adj s i).filter (fun x => x < v)).card) ∧
      (N < i → v = t ∧ k = 0) ∧
      (∃ S ⊆ (R N adj s (i - 1)).filter (fun x => x < u), S.card = d ∧
        ∀ w ∈ S, w ≠ v ∧ adj w v = false) ∧
      p ∈ R N adj s l ∧ l ≤ i - 1 ∧ u < N
  | .acc => t ∉ R N adj s N

/-- The heart of the soundness argument: if the machine has enumerated `c = |R (i-1)|`
elements of `R (i-1)`, all of them different from `v` and without an edge to `v`,
then indeed `v ∉ R i`. -/
theorem not_mem_R_of_inner {i c v k d lb : ℕ} (h : Inv N adj s t (.inner i c v k d lb))
    (hd : d = c) : v ∉ R N adj s i := by
  obtain ⟨hi1, -, hc, -, -, -, S, hS, hScard, hSprop⟩ := h
  have hSsub : S ⊆ R N adj s (i - 1) := hS.trans (Finset.filter_subset _ _)
  have hcard : (R N adj s (i - 1)).card ≤ S.card := by omega
  have hSeq : S = R N adj s (i - 1) := Finset.eq_of_subset_of_card_le hSsub hcard
  intro hv
  have hi : i - 1 + 1 = i := by omega
  rw [← hi, mem_R_succ_iff] at hv
  rcases hv with hv | ⟨-, u, hu, huv⟩
  · exact ((hSprop v (hSeq ▸ hv)).1) rfl
  · exact absurd (hSprop u (hSeq ▸ hu)).2 (by simp [huv])

theorem Inv_start (hs : s < N) : Inv N adj s t start := by
  refine ⟨le_refl 1, by omega, ?_, Nat.zero_le _, ?_⟩
  · simp [R_zero]
  · simp

theorem Inv_step (hs : s < N) {a b : Cfg} (h : Step N adj s t a b)
    (hInv : Inv N adj s t a) : Inv N adj s t b := by
  induction h with
  | @startA i c v k hv =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      exact ⟨h1, h2, h3, hv, h5, by simp [R_zero], Nat.zero_le _⟩
  | @stepA i c v k p p' l hadj hp' hl =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hInv
      exact ⟨h1, h2, h3, h4, h5, mem_R_succ_of_edge h6 hp' hadj, hl⟩
  | @doneA i c v k p l hpv =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hInv
      subst hpv
      have hmem : p ∈ R N adj s i := R_mono h7 h6
      exact ⟨h1, h2, h3, by omega, by rw [h5, filter_lt_succ_of_mem hmem]⟩
  | @startI i c v k hv =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      exact ⟨h1, by omega, h3, fun _ => ⟨hv, h5⟩, by omega, by omega, ∅, by simp, by simp, by simp⟩
  | @startB i c v k d lb u hdc hlb hu =>
      obtain ⟨h1, h2, h3, h4, h5, h6, S, hS, hScard, hSprop⟩ := hInv
      refine ⟨h1, h2, h3, h4, h5, ⟨S, ?_, hScard, hSprop⟩, by simp [R_zero], Nat.zero_le _, hu⟩
      intro x hx
      have := hS hx
      simp only [Finset.mem_filter] at this ⊢
      exact ⟨this.1, by omega⟩
  | @stepB i c v k d u p p' l hadj hp' hl =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hInv
      exact ⟨h1, h2, h3, h4, h5, h6, mem_R_succ_of_edge h7 hp' hadj, hl, h9⟩
  | @doneB i c v k d u p l hpu huv hadj =>
      obtain ⟨h1, h2, h3, h4, h5, ⟨S, hS, hScard, hSprop⟩, h7, h8, h9⟩ := hInv
      subst hpu
      have hmem : p ∈ R N adj s (i - 1) := R_mono h8 h7
      have hnot : p ∉ S := by
        intro hp
        have := hS hp
        simp only [Finset.mem_filter] at this
        omega
      refine ⟨h1, h2, h3, h4, h5, by omega, insert p S, ?_, ?_, ?_⟩
      · intro x hx
        simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · simp only [Finset.mem_filter]; exact ⟨hmem, by omega⟩
        · have := hS hx
          simp only [Finset.mem_filter] at this ⊢
          exact ⟨this.1, by omega⟩
      · rw [Finset.card_insert_of_notMem hnot, hScard]
      · intro w hw
        simp only [Finset.mem_insert] at hw
        rcases hw with rfl | hw
        · exact ⟨huv, hadj⟩
        · exact hSprop w hw
  | @doneI i c v k d lb hdc hiN =>
      have hnot := not_mem_R_of_inner hInv hdc
      obtain ⟨h1, h2, h3, h4, h5, -, -⟩ := hInv
      obtain ⟨hv, hk⟩ := h4 hiN
      exact ⟨h1, hiN, h3, by omega, by rw [hk, filter_lt_succ_of_not_mem hnot]⟩
  | @nextRound i c k hi =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      refine ⟨by omega, by omega, ?_, Nat.zero_le _, by simp⟩
      simpa [filter_lt_N_eq hs] using h5
  | @lastRound c k =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := hInv
      refine ⟨by omega, by omega, ?_, by omega, fun _ => ⟨rfl, rfl⟩, by omega, ∅, by simp, by simp,
        by simp⟩
      simpa [filter_lt_N_eq hs] using h5
  | @accept c k d lb hdc =>
      have hnot := not_mem_R_of_inner hInv hdc
      intro hmem
      exact hnot (R_subset_succ N hmem)

/-- **Soundness**: if the complement machine accepts, then `t` is not reachable from `s`. -/
theorem not_reachable_of_accept (hs : s < N)
    (h : Relation.ReflTransGen (Step N adj s t) start .acc) :
    ¬ Relation.ReflTransGen (Edge N adj) s t := by
  have key : ∀ x : Cfg, Relation.ReflTransGen (Step N adj s t) start x → Inv N adj s t x := by
    intro x hx
    induction hx with
    | refl => exact Inv_start hs
    | tail _ hbc ih => exact Inv_step hs hbc ih
  have hacc : Inv N adj s t .acc := key _ h
  intro hreach
  exact hacc (mem_R_of_reachable hs hreach)

/-! ### Completeness: constructing an accepting run -/

/-- A walk of length `≤ i` from `s` to `p` can be guessed in the `pathA` phase. -/
theorem reach_pathA {t i c v k : ℕ} :
    ∀ l, l ≤ i → ∀ p ∈ R N adj s l, ∃ l' ≤ l,
      Relation.ReflTransGen (Step N adj s t) (.pathA i c v k s 0) (.pathA i c v k p l') := by
  intro l
  induction l with
  | zero =>
      intro _ p hp
      simp only [R_zero, Finset.mem_singleton] at hp
      subst hp
      exact ⟨0, le_refl _, .refl⟩
  | succ l ih =>
      intro hl p hp
      rw [mem_R_succ_iff] at hp
      rcases hp with hp | ⟨hpN, u, hu, hadj⟩
      · obtain ⟨l', hl', hreach⟩ := ih (by omega) p hp
        exact ⟨l', by omega, hreach⟩
      · obtain ⟨l', hl', hreach⟩ := ih (by omega) u hu
        exact ⟨l' + 1, by omega, hreach.tail (Step.stepA hadj hpN (by omega))⟩

/-- A walk of length `≤ i - 1` from `s` to `p` can be guessed in the `pathB` phase. -/
theorem reach_pathB {t i c v k d u : ℕ} :
    ∀ l, l ≤ i - 1 → ∀ p ∈ R N adj s l, ∃ l' ≤ l,
      Relation.ReflTransGen (Step N adj s t) (.pathB i c v k d u s 0) (.pathB i c v k d u p l') := by
  intro l
  induction l with
  | zero =>
      intro _ p hp
      simp only [R_zero, Finset.mem_singleton] at hp
      subst hp
      exact ⟨0, le_refl _, .refl⟩
  | succ l ih =>
      intro hl p hp
      rw [mem_R_succ_iff] at hp
      rcases hp with hp | ⟨hpN, u', hu, hadj⟩
      · obtain ⟨l', hl', hreach⟩ := ih (by omega) p hp
        exact ⟨l', by omega, hreach⟩
      · obtain ⟨l', hl', hreach⟩ := ih (by omega) u' hu
        exact ⟨l' + 1, by omega, hreach.tail (Step.stepB hadj hpN (by omega))⟩

/-- The inner loop can enumerate all of `R (i-1)`, provided every element of `R (i-1)`
passes the two checks. -/
theorem reach_inner (hs : s < N) {t i c v k : ℕ}
    (hc : c = (R N adj s (i - 1)).card)
    (hcheck : ∀ w ∈ R N adj s (i - 1), w ≠ v ∧ adj w v = false) :
    ∀ n lb d, ((R N adj s (i - 1)).filter (fun x => lb ≤ x)).card = n → d + n = c →
      ∃ lb', Relation.ReflTransGen (Step N adj s t)
        (.inner i c v k d lb) (.inner i c v k c lb') := by
  intro n
  induction n with
  | zero => intro lb d _ hdn; exact ⟨lb, by rw [show d = c by omega]⟩
  | succ n ih =>
      intro lb d hfilter hdn
      have hne : ((R N adj s (i - 1)).filter (fun x => lb ≤ x)).Nonempty := by
        rw [← Finset.card_pos, hfilter]; omega
      set u := ((R N adj s (i - 1)).filter (fun x => lb ≤ x)).min' hne with hu_def
      have humem := Finset.min'_mem _ hne
      rw [← hu_def] at humem
      simp only [Finset.mem_filter] at humem
      obtain ⟨huR, hlbu⟩ := humem
      have huN : u < N := by simpa using R_subset_range hs (i - 1) huR
      have hstep1 : Step N adj s t (.inner i c v k d lb) (.pathB i c v k d u s 0) :=
        Step.startB (by omega) hlbu huN
      obtain ⟨l', hl', hreach⟩ := reach_pathB (t := t) (i := i) (c := c) (v := v) (k := k)
        (d := d) (u := u)
        (i - 1) (by omega) u huR
      obtain ⟨hne_uv, hadj_uv⟩ := hcheck u huR
      have hstep2 : Step N adj s t (.pathB i c v k d u u l') (.inner i c v k (d + 1) (u + 1)) :=
        Step.doneB rfl hne_uv hadj_uv
      have hsplit : ((R N adj s (i - 1)).filter (fun x => lb ≤ x)) =
          insert u ((R N adj s (i - 1)).filter (fun x => u + 1 ≤ x)) := by
        ext x
        simp only [Finset.mem_filter, Finset.mem_insert]
        constructor
        · rintro ⟨hx, hlx⟩
          have hxu : u ≤ x := Finset.min'_le _ x (by simp only [Finset.mem_filter]; exact ⟨hx, hlx⟩)
          rcases Nat.eq_or_lt_of_le hxu with h | h
          · exact Or.inl h.symm
          · exact Or.inr ⟨hx, by omega⟩
        · rintro (rfl | ⟨hx, hlx⟩)
          · exact ⟨huR, hlbu⟩
          · exact ⟨hx, by omega⟩
      have hcard : ((R N adj s (i - 1)).filter (fun x => u + 1 ≤ x)).card = n := by
        have hnot : u ∉ ((R N adj s (i - 1)).filter (fun x => u + 1 ≤ x)) := by
          simp only [Finset.mem_filter]
          omega
        rw [hsplit, Finset.card_insert_of_notMem hnot] at hfilter
        omega
      obtain ⟨lb', hrest⟩ := ih (u + 1) (d + 1) hcard (by omega)
      exact ⟨lb', ((Relation.ReflTransGen.single hstep1).trans hreach).tail hstep2 |>.trans hrest⟩

/-- The outer loop of round `i` scans all vertices, counting those in `R i`. -/
theorem reach_outer (hs : s < N) {t i c : ℕ} (hi : 1 ≤ i) (hiN : i ≤ N)
    (hc : c = (R N adj s (i - 1)).card) :
    ∀ v ≤ N, Relation.ReflTransGen (Step N adj s t)
      (.outer i c 0 0) (.outer i c v (((R N adj s i).filter (fun x => x < v)).card)) := by
  intro v
  induction v with
  | zero => intro _; simpa using Relation.ReflTransGen.refl
  | succ v ih =>
      intro hv
      have hvN : v < N := by omega
      have hprev := ih (by omega)
      set k := ((R N adj s i).filter (fun x => x < v)).card with hk
      by_cases hmem : v ∈ R N adj s i
      · obtain ⟨l', hl', hreach⟩ := reach_pathA (t := t) (i := i) (c := c) (v := v) (k := k)
          i (le_refl _) v hmem
        have h1 : Step N adj s t (.outer i c v k) (.pathA i c v k s 0) := Step.startA hvN
        have h2 : Step N adj s t (.pathA i c v k v l') (.outer i c (v + 1) (k + 1)) :=
          Step.doneA rfl
        have : Relation.ReflTransGen (Step N adj s t) (.outer i c 0 0) (.outer i c (v+1) (k+1)) :=
          ((hprev.tail h1).trans hreach).tail h2
        rwa [filter_lt_succ_of_mem hmem]
      · have hcheck : ∀ w ∈ R N adj s (i - 1), w ≠ v ∧ adj w v = false := by
          intro w hw
          constructor
          · rintro rfl
            exact hmem (R_mono (by omega) hw)
          · by_contra hcon
            simp only [Bool.not_eq_false] at hcon
            have : v ∈ R N adj s (i - 1 + 1) := mem_R_succ_of_edge hw hvN hcon
            rw [show i - 1 + 1 = i by omega] at this
            exact hmem this
        obtain ⟨lb', hinner⟩ := reach_inner hs (t := t) (v := v) (k := k) hc hcheck
          ((R N adj s (i - 1)).card) 0 0 (by simp) (by omega)
        have h1 : Step N adj s t (.outer i c v k) (.inner i c v k 0 0) := Step.startI hvN
        have h2 : Step N adj s t (.inner i c v k c lb') (.outer i c (v + 1) k) :=
          Step.doneI rfl hiN
        have : Relation.ReflTransGen (Step N adj s t) (.outer i c 0 0) (.outer i c (v+1) k) :=
          ((hprev.tail h1).trans hinner).tail h2
        rwa [filter_lt_succ_of_not_mem hmem]

/-- The machine reaches the beginning of round `i`, with the correct count `|R (i-1)|`. -/
theorem reach_round (hs : s < N) {t : ℕ} :
    ∀ i, 1 ≤ i → i ≤ N → Relation.ReflTransGen (Step N adj s t)
      start (.outer i ((R N adj s (i - 1)).card) 0 0) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
      intro _ hiN
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · simp only [start, Nat.add_sub_cancel, R_zero, Finset.card_singleton]
        exact .refl
      · have hprev := ih hipos (by omega)
        have houter := reach_outer hs (t := t) (i := i) (c := ((R N adj s (i - 1)).card))
          hipos (by omega) rfl N (le_refl _)
        have hlast : Step N adj s t
            (.outer i ((R N adj s (i-1)).card) N ((R N adj s i).card))
            (.outer (i + 1) ((R N adj s i).card) 0 0) := Step.nextRound (by omega)
        have := (hprev.trans houter)
        rw [filter_lt_N_eq hs] at this
        simpa using this.tail hlast

/-- **Completeness**: if `t` is not reachable from `s`, the complement machine accepts. -/
theorem accept_of_not_reachable (hs : s < N) {t : ℕ} (ht : t < N)
    (h : ¬ Relation.ReflTransGen (Edge N adj) s t) :
    Relation.ReflTransGen (Step N adj s t) start .acc := by
  have htR : t ∉ R N adj s N := fun hmem => h (reachable_of_mem_R hs N t hmem)
  have hN : 1 ≤ N := by omega
  have hround := reach_round (adj := adj) hs (t := t) N hN (le_refl _)
  have houter := reach_outer hs (t := t) (i := N) (c := ((R N adj s (N - 1)).card))
    hN (le_refl _) rfl N (le_refl _)
  have hreach1 := hround.trans houter
  rw [filter_lt_N_eq hs] at hreach1
  have hlast : Step N adj s t
      (.outer N ((R N adj s (N-1)).card) N ((R N adj s N).card))
      (.inner (N + 1) ((R N adj s N).card) t 0 0 0) := Step.lastRound
  have hcheck : ∀ w ∈ R N adj s (N + 1 - 1), w ≠ t ∧ adj w t = false := by
    intro w hw
    rw [show N + 1 - 1 = N by omega] at hw
    constructor
    · rintro rfl; exact htR hw
    · by_contra hcon
      simp only [Bool.not_eq_false] at hcon
      have : t ∈ R N adj s (N + 1) := mem_R_succ_of_edge hw ht hcon
      rw [R_stabilises hs] at this
      exact htR this
  obtain ⟨lb', hinner⟩ := reach_inner hs (t := t) (i := N + 1)
    (c := ((R N adj s N).card)) (v := t) (k := 0)
    (by rw [show N + 1 - 1 = N by omega]) hcheck
    ((R N adj s N).card) 0 0 (by rw [show N + 1 - 1 = N by omega]; simp) (by omega)
  have hacc : Step N adj s t (.inner (N + 1) ((R N adj s N).card) t 0 ((R N adj s N).card) lb')
      .acc := Step.accept rfl
  exact (((hreach1.tail hlast).trans hinner).tail hacc)

/-- The complement machine accepts exactly when `t` is unreachable from `s`. -/
theorem accept_iff_not_reachable (hs : s < N) {t : ℕ} (ht : t < N) :
    Relation.ReflTransGen (Step N adj s t) start .acc ↔
      ¬ Relation.ReflTransGen (Edge N adj) s t :=
  ⟨not_reachable_of_accept hs, accept_of_not_reachable hs ht⟩

/-! ### The space bound

The complement machine has at most `5 * (N+2)^8` reachable configurations: it uses only
`O(log N)` bits of memory beyond the digraph itself.  Since a nondeterministic machine running
in space `S` on a fixed input has `2^{O(S)}` configurations, this says exactly that the
complement machine also runs in space `O(S)`.
-/

theorem card_R_le (hs : s < N) (i : ℕ) : (R N adj s i).card ≤ N := by
  simpa using Finset.card_le_card (R_subset_range hs i)

/-- An explicit finite set containing every configuration the machine can ever reach. -/
def cfgBound (N : ℕ) : Finset Cfg :=
  ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.outer q.1 q.2.1 q.2.2.1 q.2.2.2) ∪
  ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.pathA q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) ∪
  ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.inner q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2) ∪
  ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.pathB q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2.1
        q.2.2.2.2.2.2.2) ∪
  {Cfg.acc}

theorem card_cfgBound_le (N : ℕ) : (cfgBound N).card ≤ 5 * (N + 2) ^ 8 := by
  have h4 : (N + 2) ^ 4 ≤ (N + 2) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h6 : (N + 2) ^ 6 ≤ (N + 2) ^ 8 := Nat.pow_le_pow_right (by omega) (by omega)
  have h1 : 1 ≤ (N + 2) ^ 8 := Nat.one_le_pow _ _ (by omega)
  have e1 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2)).image
      fun q => Cfg.outer q.1 q.2.1 q.2.2.1 q.2.2.2).card ≤ (N+2)^4 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e2 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.pathA q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2).card ≤ (N+2)^6 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e3 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2)).image
      fun q => Cfg.inner q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2).card ≤ (N+2)^6 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e4 : ((Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ Finset.range (N+2) ×ˢ
      Finset.range (N+2)).image
      fun q => Cfg.pathB q.1 q.2.1 q.2.2.1 q.2.2.2.1 q.2.2.2.2.1 q.2.2.2.2.2.1 q.2.2.2.2.2.2.1
        q.2.2.2.2.2.2.2).card ≤ (N+2)^8 := by
    refine le_trans Finset.card_image_le (le_of_eq ?_)
    simp [Finset.card_product]
    ring
  have e5 : ({Cfg.acc} : Finset Cfg).card = 1 := rfl
  unfold cfgBound
  refine le_trans (Finset.card_union_le _ _) ?_
  refine le_trans (Nat.add_le_add_right (Finset.card_union_le _ _) _) ?_
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) ?_
  refine le_trans (Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_right (Finset.card_union_le _ _) _) _) _) ?_
  rw [e5]
  omega

theorem Inv_of_reachable (hs : s < N) {t : ℕ} {x : Cfg}
    (hx : Relation.ReflTransGen (Step N adj s t) start x) : Inv N adj s t x := by
  induction hx with
  | refl => exact Inv_start hs
  | tail _ hbc ih => exact Inv_step hs hbc ih

theorem mem_cfgBound_of_Inv (hs : s < N) {t : ℕ} (ht : t < N) {x : Cfg}
    (h : Inv N adj s t x) : x ∈ cfgBound N := by
  have hfil : ∀ i v : ℕ, ((R N adj s i).filter (fun y => y < v)).card ≤ N := fun i v =>
    le_trans (Finset.card_le_card (Finset.filter_subset _ _)) (card_R_le hs i)
  cases x with
  | outer i c v k =>
      obtain ⟨h1, h2, h3, h4, h5⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hk : k ≤ N := h5 ▸ hfil i v
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ ?_)))
      refine Finset.mem_image.2 ⟨(i, c, v, k), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | pathA i c v k p l =>
      obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hk : k ≤ N := h5 ▸ hfil i v
      have hp : p < N := by simpa using R_subset_range hs l h6
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_right _ ?_)))
      refine Finset.mem_image.2 ⟨(i, c, v, k, p, l), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | inner i c v k d lb =>
      obtain ⟨h1, h2, h3, h4, h5, h6, S, hS, hScard, -⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hvk : v ≤ N ∧ k ≤ N := by
        rcases Nat.lt_or_ge N i with hi | hi
        · obtain ⟨hv, hk⟩ := h5 hi; exact ⟨by omega, by omega⟩
        · obtain ⟨hv, hk⟩ := h4 hi; exact ⟨by omega, hk ▸ hfil i v⟩
      have hd : d ≤ N := by
        rw [← hScard]
        exact le_trans (Finset.card_le_card (hS.trans (Finset.filter_subset _ _)))
          (card_R_le hs _)
      refine Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ ?_))
      refine Finset.mem_image.2 ⟨(i, c, v, k, d, lb), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | pathB i c v k d u p l =>
      obtain ⟨h1, h2, h3, h4, h5, ⟨S, hS, hScard, -⟩, h7, h8, h9⟩ := h
      have hc : c ≤ N := h3 ▸ card_R_le hs _
      have hvk : v ≤ N ∧ k ≤ N := by
        rcases Nat.lt_or_ge N i with hi | hi
        · obtain ⟨hv, hk⟩ := h5 hi; exact ⟨by omega, by omega⟩
        · obtain ⟨hv, hk⟩ := h4 hi; exact ⟨by omega, hk ▸ hfil i v⟩
      have hd : d ≤ N := by
        rw [← hScard]
        exact le_trans (Finset.card_le_card (hS.trans (Finset.filter_subset _ _)))
          (card_R_le hs _)
      have hp : p < N := by simpa using R_subset_range hs l h7
      refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      refine Finset.mem_image.2 ⟨(i, c, v, k, d, u, p, l), ?_, rfl⟩
      simp only [Finset.mem_product, Finset.mem_range]
      omega
  | acc => exact Finset.mem_union_right _ (Finset.mem_singleton_self _)

/-- **The space bound**: all configurations reachable by the complement machine lie in an
explicit set of size at most `5 * (N+2)^8`. -/
theorem reachable_mem_cfgBound (hs : s < N) {t : ℕ} (ht : t < N) {x : Cfg}
    (hx : Relation.ReflTransGen (Step N adj s t) start x) : x ∈ cfgBound N :=
  mem_cfgBound_of_Inv hs ht (Inv_of_reachable hs hx)

/-! ### Locality: each transition inspects at most one entry of the adjacency matrix

This shows that the complement machine is a *bona fide* machine: a transition is not allowed
to perform a hidden computation on the input graph, it may consult a single entry of the
adjacency matrix, determined by the two configurations involved. -/

/-- The single adjacency entry (if any) that a transition from `x` to `y` inspects. -/
def query : Cfg → Cfg → ℕ × ℕ
  | .pathA _ _ _ _ p _, .pathA _ _ _ _ p' _ => (p, p')
  | .pathB _ _ _ _ _ _ p _, .pathB _ _ _ _ _ _ p' _ => (p, p')
  | .pathB _ _ v _ _ u _ _, .inner _ _ _ _ _ _ => (u, v)
  | _, _ => (0, 0)

/-- **Locality**: whether the machine may pass from `x` to `y` depends on the input graph only
through the single entry `query x y` of its adjacency matrix. -/
theorem step_local (N s t : ℕ) (adj₁ adj₂ : ℕ → ℕ → Bool) (x y : Cfg)
    (h : adj₁ (query x y).1 (query x y).2 = adj₂ (query x y).1 (query x y).2) :
    Step N adj₁ s t x y ↔ Step N adj₂ s t x y := by
  have key : ∀ (e₁ e₂ : ℕ → ℕ → Bool), e₁ (query x y).1 (query x y).2 =
      e₂ (query x y).1 (query x y).2 → Step N e₁ s t x y → Step N e₂ s t x y := by
    intro e₁ e₂ he hstep
    cases hstep with
    | startA hv => exact Step.startA hv
    | stepA hadj hp' hl =>
        simp only [query] at he
        exact Step.stepA (by rw [← he]; exact hadj) hp' hl
    | doneA hpv => exact Step.doneA hpv
    | startI hv => exact Step.startI hv
    | startB hdc hlb hu => exact Step.startB hdc hlb hu
    | stepB hadj hp' hl =>
        simp only [query] at he
        exact Step.stepB (by rw [← he]; exact hadj) hp' hl
    | doneB hpu huv hadj =>
        simp only [query] at he
        exact Step.doneB hpu huv (by rw [← he]; exact hadj)
    | doneI hdc hiN => exact Step.doneI hdc hiN
    | nextRound hi => exact Step.nextRound hi
    | lastRound => exact Step.lastRound
    | accept hdc => exact Step.accept hdc
  exact ⟨key adj₁ adj₂ h, key adj₂ adj₁ h.symm⟩

end IS

/-!
## `NL = coNL`

A nondeterministic machine running in space `S` on a fixed input has a *configuration graph*:
a finite digraph whose vertices are the (at most `2^{O(S)}`) configurations, with an edge
`x → y` when the machine can pass from `x` to `y` in one step.  The machine accepts iff the
accepting configuration is reachable from the initial one in this graph.

`CS.immerman_szelepcsenyi` below states that the *complement* of such an acceptance condition
is again of exactly the same form: for any finite configuration type `C`, any transition
relation `step`, and any two configurations `a b : C`, non-reachability of `b` from `a` is
equivalent to reachability of an accepting configuration in the configuration graph of the
explicitly constructed machine `IS.Step`, which is uniform in `step` and has only
`5 * (Fintype.card C + 2) ^ 8` reachable configurations (`CS.immerman_szelepcsenyi_space`),
i.e. runs in space `O(S)`.  This is Immerman–Szelepcsényi: `NL = coNL`, and more generally
`NSPACE(S) = coNSPACE(S)` for `S ≥ log`.
-/

open IS

variable {C : Type*} [Fintype C]

/-- An indexing of the configurations of a machine by `{0, …, card C - 1}`. -/
noncomputable def enc (C : Type*) [Fintype C] : C ≃ Fin (Fintype.card C) := Fintype.equivFin C

/-- The adjacency matrix of the configuration graph, transported to `ℕ`. -/
noncomputable def adjOf (step : C → C → Bool) : ℕ → ℕ → Bool := fun x y =>
  if hx : x < Fintype.card C then
    if hy : y < Fintype.card C then
      step ((enc C).symm ⟨x, hx⟩) ((enc C).symm ⟨y, hy⟩)
    else false
  else false

theorem adjOf_apply (step : C → C → Bool) (x y : C) :
    adjOf step (enc C x : ℕ) (enc C y : ℕ) = step x y := by
  simp only [adjOf, dif_pos (enc C x).isLt, dif_pos (enc C y).isLt]
  simp

theorem reachable_transport (step : C → C → Bool) (a b : C) :
    Relation.ReflTransGen (fun x y => step x y = true) a b ↔
      Relation.ReflTransGen (Edge (Fintype.card C) (adjOf step)) (enc C a : ℕ) (enc C b : ℕ) := by
  constructor
  · intro h
    induction h with
    | refl => exact .refl
    | @tail y z _ hyz ih =>
        refine ih.tail ⟨(enc C y).isLt, (enc C z).isLt, ?_⟩
        rw [adjOf_apply]
        exact hyz
  · intro h
    have key : ∀ z : ℕ, Relation.ReflTransGen (Edge (Fintype.card C) (adjOf step)) (enc C a : ℕ) z →
        ∃ y : C, z = (enc C y : ℕ) ∧ Relation.ReflTransGen (fun x y => step x y = true) a y := by
      intro z hz
      induction hz with
      | refl => exact ⟨a, rfl, .refl⟩
      | @tail p q _ hpq ih =>
          obtain ⟨y, rfl, hay⟩ := ih
          obtain ⟨-, hqlt, hadj⟩ := hpq
          refine ⟨(enc C).symm ⟨q, hqlt⟩, by simp, hay.tail ?_⟩
          rw [← adjOf_apply step y ((enc C).symm ⟨q, hqlt⟩)]
          simpa using hadj
    obtain ⟨y, hy, hay⟩ := key _ h
    have : b = y := (enc C).injective (Fin.val_injective hy)
    rwa [this]

/-- **Immerman–Szelepcsényi: `NL = coNL`.**

Let `step` be the one-step relation of a nondeterministic machine with (finitely many)
configurations `C`, let `a` be its initial and `b` its accepting configuration, so that the
machine *rejects* exactly when `b` is not reachable from `a`.

Then rejection is itself an acceptance condition of the same shape, for the explicitly
constructed machine `IS.Step`: `b` is unreachable from `a` if and only if the configuration
`IS.Cfg.acc` is reachable from `IS.start` in the configuration graph of `IS.Step`.

The new machine is built uniformly from `step` and (see
`CS.immerman_szelepcsenyi_space`) has at most `5 * (Fintype.card C + 2) ^ 8` reachable
configurations; so if the original machine runs in space `S ≥ log n`, the new one runs in
space `O(S)`.  With `S = log n` this is `NL = coNL`. -/
theorem immerman_szelepcsenyi {C : Type*} [Fintype C] (step : C → C → Bool) (a b : C) :
    ¬ Relation.ReflTransGen (fun x y => step x y = true) a b ↔
      Relation.ReflTransGen
        (IS.Step (Fintype.card C) (adjOf step) (enc C a : ℕ) (enc C b : ℕ))
        IS.start IS.Cfg.acc := by
  rw [reachable_transport step a b]
  exact (IS.accept_iff_not_reachable (enc C a).isLt (enc C b).isLt).symm

/-- **The space bound for the complement machine.**  Every configuration reachable by the
machine of `CS.immerman_szelepcsenyi` lies in an explicit set of at most
`5 * (Fintype.card C + 2) ^ 8` configurations: the construction costs only a constant factor
in space. -/
theorem immerman_szelepcsenyi_space {C : Type*} [Fintype C] (step : C → C → Bool) (a b : C) :
    ∃ F : Finset IS.Cfg, F.card ≤ 5 * (Fintype.card C + 2) ^ 8 ∧
      ∀ x : IS.Cfg, Relation.ReflTransGen
        (IS.Step (Fintype.card C) (adjOf step) (enc C a : ℕ) (enc C b : ℕ)) IS.start x → x ∈ F :=
  ⟨IS.cfgBound (Fintype.card C), IS.card_cfgBound_le _,
    fun _ hx => IS.reachable_mem_cfgBound (enc C a).isLt (enc C b).isLt hx⟩

end CS

