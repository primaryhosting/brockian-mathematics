/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

universe u

variable {V : Type u}

/-! ## Walks and shortest-path distances

A weighted directed graph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`; the value `⊤` means "no edge", and all weights are nonnegative
by construction.  A walk starting at `a` is described by the list `l` of the vertices
it visits after `a`; its endpoint is `l.getLastD a`. -/

/-- The cost of the walk that starts at `a` and then visits the vertices of `l` in order. -/
noncomputable def walkCost (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | a, b :: l => w a b + walkCost w b l

/-- The shortest-path distance from `s` to `t`: the infimum of the costs of all walks
from `s` to `t` (`⊤` if `t` is unreachable from `s`). -/
noncomputable def sdist (w : V → V → ℝ≥0∞) (s t : V) : ℝ≥0∞ :=
  ⨅ l : List V, ⨅ _ : l.getLastD s = t, walkCost w s l

lemma sdist_le (w : V → V → ℝ≥0∞) (s t : V) (l : List V) (hl : l.getLastD s = t) :
    sdist w s t ≤ walkCost w s l :=
  iInf_le_of_le l (iInf_le_of_le hl le_rfl)

lemma le_sdist (w : V → V → ℝ≥0∞) (s t : V) (c : ℝ≥0∞)
    (h : ∀ l : List V, l.getLastD s = t → c ≤ walkCost w s l) : c ≤ sdist w s t :=
  le_iInf fun l => le_iInf fun hl => h l hl

lemma sdist_self (w : V → V → ℝ≥0∞) (s : V) : sdist w s s = 0 := by
  have := sdist_le w s s [] (by simp)
  simpa [walkCost] using this

lemma walkCost_append (w : V → V → ℝ≥0∞) (a t : V) (l : List V) :
    walkCost w a (l ++ [t]) = walkCost w a l + w (l.getLastD a) t := by
  induction l generalizing a with
  | nil => simp [walkCost]
  | cons b l ih =>
      rw [List.cons_append, walkCost, walkCost, ih b, List.getLastD_cons, add_assoc]

/-- The single-edge bound. -/
lemma sdist_le_edge (w : V → V → ℝ≥0∞) (s t : V) : sdist w s t ≤ w s t := by
  have := sdist_le w s t [t] (by simp)
  simpa [walkCost] using this

lemma sdist_triangle (w : V → V → ℝ≥0∞) (s x t : V) :
    sdist w s t ≤ sdist w s x + w x t := by
  have h : sdist w s x + w x t
      = ⨅ l : List V, ⨅ _ : l.getLastD s = x, (walkCost w s l + w x t) := by
    rw [sdist, ENNReal.iInf_add]
    exact iInf_congr fun l => ENNReal.iInf_add
  rw [h]
  refine le_iInf fun l => le_iInf fun hl => ?_
  have hc : walkCost w s (l ++ [t]) = walkCost w s l + w x t := by
    rw [walkCost_append, hl]
  rw [← hc]
  exact sdist_le w s t _ (by simp)

/-- Sanity check that `sdist` is a genuine infimum over walks: in the edgeless graph
(all weights `⊤`) every vertex other than the source is at distance `⊤`. -/
example (s t : V) (hst : t ≠ s) : sdist (fun _ _ => (⊤ : ℝ≥0∞)) s t = ⊤ := by
  refine top_le_iff.mp (le_sdist _ s t ⊤ fun l hl => ?_)
  cases l with
  | nil => exact absurd (by simpa using hl.symm) hst
  | cons b l => simp [walkCost]

/-! ## The algorithm -/

/-- A state of Dijkstra's algorithm: the set of settled vertices together with the
current tentative distances. -/
structure DState (V : Type u) where
  visited : Finset V
  dist : V → ℝ≥0∞

variable [Fintype V] [DecidableEq V]

/-- One step of Dijkstra's algorithm: pick an unvisited vertex `u` of minimal tentative
distance, mark it visited, and relax all edges out of `u`. -/
noncomputable def step (w : V → V → ℝ≥0∞) (st : DState V) : DState V :=
  if h : (st.visitedᶜ : Finset V).Nonempty then
    let u := ((st.visitedᶜ : Finset V).exists_min_image st.dist h).choose
    ⟨insert u st.visited, fun v => st.dist v ⊓ (st.dist u + w u v)⟩
  else st

/-- The initial state: nothing visited, `dist s = 0` and `dist v = ⊤` otherwise. -/
noncomputable def initState (s : V) : DState V :=
  ⟨∅, fun v => if v = s then 0 else ⊤⟩

/-- Dijkstra's algorithm: run `Fintype.card V` steps from the initial state and return
the resulting distance array. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) : V → ℝ≥0∞ :=
  ((step w)^[Fintype.card V] (initState s)).dist

/-- The loop invariant of Dijkstra's algorithm. -/
def Inv (w : V → V → ℝ≥0∞) (s : V) (st : DState V) : Prop :=
  (∀ x ∈ st.visited, st.dist x = sdist w s x) ∧
  (∀ v ∉ st.visited, st.dist v =
      (if v = s then 0 else ⊤) ⊓ ⨅ x ∈ st.visited, (sdist w s x + w x v))

omit [Fintype V] in
lemma inv_init (w : V → V → ℝ≥0∞) (s : V) : Inv w s (initState s) := by
  constructor
  · intro x hx
    simp [initState] at hx
  · intro v _
    simp [initState]

omit [Fintype V] in
lemma inv_le_edge (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st)
    (v : V) (hv : v ∉ st.visited) (x : V) (hx : x ∈ st.visited) :
    st.dist v ≤ sdist w s x + w x v := by
  rw [h.2 v hv]
  exact le_trans inf_le_right (iInf₂_le x hx)

omit [Fintype V] in
lemma inv_le_init (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st)
    (v : V) (hv : v ∉ st.visited) : st.dist v ≤ (if v = s then 0 else ⊤) := by
  rw [h.2 v hv]
  exact inf_le_left

omit [Fintype V] in
/-- From the invariant: tentative distances always dominate the true distances. -/
lemma inv_ge (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st) (v : V) :
    sdist w s v ≤ st.dist v := by
  by_cases hv : v ∈ st.visited
  · rw [h.1 v hv]
  · rw [h.2 v hv]
    refine le_inf ?_ (le_iInf₂ fun x _ => sdist_triangle w s x v)
    by_cases hvs : v = s
    · subst hvs; simp [sdist_self]
    · simp [hvs]

omit [Fintype V] in
/-- Auxiliary induction: any walk that starts inside the visited set and leaves it
witnesses a tentative distance of an unvisited vertex. -/
lemma key_aux (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st) :
    ∀ (l : List V) (a : V), a ∈ st.visited → l.getLastD a ∉ st.visited →
      ∃ y ∉ st.visited, st.dist y ≤ sdist w s a + walkCost w a l := by
  intro l
  induction l with
  | nil => intro a ha hend; exact absurd (by simpa using ha) hend
  | cons b l ih =>
      intro a ha hend
      rw [List.getLastD_cons] at hend
      by_cases hb : b ∈ st.visited
      · obtain ⟨y, hy, hle⟩ := ih b hb hend
        refine ⟨y, hy, hle.trans ?_⟩
        have h1 : sdist w s b ≤ sdist w s a + w a b := sdist_triangle w s a b
        calc sdist w s b + walkCost w b l
            ≤ (sdist w s a + w a b) + walkCost w b l := by gcongr
          _ = sdist w s a + walkCost w a (b :: l) := by rw [walkCost, add_assoc]
      · refine ⟨b, hb, ?_⟩
        have h1 : st.dist b ≤ sdist w s a + w a b := inv_le_edge w s st h b hb a ha
        refine h1.trans ?_
        rw [walkCost, ← add_assoc]
        exact le_self_add

omit [Fintype V] in
/-- Any walk from `s` to an unvisited vertex costs at least the tentative distance of
some unvisited vertex. -/
lemma key (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st)
    (l : List V) (hl : l.getLastD s ∉ st.visited) :
    ∃ y ∉ st.visited, st.dist y ≤ walkCost w s l := by
  by_cases hs : s ∈ st.visited
  · have := key_aux w s st h l s hs hl
    simpa [sdist_self] using this
  · refine ⟨s, hs, ?_⟩
    have h0 : st.dist s ≤ 0 := by simpa using inv_le_init w s st h s hs
    exact h0.trans (zero_le _)

omit [Fintype V] in
/-- The vertex chosen by a step of Dijkstra's algorithm is settled correctly. -/
lemma dist_chosen (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st)
    (u : V) (hu : u ∉ st.visited) (hmin : ∀ y ∉ st.visited, st.dist u ≤ st.dist y) :
    st.dist u = sdist w s u := by
  refine le_antisymm ?_ (inv_ge w s st h u)
  refine le_sdist w s u _ fun l hl => ?_
  obtain ⟨y, hy, hle⟩ := key w s st h l (by rw [hl]; exact hu)
  exact (hmin y hy).trans hle

/-- Description of a step when there is still an unvisited vertex. -/
lemma step_spec (w : V → V → ℝ≥0∞) (st : DState V) (h : (st.visitedᶜ : Finset V).Nonempty) :
    ∃ u : V, u ∉ st.visited ∧ (∀ y ∉ st.visited, st.dist u ≤ st.dist y) ∧
      step w st = ⟨insert u st.visited, fun v => st.dist v ⊓ (st.dist u + w u v)⟩ := by
  obtain ⟨hmem, hmin⟩ := ((st.visitedᶜ : Finset V).exists_min_image st.dist h).choose_spec
  refine ⟨_, by simpa using hmem, fun y hy => hmin y (by simpa using hy), ?_⟩
  simp only [step, dif_pos h]

lemma step_of_not_nonempty (w : V → V → ℝ≥0∞) (st : DState V)
    (h : ¬ (st.visitedᶜ : Finset V).Nonempty) : step w st = st := by
  simp only [step, dif_neg h]

lemma inv_step (w : V → V → ℝ≥0∞) (s : V) (st : DState V) (h : Inv w s st) :
    Inv w s (step w st) := by
  by_cases hne : (st.visitedᶜ : Finset V).Nonempty
  · obtain ⟨u, hu, hmin, hstep⟩ := step_spec w st hne
    have hdu : st.dist u = sdist w s u := dist_chosen w s st h u hu hmin
    rw [hstep]
    constructor
    · intro x hx
      simp only [Finset.mem_insert] at hx
      rcases hx with rfl | hx
      · simp only
        rw [hdu]
        exact inf_eq_left.2 le_self_add
      · have hxx : st.dist x = sdist w s x := h.1 x hx
        simp only
        rw [hxx, hdu]
        exact inf_eq_left.2 (sdist_triangle w s u x)
    · intro v hv
      simp only [Finset.mem_insert, not_or] at hv
      obtain ⟨hvu, hvS⟩ := hv
      simp only
      rw [h.2 v hvS, hdu, Finset.iInf_insert]
      rw [inf_assoc, inf_comm (sdist w s u + w u v) _]
  · rw [step_of_not_nonempty w st hne]
    exact h

lemma card_step (w : V → V → ℝ≥0∞) (st : DState V) (k : ℕ)
    (h : st.visited = Finset.univ ∨ st.visited.card = k) :
    (step w st).visited = Finset.univ ∨ (step w st).visited.card = k + 1 := by
  by_cases hne : (st.visitedᶜ : Finset V).Nonempty
  · obtain ⟨u, hu, -, hstep⟩ := step_spec w st hne
    have hcard : st.visited.card = k := by
      rcases h with h | h
      · exact absurd (h ▸ Finset.mem_univ u) hu
      · exact h
    right
    rw [hstep]
    simp only
    rw [Finset.card_insert_of_notMem hu, hcard]
  · left
    rw [step_of_not_nonempty w st hne]
    have : (st.visitedᶜ : Finset V) = ∅ := Finset.not_nonempty_iff_eq_empty.1 hne
    simpa using congrArg (fun t : Finset V => tᶜ) this

lemma iterate_inv (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) :
    Inv w s ((step w)^[k] (initState s)) ∧
      (((step w)^[k] (initState s)).visited = Finset.univ ∨
        ((step w)^[k] (initState s)).visited.card = k) := by
  induction k with
  | zero => exact ⟨inv_init w s, Or.inr (by simp [initState])⟩
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact ⟨inv_step w s _ ih.1, card_step w _ k ih.2⟩

/-- **Correctness of Dijkstra's algorithm.**  For a finite directed graph with
nonnegative edge weights (encoded by `w : V → V → ℝ≥0∞`, where `⊤` means "no edge"),
the distance array computed by Dijkstra's algorithm from the source `s` equals the
shortest-path distance from `s`, i.e. the infimum of the costs of all walks from `s`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s : V) (v : V) :
    dijkstra w s v = sdist w s v := by
  obtain ⟨hinv, hcard⟩ := iterate_inv w s (Fintype.card V)
  have huniv : ((step w)^[Fintype.card V] (initState s)).visited = Finset.univ := by
    rcases hcard with h | h
    · exact h
    · exact Finset.card_eq_iff_eq_univ _ |>.1 h
  exact hinv.1 v (by rw [huniv]; exact Finset.mem_univ v)

end CS

