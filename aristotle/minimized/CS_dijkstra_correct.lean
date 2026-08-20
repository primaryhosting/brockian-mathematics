import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Statement: Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

variable {V : Type*} [Fintype V] [DecidableEq V]

/-! ## Walks and shortest-path distances

A weighted digraph on the finite vertex type `V` is given by a weight function
`w : V → V → ℕ∞`, where `w u v = ⊤` encodes the absence of an edge from `u` to `v`.
All weights are nonnegative by construction. -/

/-- `walkCost w u l` is the total weight of the walk that starts at `u` and then visits
the vertices of `l` in order. -/

def walkCost (w : V → V → ℕ∞) : V → List V → ℕ∞
  | _, [] => 0
  | u, v :: l => w u v + walkCost w v l

omit [Fintype V] [DecidableEq V] in

@[simp] theorem walkCost_cons (w : V → V → ℕ∞) (u v : V) (l : List V) :
    walkCost w u (v :: l) = w u v + walkCost w v l := rfl

omit [Fintype V] [DecidableEq V] in

theorem walkCost_append (w : V → V → ℕ∞) (u : V) (l : List V) (v : V) :
    walkCost w u (l ++ [v]) = walkCost w u l + w (l.getLastD u) v := by
  induction l generalizing u with
  | nil => simp
  | cons a t ih =>
      rw [List.cons_append, walkCost_cons, walkCost_cons, ih, List.getLastD_cons, add_assoc]

/-- The shortest-path distance from `src` to `t`: the infimum of the costs of all walks
from `src` to `t` (`⊤` if there is no finite-cost walk). -/

noncomputable def sdist (w : V → V → ℕ∞) (src t : V) : ℕ∞ :=
  sInf {c | ∃ l : List V, l.getLastD src = t ∧ walkCost w src l = c}

omit [Fintype V] [DecidableEq V] in

theorem sdist_le_walkCost (w : V → V → ℕ∞) (src t : V) {l : List V}
    (hl : l.getLastD src = t) : sdist w src t ≤ walkCost w src l :=
  sInf_le ⟨l, hl, rfl⟩

omit [Fintype V] [DecidableEq V] in

theorem le_sdist (w : V → V → ℕ∞) (src t : V) {c : ℕ∞}
    (h : ∀ l : List V, l.getLastD src = t → c ≤ walkCost w src l) : c ≤ sdist w src t :=
  le_sInf (by rintro b ⟨l, hl, rfl⟩; exact h l hl)

omit [Fintype V] [DecidableEq V] in

theorem exists_walk_sdist (w : V → V → ℕ∞) (src t : V) :
    ∃ l : List V, l.getLastD src = t ∧ walkCost w src l = sdist w src t := by
  have hne : {c : ℕ∞ | ∃ l : List V, l.getLastD src = t ∧ walkCost w src l = c}.Nonempty :=
    ⟨walkCost w src [t], [t], rfl, rfl⟩
  simpa [sdist, Set.mem_setOf_eq] using csInf_mem hne

omit [Fintype V] [DecidableEq V] in

theorem sdist_triangle (w : V → V → ℕ∞) (src t v : V) :
    sdist w src v ≤ sdist w src t + w t v := by
  obtain ⟨l, hl, hc⟩ := exists_walk_sdist w src t
  have h : sdist w src v ≤ walkCost w src (l ++ [v]) := by
    refine sdist_le_walkCost w src v ?_
    simp
  rwa [walkCost_append, hl, hc] at h

/-! ## The algorithm

The state of the algorithm is a pair `(S, d)` where `S` is the set of settled vertices and
`d` the current tentative distance function.  One step picks an unsettled vertex `u` of
minimal tentative distance, settles it, and relaxes all edges out of `u`. -/

/-- One step of Dijkstra's algorithm. -/

noncomputable def stepD (w : V → V → ℕ∞) (st : Finset V × (V → ℕ∞)) : Finset V × (V → ℕ∞) :=
  if h : (univ \ st.1).Nonempty then
    let u := ((univ \ st.1).exists_min_image st.2 h).choose
    (insert u st.1, fun v => st.2 v ⊓ (st.2 u + w u v))
  else st

/-- The state of Dijkstra's algorithm from source `src` after `n` steps. -/

noncomputable def dijkstraAux (w : V → V → ℕ∞) (src : V) : ℕ → Finset V × (V → ℕ∞)
  | 0 => (∅, fun v => if v = src then 0 else ⊤)
  | n + 1 => stepD w (dijkstraAux w src n)

/-- Dijkstra's algorithm: run `card V` steps from the source `src` and read off the
distance function. -/

noncomputable def dijkstra (w : V → V → ℕ∞) (src t : V) : ℕ∞ :=
  (dijkstraAux w src (Fintype.card V)).2 t

/-- `tent w src S v` is the least cost of a walk from `src` to `v` whose last edge leaves a
settled vertex (or the empty walk, when `v = src`); this is what the algorithm stores. -/

noncomputable def tent (w : V → V → ℕ∞) (src : V) (S : Finset V) (v : V) : ℕ∞ :=
  (if v = src then 0 else ⊤) ⊓ S.inf fun s => sdist w src s + w s v

omit [Fintype V] in

theorem sdist_le_tent (w : V → V → ℕ∞) (src : V) (S : Finset V) (v : V) :
    sdist w src v ≤ tent w src S v := by
  refine le_inf ?_ ?_
  · split
    · subst ‹v = src›; simp
    · exact le_top
  · exact Finset.le_inf fun s _ => sdist_triangle w src s v

theorem stepD_spec (w : V → V → ℕ∞) (S : Finset V) (d : V → ℕ∞) (h : (univ \ S).Nonempty) :
    ∃ u, u ∉ S ∧ (∀ v ∉ S, d u ≤ d v) ∧
      stepD w (S, d) = (insert u S, fun v => d v ⊓ (d u + w u v)) := by
  classical
  obtain ⟨hmem, hmin⟩ := ((univ \ S).exists_min_image d h).choose_spec
  refine ⟨((univ \ S).exists_min_image d h).choose, (mem_sdiff.1 hmem).2, ?_, ?_⟩
  · intro v hv
    exact hmin v (mem_sdiff.2 ⟨mem_univ v, hv⟩)
  · simp only [stepD, dif_pos h]

omit [Fintype V] in
/-- Key step: if `u` is an unsettled vertex of minimal tentative distance, then every walk
from `src` ending outside `S` costs at least `d u`. -/

theorem key_le_walkCost (w : V → V → ℕ∞) (src : V) (S : Finset V) (d : V → ℕ∞)
    (hd : ∀ v, d v = tent w src S v) (u : V) (hmin : ∀ v ∉ S, d u ≤ d v) :
    ∀ l : List V, l.getLastD src ∉ S → d u ≤ walkCost w src l := by
  intro l
  induction l using List.reverseRecOn with
  | nil =>
      intro hsrc
      have := hmin src (by simpa using hsrc)
      simpa [hd src, tent] using this
  | append_singleton l v ih =>
      intro hv
      rw [List.getLastD_concat] at hv
      rw [walkCost_append]
      set z := l.getLastD src with hz
      by_cases hzS : z ∈ S
      · -- the last edge leaves a settled vertex
        have h1 : sdist w src z ≤ walkCost w src l := sdist_le_walkCost w src z hz.symm
        have h2 : tent w src S v ≤ sdist w src z + w z v :=
          le_trans inf_le_right (Finset.inf_le hzS)
        calc d u ≤ d v := hmin v (by simpa using hv)
          _ = tent w src S v := hd v
          _ ≤ sdist w src z + w z v := h2
          _ ≤ walkCost w src l + w z v := by gcongr
      · exact le_trans (ih hzS) (by simp)

/-- The invariant maintained by Dijkstra's algorithm. -/

def Inv (w : V → V → ℕ∞) (src : V) (S : Finset V) (d : V → ℕ∞) : Prop :=
  (∀ v, d v = tent w src S v) ∧ (∀ s ∈ S, d s = sdist w src s) ∧
    (∀ s ∈ S, ∀ v ∉ S, d s ≤ d v)

theorem inv_init (w : V → V → ℕ∞) (src : V) :
    Inv w src (dijkstraAux w src 0).1 (dijkstraAux w src 0).2 := by
  refine ⟨fun v => ?_, by simp [dijkstraAux], by simp [dijkstraAux]⟩
  simp [dijkstraAux, tent]

theorem inv_step (w : V → V → ℕ∞) (src : V) (S : Finset V) (d : V → ℕ∞)
    (h : Inv w src S d) : Inv w src (stepD w (S, d)).1 (stepD w (S, d)).2 := by
  obtain ⟨hd, hsdist, hmono⟩ := h
  by_cases hS : (univ \ S).Nonempty
  · obtain ⟨u, huS, hmin, hstep⟩ := stepD_spec w S d hS
    rw [hstep]
    -- the chosen vertex is correctly settled
    have hu : d u = sdist w src u := by
      refine le_antisymm ?_ ?_
      · refine le_sdist w src u fun l hl => ?_
        exact key_le_walkCost w src S d hd u hmin l (by rw [hl]; exact huS)
      · rw [hd u]; exact sdist_le_tent w src S u
    dsimp only
    refine ⟨fun v => ?_, ?_, ?_⟩
    · show d v ⊓ (d u + w u v) = tent w src (insert u S) v
      rw [hd v, hu]
      simp only [tent, Finset.inf_insert]
      ac_rfl
    · intro s hs
      rcases Finset.mem_insert.1 hs with rfl | hs
      · show d s ⊓ (d s + w s s) = sdist w src s
        rw [inf_eq_left.2 le_self_add]; exact hu
      · show d s ⊓ (d u + w u s) = sdist w src s
        have h2 : d s ≤ d u + w u s := le_trans (hmono s hs u huS) le_self_add
        rw [inf_eq_left.2 h2]
        exact hsdist s hs
    · intro s hs v hv
      have hvS : v ∉ S := fun hc => hv (Finset.mem_insert_of_mem hc)
      refine le_inf (le_trans inf_le_left ?_) (le_trans inf_le_left ?_)
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact hmin v hvS
        · exact hmono s hs v hvS
      · rcases Finset.mem_insert.1 hs with rfl | hs
        · exact le_self_add
        · exact le_trans (hmono s hs u huS) le_self_add
  · rw [show stepD w (S, d) = (S, d) by simp [stepD, hS]]
    exact ⟨hd, hsdist, hmono⟩

theorem inv_aux (w : V → V → ℕ∞) (src : V) (n : ℕ) :
    Inv w src (dijkstraAux w src n).1 (dijkstraAux w src n).2 := by
  induction n with
  | zero => exact inv_init w src
  | succ n ih =>
      have : dijkstraAux w src (n + 1) = stepD w ((dijkstraAux w src n).1,
          (dijkstraAux w src n).2) := by
        simp [dijkstraAux]
      rw [this]
      exact inv_step w src _ _ ih

/-- After `n` steps, either all vertices are settled or at least `n` of them are. -/

theorem card_visited (w : V → V → ℕ∞) (src : V) (n : ℕ) :
    (dijkstraAux w src n).1 = univ ∨ n ≤ (dijkstraAux w src n).1.card := by
  induction n with
  | zero => right; simp
  | succ n ih =>
      have hstep : dijkstraAux w src (n + 1) = stepD w ((dijkstraAux w src n).1,
          (dijkstraAux w src n).2) := by simp [dijkstraAux]
      rcases ih with h | h
      · left
        have : ¬ (univ \ (dijkstraAux w src n).1).Nonempty := by
          simp [h]
        rw [hstep, show stepD w ((dijkstraAux w src n).1, (dijkstraAux w src n).2)
          = ((dijkstraAux w src n).1, (dijkstraAux w src n).2) by simp [stepD, this]]
        exact h
      · by_cases hS : (univ \ (dijkstraAux w src n).1).Nonempty
        · obtain ⟨u, huS, _, heq⟩ := stepD_spec w (dijkstraAux w src n).1
            (dijkstraAux w src n).2 hS
          right
          rw [hstep, heq]
          simpa [Finset.card_insert_of_notMem huS] using h
        · left
          have : univ \ (dijkstraAux w src n).1 = ∅ := Finset.not_nonempty_iff_eq_empty.1 hS
          have h2 : (dijkstraAux w src n).1 = univ := by
            have := Finset.sdiff_eq_empty_iff_subset.1 this
            exact Finset.eq_univ_of_forall fun v => this (mem_univ v)
          rw [hstep, show stepD w ((dijkstraAux w src n).1, (dijkstraAux w src n).2)
            = ((dijkstraAux w src n).1, (dijkstraAux w src n).2) by simp [stepD, hS]]
          exact h2

theorem visited_eq_univ (w : V → V → ℕ∞) (src : V) :
    (dijkstraAux w src (Fintype.card V)).1 = univ := by
  rcases card_visited w src (Fintype.card V) with h | h
  · exact h
  · exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) h)

/-- **Correctness of Dijkstra's algorithm.**  On a finite digraph with nonnegative weights
`w : V → V → ℕ∞` (`⊤` meaning "no edge"), the value computed by Dijkstra's algorithm from
`src` at `t` is the shortest-path distance from `src` to `t`, i.e. the infimum of the costs
of all walks from `src` to `t`. -/

theorem dijkstra_correct (w : V → V → ℕ∞) (src t : V) :
    dijkstra w src t = sdist w src t := by
  have h := (inv_aux w src (Fintype.card V)).2.1
  exact h t (by rw [visited_eq_univ]; exact mem_univ t)

/-! ## A sanity check that the model is non-degenerate

On the graph with vertices `0, 1, 2`, edges `0 →(1) 1`, `1 →(1) 2` and `0 →(5) 2`, the
shortest distance from `0` to `2` is at most `2`, strictly less than the direct edge. -/
