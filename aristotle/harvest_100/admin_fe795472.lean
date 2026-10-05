/-
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring, so the
-- required header is repeated as the module docstring just below.)
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-! ## Walks and graph distance

A graph on a vertex type `V` is given by a weight function `w : V → V → ℝ≥0∞`.
Weights live in `ℝ≥0∞`, so they are automatically nonnegative; the value `⊤`
means "no edge".  A walk starting at `u` is a list `l` of the vertices visited
after `u`. -/

section Walks

variable {V : Type*}

/-- The total weight of the walk that starts at `u` and then visits the
vertices of `l` in order. -/
noncomputable def walkWeight (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | u, x :: l => w u x + walkWeight w x l

/-- The endpoint of the walk that starts at `u` and then visits the vertices
of `l` in order. -/
def walkEnd : V → List V → V
  | u, [] => u
  | _, x :: l => walkEnd x l

/-- The shortest-path distance from `s` to `v`: the infimum of the weights of
all walks from `s` to `v` (equal to `⊤` if `v` is unreachable from `s`). -/
noncomputable def graphDist (w : V → V → ℝ≥0∞) (s v : V) : ℝ≥0∞ :=
  ⨅ l : {l : List V // walkEnd s l = v}, walkWeight w s l

lemma walkEnd_append (u : V) (l m : List V) :
    walkEnd u (l ++ m) = walkEnd (walkEnd u l) m := by
  induction l generalizing u with
  | nil => simp [walkEnd]
  | cons x l ih => simp [walkEnd, ih]

lemma walkWeight_append (w : V → V → ℝ≥0∞) (u : V) (l m : List V) :
    walkWeight w u (l ++ m) = walkWeight w u l + walkWeight w (walkEnd u l) m := by
  induction l generalizing u with
  | nil => simp [walkWeight, walkEnd]
  | cons x l ih => simp [walkWeight, walkEnd, ih, add_assoc]

/-- The distance is at most the weight of any particular walk. -/
lemma graphDist_le (w : V → V → ℝ≥0∞) (s v : V) (l : List V) (hl : walkEnd s l = v) :
    graphDist w s v ≤ walkWeight w s l :=
  iInf_le (fun l : {l : List V // walkEnd s l = v} => walkWeight w s l.1) ⟨l, hl⟩

lemma graphDist_self (w : V → V → ℝ≥0∞) (s : V) : graphDist w s s = 0 :=
  le_antisymm (by simpa [walkWeight] using graphDist_le w s s [] rfl) (zero_le _)

/-- Triangle-type inequality along a single edge. -/
lemma graphDist_edge_le (w : V → V → ℝ≥0∞) (s u v : V) :
    graphDist w s v ≤ graphDist w s u + w u v := by
  have h : graphDist w s u + w u v
      = ⨅ l : {l : List V // walkEnd s l = u}, (walkWeight w s l.1 + w u v) := by
    rw [graphDist, ENNReal.iInf_add]
  rw [h]
  refine le_iInf fun l => ?_
  have h1 : walkEnd s (l.1 ++ [v]) = v := by
    rw [walkEnd_append, l.2]; simp [walkEnd]
  have h2 : walkWeight w s (l.1 ++ [v]) = walkWeight w s l.1 + w u v := by
    rw [walkWeight_append, l.2]; simp [walkWeight]
  calc graphDist w s v ≤ walkWeight w s (l.1 ++ [v]) := graphDist_le w s v _ h1
    _ = walkWeight w s l.1 + w u v := h2

/-- Sanity check that `graphDist` is not degenerate: in a graph with no edges
at all, distinct vertices are at distance `⊤`. -/
lemma graphDist_of_no_edges (s v : V) (hsv : v ≠ s) :
    graphDist (fun _ _ => (⊤ : ℝ≥0∞)) s v = ⊤ := by
  refine top_unique (le_iInf fun l => ?_)
  rcases l with ⟨l, hl⟩
  match l, hl with
  | [], hl => exact absurd hl.symm hsv
  | x :: l, _ => simp [walkWeight]

end Walks

/-! ## The algorithm -/

section Algorithm

variable {V : Type*} [DecidableEq V] [Fintype V]

/-- One step of Dijkstra's algorithm: pick an unvisited vertex `u` of minimal
tentative distance, mark it visited, and relax all edges out of `u`. -/
noncomputable def dijkstraStep (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞)) :
    Finset V × (V → ℝ≥0∞) :=
  if h : (st.1ᶜ).Nonempty then
    (insert (Finset.exists_min_image st.1ᶜ st.2 h).choose st.1,
      fun v => min (st.2 v)
        (st.2 (Finset.exists_min_image st.1ᶜ st.2 h).choose
          + w (Finset.exists_min_image st.1ᶜ st.2 h).choose v))
  else st

/-- The initial state: nothing visited, the source `s` at tentative distance
`0` and every other vertex at tentative distance `⊤`. -/
noncomputable def dijkstraInit (s : V) : Finset V × (V → ℝ≥0∞) :=
  (∅, fun v => if v = s then 0 else ⊤)

/-- Dijkstra's algorithm: run `Fintype.card V` relaxation steps starting from
the initial state and return the resulting distance array. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) : V → ℝ≥0∞ :=
  ((dijkstraStep w)^[Fintype.card V] (dijkstraInit s)).2

/-! ## The loop invariant -/

/-- The loop invariant of Dijkstra's algorithm, for a set `S` of visited
vertices and a tentative distance array `d`: tentative distances never
undershoot the true distances, visited vertices carry their true distance, all
edges out of visited vertices are relaxed, and the source has distance `0`. -/
def DijkstraInv (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) : Prop :=
  (∀ v : V, graphDist w s v ≤ d v) ∧
  (∀ v ∈ S, d v = graphDist w s v) ∧
  (∀ a ∈ S, ∀ b : V, d b ≤ d a + w a b) ∧
  d s = 0

omit [Fintype V] in
lemma dijkstraInv_init (w : V → V → ℝ≥0∞) (s : V) :
    DijkstraInv w s (dijkstraInit s).1 (dijkstraInit s).2 := by
  refine ⟨fun v => ?_, by simp [dijkstraInit], by simp [dijkstraInit], by simp [dijkstraInit]⟩
  by_cases h : v = s
  · subst h; simp [dijkstraInit, graphDist_self]
  · simp [dijkstraInit, h]

omit [Fintype V] in
/-- Along any walk ending at an unvisited vertex `u` of minimal tentative
distance, the tentative distance of `u` is bounded by the tentative distance of
the starting vertex plus the weight of the walk. -/
lemma dijkstra_walk_bound (w : V → V → ℝ≥0∞) (S : Finset V) (d : V → ℝ≥0∞) (u : V)
    (hu : u ∉ S) (hmin : ∀ v : V, v ∉ S → d u ≤ d v)
    (hrelax : ∀ a ∈ S, ∀ b : V, d b ≤ d a + w a b) :
    ∀ (l : List V) (x : V), x ∈ S → walkEnd x l = u → d u ≤ d x + walkWeight w x l := by
  intro l
  induction l with
  | nil =>
      intro x hx he
      simp only [walkEnd] at he
      exact absurd (he ▸ hx) hu
  | cons y l ih =>
      intro x hx he
      simp only [walkEnd] at he
      simp only [walkWeight]
      have hy : d y ≤ d x + w x y := hrelax x hx y
      by_cases hyS : y ∈ S
      · calc d u ≤ d y + walkWeight w y l := ih y hyS he
          _ ≤ (d x + w x y) + walkWeight w y l := by gcongr
          _ = d x + (w x y + walkWeight w y l) := by rw [add_assoc]
      · calc d u ≤ d y := hmin y hyS
          _ ≤ d x + w x y := hy
          _ ≤ d x + (w x y + walkWeight w y l) := by
              gcongr
              exact le_self_add

omit [Fintype V] in
/-- Key step: an unvisited vertex of minimal tentative distance already carries
its true distance. -/
lemma dijkstra_min_eq_dist (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞)
    (hinv : DijkstraInv w s S d) (u : V) (hu : u ∉ S)
    (hmin : ∀ v : V, v ∉ S → d u ≤ d v) : d u = graphDist w s u := by
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  refine le_antisymm ?_ (h1 u)
  by_cases hs : s ∈ S
  · rw [graphDist]
    refine le_iInf fun l => ?_
    have h := dijkstra_walk_bound w S d u hu hmin h3 l.1 s hs l.2
    rwa [h4, zero_add] at h
  · exact le_trans (le_trans (hmin s hs) (le_of_eq h4)) (zero_le _)

omit [Fintype V] in
/-- The invariant is preserved by one relaxation round. -/
lemma dijkstraInv_update (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞)
    (hinv : DijkstraInv w s S d) (u : V) (hu : u ∉ S)
    (hmin : ∀ v : V, v ∉ S → d u ≤ d v) :
    DijkstraInv w s (insert u S) (fun v => min (d v) (d u + w u v)) := by
  have hkey : d u = graphDist w s u := dijkstra_min_eq_dist w s S d hinv u hu hmin
  obtain ⟨h1, h2, h3, h4⟩ := hinv
  have hfix : ∀ a ∈ insert u S, min (d a) (d u + w u a) = d a := by
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact min_eq_left le_self_add
    · refine min_eq_left ?_
      rw [h2 a ha, hkey]
      exact graphDist_edge_le w s u a
  refine ⟨fun v => ?_, fun v hv => ?_, fun a ha b => ?_, ?_⟩
  · exact le_min (h1 v) (by rw [hkey]; exact graphDist_edge_le w s u v)
  · show min (d v) (d u + w u v) = graphDist w s v
    rw [hfix v hv]
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hkey
    · exact h2 v hv
  · show min (d b) (d u + w u b) ≤ min (d a) (d u + w u a) + w a b
    rw [hfix a ha]
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (h3 a ha b)
  · show min (d s) (d u + w u s) = 0
    simp [h4]

lemma dijkstraInv_step (w : V → V → ℝ≥0∞) (s : V) (st : Finset V × (V → ℝ≥0∞))
    (hinv : DijkstraInv w s st.1 st.2) :
    DijkstraInv w s (dijkstraStep w st).1 (dijkstraStep w st).2 := by
  rw [dijkstraStep]
  split_ifs with hne
  · obtain ⟨humem, humin⟩ := (Finset.exists_min_image st.1ᶜ st.2 hne).choose_spec
    have huS : (Finset.exists_min_image st.1ᶜ st.2 hne).choose ∉ st.1 := by
      simpa using humem
    exact dijkstraInv_update w s st.1 st.2 hinv _ huS
      (fun v hv => humin v (by simpa using hv))
  · exact hinv

lemma dijkstraInv_iterate (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) :
    DijkstraInv w s ((dijkstraStep w)^[k] (dijkstraInit s)).1
      ((dijkstraStep w)^[k] (dijkstraInit s)).2 := by
  induction k with
  | zero => simpa using dijkstraInv_init w s
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact dijkstraInv_step w s _ ih

/-! ## Termination: after `Fintype.card V` steps every vertex is visited -/

lemma dijkstraStep_of_univ (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞))
    (h : st.1 = Finset.univ) : dijkstraStep w st = st := by
  rw [dijkstraStep, dif_neg]
  simp [h]

lemma dijkstraStep_card (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞))
    (h : (st.1ᶜ).Nonempty) : (dijkstraStep w st).1.card = st.1.card + 1 := by
  rw [dijkstraStep, dif_pos h]
  have humem := ((Finset.exists_min_image st.1ᶜ st.2 h).choose_spec).1
  exact Finset.card_insert_of_notMem (by simpa using humem)

lemma dijkstra_card_iterate (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) :
    ((dijkstraStep w)^[k] (dijkstraInit s)).1 = Finset.univ ∨
      k ≤ ((dijkstraStep w)^[k] (dijkstraInit s)).1.card := by
  induction k with
  | zero => right; simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      rcases ih with h | h
      · left; rw [dijkstraStep_of_univ w _ h]; exact h
      · by_cases hu : ((dijkstraStep w)^[k] (dijkstraInit s)).1 = Finset.univ
        · left; rw [dijkstraStep_of_univ w _ hu]; exact hu
        · right
          have hne : ((((dijkstraStep w)^[k] (dijkstraInit s)).1)ᶜ).Nonempty := by
            rw [Finset.nonempty_iff_ne_empty, Ne, Finset.compl_eq_empty_iff]
            exact hu
          rw [dijkstraStep_card w _ hne]
          omega

/-- After `Fintype.card V` steps every vertex has been visited. -/
lemma dijkstra_visited_all (w : V → V → ℝ≥0∞) (s : V) :
    ((dijkstraStep w)^[Fintype.card V] (dijkstraInit s)).1 = Finset.univ := by
  rcases dijkstra_card_iterate w s (Fintype.card V) with h | h
  · exact h
  · refine Finset.eq_univ_of_card _ (le_antisymm ?_ h)
    simpa using Finset.card_le_univ ((dijkstraStep w)^[Fintype.card V] (dijkstraInit s)).1

/-! ## Correctness -/

/-- **Correctness of Dijkstra's algorithm.**  On a finite graph with
nonnegative edge weights (encoded as elements of `ℝ≥0∞`, with `⊤` meaning "no
edge"), the array computed by Dijkstra's algorithm from a source `s` gives, for
every vertex `v`, the shortest-path distance from `s` to `v`, i.e. the infimum
of the weights of all walks from `s` to `v`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s v : V) :
    dijkstra w s v = graphDist w s v := by
  have hinv := dijkstraInv_iterate w s (Fintype.card V)
  have huniv := dijkstra_visited_all w s
  exact hinv.2.1 v (by rw [huniv]; exact Finset.mem_univ v)

end Algorithm

/-! ## A worked example

A two-vertex graph with a single edge `0 → 1` of weight `5`: the algorithm
returns `0` for the source and `5` for the other vertex. -/

section Example

/-- The weight function of a two-vertex graph with a single edge `0 → 1` of
weight `5`. -/
noncomputable def exampleWeight : Fin 2 → Fin 2 → ℝ≥0∞ :=
  fun a b => if a = 0 ∧ b = 1 then 5 else ⊤

lemma graphDist_exampleWeight : graphDist exampleWeight 0 1 = 5 := by
  refine le_antisymm ?_ ?_
  · have h := graphDist_le exampleWeight 0 1 [1] rfl
    simpa [walkWeight, exampleWeight] using h
  · rw [graphDist]
    refine le_iInf fun l => ?_
    obtain ⟨l, hl⟩ := l
    have key : ∀ (l : List (Fin 2)) (x : Fin 2), walkEnd x l = 1 → x = 0 →
        (5 : ℝ≥0∞) ≤ walkWeight exampleWeight x l := by
      intro l
      induction l with
      | nil => intro x he hx; rw [hx] at he; exact absurd he (by decide)
      | cons y l ih =>
          intro x he hx
          subst hx
          simp only [walkWeight]
          fin_cases y
          · simp [exampleWeight]
          · simp [exampleWeight]
    exact key l 0 hl rfl

example : dijkstra exampleWeight 0 1 = 5 := by
  rw [dijkstra_correct, graphDist_exampleWeight]

example : dijkstra exampleWeight 0 0 = 0 := by
  rw [dijkstra_correct, graphDist_self]

end Example

end CS

