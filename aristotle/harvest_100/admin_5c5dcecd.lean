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

variable {V : Type*}

/-! ## Graphs, walks and shortest-path distance

A weighted digraph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`.  Weights are nonnegative by construction (this is exactly the
hypothesis Dijkstra's algorithm needs), and the value `⊤` encodes the absence of an edge. -/

/-- `walkCost w a l` is the total weight of the walk that starts at `a` and then visits
the vertices of `l` in order. -/
noncomputable def walkCost (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | a, x :: t => w a x + walkCost w x t

/-- The shortest-path distance from `s` to `v`: the infimum of the weights of all walks
from `s` to `v`.  A walk from `s` to `v` is encoded by the list `l` of vertices visited
after `s`, the condition being `l.getLastD s = v` (so the empty list is the trivial walk
from `s` to `s`).  If `v` is not reachable from `s` the infimum is `⊤`. -/
noncomputable def sdist (w : V → V → ℝ≥0∞) (s v : V) : ℝ≥0∞ :=
  ⨅ l : List V, ⨅ _ : l.getLastD s = v, walkCost w s l

lemma walkCost_append (w : V → V → ℝ≥0∞) :
    ∀ (l m : List V) (a : V),
      walkCost w a (l ++ m) = walkCost w a l + walkCost w (l.getLastD a) m := by
  intro l
  induction l with
  | nil => intro m a; simp [walkCost]
  | cons x t ih =>
      intro m a
      simp only [List.cons_append, walkCost, ih, List.getLastD_cons, add_assoc]

lemma sdist_le_walkCost (w : V → V → ℝ≥0∞) (s v : V) (l : List V) (hl : l.getLastD s = v) :
    sdist w s v ≤ walkCost w s l := by
  subst hl
  rw [sdist]
  exact iInf_le_of_le l (iInf_le _ rfl)

lemma le_sdist (w : V → V → ℝ≥0∞) (s v : V) (c : ℝ≥0∞)
    (h : ∀ l : List V, l.getLastD s = v → c ≤ walkCost w s l) : c ≤ sdist w s v := by
  rw [sdist]
  exact le_iInf fun l => le_iInf fun hl => h l hl

@[simp] lemma sdist_self (w : V → V → ℝ≥0∞) (s : V) : sdist w s s = 0 := by
  refine le_antisymm ?_ (zero_le _)
  simpa [walkCost] using sdist_le_walkCost w s s [] rfl

/-- Triangle inequality along a single edge. -/
lemma sdist_edge (w : V → V → ℝ≥0∞) (s u v : V) : sdist w s v ≤ sdist w s u + w u v := by
  have hrw : sdist w s u + w u v
      = ⨅ l : List V, ⨅ _ : l.getLastD s = u, (walkCost w s l + w u v) := by
    rw [sdist, ENNReal.iInf_add]
    exact iInf_congr fun l => ENNReal.iInf_add
  rw [hrw]
  refine le_iInf fun l => le_iInf fun hl => ?_
  have hcost : walkCost w s (l ++ [v]) = walkCost w s l + w u v := by
    rw [walkCost_append, hl]
    simp [walkCost]
  have hlast : (l ++ [v]).getLastD s = v := by simp
  have h := sdist_le_walkCost w s v (l ++ [v]) hlast
  rwa [hcost] at h


/-- The distance is at most the weight of the direct edge. -/
lemma sdist_le_edge (w : V → V → ℝ≥0∞) (s v : V) : sdist w s v ≤ w s v := by
  simpa [walkCost] using sdist_le_walkCost w s v [v] (by simp)

/-- Sanity check: with no edges at all, every vertex other than the source is at
distance `⊤`, i.e. `sdist` is not degenerate. -/
example {V : Type*} (s v : V) (h : v ≠ s) : sdist (fun _ _ => (⊤ : ℝ≥0∞)) s v = ⊤ := by
  refine le_antisymm le_top (le_sdist _ _ _ _ ?_)
  intro l hl
  match l with
  | [] => exact absurd hl.symm h
  | x :: t => simp [walkCost]

/-- Sanity check: if every edge has weight at least `1`, then every vertex other than the
source is at distance at least `1`. -/
example (w : V → V → ℝ≥0∞) (h1 : ∀ x y, 1 ≤ w x y) (s v : V) (h : v ≠ s) :
    1 ≤ sdist w s v := by
  refine le_sdist _ _ _ _ ?_
  intro l hl
  match l with
  | [] => exact absurd hl.symm h
  | x :: t =>
      show (1 : ℝ≥0∞) ≤ w s x + walkCost w x t
      exact le_trans (h1 s x) le_self_add

/-! ## The algorithm -/

variable [Fintype V] [DecidableEq V]

/-- The unvisited vertex with the smallest tentative distance (the vertex that Dijkstra's
algorithm extracts from the priority queue). -/
noncomputable def pick (d : V → ℝ≥0∞) (S : Finset V) (h : (Finset.univ \ S).Nonempty) : V :=
  ((Finset.univ \ S).exists_min_image d h).choose

lemma pick_not_mem (d : V → ℝ≥0∞) (S : Finset V) (h : (Finset.univ \ S).Nonempty) :
    pick d S h ∉ S :=
  (Finset.mem_sdiff.mp ((Finset.univ \ S).exists_min_image d h).choose_spec.1).2

lemma pick_min (d : V → ℝ≥0∞) (S : Finset V) (h : (Finset.univ \ S).Nonempty) :
    ∀ y ∉ S, d (pick d S h) ≤ d y := by
  intro y hy
  exact ((Finset.univ \ S).exists_min_image d h).choose_spec.2 y
    (Finset.mem_sdiff.mpr ⟨Finset.mem_univ y, hy⟩)

/-- One iteration of Dijkstra's main loop: extract the unvisited vertex `u` of minimal
tentative distance, mark it visited, and relax all edges leaving `u`. -/
noncomputable def dijkstraStep (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞)) :
    Finset V × (V → ℝ≥0∞) :=
  if h : (Finset.univ \ st.1).Nonempty then
    (insert (pick st.2 st.1 h) st.1,
      fun v => min (st.2 v) (st.2 (pick st.2 st.1 h) + w (pick st.2 st.1 h) v))
  else st

/-- The initial state of the algorithm: nothing visited, tentative distance `0` at the
source and `⊤` everywhere else. -/
noncomputable def initState (s : V) : Finset V × (V → ℝ≥0∞) :=
  ((∅ : Finset V), fun v => if v = s then 0 else ⊤)

/-- Dijkstra's algorithm: iterate the main loop `|V|` times starting from `initState s`,
and return the resulting distance function. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) : V → ℝ≥0∞ :=
  ((dijkstraStep w)^[Fintype.card V] (initState s)).2

/-- The loop invariant: tentative distances are upper bounds for the true distances,
they are exact on visited vertices, and on an unvisited vertex `v` the tentative distance
is the length of the best walk to `v` all of whose intermediate vertices are visited. -/
def Inv (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) : Prop :=
  (∀ v, sdist w s v ≤ d v) ∧
  (∀ x ∈ S, d x = sdist w s x) ∧
  (∀ v ∉ S, d v = min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))

omit [Fintype V] in
/-- Key step of the greedy argument: a walk from a visited vertex `a` to the extracted
vertex `u`, prefixed by a shortest walk from `s` to `a`, is at least as long as `d u`. -/
lemma greedy_aux (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞)
    (hC : ∀ v ∉ S, d v = min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))
    (u : V) (hu : u ∉ S) (hmin : ∀ y ∉ S, d u ≤ d y) :
    ∀ (l : List V) (a : V), a ∈ S → l.getLastD a = u → d u ≤ sdist w s a + walkCost w a l := by
  intro l
  induction l with
  | nil =>
      intro a ha hl
      simp only [List.getLastD_nil] at hl
      exact absurd (hl ▸ ha) hu
  | cons x t ih =>
      intro a ha hl
      rw [List.getLastD_cons] at hl
      have hcost : walkCost w a (x :: t) = w a x + walkCost w x t := rfl
      by_cases hx : x ∈ S
      · calc d u ≤ sdist w s x + walkCost w x t := ih x hx hl
          _ ≤ (sdist w s a + w a x) + walkCost w x t := by gcongr; exact sdist_edge w s a x
          _ = sdist w s a + walkCost w a (x :: t) := by rw [hcost, add_assoc]
      · have hiInf : (⨅ y ∈ S, sdist w s y + w y x) ≤ sdist w s a + w a x :=
          iInf₂_le_of_le a ha le_rfl
        have hdx : d x ≤ sdist w s a + w a x := by
          rw [hC x hx]
          exact le_trans (min_le_right _ _) hiInf
        calc d u ≤ d x := hmin x hx
          _ ≤ sdist w s a + w a x := hdx
          _ ≤ sdist w s a + walkCost w a (x :: t) := by
              rw [hcost]
              exact add_le_add le_rfl le_self_add

omit [Fintype V] in
/-- The greedy choice is correct: the extracted vertex already has its final distance. -/
lemma greedy (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞)
    (hA : ∀ v, sdist w s v ≤ d v)
    (hC : ∀ v ∉ S, d v = min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))
    (u : V) (hu : u ∉ S) (hmin : ∀ y ∉ S, d u ≤ d y) : d u = sdist w s u := by
  refine le_antisymm ?_ (hA u)
  refine le_sdist w s u _ ?_
  intro l hl
  by_cases hs : s ∈ S
  · simpa using greedy_aux w s S d hC u hu hmin l s hs hl
  · have h0 : d s = 0 := by
      rw [hC s hs, if_pos rfl]
      exact min_eq_left (zero_le _)
    calc d u ≤ d s := hmin s hs
      _ = 0 := h0
      _ ≤ walkCost w s l := zero_le _

omit [Fintype V] in
/-- The invariant is preserved by "visit `u` and relax its outgoing edges". -/
lemma inv_relax (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) (h : Inv w s S d)
    (u : V) (hu : u ∉ S) (hmin : ∀ y ∉ S, d u ≤ d y) :
    Inv w s (insert u S) (fun v => min (d v) (d u + w u v)) := by
  obtain ⟨hA, hB, hC⟩ := h
  have hdu : d u = sdist w s u := greedy w s S d hA hC u hu hmin
  refine ⟨?_, ?_, ?_⟩
  · intro v
    dsimp only
    exact le_min (hA v) (by rw [hdu]; exact sdist_edge w s u v)
  · intro x hx
    dsimp only
    rcases Finset.mem_insert.mp hx with heq | hx
    · rw [heq, min_eq_left le_self_add, hdu]
    · have hle : d x ≤ d u + w u x := by
        rw [hB x hx, hdu]
        exact sdist_edge w s u x
      rw [min_eq_left hle, hB x hx]
  · intro v hv
    have hv1 : v ∉ S := fun hmem => hv (Finset.mem_insert_of_mem hmem)
    dsimp only
    rw [hC v hv1, hdu, Finset.iInf_insert]
    show min (min (if v = s then 0 else ⊤) (⨅ x ∈ S, sdist w s x + w x v))
        (sdist w s u + w u v)
      = min (if v = s then 0 else ⊤)
        (min (sdist w s u + w u v) (⨅ x ∈ S, sdist w s x + w x v))
    rw [min_assoc, min_comm (⨅ x ∈ S, sdist w s x + w x v)]

lemma inv_step (w : V → V → ℝ≥0∞) (s : V) (st : Finset V × (V → ℝ≥0∞))
    (h : Inv w s st.1 st.2) :
    Inv w s (dijkstraStep w st).1 (dijkstraStep w st).2 := by
  by_cases hne : (Finset.univ \ st.1).Nonempty
  · have hstep : dijkstraStep w st = (insert (pick st.2 st.1 hne) st.1,
        fun v => min (st.2 v) (st.2 (pick st.2 st.1 hne) + w (pick st.2 st.1 hne) v)) := by
      rw [dijkstraStep, dif_pos hne]
    rw [hstep]
    exact inv_relax w s st.1 st.2 h _ (pick_not_mem _ _ _) (pick_min _ _ _)
  · rw [dijkstraStep, dif_neg hne]
    exact h

omit [Fintype V] in
lemma inv_initState (w : V → V → ℝ≥0∞) (s : V) :
    Inv w s (initState s).1 (initState s).2 := by
  refine ⟨?_, ?_, ?_⟩
  · intro v
    by_cases h : v = s <;> simp [initState, h]
  · intro x hx
    simp [initState] at hx
  · intro v _
    simp [initState]

lemma inv_iterate (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) :
    Inv w s ((dijkstraStep w)^[k] (initState s)).1 ((dijkstraStep w)^[k] (initState s)).2 := by
  induction k with
  | zero => simpa using inv_initState w s
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact inv_step w s _ ih

lemma card_iterate (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) (hk : k ≤ Fintype.card V) :
    (((dijkstraStep w)^[k] (initState s)).1).card = k := by
  induction k with
  | zero => simp [initState]
  | succ k ih =>
      have hcard := ih (le_of_lt (lt_of_lt_of_le (Nat.lt_succ_self k) hk))
      rw [Function.iterate_succ_apply']
      have hne : (Finset.univ \ ((dijkstraStep w)^[k] (initState s)).1).Nonempty := by
        by_contra hcon
        rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hcon
        have huniv : ((dijkstraStep w)^[k] (initState s)).1 = Finset.univ :=
          Finset.eq_univ_of_forall fun x => hcon (Finset.mem_univ x)
        rw [huniv, Finset.card_univ] at hcard
        omega
      have hstep : dijkstraStep w ((dijkstraStep w)^[k] (initState s))
          = (insert (pick ((dijkstraStep w)^[k] (initState s)).2
                ((dijkstraStep w)^[k] (initState s)).1 hne)
              ((dijkstraStep w)^[k] (initState s)).1,
            fun v => min (((dijkstraStep w)^[k] (initState s)).2 v)
              (((dijkstraStep w)^[k] (initState s)).2
                  (pick ((dijkstraStep w)^[k] (initState s)).2
                    ((dijkstraStep w)^[k] (initState s)).1 hne)
                + w (pick ((dijkstraStep w)^[k] (initState s)).2
                    ((dijkstraStep w)^[k] (initState s)).1 hne) v)) := by
        rw [dijkstraStep, dif_pos hne]
      rw [hstep, Finset.card_insert_of_notMem (pick_not_mem _ _ _), hcard]

/-- **Correctness of Dijkstra's algorithm.**  On a finite digraph with nonnegative edge
weights (encoded by `w : V → V → ℝ≥0∞`, where `⊤` marks the absence of an edge), the
distances computed by Dijkstra's algorithm from a source `s` are exactly the shortest-path
distances from `s`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s v : V) : dijkstra w s v = sdist w s v := by
  have hinv := inv_iterate w s (Fintype.card V)
  have hcard := card_iterate w s (Fintype.card V) le_rfl
  have huniv : ((dijkstraStep w)^[Fintype.card V] (initState s)).1 = Finset.univ :=
    Finset.eq_univ_of_card _ hcard
  exact hinv.2.1 v (huniv ▸ Finset.mem_univ v)

end CS

#print axioms CS.dijkstra_correct

