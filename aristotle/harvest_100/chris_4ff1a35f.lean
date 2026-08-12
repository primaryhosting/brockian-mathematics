import Mathlib

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

/-!
# Dijkstra's algorithm

We formalize Dijkstra's algorithm on a finite directed graph with nonnegative edge weights,
and prove that it computes the shortest-path distances.

Weights take values in `ℝ≥0∞` (the nonnegative extended reals): this encodes both the
nonnegativity of the weights and the absence of an edge (weight `⊤`).

* `CS.walkWeight` : the weight of a walk, given as the list of vertices visited after the source.
* `CS.graphDist w src v` : the shortest-path distance, i.e. the infimum of the weights of
  all walks from `src` to `v`.
* `CS.dijkstra w src` : the output of Dijkstra's algorithm.
* `CS.dijkstra_correct` : `CS.dijkstra w src v = CS.graphDist w src v` for every `v`.
-/

namespace CS

variable {V : Type*}

/-- A walk starting at `src` is represented by the list `p` of the vertices visited after
`src`; its endpoint is the last element of `p`, or `src` if `p` is empty. -/
def walkEnd (src : V) (p : List V) : V := p.getLastD src

/-- The weight of the walk starting at `a` and visiting the vertices of `p` in order. -/
noncomputable def walkWeight (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | a, x :: p => w a x + walkWeight w x p

/-- The set of walks from `src` to `v` all of whose vertices, except possibly the last one,
belong to `S`. -/
def walks (src : V) (S : Finset V) (v : V) : Set (List V) :=
  {p | walkEnd src p = v ∧ ∀ x ∈ (src :: p).dropLast, x ∈ S}

/-- The distance from `src` to `v` along walks whose vertices, except the last one, lie in `S`. -/
noncomputable def restDist (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) (v : V) : ℝ≥0∞ :=
  ⨅ p ∈ walks src S v, walkWeight w src p

/-- The shortest-path distance from `src` to `v`: the infimum of the weights of all walks
from `src` to `v`. -/
noncomputable def graphDist (w : V → V → ℝ≥0∞) (src v : V) : ℝ≥0∞ :=
  ⨅ p ∈ {p : List V | walkEnd src p = v}, walkWeight w src p

/-- An element of `T` minimizing `d`. -/
noncomputable def pick (T : Finset V) (hT : T.Nonempty) (d : V → ℝ≥0∞) : V :=
  (T.exists_min_image d hT).choose

/-- One step of Dijkstra's algorithm: pick a vertex `u` outside the settled set `S`
with minimal tentative distance, settle it, and relax all edges out of `u`. -/
noncomputable def step [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞)
    (st : Finset V × (V → ℝ≥0∞)) : Finset V × (V → ℝ≥0∞) :=
  if h : (Finset.univ \ st.1).Nonempty then
    (insert (pick _ h st.2) st.1,
      fun v => min (st.2 v) (st.2 (pick _ h st.2) + w (pick _ h st.2) v))
  else st

/-- The initial state of Dijkstra's algorithm. -/
noncomputable def initState [DecidableEq V] (src : V) : Finset V × (V → ℝ≥0∞) :=
  (∅, fun v => if v = src then 0 else ⊤)

/-- Dijkstra's algorithm: iterate `step` as many times as there are vertices. -/
noncomputable def dijkstra [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (src : V) : V → ℝ≥0∞ :=
  ((step w)^[Fintype.card V] (initState src)).2

/-! ### Basic lemmas about walks -/

lemma pick_mem (T : Finset V) (hT : T.Nonempty) (d : V → ℝ≥0∞) : pick T hT d ∈ T :=
  (T.exists_min_image d hT).choose_spec.1

lemma pick_le (T : Finset V) (hT : T.Nonempty) (d : V → ℝ≥0∞) {x : V} (hx : x ∈ T) :
    d (pick T hT d) ≤ d x :=
  (T.exists_min_image d hT).choose_spec.2 x hx

lemma walkEnd_nil (src : V) : walkEnd src [] = src := rfl

lemma walkEnd_cons (a x : V) (p : List V) : walkEnd a (x :: p) = walkEnd x p :=
  List.getLastD_cons

lemma walkEnd_concat (a v : V) (p : List V) : walkEnd a (p ++ [v]) = v := by
  simp [walkEnd]

lemma walkEnd_mem (a : V) (p : List V) : walkEnd a p ∈ a :: p := by
  induction p generalizing a with
  | nil => simp [walkEnd]
  | cons x q ih =>
      rw [walkEnd_cons]
      have := ih x
      simp only [List.mem_cons] at this ⊢
      tauto

lemma walkWeight_concat (w : V → V → ℝ≥0∞) (a v : V) (p : List V) :
    walkWeight w a (p ++ [v]) = walkWeight w a p + w (walkEnd a p) v := by
  induction p generalizing a with
  | nil => simp [walkWeight, walkEnd]
  | cons x q ih => simp [walkWeight, ih, walkEnd_cons, add_assoc]

/-- If all vertices of `a :: p` except the last lie in `S`, and the last one lies in `S` too,
then all of them lie in `S`. -/
lemma mem_of_dropLast_mem {S : Finset V} {a : V} {p : List V}
    (h : ∀ x ∈ (a :: p).dropLast, x ∈ S) (hend : walkEnd a p ∈ S) :
    ∀ x ∈ a :: p, x ∈ S := by
  induction p generalizing a with
  | nil =>
      intro x hx
      simp only [List.mem_singleton] at hx
      subst hx
      simpa [walkEnd] using hend
  | cons y q ih =>
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact h x (by simp)
      · refine ih (a := y) (fun z hz => h z (by simp [hz])) ?_ x hx
        rw [← walkEnd_cons a y q]
        exact hend

/-! ### Basic lemmas about the restricted distance -/

lemma restDist_le_of_mem (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) (v : V) {p : List V}
    (hp : p ∈ walks src S v) : restDist w src S v ≤ walkWeight w src p :=
  iInf₂_le p hp

lemma le_restDist (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) (v : V) {c : ℝ≥0∞}
    (h : ∀ p ∈ walks src S v, c ≤ walkWeight w src p) : c ≤ restDist w src S v :=
  le_iInf₂ h

lemma restDist_self (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) : restDist w src S src = 0 :=
  le_antisymm (by
    have h : ([] : List V) ∈ walks src S src := ⟨rfl, by simp⟩
    simpa [walkWeight] using restDist_le_of_mem w src S src h) (zero_le _)

lemma restDist_mono (w : V → V → ℝ≥0∞) (src : V) {S T : Finset V} (hST : S ⊆ T) (v : V) :
    restDist w src T v ≤ restDist w src S v :=
  le_restDist w src S v (fun _ hp =>
    restDist_le_of_mem w src T v ⟨hp.1, fun x hx => hST (hp.2 x hx)⟩)

/-- Appending an edge `a → v` to a walk ending at `a ∈ S`. -/
lemma restDist_append_edge (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) {a : V} (ha : a ∈ S)
    (v : V) : restDist w src S v ≤ restDist w src S a + w a v := by
  have hrw : restDist w src S a + w a v
      = ⨅ p, ⨅ _ : p ∈ walks src S a, (walkWeight w src p + w a v) := by
    rw [restDist]; simp only [ENNReal.iInf_add]
  rw [hrw]
  refine le_iInf₂ (fun p hp => ?_)
  have hend : walkEnd src p = a := hp.1
  have hmem : p ++ [v] ∈ walks src S v := by
    refine ⟨walkEnd_concat src v p, ?_⟩
    intro x hx
    have hx' : x ∈ src :: p := by
      have hd : (src :: (p ++ [v])).dropLast = src :: p := by
        rw [← List.cons_append]; exact List.dropLast_concat
      rwa [hd] at hx
    exact mem_of_dropLast_mem hp.2 (by rw [hend]; exact ha) x hx'
  calc restDist w src S v ≤ walkWeight w src (p ++ [v]) := restDist_le_of_mem w src S v hmem
    _ = walkWeight w src p + w a v := by rw [walkWeight_concat, hend]

lemma graphDist_eq_restDist_univ [Fintype V] (w : V → V → ℝ≥0∞) (src v : V) :
    graphDist w src v = restDist w src Finset.univ v := by
  apply le_antisymm
  · exact le_iInf₂ (fun p hp => iInf₂_le (f := fun p (_ : p ∈ {p : List V | walkEnd src p = v}) =>
      walkWeight w src p) p hp.1)
  · exact le_iInf₂ (fun p hp => iInf₂_le (f := fun p (_ : p ∈ walks src Finset.univ v) =>
      walkWeight w src p) p ⟨hp, by simp⟩)

lemma graphDist_le_restDist [Fintype V] (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) (v : V) :
    graphDist w src v ≤ restDist w src S v := by
  rw [graphDist_eq_restDist_univ]
  exact restDist_mono w src (Finset.subset_univ S) v

lemma graphDist_append_edge [Fintype V] (w : V → V → ℝ≥0∞) (src a v : V) :
    graphDist w src v ≤ graphDist w src a + w a v := by
  rw [graphDist_eq_restDist_univ, graphDist_eq_restDist_univ]
  exact restDist_append_edge w src Finset.univ (Finset.mem_univ a) v

/-! ### The invariant -/

/-- The invariant maintained by Dijkstra's algorithm: the tentative distances are the
distances along walks whose intermediate vertices are settled, and the settled vertices
already carry their true distance. -/
def Inv (w : V → V → ℝ≥0∞) (src : V) (st : Finset V × (V → ℝ≥0∞)) : Prop :=
  (∀ v, st.2 v = restDist w src st.1 v) ∧ (∀ z ∈ st.1, st.2 z = graphDist w src z)

lemma inv_initState [DecidableEq V] (w : V → V → ℝ≥0∞) (src : V) :
    Inv w src (initState src) := by
  refine ⟨fun v => ?_, fun z hz => absurd hz (by simp [initState])⟩
  simp only [initState]
  by_cases hv : v = src
  · subst hv; simp [restDist_self]
  · rw [if_neg hv]
    symm
    rw [eq_top_iff]
    refine le_restDist w src ∅ v (fun p hp => ?_)
    exfalso
    match p with
    | [] => exact hv hp.1.symm
    | x :: q =>
        have := hp.2 src (by simp)
        simp at this

/-- Key lemma: a walk which leaves the settled set `S` has weight at least the tentative
distance of some unsettled vertex.  This is where nonnegativity of the weights is used. -/
lemma exists_unsettled_le (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) :
    ∀ (p : List V) (a : V) (c : ℝ≥0∞), restDist w src S a ≤ c → a ∈ S → walkEnd a p ∉ S →
      ∃ y ∉ S, restDist w src S y ≤ c + walkWeight w a p := by
  intro p
  induction p with
  | nil => intro a c _ haS hend; exact absurd haS (by simpa [walkEnd] using hend)
  | cons x q ih =>
      intro a c ha haS hend
      have h1 : restDist w src S x ≤ c + w a x :=
        le_trans (restDist_append_edge w src S haS x) (add_le_add ha le_rfl)
      have hw : walkWeight w a (x :: q) = w a x + walkWeight w x q := rfl
      by_cases hx : x ∈ S
      · have hend' : walkEnd x q ∉ S := by rwa [← walkEnd_cons a x q]
        obtain ⟨y, hy, hle⟩ := ih x (c + w a x) h1 hx hend'
        exact ⟨y, hy, by rw [hw, ← add_assoc]; exact hle⟩
      · exact ⟨x, hx, by rw [hw, ← add_assoc]; exact le_trans h1 le_self_add⟩

/-- The relaxation inequality: after settling `u`, the updated tentative distances are at most
the weight of any walk whose intermediate vertices lie in `insert u S`. -/
lemma relax_le [Fintype V] (w : V → V → ℝ≥0∞) (src : V) (S : Finset V) (d : V → ℝ≥0∞) (u : V)
    (hJ : ∀ v, d v = restDist w src S v) (hK : ∀ z ∈ S, d z = graphDist w src z)
    (hdu : d u = graphDist w src u) [DecidableEq V] :
    ∀ (p : List V) (v : V), p ∈ walks src (insert u S) v →
      min (d v) (d u + w u v) ≤ walkWeight w src p := by
  intro p
  induction p using List.reverseRecOn with
  | nil =>
      intro v hp
      have hv : src = v := hp.1
      subst hv
      have hds : d src = 0 := by rw [hJ, restDist_self]
      have h0 : walkWeight w src ([] : List V) = 0 := rfl
      rw [h0, ← hds]
      exact min_le_left _ _
  | append_singleton q x ih =>
      intro v hp
      obtain ⟨hpe, hpS⟩ := hp
      have hx : x = v := by rw [← hpe]; exact (walkEnd_concat src x q).symm
      subst hx
      have hdrop : (src :: (q ++ [x])).dropLast = src :: q := by
        rw [← List.cons_append]; exact List.dropLast_concat
      set z := walkEnd src q with hz
      have hzmem : z ∈ insert u S := hpS z (by rw [hdrop]; exact walkEnd_mem src q)
      have hq : q ∈ walks src (insert u S) z := by
        refine ⟨rfl, fun y hy => hpS y ?_⟩
        rw [hdrop]
        exact List.dropLast_subset _ hy
      have IH := ih z hq
      have hwq : walkWeight w src (q ++ [x]) = walkWeight w src q + w z x := by
        rw [walkWeight_concat]
      rcases Finset.mem_insert.mp hzmem with hzu | hzS
      · rw [hzu] at IH hwq
        have hu : min (d u) (d u + w u u) = d u := min_eq_left le_self_add
        rw [hu] at IH
        rw [hwq]
        exact le_trans (min_le_right _ _) (add_le_add IH le_rfl)
      · have hdz : d z ≤ d u + w u z := by
          rw [hK z hzS, hdu]; exact graphDist_append_edge w src u z
        rw [min_eq_left hdz] at IH
        rw [hwq]
        calc min (d x) (d u + w u x) ≤ d x := min_le_left _ _
          _ ≤ d z + w z x := by
              rw [hJ, hJ]; exact restDist_append_edge w src S hzS x
          _ ≤ walkWeight w src q + w z x := add_le_add IH le_rfl

lemma inv_step [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (src : V)
    (st : Finset V × (V → ℝ≥0∞)) (h : Inv w src st) : Inv w src (step w st) := by
  obtain ⟨hJ, hK⟩ := h
  rw [step]
  split_ifs with hne
  · set S := st.1 with hS
    set d := st.2 with hd
    set u := pick (Finset.univ \ S) hne d with hu
    have huS : u ∉ S := by
      have := pick_mem (Finset.univ \ S) hne d
      simpa [hu, Finset.mem_sdiff] using this
    have hmin : ∀ y, y ∉ S → d u ≤ d y := by
      intro y hy
      exact pick_le (Finset.univ \ S) hne d (by simp [Finset.mem_sdiff, hy])
    -- the extracted vertex has its final distance
    have hdu : d u = graphDist w src u := by
      refine le_antisymm ?_ (by rw [hJ u]; exact graphDist_le_restDist w src S u)
      refine le_iInf₂ (fun p (hp : walkEnd src p = u) => ?_)
      by_cases hsrc : src ∈ S
      · obtain ⟨y, hy, hle⟩ :=
          exists_unsettled_le w src S p src 0 (le_of_eq (restDist_self w src S)) hsrc
            (by rw [hp]; exact huS)
        calc d u ≤ d y := hmin y hy
          _ = restDist w src S y := hJ y
          _ ≤ 0 + walkWeight w src p := hle
          _ = walkWeight w src p := by rw [zero_add]
      · calc d u ≤ d src := hmin src hsrc
          _ = restDist w src S src := hJ src
          _ = 0 := restDist_self w src S
          _ ≤ walkWeight w src p := zero_le _
    have hkey : ∀ z ∈ S, min (d z) (d u + w u z) = d z := by
      intro z hz
      refine min_eq_left ?_
      rw [hK z hz, hdu]
      exact graphDist_append_edge w src u z
    refine ⟨fun v => ?_, fun z hz => ?_⟩
    · show min (d v) (d u + w u v) = restDist w src (insert u S) v
      refine le_antisymm ?_ ?_
      · refine le_restDist w src (insert u S) v (fun p hp => ?_)
        exact relax_le w src S d u hJ hK hdu p v hp
      · refine le_min ?_ ?_
        · rw [hJ v]; exact restDist_mono w src (Finset.subset_insert u S) v
        · calc restDist w src (insert u S) v
              ≤ restDist w src (insert u S) u + w u v :=
                restDist_append_edge w src _ (Finset.mem_insert_self u S) v
            _ ≤ restDist w src S u + w u v :=
                add_le_add (restDist_mono w src (Finset.subset_insert u S) u) le_rfl
            _ = d u + w u v := by rw [hJ u]
    · replace hz : z ∈ insert u S := hz
      show min (d z) (d u + w u z) = graphDist w src z
      rcases Finset.mem_insert.mp hz with rfl | hz
      · rw [min_eq_left (le_self_add : d u ≤ d u + w u u)]; exact hdu
      · rw [hkey z hz]; exact hK z hz
  · exact ⟨hJ, hK⟩

lemma inv_iterate [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (src : V) (k : ℕ) :
    Inv w src ((step w)^[k] (initState src)) := by
  induction k with
  | zero => simpa using inv_initState w src
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact inv_step w src _ ih

/-! ### Termination -/

lemma card_step [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞)) :
    min (Fintype.card V) (st.1.card + 1) ≤ (step w st).1.card := by
  rw [step]
  split_ifs with hne
  · have huS : pick (Finset.univ \ st.1) hne st.2 ∉ st.1 := by
      have := pick_mem (Finset.univ \ st.1) hne st.2
      simpa [Finset.mem_sdiff] using this
    simp only [Finset.card_insert_of_notMem huS]
    exact min_le_right _ _
  · have : st.1 = Finset.univ := by
      rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at hne
      exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _)
        (Finset.card_le_card hne))
    rw [this, Finset.card_univ]
    exact min_le_left _ _

lemma card_iterate [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (src : V) (k : ℕ) :
    min (Fintype.card V) k ≤ ((step w)^[k] (initState src)).1.card := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      have h1 := card_step w ((step w)^[k] (initState src))
      have h2 : ((step w)^[k] (initState src)).1.card ≤ Fintype.card V :=
        Finset.card_le_univ _
      omega

lemma settled_univ [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (src : V) :
    ((step w)^[Fintype.card V] (initState src)).1 = Finset.univ := by
  have h := card_iterate w src (Fintype.card V)
  rw [min_self] at h
  exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) h)

/-- **Correctness of Dijkstra's algorithm**: on a finite directed graph with nonnegative
(extended-real) edge weights, the algorithm computes the shortest-path distance from the
source to every vertex. -/
theorem dijkstra_correct [Fintype V] [DecidableEq V] (w : V → V → ℝ≥0∞) (src v : V) :
    dijkstra w src v = graphDist w src v := by
  have hInv := (inv_iterate w src (Fintype.card V)).1 v
  rw [dijkstra, hInv, settled_univ, ← graphDist_eq_restDist_univ]

/-! ### Lower bounds via potentials, and a worked example

The lemmas below are not needed for the correctness proof; they serve to compute
shortest-path distances in concrete examples, and thus to check that the definitions
above are the intended ones. -/

/-- If `pot` is a feasible potential (`pot v ≤ pot u + w u v` for all `u`, `v`), then it
bounds the weight of every walk from below. -/
lemma le_walkWeight_of_potential (w : V → V → ℝ≥0∞) (pot : V → ℝ≥0∞)
    (h : ∀ u v, pot v ≤ pot u + w u v) (a : V) (p : List V) :
    pot (walkEnd a p) ≤ pot a + walkWeight w a p := by
  induction p generalizing a with
  | nil => simp [walkEnd, walkWeight]
  | cons x q ih =>
      have hw : walkWeight w a (x :: q) = w a x + walkWeight w x q := rfl
      calc pot (walkEnd a (x :: q)) = pot (walkEnd x q) := by rw [walkEnd_cons]
        _ ≤ pot x + walkWeight w x q := ih x
        _ ≤ pot a + w a x + walkWeight w x q := add_le_add (h a x) le_rfl
        _ = pot a + walkWeight w a (x :: q) := by rw [hw, add_assoc]

/-- A feasible potential bounds the shortest-path distance from below. -/
lemma le_graphDist_of_potential (w : V → V → ℝ≥0∞) (pot : V → ℝ≥0∞)
    (h : ∀ u v, pot v ≤ pot u + w u v) (src v : V) :
    pot v ≤ pot src + graphDist w src v := by
  rw [graphDist]
  simp only [ENNReal.add_iInf]
  refine le_iInf₂ (fun p (hp : walkEnd src p = v) => ?_)
  rw [← hp]
  exact le_walkWeight_of_potential w pot h src p

section Example

/-- A three-vertex example: the direct edge `0 → 1` has weight `5`, but going through
vertex `2` costs only `1 + 1 = 2`. -/
noncomputable def exampleWeights : Fin 3 → Fin 3 → ℝ≥0∞ :=
  ![![⊤, 5, 1], ![⊤, ⊤, ⊤], ![⊤, 1, ⊤]]

/-- A feasible potential for `exampleWeights`. -/
noncomputable def examplePotential : Fin 3 → ℝ≥0∞ := ![0, 2, 1]

lemma examplePotential_feasible (u v : Fin 3) :
    examplePotential v ≤ examplePotential u + exampleWeights u v := by
  fin_cases u <;> fin_cases v <;>
    simp [examplePotential, exampleWeights] <;> norm_num

/-- In the example the shortest distance from `0` to `1` is `2`, attained by the
two-edge path through `2` rather than by the direct edge of weight `5`. -/
theorem exampleGraphDist : graphDist exampleWeights 0 1 = 2 := by
  refine le_antisymm ?_ ?_
  · have hmem : ([2, 1] : List (Fin 3)) ∈ {p : List (Fin 3) | walkEnd 0 p = 1} := by
      simp [walkEnd]
    have h := iInf₂_le (f := fun p (_ : p ∈ {p : List (Fin 3) | walkEnd 0 p = 1}) =>
      walkWeight exampleWeights 0 p) _ hmem
    refine le_trans h (le_of_eq ?_)
    show exampleWeights 0 2 + (exampleWeights 2 1 + 0) = 2
    simp [exampleWeights, Matrix.cons_val]
    norm_num
  · have h := le_graphDist_of_potential exampleWeights examplePotential
      examplePotential_feasible 0 1
    simpa [examplePotential] using h

/-- Dijkstra's algorithm returns the value `2` on the example. -/
theorem exampleDijkstra : dijkstra exampleWeights 0 1 = 2 := by
  rw [dijkstra_correct]
  exact exampleGraphDist

end Example

/-! ### A version with real-valued nonnegative weights

The development above uses `ℝ≥0∞`-valued weights, where `⊤` marks a missing edge.  The
following corollary specializes it to genuinely real-valued weights `wr` subject to an
explicit nonnegativity hypothesis (all edges present). -/

/-- The weight of a walk for real-valued edge weights. -/
def realWalkWeight (wr : V → V → ℝ) : V → List V → ℝ
  | _, [] => 0
  | a, x :: p => wr a x + realWalkWeight wr x p

lemma realWalkWeight_nonneg (wr : V → V → ℝ) (hw : ∀ u v, 0 ≤ wr u v) (a : V) (p : List V) :
    0 ≤ realWalkWeight wr a p := by
  induction p generalizing a with
  | nil => simp [realWalkWeight]
  | cons x q ih => exact add_nonneg (hw a x) (ih x)

lemma walkWeight_ofReal (wr : V → V → ℝ) (hw : ∀ u v, 0 ≤ wr u v) (a : V) (p : List V) :
    walkWeight (fun u v => ENNReal.ofReal (wr u v)) a p
      = ENNReal.ofReal (realWalkWeight wr a p) := by
  induction p generalizing a with
  | nil => simp [walkWeight, realWalkWeight]
  | cons x q ih =>
      have hw1 : walkWeight (fun u v => ENNReal.ofReal (wr u v)) a (x :: q)
          = ENNReal.ofReal (wr a x) + walkWeight (fun u v => ENNReal.ofReal (wr u v)) x q := rfl
      rw [hw1, ih x, realWalkWeight,
        ENNReal.ofReal_add (hw a x) (realWalkWeight_nonneg wr hw x q)]

/-- **Correctness of Dijkstra's algorithm for nonnegative real weights**: the algorithm run on
the weights `ENNReal.ofReal ∘ wr` returns, at every vertex `v`, the infimum of the weights of
all walks from the source to `v`. -/
theorem dijkstra_correct_real [Fintype V] [DecidableEq V] (wr : V → V → ℝ)
    (hw : ∀ u v, 0 ≤ wr u v) (src v : V) :
    dijkstra (fun u v => ENNReal.ofReal (wr u v)) src v
      = ⨅ p ∈ {p : List V | walkEnd src p = v}, ENNReal.ofReal (realWalkWeight wr src p) := by
  rw [dijkstra_correct, graphDist]
  exact iInf_congr fun p => iInf_congr fun _ => walkWeight_ofReal wr hw src p

end CS

