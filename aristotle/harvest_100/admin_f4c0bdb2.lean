import Mathlib

/-!
# Correctness of Dijkstra's algorithm

We model a finite weighted digraph on a finite vertex type `V` by a weight function
`w : V → V → ℝ≥0∞`.  Using `ℝ≥0∞` (extended nonnegative reals) as the weight type
encodes exactly the hypotheses of Dijkstra's algorithm:

* every weight is nonnegative;
* `w u v = ⊤` means "there is no edge from `u` to `v`" (an infinitely expensive edge).

A *path* starting at `x` is a list `l : List V` of the vertices visited after `x`.
`pathCost w x l` is its total weight and `pathEnd x l` its final vertex.
`spDist w s t` is the shortest-path distance, the infimum of the costs of all paths
from `s` to `t` (`⊤` if `t` is unreachable from `s`).

`dijkstra w s` runs the usual Dijkstra loop (`Fintype.card V` rounds of
"extract an unvisited vertex of minimal tentative distance, then relax its outgoing
edges"), and the main theorem `CS.dijkstra_correct` states that it returns exactly
the shortest-path distances from `s`.

The two mathematical ingredients are isolated as `CS.key_extract` (the extracted
vertex already has its final distance — this is the step that uses nonnegativity of
the weights) and `CS.key_update` (relaxing the edges out of the extracted vertex
updates the restricted distances correctly).
-/

open scoped Classical ENNReal

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace CS

variable {V : Type*}

/-! ## Paths -/

/-- The endpoint of the path that starts at `x` and then visits the vertices of `l`. -/
def pathEnd (x : V) : List V → V
  | [] => x
  | y :: l => pathEnd y l

/-- The total weight of the path that starts at `x` and then visits the vertices of `l`. -/
noncomputable def pathCost (w : V → V → ℝ≥0∞) (x : V) : List V → ℝ≥0∞
  | [] => 0
  | y :: l => w x y + pathCost w y l

/-- `interIn S x l` says that all vertices of the path `x :: l`, except its endpoint,
belong to `S`. -/
def interIn (S : Finset V) : V → List V → Prop
  | _, [] => True
  | x, y :: l => x ∈ S ∧ interIn S y l

/-- The infimum of the costs of paths from `s` to `t` all of whose vertices, except
the endpoint `t`, lie in `S`. -/
noncomputable def distS (w : V → V → ℝ≥0∞) (S : Finset V) (s t : V) : ℝ≥0∞ :=
  sInf {c | ∃ l : List V, pathEnd s l = t ∧ interIn S s l ∧ pathCost w s l = c}

/-- The shortest-path distance from `s` to `t`: the infimum of the costs of all paths
from `s` to `t`. -/
noncomputable def spDist (w : V → V → ℝ≥0∞) (s t : V) : ℝ≥0∞ :=
  sInf {c | ∃ l : List V, pathEnd s l = t ∧ pathCost w s l = c}

/-- An element of `x :: l` on which `d` is minimal. -/
noncomputable def argMin (d : V → ℝ≥0∞) (x : V) : List V → V
  | [] => x
  | y :: l => argMin d (if d y < d x then y else x) l

/-! ## Basic facts about paths -/

lemma pathEnd_cons (x y : V) (l : List V) : pathEnd x (y :: l) = pathEnd y l := rfl

lemma pathEnd_append (x : V) (l : List V) (y : V) : pathEnd x (l ++ [y]) = y := by
  induction l generalizing x with
  | nil => rfl
  | cons z l ih => simpa [pathEnd] using ih z

lemma pathCost_append (w : V → V → ℝ≥0∞) (x : V) (l : List V) (y : V) :
    pathCost w x (l ++ [y]) = pathCost w x l + w (pathEnd x l) y := by
  induction l generalizing x with
  | nil => simp [pathCost, pathEnd]
  | cons z l ih => simp [pathCost, pathEnd, ih z, add_assoc]

lemma interIn_append {S : Finset V} {x : V} {l : List V} (y : V)
    (h : interIn S x l) (h' : pathEnd x l ∈ S) : interIn S x (l ++ [y]) := by
  induction l generalizing x with
  | nil => exact ⟨h', trivial⟩
  | cons z l ih => exact ⟨h.1, ih h.2 h'⟩

lemma interIn_mono {S T : Finset V} (hST : S ⊆ T) {x : V} {l : List V}
    (h : interIn S x l) : interIn T x l := by
  induction l generalizing x with
  | nil => trivial
  | cons z l ih => exact ⟨hST h.1, ih h.2⟩

/-! ## Basic facts about the distances -/

lemma le_distS {w : V → V → ℝ≥0∞} {S : Finset V} {s t : V} {c : ℝ≥0∞}
    (h : ∀ l : List V, pathEnd s l = t → interIn S s l → c ≤ pathCost w s l) :
    c ≤ distS w S s t := by
  refine le_sInf ?_
  rintro b ⟨l, hl, hi, rfl⟩
  exact h l hl hi

lemma le_spDist {w : V → V → ℝ≥0∞} {s t : V} {c : ℝ≥0∞}
    (h : ∀ l : List V, pathEnd s l = t → c ≤ pathCost w s l) : c ≤ spDist w s t := by
  refine le_sInf ?_
  rintro b ⟨l, hl, rfl⟩
  exact h l hl

lemma distS_le {w : V → V → ℝ≥0∞} {S : Finset V} {s t : V} (l : List V)
    (h : pathEnd s l = t) (h' : interIn S s l) : distS w S s t ≤ pathCost w s l :=
  sInf_le ⟨l, h, h', rfl⟩

lemma spDist_le {w : V → V → ℝ≥0∞} {s t : V} (l : List V) (h : pathEnd s l = t) :
    spDist w s t ≤ pathCost w s l :=
  sInf_le ⟨l, h, rfl⟩

lemma spDist_le_distS (w : V → V → ℝ≥0∞) (S : Finset V) (s t : V) :
    spDist w s t ≤ distS w S s t := by
  refine sInf_le_sInf ?_
  rintro b ⟨l, hl, _, hc⟩
  exact ⟨l, hl, hc⟩

lemma distS_mono {S T : Finset V} (hST : S ⊆ T) (w : V → V → ℝ≥0∞) (s t : V) :
    distS w T s t ≤ distS w S s t := by
  refine sInf_le_sInf ?_
  rintro b ⟨l, hl, hi, hc⟩
  exact ⟨l, hl, interIn_mono hST hi, hc⟩

lemma distS_self (w : V → V → ℝ≥0∞) (S : Finset V) (s : V) : distS w S s s = 0 :=
  le_antisymm (by simpa [pathCost] using distS_le (w := w) (S := S) ([] : List V) rfl trivial)
    (zero_le _)

lemma spDist_self (w : V → V → ℝ≥0∞) (s : V) : spDist w s s = 0 :=
  le_antisymm (by simpa [pathCost] using spDist_le (w := w) ([] : List V) rfl) (zero_le _)

/-- Extending a path by one edge: relaxation inequality for `distS`. -/
lemma distS_edge {S T : Finset V} (hST : S ⊆ T) (w : V → V → ℝ≥0∞) (s : V) {x : V}
    (hx : x ∈ T) (y : V) : distS w T s y ≤ distS w S s x + w x y := by
  rw [← tsub_le_iff_right]
  refine le_sInf ?_
  rintro b ⟨l, hl, hi, rfl⟩
  rw [tsub_le_iff_right]
  calc distS w T s y ≤ pathCost w s (l ++ [y]) :=
        distS_le _ (pathEnd_append _ _ _)
          (interIn_append y (interIn_mono hST hi) (by rw [hl]; exact hx))
    _ = pathCost w s l + w x y := by rw [pathCost_append, hl]

/-- Extending a path by one edge: relaxation inequality for `spDist`. -/
lemma spDist_edge (w : V → V → ℝ≥0∞) (s x y : V) :
    spDist w s y ≤ spDist w s x + w x y := by
  rw [← tsub_le_iff_right]
  refine le_sInf ?_
  rintro b ⟨l, hl, rfl⟩
  rw [tsub_le_iff_right]
  calc spDist w s y ≤ pathCost w s (l ++ [y]) := spDist_le _ (pathEnd_append _ _ _)
    _ = pathCost w s l + w x y := by rw [pathCost_append, hl]

/-! ## Properties of `argMin` -/

lemma argMin_mem (d : V → ℝ≥0∞) (x : V) (l : List V) : argMin d x l ∈ x :: l := by
  induction l generalizing x with
  | nil => simp [argMin]
  | cons y l ih =>
    rw [argMin]
    by_cases hc : d y < d x
    · rw [if_pos hc]
      exact List.mem_cons_of_mem x (ih y)
    · rw [if_neg hc]
      rcases List.mem_cons.mp (ih x) with h | h
      · rw [h]; exact List.mem_cons_self
      · exact List.mem_cons_of_mem x (List.mem_cons_of_mem y h)

lemma argMin_le (d : V → ℝ≥0∞) (x : V) (l : List V) :
    ∀ v ∈ x :: l, d (argMin d x l) ≤ d v := by
  induction l generalizing x with
  | nil =>
    intro v hv
    rw [List.mem_singleton] at hv
    simp [argMin, hv]
  | cons y l ih =>
    intro v hv
    rw [argMin]
    have hzx : d (if d y < d x then y else x) ≤ d x := by
      by_cases hc : d y < d x
      · rw [if_pos hc]; exact hc.le
      · rw [if_neg hc]
    have hzy : d (if d y < d x then y else x) ≤ d y := by
      by_cases hc : d y < d x
      · rw [if_pos hc]
      · rw [if_neg hc]; exact not_lt.mp hc
    have hself : d (argMin d (if d y < d x then y else x) l)
        ≤ d (if d y < d x then y else x) := ih _ _ List.mem_cons_self
    rcases List.mem_cons.mp hv with rfl | hv'
    · exact hself.trans hzx
    · rcases List.mem_cons.mp hv' with rfl | hv''
      · exact hself.trans hzy
      · exact ih _ v (List.mem_cons_of_mem _ hv'')

section Fintype

variable [Fintype V]

lemma interIn_univ {x : V} {l : List V} : interIn (Finset.univ : Finset V) x l := by
  induction l generalizing x with
  | nil => trivial
  | cons z l ih => exact ⟨Finset.mem_univ _, ih⟩

lemma distS_univ (w : V → V → ℝ≥0∞) (s t : V) :
    distS w (Finset.univ : Finset V) s t = spDist w s t := by
  refine le_antisymm ?_ (spDist_le_distS w _ s t)
  refine sInf_le_sInf ?_
  rintro b ⟨l, hl, hc⟩
  exact ⟨l, hl, interIn_univ, hc⟩

end Fintype

/-! ## The two key lemmas -/

section Key

variable [DecidableEq V]

/-- **Extraction is correct.**  If the tentative distances `d` are the `S`-restricted
distances and `u` is an unvisited vertex minimizing `d`, then `d u` is already the true
shortest-path distance.  This is where nonnegativity of the weights is used: the part of
a path lying beyond the first unvisited vertex it meets can only increase its cost. -/
lemma key_extract (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V) (d : V → ℝ≥0∞)
    (hd : ∀ v, d v = distS w S s v) (hu : u ∉ S) (hmin : ∀ y, y ∉ S → d u ≤ d y) :
    d u = spDist w s u := by
  have hA : ∀ (l : List V) (x : V) (c : ℝ≥0∞), distS w S s x ≤ c → pathEnd x l ∉ S →
      d u ≤ c + pathCost w x l := by
    intro l
    induction l with
    | nil =>
      intro x c hc hx
      calc d u ≤ d x := hmin x hx
        _ = distS w S s x := hd x
        _ ≤ c := hc
        _ ≤ c + pathCost w x [] := le_self_add
    | cons y l ih =>
      intro x c hc hx
      by_cases hxS : x ∈ S
      · have h1 : distS w S s y ≤ c + w x y :=
          (distS_edge (le_refl S) w s hxS y).trans (by gcongr)
        have h2 := ih y (c + w x y) h1 hx
        calc d u ≤ c + w x y + pathCost w y l := h2
          _ = c + pathCost w x (y :: l) := by simp [pathCost, add_assoc]
      · calc d u ≤ d x := hmin x hxS
          _ = distS w S s x := hd x
          _ ≤ c := hc
          _ ≤ c + pathCost w x (y :: l) := le_self_add
  refine le_antisymm (le_spDist ?_) ?_
  · intro l hl
    have := hA l s 0 (le_of_eq (distS_self w S s)) (by rw [hl]; exact hu)
    simpa using this
  · rw [hd u]; exact spDist_le_distS w S s u

/-- **Relaxation is correct.**  Relaxing the edges out of a vertex `u` whose tentative
distance is already final turns the `S`-restricted distances into the
`insert u S`-restricted distances. -/
lemma key_update (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V) (d : V → ℝ≥0∞)
    (hd : ∀ v, d v = distS w S s v) (hz : ∀ z ∈ S, d z = spDist w s z)
    (hu : d u = spDist w s u) (v : V) :
    min (d v) (d u + w u v) = distS w (insert u S) s v := by
  have hB : ∀ (l : List V) (x : V) (c : ℝ≥0∞), interIn (insert u S) x l →
      min (d x) (d u + w u x) ≤ c → spDist w s x ≤ c →
      min (d (pathEnd x l)) (d u + w u (pathEnd x l)) ≤ c + pathCost w x l := by
    intro l
    induction l with
    | nil => intro x c _ h1 _; simpa [pathCost, pathEnd] using h1
    | cons y l ih =>
      intro x c hi h1 h2
      obtain ⟨hxS, hi'⟩ := hi
      have hdy : min (d y) (d u + w u y) ≤ c + w x y := by
        rcases Finset.mem_insert.mp hxS with rfl | hxS'
        · have hcu : d x ≤ c := by rw [hu]; exact h2
          exact (min_le_right _ _).trans (by gcongr)
        · have hdx : d x ≤ c := ((hz x hxS').le).trans h2
          have hy : d y ≤ c + w x y := by
            rw [hd y]
            calc distS w S s y ≤ distS w S s x + w x y := distS_edge (le_refl S) w s hxS' y
              _ = d x + w x y := by rw [hd x]
              _ ≤ c + w x y := by gcongr
          exact (min_le_left _ _).trans hy
      have hsy : spDist w s y ≤ c + w x y := (spDist_edge w s x y).trans (by gcongr)
      have h3 := ih y (c + w x y) hi' hdy hsy
      calc min (d (pathEnd x (y :: l))) (d u + w u (pathEnd x (y :: l)))
          = min (d (pathEnd y l)) (d u + w u (pathEnd y l)) := by rw [pathEnd_cons]
        _ ≤ c + w x y + pathCost w y l := h3
        _ = c + pathCost w x (y :: l) := by simp [pathCost, add_assoc]
  refine le_antisymm (le_distS ?_) (le_min ?_ ?_)
  · intro l hl hi
    have h0 : min (d s) (d u + w u s) ≤ 0 := by
      have hs : d s = 0 := by rw [hd s, distS_self]
      simp [hs]
    have := hB l s 0 hi h0 (by simp [spDist_self])
    rw [hl] at this
    simpa using this
  · rw [hd v]; exact distS_mono (Finset.subset_insert u S) w s v
  · rw [hd u]
    exact distS_edge (Finset.subset_insert u S) w s (Finset.mem_insert_self u S) v

end Key

/-! ## The algorithm -/

section Algorithm

variable [Fintype V] [DecidableEq V]

/-- One round of Dijkstra's algorithm, given the list of currently unvisited vertices:
extract an unvisited vertex `u` of minimal tentative distance, mark it visited,
and relax all edges out of `u`. -/
noncomputable def stepList (w : V → V → ℝ≥0∞) (S : Finset V) (d : V → ℝ≥0∞) :
    List V → Finset V × (V → ℝ≥0∞)
  | [] => (S, d)
  | x :: l =>
      (insert (argMin d x l) S,
        fun v => min (d v) (d (argMin d x l) + w (argMin d x l) v))

/-- One round of Dijkstra's algorithm. -/
noncomputable def step (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞)) :
    Finset V × (V → ℝ≥0∞) :=
  stepList w st.1 st.2 (Finset.univ \ st.1).toList

/-- **Dijkstra's algorithm**: `Fintype.card V` rounds starting from the initial state
in which nothing is visited, the source `s` has tentative distance `0` and every other
vertex has tentative distance `⊤`. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) (t : V) : ℝ≥0∞ :=
  ((step w)^[Fintype.card V] (∅, fun v => if v = s then 0 else ⊤)).2 t

/-! ## The loop invariant -/

/-- The loop invariant of Dijkstra's algorithm: the tentative distances are the
distances restricted to paths through visited vertices, and for a visited vertex this
is already the true shortest-path distance. -/
def Inv (w : V → V → ℝ≥0∞) (s : V) (st : Finset V × (V → ℝ≥0∞)) : Prop :=
  (∀ v, st.2 v = distS w st.1 s v) ∧ (∀ z ∈ st.1, st.2 z = spDist w s z)

omit [Fintype V] in
lemma inv_init (w : V → V → ℝ≥0∞) (s : V) :
    Inv w s ((∅ : Finset V), fun v => if v = s then 0 else ⊤) := by
  constructor
  · intro v
    by_cases hv : v = s
    · subst hv; simp [distS_self]
    · simp only [hv, if_false]
      refine le_antisymm (le_distS ?_) le_top
      intro l hl hi
      cases l with
      | nil => exact absurd hl.symm hv
      | cons y l => exact absurd hi.1 (by simp)
  · intro z hz
    exact absurd hz (by simp)

lemma inv_step (w : V → V → ℝ≥0∞) (s : V) (st : Finset V × (V → ℝ≥0∞)) (h : Inv w s st) :
    Inv w s (step w st) := by
  obtain ⟨hA, hB⟩ := h
  rw [step]
  cases hl : (Finset.univ \ st.1).toList with
  | nil => exact ⟨hA, hB⟩
  | cons x l =>
    have humem : argMin st.2 x l ∈ Finset.univ \ st.1 := by
      rw [← Finset.mem_toList, hl]
      exact argMin_mem _ _ _
    have hunot : argMin st.2 x l ∉ st.1 := (Finset.mem_sdiff.mp humem).2
    have hmin : ∀ y, y ∉ st.1 → st.2 (argMin st.2 x l) ≤ st.2 y := by
      intro y hy
      refine argMin_le st.2 x l y ?_
      rw [← hl, Finset.mem_toList]
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_univ _, hy⟩
    have hfin : st.2 (argMin st.2 x l) = spDist w s (argMin st.2 x l) :=
      key_extract w st.1 s _ st.2 hA hunot hmin
    refine ⟨fun v => key_update w st.1 s _ st.2 hA hB hfin v, ?_⟩
    intro z hz
    have hval : (stepList w st.1 st.2 (x :: l)).2 z
        = min (st.2 z) (st.2 (argMin st.2 x l) + w (argMin st.2 x l) z) := rfl
    rcases Finset.mem_insert.mp hz with heq | hz'
    · rw [hval, heq, min_eq_left le_self_add]
      exact hfin
    · have h1 : st.2 z = spDist w s z := hB z hz'
      have h2 : st.2 z ≤ st.2 (argMin st.2 x l) + w (argMin st.2 x l) z := by
        rw [h1, hfin]
        exact spDist_edge w s _ z
      rw [hval, min_eq_left h2, h1]

lemma inv_iterate (w : V → V → ℝ≥0∞) (s : V) (n : ℕ) (st : Finset V × (V → ℝ≥0∞))
    (h : Inv w s st) : Inv w s ((step w)^[n] st) := by
  induction n generalizing st with
  | zero => simpa using h
  | succ n ih => rw [Function.iterate_succ_apply]; exact ih _ (inv_step w s st h)

/-! ## Termination -/

lemma step_of_univ (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞))
    (h : st.1 = Finset.univ) : (step w st).1 = Finset.univ := by
  rw [step]
  have hnil : (Finset.univ \ st.1).toList = [] := by
    rw [Finset.toList_eq_nil, h, Finset.sdiff_self]
  rw [hnil]
  exact h

lemma step_card (w : V → V → ℝ≥0∞) (st : Finset V × (V → ℝ≥0∞))
    (h : st.1 ≠ Finset.univ) : (step w st).1.card = st.1.card + 1 := by
  rw [step]
  cases hl : (Finset.univ \ st.1).toList with
  | nil =>
    exfalso
    rw [Finset.toList_eq_nil, Finset.sdiff_eq_empty_iff_subset] at hl
    exact h (Finset.eq_univ_of_forall fun v => hl (Finset.mem_univ v))
  | cons x l =>
    have humem : argMin st.2 x l ∈ Finset.univ \ st.1 := by
      rw [← Finset.mem_toList, hl]
      exact argMin_mem _ _ _
    have hunot : argMin st.2 x l ∉ st.1 := (Finset.mem_sdiff.mp humem).2
    show (insert (argMin st.2 x l) st.1).card = st.1.card + 1
    exact Finset.card_insert_of_notMem hunot

/-- After `n` rounds either everything is visited, or exactly `n` vertices are. -/
lemma card_iterate (w : V → V → ℝ≥0∞) (d₀ : V → ℝ≥0∞) (n : ℕ) :
    ((step w)^[n] ((∅ : Finset V), d₀)).1 = Finset.univ ∨
      ((step w)^[n] ((∅ : Finset V), d₀)).1.card = n := by
  induction n with
  | zero => right; simp
  | succ n ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · exact Or.inl (step_of_univ w _ h)
    · by_cases hu : ((step w)^[n] ((∅ : Finset V), d₀)).1 = Finset.univ
      · exact Or.inl (step_of_univ w _ hu)
      · right; rw [step_card w _ hu, h]

lemma visited_all (w : V → V → ℝ≥0∞) (d₀ : V → ℝ≥0∞) :
    ((step w)^[Fintype.card V] ((∅ : Finset V), d₀)).1 = Finset.univ := by
  rcases card_iterate w d₀ (Fintype.card V) with h | h
  · exact h
  · exact Finset.eq_univ_of_card _ h

/-! ## Main theorem -/

/-- **Correctness of Dijkstra's algorithm.**  On a finite digraph with nonnegative
edge weights (encoded as `ℝ≥0∞`-valued weights, `⊤` meaning "no edge"),
`dijkstra w s t` equals the shortest-path distance from `s` to `t`, i.e. the infimum
of the costs of all paths from `s` to `t`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s t : V) : dijkstra w s t = spDist w s t := by
  have h := inv_iterate w s (Fintype.card V) _ (inv_init w s)
  have hu := visited_all w (fun v => if v = s then 0 else (⊤ : ℝ≥0∞))
  rw [dijkstra, h.1 t, hu, distS_univ]

end Algorithm

/-! ## Graphs with real nonnegative weights

The formulation above uses `ℝ≥0∞`-valued weights, which is how nonnegativity of the
weights and absence of edges are encoded.  We spell out the corresponding statement for
a graph given by an adjacency relation `adj` together with genuinely real, nonnegative
edge weights `wr`. -/

section RealWeights

variable [Fintype V] [DecidableEq V]

/-- The real total weight of the path that starts at `x` and then visits the vertices
of `l`. -/
def rPathCost (wr : V → V → ℝ) (x : V) : List V → ℝ
  | [] => 0
  | y :: l => wr x y + rPathCost wr y l

/-- `edgesIn adj x l` says that every step of the path `x :: l` is an edge. -/
def edgesIn (adj : V → V → Prop) : V → List V → Prop
  | _, [] => True
  | x, y :: l => adj x y ∧ edgesIn adj y l

/-- The `ℝ≥0∞`-valued weight function attached to a graph with adjacency relation `adj`
and real edge weights `wr`: a missing edge gets weight `⊤`. -/
noncomputable def toENN (adj : V → V → Prop) (wr : V → V → ℝ) : V → V → ℝ≥0∞ :=
  fun u v => if adj u v then ENNReal.ofReal (wr u v) else ⊤

omit [Fintype V] [DecidableEq V] in
lemma rPathCost_nonneg {wr : V → V → ℝ} (hw : ∀ u v, 0 ≤ wr u v) (x : V) (l : List V) :
    0 ≤ rPathCost wr x l := by
  induction l generalizing x with
  | nil => simp [rPathCost]
  | cons y l ih => exact add_nonneg (hw x y) (ih y)

omit [Fintype V] [DecidableEq V] in
/-- Along a path all of whose steps are edges, the `ℝ≥0∞`-cost is the real cost. -/
lemma pathCost_toENN {adj : V → V → Prop} {wr : V → V → ℝ} (hw : ∀ u v, 0 ≤ wr u v)
    (x : V) (l : List V) (h : edgesIn adj x l) :
    pathCost (toENN adj wr) x l = ENNReal.ofReal (rPathCost wr x l) := by
  induction l generalizing x with
  | nil => simp [pathCost, rPathCost]
  | cons y l ih =>
    obtain ⟨hadj, h'⟩ := h
    rw [pathCost, rPathCost, ih y h', toENN, if_pos hadj,
      ← ENNReal.ofReal_add (hw x y) (rPathCost_nonneg hw y l)]

omit [Fintype V] [DecidableEq V] in
/-- A path using a missing edge has infinite cost. -/
lemma pathCost_toENN_of_not_edgesIn {adj : V → V → Prop} {wr : V → V → ℝ}
    (x : V) (l : List V) (h : ¬ edgesIn adj x l) :
    pathCost (toENN adj wr) x l = ⊤ := by
  induction l generalizing x with
  | nil => exact absurd trivial h
  | cons y l ih =>
    by_cases hadj : adj x y
    · have h' : ¬ edgesIn adj y l := fun hc => h ⟨hadj, hc⟩
      rw [pathCost, ih y h', add_top]
    · rw [pathCost, toENN, if_neg hadj, top_add]

/-- **Correctness of Dijkstra's algorithm, for real nonnegative edge weights.**
On a finite digraph with adjacency relation `adj` and nonnegative real edge weights `wr`,
Dijkstra's algorithm returns the infimum of the real costs of the paths from `s` to `t`
(and `⊤` when there is no such path). -/
theorem dijkstra_correct_real (adj : V → V → Prop) (wr : V → V → ℝ)
    (hw : ∀ u v, 0 ≤ wr u v) (s t : V) :
    dijkstra (toENN adj wr) s t =
      sInf {c : ℝ≥0∞ | ∃ l : List V, pathEnd s l = t ∧ edgesIn adj s l ∧
        c = ENNReal.ofReal (rPathCost wr s l)} := by
  rw [dijkstra_correct]
  refine le_antisymm (le_sInf ?_) (le_spDist ?_)
  · rintro c ⟨l, hl, he, rfl⟩
    rw [← pathCost_toENN hw s l he]
    exact spDist_le l hl
  · intro l hl
    by_cases he : edgesIn adj s l
    · exact sInf_le ⟨l, hl, he, (pathCost_toENN hw s l he)⟩
    · rw [pathCost_toENN_of_not_edgesIn (wr := wr) s l he]
      exact le_top

end RealWeights

/-! ## A sanity check

On the two-vertex graph with the single edge `0 → 1` of weight `5`, the shortest-path
distance from `0` to `1` is indeed `5`. -/

section Sanity

/-- The two-vertex graph with a single edge `0 → 1` of weight `5`. -/
noncomputable def exampleWeight : Fin 2 → Fin 2 → ℝ≥0∞ :=
  fun i j => if i = 0 ∧ j = 1 then 5 else ⊤

lemma exampleWeight_spDist : spDist exampleWeight 0 1 = 5 := by
  refine le_antisymm ?_ (le_spDist ?_)
  · calc spDist exampleWeight 0 1 ≤ pathCost exampleWeight 0 [1] := spDist_le _ rfl
      _ = 5 := by simp [pathCost, exampleWeight]
  · intro l hl
    match l with
    | [] => exact absurd hl (by decide)
    | y :: l' =>
      fin_cases y
      · simp [pathCost, exampleWeight]
      · rw [pathCost]
        refine le_trans ?_ le_self_add
        simp [exampleWeight]

/-- Dijkstra's algorithm returns `5`, as it should. -/
example : dijkstra exampleWeight 0 1 = 5 := by
  rw [dijkstra_correct, exampleWeight_spDist]

example : spDist exampleWeight 1 0 = ⊤ := by
  refine le_antisymm le_top (le_spDist ?_)
  intro l hl
  match l with
  | [] => exact absurd hl (by decide)
  | y :: l' =>
    have : exampleWeight 1 y = ⊤ := by
      fin_cases y <;> simp [exampleWeight]
    rw [pathCost, this, top_add]

end Sanity

end CS

import Mathlib
import RequestProject.Dijkstra

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

