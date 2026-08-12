import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Statement: Dijkstra's algorithm computes shortest-path distances on nonnegative-weight graphs.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped ENNReal

namespace CS

variable {V : Type*}

/-! ## Walks, their costs, and shortest-path distances

A weighted directed graph on the vertex type `V` is given by a weight function
`w : V → V → ℝ≥0∞`.  Values in `ℝ≥0∞` are automatically nonnegative (this is the
"nonnegative weights" hypothesis), and `w u v = ⊤` encodes the absence of an edge
from `u` to `v`.

A walk starting at `s` is described by the list `l` of the vertices it visits after `s`. -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/
def endpt : V → List V → V
  | s, [] => s
  | _, x :: l => endpt x l

/-- The total weight of the walk that starts at `s` and visits the vertices of `l` in order. -/
noncomputable def cost (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | s, x :: l => w s x + cost w x l

/-- `Restr S s l` says that every vertex of the walk `s :: l` **except its endpoint**
lies in `S`. -/
def Restr (S : Finset V) : V → List V → Prop
  | _, [] => True
  | s, x :: l => s ∈ S ∧ Restr S x l

@[simp] lemma endpt_nil (s : V) : endpt s [] = s := rfl
@[simp] lemma endpt_cons (s x : V) (l : List V) : endpt s (x :: l) = endpt x l := rfl
@[simp] lemma cost_nil (w : V → V → ℝ≥0∞) (s : V) : cost w s [] = 0 := rfl
@[simp] lemma cost_cons (w : V → V → ℝ≥0∞) (s x : V) (l : List V) :
    cost w s (x :: l) = w s x + cost w x l := rfl
@[simp] lemma Restr_nil (S : Finset V) (s : V) : Restr S s [] := trivial
@[simp] lemma Restr_cons (S : Finset V) (s x : V) (l : List V) :
    Restr S s (x :: l) ↔ s ∈ S ∧ Restr S x l := Iff.rfl

lemma endpt_append (s : V) (l₁ l₂ : List V) :
    endpt s (l₁ ++ l₂) = endpt (endpt s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons x l ih => simp [ih]

lemma cost_append (w : V → V → ℝ≥0∞) (s : V) (l₁ l₂ : List V) :
    cost w s (l₁ ++ l₂) = cost w s l₁ + cost w (endpt s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons x l ih => simp [ih, add_assoc]

lemma Restr_append (S : Finset V) (s : V) (l₁ l₂ : List V) :
    Restr S s (l₁ ++ l₂) ↔ Restr S s l₁ ∧ Restr S (endpt s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons x l ih => simp [ih, and_assoc]

lemma Restr_mono {S S' : Finset V} (h : S ⊆ S') :
    ∀ (s : V) (l : List V), Restr S s l → Restr S' s l := by
  intro s l
  induction l generalizing s with
  | nil => simp
  | cons x l ih => exact fun ⟨hs, hl⟩ => ⟨h hs, ih x hl⟩

lemma Restr_univ [Fintype V] (s : V) (l : List V) : Restr (Finset.univ : Finset V) s l := by
  induction l generalizing s with
  | nil => simp
  | cons x l ih => exact ⟨Finset.mem_univ s, ih x⟩

lemma Restr_empty_eq_nil (s : V) (l : List V) (h : Restr (∅ : Finset V) s l) : l = [] := by
  cases l with
  | nil => rfl
  | cons x l => exact absurd h.1 (Finset.notMem_empty s)

/-- The shortest-path distance from `s` to `t`: the infimum of the costs of all walks. -/
noncomputable def gdist (w : V → V → ℝ≥0∞) (s t : V) : ℝ≥0∞ :=
  ⨅ l : List V, ⨅ _ : endpt s l = t, cost w s l

/-- The shortest-path distance from `s` to `t` among walks all of whose vertices, except
the endpoint `t`, lie in `S`. -/
noncomputable def rdist (w : V → V → ℝ≥0∞) (S : Finset V) (s t : V) : ℝ≥0∞ :=
  ⨅ l : List V, ⨅ _ : endpt s l = t, ⨅ _ : Restr S s l, cost w s l

lemma gdist_le_cost {w : V → V → ℝ≥0∞} {s t : V} {l : List V} (hl : endpt s l = t) :
    gdist w s t ≤ cost w s l :=
  iInf_le_of_le l (iInf_le_of_le hl le_rfl)

/-- The distance from a vertex to itself is `0` (the empty walk). -/
lemma gdist_self (w : V → V → ℝ≥0∞) (s : V) : gdist w s s = 0 :=
  le_antisymm (by simpa using gdist_le_cost (w := w) (l := ([] : List V)) rfl) (zero_le _)

/-- A single edge is a walk, so the distance is at most the weight of the edge. -/
lemma gdist_le_edge (w : V → V → ℝ≥0∞) (s t : V) : gdist w s t ≤ w s t := by
  simpa using gdist_le_cost (w := w) (l := [t]) rfl

lemma rdist_le_cost {w : V → V → ℝ≥0∞} {S : Finset V} {s t : V} {l : List V}
    (hl : endpt s l = t) (hr : Restr S s l) : rdist w S s t ≤ cost w s l :=
  iInf_le_of_le l (iInf_le_of_le hl (iInf_le_of_le hr le_rfl))

lemma le_rdist {w : V → V → ℝ≥0∞} {S : Finset V} {s t : V} {a : ℝ≥0∞}
    (h : ∀ l : List V, endpt s l = t → Restr S s l → a ≤ cost w s l) : a ≤ rdist w S s t :=
  le_iInf fun l => le_iInf fun hl => le_iInf fun hr => h l hl hr

lemma le_gdist {w : V → V → ℝ≥0∞} {s t : V} {a : ℝ≥0∞}
    (h : ∀ l : List V, endpt s l = t → a ≤ cost w s l) : a ≤ gdist w s t :=
  le_iInf fun l => le_iInf fun hl => h l hl

lemma gdist_le_rdist (w : V → V → ℝ≥0∞) (S : Finset V) (s t : V) :
    gdist w s t ≤ rdist w S s t :=
  le_rdist fun _ hl _ => gdist_le_cost hl

lemma rdist_mono (w : V → V → ℝ≥0∞) {S S' : Finset V} (h : S ⊆ S') (s t : V) :
    rdist w S' s t ≤ rdist w S s t :=
  le_rdist fun l hl hr => rdist_le_cost hl (Restr_mono h s l hr)

lemma rdist_self (w : V → V → ℝ≥0∞) (S : Finset V) (s : V) : rdist w S s s = 0 :=
  le_antisymm (by simpa using rdist_le_cost (l := ([] : List V)) rfl (Restr_nil S s)) (zero_le _)

lemma rdist_univ [Fintype V] (w : V → V → ℝ≥0∞) (s t : V) :
    rdist w (Finset.univ : Finset V) s t = gdist w s t :=
  le_antisymm (le_gdist fun l hl => rdist_le_cost hl (Restr_univ s l))
    (gdist_le_rdist w _ s t)

lemma rdist_empty [DecidableEq V] (w : V → V → ℝ≥0∞) (s t : V) :
    rdist w (∅ : Finset V) s t = if t = s then 0 else ⊤ := by
  by_cases h : t = s
  · subst h; simp [rdist_self]
  · simp only [h, if_false]
    rw [eq_top_iff]
    exact le_rdist fun l hl hr => by
      rw [Restr_empty_eq_nil s l hr] at hl; exact absurd hl.symm h

lemma rdist_add (w : V → V → ℝ≥0∞) (S : Finset V) (s t : V) (c : ℝ≥0∞) :
    rdist w S s t + c
      = ⨅ l : List V, ⨅ _ : endpt s l = t, ⨅ _ : Restr S s l, (cost w s l + c) := by
  simp only [rdist, ENNReal.iInf_add]

/-- Extending a walk ending at a vertex `z ∈ S` by the edge `z → v`. -/
lemma rdist_extend (w : V → V → ℝ≥0∞) {S : Finset V} {z : V} (hz : z ∈ S) (s v : V) :
    rdist w S s v ≤ rdist w S s z + w z v := by
  rw [rdist_add]
  refine le_iInf fun l => le_iInf fun hl => le_iInf fun hr => ?_
  have hend : endpt s (l ++ [v]) = v := by rw [endpt_append]; simp
  have hres : Restr S s (l ++ [v]) := by
    rw [Restr_append]
    exact ⟨hr, by simp [hl, hz]⟩
  have := rdist_le_cost (w := w) hend hres
  rwa [cost_append, hl, cost_cons, cost_nil, add_zero] at this

/-- If a walk from `s` ends outside `S`, it has a prefix that stays inside `S` (except for
its endpoint), ends outside `S`, and costs no more. -/
lemma exists_good_prefix (w : V → V → ℝ≥0∞) (S : Finset V) :
    ∀ (s : V) (l : List V), endpt s l ∉ S →
      ∃ p : List V, Restr S s p ∧ endpt s p ∉ S ∧ cost w s p ≤ cost w s l := by
  intro s l
  induction l generalizing s with
  | nil => exact fun h => ⟨[], trivial, h, le_rfl⟩
  | cons x l ih =>
      intro h
      by_cases hs : s ∈ S
      · rcases ih x (by simpa using h) with ⟨p, hp1, hp2, hp3⟩
        refine ⟨x :: p, ⟨hs, hp1⟩, by simpa using hp2, ?_⟩
        simp only [cost_cons]
        exact add_le_add le_rfl hp3
      · exact ⟨[], trivial, hs, by simp⟩

/-- **Key step of Dijkstra's algorithm.** If `u ∉ S` minimises the `S`-restricted distance
among all vertices outside `S`, then this restricted distance is the true distance. -/
lemma rdist_eq_gdist_of_min (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V) (hu : u ∉ S)
    (hmin : ∀ v, v ∉ S → rdist w S s u ≤ rdist w S s v) :
    rdist w S s u = gdist w s u := by
  refine le_antisymm (le_gdist fun l hl => ?_) (gdist_le_rdist w S s u)
  have hend : endpt s l ∉ S := by rw [hl]; exact hu
  rcases exists_good_prefix w S s l hend with ⟨p, hp1, hp2, hp3⟩
  calc rdist w S s u ≤ rdist w S s (endpt s p) := hmin _ hp2
    _ ≤ cost w s p := rdist_le_cost rfl hp1
    _ ≤ cost w s l := hp3

variable [DecidableEq V]

/-- **The relaxation step is correct.** Adding the settled vertex `u` to `S` changes the
restricted distances exactly the way Dijkstra's relaxation does. -/
lemma rdist_insert (w : V → V → ℝ≥0∞) (S : Finset V) (s u : V)
    (hex : rdist w S s u = gdist w s u)
    (hA : ∀ z ∈ S, rdist w S s z = gdist w s z) (v : V) :
    rdist w (insert u S) s v = min (rdist w S s v) (rdist w S s u + w u v) := by
  refine le_antisymm (le_min (rdist_mono w (Finset.subset_insert u S) s v) ?_) ?_
  · calc rdist w (insert u S) s v
        ≤ rdist w (insert u S) s u + w u v :=
          rdist_extend w (Finset.mem_insert_self u S) s v
      _ ≤ rdist w S s u + w u v :=
          add_le_add (rdist_mono w (Finset.subset_insert u S) s u) le_rfl
  · refine le_rdist fun l hl hr => ?_
    rcases List.eq_nil_or_concat l with rfl | ⟨L, b, rfl⟩
    · simp only [endpt_nil] at hl
      subst hl
      simp [rdist_self]
    · simp only [List.concat_eq_append] at hl hr ⊢
      have hb : b = v := by rw [endpt_append] at hl; simpa using hl
      subst hb
      rw [Restr_append] at hr
      obtain ⟨hL, hz⟩ := hr
      have hzS : endpt s L ∈ insert u S := by simpa using hz.1
      have hcost : cost w s (L ++ [b]) = cost w s L + w (endpt s L) b := by
        rw [cost_append, cost_cons, cost_nil, add_zero]
      rw [hcost]
      rcases Finset.mem_insert.mp hzS with hzu | hzS'
      · rw [hzu]
        refine le_trans (min_le_right _ _) (add_le_add ?_ le_rfl)
        rw [hex]
        exact gdist_le_cost hzu
      · refine le_trans (min_le_left _ _) ?_
        calc rdist w S s b ≤ rdist w S s (endpt s L) + w (endpt s L) b :=
              rdist_extend w hzS' s b
          _ ≤ cost w s L + w (endpt s L) b := by
              refine add_le_add ?_ le_rfl
              rw [hA _ hzS']
              exact gdist_le_cost rfl

/-! ## The algorithm -/

variable [Fintype V]

open Classical in
/-- The unsettled vertex with minimal tentative distance (the vertex extracted from the
priority queue). -/
noncomputable def pick (d : V → ℝ≥0∞) (T : Finset V) (h : T.Nonempty) : V :=
  (Finset.exists_min_image T d h).choose

omit [DecidableEq V] [Fintype V] in
lemma pick_mem (d : V → ℝ≥0∞) (T : Finset V) (h : T.Nonempty) : pick d T h ∈ T :=
  (Finset.exists_min_image T d h).choose_spec.1

omit [DecidableEq V] [Fintype V] in
lemma pick_min (d : V → ℝ≥0∞) (T : Finset V) (h : T.Nonempty) :
    ∀ v ∈ T, d (pick d T h) ≤ d v :=
  (Finset.exists_min_image T d h).choose_spec.2

/-- The main loop of Dijkstra's algorithm: `T` is the set of unsettled vertices and `d` the
array of tentative distances.  At each round the unsettled vertex `u` of least tentative
distance is settled and all its outgoing edges are relaxed. -/
noncomputable def dijkstraAux (w : V → V → ℝ≥0∞) : ℕ → Finset V → (V → ℝ≥0∞) → (V → ℝ≥0∞)
  | 0, _, d => d
  | n + 1, T, d =>
      if h : T.Nonempty then
        dijkstraAux w n (T.erase (pick d T h))
          (fun v => min (d v) (d (pick d T h) + w (pick d T h) v))
      else d

/-- Dijkstra's algorithm run from the source `s`: start with all vertices unsettled,
tentative distance `0` at `s` and `⊤` elsewhere, and run `card V` rounds. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) : V → ℝ≥0∞ :=
  dijkstraAux w (Fintype.card V) Finset.univ (fun v => if v = s then 0 else ⊤)

lemma dijkstraAux_correct (w : V → V → ℝ≥0∞) (s : V) :
    ∀ (n : ℕ) (T : Finset V) (d : V → ℝ≥0∞), T.card ≤ n →
      (∀ v, d v = rdist w Tᶜ s v) → (∀ z ∈ Tᶜ, rdist w Tᶜ s z = gdist w s z) →
      ∀ v, dijkstraAux w n T d v = gdist w s v := by
  intro n
  induction n with
  | zero =>
      intro T d hcard h1 _ v
      have hT : T = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hcard)
      subst hT
      simpa [dijkstraAux, rdist_univ] using h1 v
  | succ n ih =>
      intro T d hcard h1 h2 v
      by_cases hT : T.Nonempty
      · set u := pick d T hT with hu
        have huT : u ∈ T := pick_mem d T hT
        have huS : u ∉ Tᶜ := by simpa using huT
        -- `u` minimises the restricted distance among unsettled vertices
        have hmin : ∀ x, x ∉ Tᶜ → rdist w Tᶜ s u ≤ rdist w Tᶜ s x := by
          intro x hx
          have hxT : x ∈ T := by simpa using hx
          have := pick_min d T hT x hxT
          rwa [h1, h1] at this
        have hex : rdist w Tᶜ s u = gdist w s u :=
          rdist_eq_gdist_of_min w Tᶜ s u huS hmin
        have hcompl : (T.erase u)ᶜ = insert u Tᶜ := by
          ext x; by_cases hxu : x = u <;> simp [hxu, huT]
        have hstep : ∀ x, min (d x) (d u + w u x) = rdist w (T.erase u)ᶜ s x := by
          intro x
          rw [hcompl, rdist_insert w Tᶜ s u hex h2 x, h1, h1]
        have hcard' : (T.erase u).card ≤ n := by
          have := Finset.card_erase_of_mem huT
          have hpos : 0 < T.card := Finset.card_pos.mpr hT
          omega
        have h2' : ∀ z ∈ (T.erase u)ᶜ, rdist w (T.erase u)ᶜ s z = gdist w s z := by
          intro z hz
          rw [hcompl] at hz ⊢
          refine le_antisymm ?_ (gdist_le_rdist w _ s z)
          rcases Finset.mem_insert.mp hz with rfl | hzS
          · exact (rdist_mono w (Finset.subset_insert u Tᶜ) s _).trans hex.le
          · exact (rdist_mono w (Finset.subset_insert u Tᶜ) s z).trans (h2 z hzS).le
        have := ih (T.erase u) (fun x => min (d x) (d u + w u x)) hcard'
          (fun x => hstep x) h2' v
        rw [dijkstraAux, dif_pos hT]
        exact this
      · have hT' : T = ∅ := Finset.not_nonempty_iff_eq_empty.mp hT
        subst hT'
        rw [dijkstraAux, dif_neg hT]
        simpa [rdist_univ] using h1 v

/-- **Dijkstra's algorithm is correct**: on a finite graph with nonnegative edge weights
(encoded as `w : V → V → ℝ≥0∞`, with `⊤` meaning "no edge"), the array computed by
Dijkstra's algorithm from the source `s` gives, at every vertex `t`, the shortest-path
distance from `s` to `t`, i.e. the infimum of the costs of all walks from `s` to `t`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s t : V) :
    dijkstra w s t = gdist w s t := by
  refine dijkstraAux_correct w s (Fintype.card V) Finset.univ _ (by simp) ?_ ?_ t
  · intro v
    rw [Finset.compl_univ, rdist_empty]
  · intro z hz
    simp at hz

/-- Real-valued version: for a finite graph with a nonnegative real weight function `wr`
on the edges of a relation `E`, Dijkstra's algorithm computes the shortest-path distances. -/
theorem dijkstra_correct_real (E : V → V → Prop) [DecidableRel E]
    (wr : V → V → ℝ) (_hwr : ∀ u v, 0 ≤ wr u v) (s t : V) :
    dijkstra (fun u v => if E u v then ENNReal.ofReal (wr u v) else ⊤) s t
      = gdist (fun u v => if E u v then ENNReal.ofReal (wr u v) else ⊤) s t :=
  dijkstra_correct _ s t

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

