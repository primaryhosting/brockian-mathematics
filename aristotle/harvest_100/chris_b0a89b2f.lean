-- (Lean requires `import` to be the first command of a file, so the header comment
-- follows it.)
import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
We formalise Dijkstra's algorithm on a finite directed graph whose edge weights are
nonnegative (encoded by taking values in `ℝ≥0∞`, where `⊤` means "no edge"), and prove
that it computes the true shortest-path distances from a fixed source.
-/

namespace CS

open scoped ENNReal

variable {V : Type*}

/-! ## Walks, their weights, and the shortest-path distance -/

/-- The endpoint of the walk that starts at `s` and visits the vertices of `l` in order. -/
def endp (s : V) : List V → V
  | [] => s
  | v :: l => endp v l

/-- The total weight of the walk starting at `s` and visiting the vertices of `l` in order. -/
noncomputable def wt (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | s, v :: l => w s v + wt w v l

/-- The shortest-path distance from `s` to `t`: the infimum of the weights of all walks
from `s` to `t` (`⊤` if there is no such walk). -/
noncomputable def gdist (w : V → V → ℝ≥0∞) (s t : V) : ℝ≥0∞ :=
  sInf {x | ∃ l : List V, endp s l = t ∧ wt w s l = x}

@[simp] lemma endp_nil (s : V) : endp s ([] : List V) = s := rfl

@[simp] lemma endp_cons (s v : V) (l : List V) : endp s (v :: l) = endp v l := rfl

@[simp] lemma wt_nil (w : V → V → ℝ≥0∞) (s : V) : wt w s [] = 0 := rfl

@[simp] lemma wt_cons (w : V → V → ℝ≥0∞) (s v : V) (l : List V) :
    wt w s (v :: l) = w s v + wt w v l := rfl

lemma endp_append (s : V) (l₁ l₂ : List V) :
    endp s (l₁ ++ l₂) = endp (endp s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons a t ih => simpa using ih a

lemma wt_append (w : V → V → ℝ≥0∞) (s : V) (l₁ l₂ : List V) :
    wt w s (l₁ ++ l₂) = wt w s l₁ + wt w (endp s l₁) l₂ := by
  induction l₁ generalizing s with
  | nil => simp
  | cons a t ih => simp [ih a, add_assoc]

lemma endp_mem (s : V) {l : List V} (hl : l ≠ []) : endp s l ∈ l := by
  induction l generalizing s with
  | nil => exact absurd rfl hl
  | cons a t ih =>
      rcases eq_or_ne t [] with rfl | ht
      · simp
      · exact List.mem_cons_of_mem _ (ih a ht)

/-- Any walk gives an upper bound for the distance. -/
lemma gdist_le (w : V → V → ℝ≥0∞) {s t : V} {l : List V} (h : endp s l = t) :
    gdist w s t ≤ wt w s l :=
  sInf_le ⟨l, h, rfl⟩

/-- To lower-bound the distance it suffices to lower-bound the weight of every walk. -/
lemma le_gdist (w : V → V → ℝ≥0∞) {s t : V} {c : ℝ≥0∞}
    (h : ∀ l : List V, endp s l = t → c ≤ wt w s l) : c ≤ gdist w s t := by
  refine le_sInf ?_
  rintro x ⟨l, hl, rfl⟩
  exact h l hl

@[simp] lemma gdist_self (w : V → V → ℝ≥0∞) (s : V) : gdist w s s = 0 :=
  le_antisymm (by simpa using gdist_le w (l := ([] : List V)) rfl) (zero_le _)

/-- Triangle inequality along a single edge. -/
lemma gdist_triangle_edge (w : V → V → ℝ≥0∞) (s u v : V) :
    gdist w s v ≤ gdist w s u + w u v := by
  have hadd : gdist w s u + w u v
      = ⨅ b ∈ {x : ℝ≥0∞ | ∃ l : List V, endp s l = u ∧ wt w s l = x}, b + w u v :=
    ENNReal.sInf_add
  rw [hadd]
  refine le_iInf₂ ?_
  rintro x ⟨l, hl, rfl⟩
  have h : endp s (l ++ [v]) = v := by simp [endp_append, hl]
  calc gdist w s v ≤ wt w s (l ++ [v]) := gdist_le w h
    _ = wt w s l + w u v := by simp [wt_append, hl]

/-- Splitting a walk at its first vertex outside `S`. -/
lemma exists_split (S : Finset V) :
    ∀ (l : List V), (∃ v ∈ l, v ∉ S) →
      ∃ (l₁ : List V) (x : V) (l₂ : List V),
        l = l₁ ++ x :: l₂ ∧ (∀ y ∈ l₁, y ∈ S) ∧ x ∉ S := by
  intro l
  induction l with
  | nil => rintro ⟨v, hv, -⟩; simp at hv
  | cons a t ih =>
      intro h
      by_cases ha : a ∈ S
      · obtain ⟨v, hv, hvS⟩ := h
        rcases List.mem_cons.1 hv with rfl | hv'
        · exact absurd ha hvS
        · obtain ⟨l₁, x, l₂, rfl, h₁, h₂⟩ := ih ⟨v, hv', hvS⟩
          exact ⟨a :: l₁, x, l₂, by simp, by
            intro y hy
            rcases List.mem_cons.1 hy with rfl | hy'
            · exact ha
            · exact h₁ y hy', h₂⟩
      · exact ⟨[], a, t, by simp, by simp, ha⟩

/-! ## The algorithm -/

/-- The state of Dijkstra's algorithm: a set `S` of settled vertices and tentative
distances `D`. -/
structure State (V : Type*) where
  /-- the settled vertices -/
  S : Finset V
  /-- the tentative distances -/
  D : V → ℝ≥0∞

/-- A vertex of `T` minimising `D`. -/
noncomputable def pick (D : V → ℝ≥0∞) (T : Finset V) (h : T.Nonempty) : V :=
  (T.exists_min_image D h).choose

lemma pick_mem (D : V → ℝ≥0∞) (T : Finset V) (h : T.Nonempty) : pick D T h ∈ T :=
  (T.exists_min_image D h).choose_spec.1

lemma pick_min (D : V → ℝ≥0∞) (T : Finset V) (h : T.Nonempty) :
    ∀ v ∈ T, D (pick D T h) ≤ D v :=
  (T.exists_min_image D h).choose_spec.2

variable [Fintype V] [DecidableEq V]

/-- One iteration of Dijkstra's algorithm: settle an unsettled vertex of minimal tentative
distance and relax all edges out of it. -/
noncomputable def step (w : V → V → ℝ≥0∞) (st : State V) : State V :=
  if h : st.Sᶜ.Nonempty then
    let u := pick st.D st.Sᶜ h
    ⟨insert u st.S, fun v => min (st.D v) (st.D u + w u v)⟩
  else st

/-- The initial state: only the source is settled. -/
noncomputable def init (w : V → V → ℝ≥0∞) (s : V) : State V :=
  ⟨{s}, fun v => if v = s then 0 else w s v⟩

/-- Dijkstra's algorithm: iterate `step` until every vertex is settled. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) : State V :=
  (step w)^[Fintype.card V] (init w s)

/-! ## The loop invariant -/

/-- The loop invariant of Dijkstra's algorithm. -/
structure Inv (w : V → V → ℝ≥0∞) (s : V) (st : State V) : Prop where
  /-- the source is settled -/
  src : s ∈ st.S
  /-- tentative distances are upper bounds for the true distance -/
  ge : ∀ v, gdist w s v ≤ st.D v
  /-- settled vertices carry the true distance -/
  settled : ∀ v ∈ st.S, st.D v = gdist w s v
  /-- all edges out of settled vertices have been relaxed -/
  relax : ∀ y ∈ st.S, ∀ v, v ∉ st.S → st.D v ≤ gdist w s y + w y v

omit [Fintype V] in
lemma inv_init (w : V → V → ℝ≥0∞) (s : V) : Inv w s (init w s) where
  src := by simp [init]
  ge := by
    intro v
    by_cases h : v = s
    · subst h; simp [init]
    · simp only [init, if_neg h]
      simpa using gdist_le w (l := [v]) rfl
  settled := by
    intro v hv
    simp only [init, Finset.mem_singleton] at hv
    subst hv
    simp [init]
  relax := by
    intro y hy v hv
    simp only [init, Finset.mem_singleton] at hy
    subst hy
    simp only [init, Finset.mem_singleton] at hv
    simp [init, hv]

/-- The key step: the unsettled vertex with minimal tentative distance has the correct
tentative distance. -/
lemma pick_eq_gdist (w : V → V → ℝ≥0∞) (s : V) {st : State V} (hst : Inv w s st)
    (h : st.Sᶜ.Nonempty) : st.D (pick st.D st.Sᶜ h) = gdist w s (pick st.D st.Sᶜ h) := by
  set u := pick st.D st.Sᶜ h with hu
  have huS : u ∉ st.S := by
    have := pick_mem st.D st.Sᶜ h
    simpa using this
  refine le_antisymm ?_ (hst.ge u)
  refine le_gdist w ?_
  intro l hl
  have hlne : l ≠ [] := by
    rintro rfl
    exact huS (by simpa [hl.symm] using hst.src)
  have hmem : ∃ v ∈ l, v ∉ st.S := ⟨u, hl ▸ endp_mem s hlne, huS⟩
  obtain ⟨l₁, x, l₂, rfl, h₁, hx⟩ := exists_split st.S l hmem
  set y := endp s l₁ with hy
  have hyS : y ∈ st.S := by
    rcases eq_or_ne l₁ [] with rfl | hne
    · simpa [hy] using hst.src
    · exact h₁ _ (endp_mem s hne)
  calc st.D u ≤ st.D x := pick_min st.D st.Sᶜ h x (by simpa using hx)
    _ ≤ gdist w s y + w y x := hst.relax y hyS x hx
    _ ≤ wt w s l₁ + w y x := add_le_add (gdist_le w rfl) le_rfl
    _ ≤ wt w s l₁ + (w y x + wt w x l₂) := add_le_add le_rfl le_self_add
    _ = wt w s (l₁ ++ x :: l₂) := by rw [wt_append]; rfl

lemma inv_step (w : V → V → ℝ≥0∞) (s : V) {st : State V} (hst : Inv w s st) :
    Inv w s (step w st) := by
  by_cases h : st.Sᶜ.Nonempty
  · have hDu : st.D (pick st.D st.Sᶜ h) = gdist w s (pick st.D st.Sᶜ h) :=
      pick_eq_gdist w s hst h
    set u := pick st.D st.Sᶜ h with hu
    have huS : u ∉ st.S := by simpa using pick_mem st.D st.Sᶜ h
    have hstep : step w st = ⟨insert u st.S, fun v => min (st.D v) (st.D u + w u v)⟩ := by
      simp [step, h, hu]
    rw [hstep]
    refine ⟨?_, ?_, ?_, ?_⟩
    · exact Finset.mem_insert_of_mem hst.src
    · intro v
      simp only [le_min_iff]
      refine ⟨hst.ge v, ?_⟩
      rw [hDu]
      exact gdist_triangle_edge w s u v
    · intro v hv
      refine le_antisymm ?_ ?_
      · rcases Finset.mem_insert.1 hv with rfl | hv'
        · simp [hDu]
        · rw [← hst.settled v hv']
          exact min_le_left _ _
      · simp only [le_min_iff]
        refine ⟨hst.ge v, ?_⟩
        rw [hDu]
        exact gdist_triangle_edge w s u v
    · intro y hy v hv
      have hvS : v ∉ st.S := fun hc => hv (Finset.mem_insert_of_mem hc)
      rcases Finset.mem_insert.1 hy with rfl | hy'
      · refine le_trans (min_le_right _ _) ?_
        rw [hDu]
      · exact le_trans (min_le_left _ _) (hst.relax y hy' v hvS)
  · rwa [step, dif_neg h]

lemma inv_iterate (w : V → V → ℝ≥0∞) (s : V) :
    ∀ (n : ℕ) {st : State V}, Inv w s st → Inv w s ((step w)^[n] st) := by
  intro n
  induction n with
  | zero => intro st hst; simpa using hst
  | succ k ih =>
      intro st hst
      rw [Function.iterate_succ_apply]
      exact ih (inv_step w s hst)

/-! ## Termination: after `card V` iterations every vertex is settled -/

lemma step_fixed (w : V → V → ℝ≥0∞) {st : State V} (h : ¬ st.Sᶜ.Nonempty) :
    step w st = st := by
  rw [step, dif_neg h]

lemma iterate_fixed (w : V → V → ℝ≥0∞) {st : State V} (h : ¬ st.Sᶜ.Nonempty) :
    ∀ n : ℕ, (step w)^[n] st = st := by
  intro n
  induction n with
  | zero => simp
  | succ k ih => rw [Function.iterate_succ_apply, step_fixed w h, ih]

lemma card_iterate (w : V → V → ℝ≥0∞) :
    ∀ (n : ℕ) (st : State V),
      min (Fintype.card V) (st.S.card + n) ≤ ((step w)^[n] st).S.card := by
  intro n
  induction n with
  | zero =>
      intro st
      simp only [Function.iterate_zero_apply, Nat.add_zero]
      exact min_le_right _ _
  | succ k ih =>
      intro st
      rw [Function.iterate_succ_apply]
      by_cases h : st.Sᶜ.Nonempty
      · have hstep : (step w st).S = insert (pick st.D st.Sᶜ h) st.S := by simp [step, h]
        have huS : pick st.D st.Sᶜ h ∉ st.S := by simpa using pick_mem st.D st.Sᶜ h
        have hcard : (step w st).S.card = st.S.card + 1 := by
          rw [hstep, Finset.card_insert_of_notMem huS]
        refine le_trans ?_ (ih (step w st))
        rw [hcard]
        exact min_le_min_left _ (by omega)
      · rw [step_fixed w h, iterate_fixed w h]
        have : st.S = Finset.univ := by
          simpa [Finset.compl_eq_empty_iff] using Finset.not_nonempty_iff_eq_empty.1 h
        rw [this]
        simp

/-! ## Correctness -/

/-- **Correctness of Dijkstra's algorithm.**  On a finite directed graph with nonnegative
edge weights `w : V → V → ℝ≥0∞` (the value `⊤` encoding a missing edge), the tentative
distance computed by `dijkstra w s` at every vertex `v` is the true shortest-path distance
from `s` to `v`, i.e. the infimum of the weights of all walks from `s` to `v`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s v : V) :
    (dijkstra w s).D v = gdist w s v := by
  have hinv : Inv w s (dijkstra w s) := inv_iterate w s _ (inv_init w s)
  have hcard : Fintype.card V ≤ (dijkstra w s).S.card := by
    have := card_iterate w (Fintype.card V) (init w s)
    refine le_trans ?_ this
    exact le_min le_rfl (by omega)
  have huniv : (dijkstra w s).S = Finset.univ :=
    Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) hcard)
  exact hinv.settled v (huniv ▸ Finset.mem_univ v)

/-! ## Sanity checks (non-vacuity of the statement) -/

omit [Fintype V] [DecidableEq V] in
/-- With no edges at all, a vertex different from the source is at distance `⊤`. -/
lemma gdist_top_of_no_edges (w : V → V → ℝ≥0∞) (hw : ∀ u v, w u v = ⊤) {s t : V}
    (h : s ≠ t) : gdist w s t = ⊤ := by
  refine eq_top_iff.2 (le_gdist w ?_)
  intro l hl
  cases l with
  | nil => exact absurd hl h
  | cons a l' => simp [hw]

/-- On the two-vertex graph with the single edge `false → true` of weight `3`, Dijkstra
returns the distance `3`. -/
example :
    (dijkstra (fun a b : Bool => if a = false ∧ b = true then 3 else ⊤) false).D true = 3 := by
  set w : Bool → Bool → ℝ≥0∞ := fun a b => if a = false ∧ b = true then 3 else ⊤ with hwdef
  rw [dijkstra_correct]
  refine le_antisymm ?_ (le_gdist w ?_)
  · simpa [hwdef] using gdist_le w (l := [true]) rfl
  · intro l hl
    match l with
    | [] => exact absurd hl (by simp)
    | [a] =>
        have : a = true := hl
        subst this
        simp [hwdef]
    | a :: b :: l' =>
        cases a with
        | false => simp [hwdef]
        | true => simp [hwdef]

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

