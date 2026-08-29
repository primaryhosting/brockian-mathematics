import Mathlib

/-!
# Dijkstra Correct
Category: Computer Science
Target: CS.dijkstra_correct
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open scoped ENNReal

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `wcost w u l` is the total weight of the walk that starts at `u` and visits the
vertices of `l` in order. -/
noncomputable def wcost (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | u, v :: l => w u v + wcost w v l

/-- `endpt u l` is the final vertex of the walk starting at `u` and visiting `l` in order. -/
def endpt : V → List V → V
  | u, [] => u
  | _, v :: l => endpt v l

/-- The shortest-path distance from `s` to `t`: the infimum of the weights of all walks
from `s` to `t` (`⊤` if `t` is unreachable). -/
noncomputable def gdist (w : V → V → ℝ≥0∞) (s t : V) : ℝ≥0∞ :=
  sInf {c | ∃ l : List V, endpt s l = t ∧ wcost w s l = c}

/-- `InS S u l` says that every vertex of the walk `u :: l`, except its last one,
belongs to `S`. -/
def InS (S : Finset V) : V → List V → Prop
  | _, [] => True
  | u, v :: l => u ∈ S ∧ InS S v l

/-- The invariants maintained by Dijkstra's algorithm: `S` is the set of settled
vertices and `d` the current tentative distances. -/
structure Inv (w : V → V → ℝ≥0∞) (s : V) (S : Finset V) (d : V → ℝ≥0∞) : Prop where
  zero : d s = 0
  ge : ∀ v, gdist w s v ≤ d v
  visited : ∀ x ∈ S, d x = gdist w s x
  order : ∀ x ∈ S, ∀ y ∉ S, d x ≤ d y
  relax : ∀ x ∈ S, ∀ y, d y ≤ d x + w x y

/-- The vertex of `S` with minimal tentative distance. -/
noncomputable def argmin (S : Finset V) (d : V → ℝ≥0∞) (h : S.Nonempty) : V :=
  (S.exists_min_image d h).choose

omit [Fintype V] [DecidableEq V] in
lemma argmin_mem (S : Finset V) (d : V → ℝ≥0∞) (h : S.Nonempty) : argmin S d h ∈ S :=
  (S.exists_min_image d h).choose_spec.1

omit [Fintype V] [DecidableEq V] in
lemma argmin_le (S : Finset V) (d : V → ℝ≥0∞) (h : S.Nonempty) :
    ∀ y ∈ S, d (argmin S d h) ≤ d y :=
  (S.exists_min_image d h).choose_spec.2

/-- One iteration of Dijkstra's algorithm: settle the closest unsettled vertex `u`
and relax all edges out of `u`. -/
noncomputable def step (w : V → V → ℝ≥0∞) (p : Finset V × (V → ℝ≥0∞)) :
    Finset V × (V → ℝ≥0∞) :=
  if h : (p.1ᶜ).Nonempty then
    (insert (argmin p.1ᶜ p.2 h) p.1,
      fun v => min (p.2 v) (p.2 (argmin p.1ᶜ p.2 h) + w (argmin p.1ᶜ p.2 h) v))
  else p

/-- The initial state: nothing settled, distance `0` at the source and `⊤` elsewhere. -/
noncomputable def init (s : V) : Finset V × (V → ℝ≥0∞) :=
  (∅, fun v => if v = s then 0 else ⊤)

/-- Dijkstra's algorithm: iterate `step` once per vertex, starting from `init s`. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) : V → ℝ≥0∞ :=
  ((step w)^[Fintype.card V] (init s)).2

/-! ### Basic facts about walks -/

omit [Fintype V] [DecidableEq V] in
lemma wcost_append_singleton (w : V → V → ℝ≥0∞) (u : V) (l : List V) (v : V) :
    wcost w u (l ++ [v]) = wcost w u l + w (endpt u l) v := by
  induction l generalizing u with
  | nil => simp [wcost, endpt]
  | cons a l ih => simp [wcost, endpt, ih, add_assoc]

omit [Fintype V] [DecidableEq V] in
lemma endpt_append_singleton (u : V) (l : List V) (v : V) : endpt u (l ++ [v]) = v := by
  induction l generalizing u with
  | nil => simp [endpt]
  | cons a l ih => simp [endpt, ih]

omit [Fintype V] [DecidableEq V] in
lemma gdist_le_of_walk (w : V → V → ℝ≥0∞) (s : V) (l : List V) :
    gdist w s (endpt s l) ≤ wcost w s l :=
  sInf_le ⟨l, rfl, rfl⟩

omit [Fintype V] [DecidableEq V] in
lemma gdist_triangle (w : V → V → ℝ≥0∞) (s u v : V) :
    gdist w s v ≤ gdist w s u + w u v := by
  simp only [gdist]
  rw [ENNReal.sInf_add]
  refine le_iInf₂ ?_
  rintro c ⟨l, hl, rfl⟩
  have h1 : gdist w s (endpt s (l ++ [v])) ≤ wcost w s (l ++ [v]) := gdist_le_of_walk w s _
  rw [endpt_append_singleton, wcost_append_singleton, hl] at h1
  exact h1

omit [Fintype V] [DecidableEq V] in
lemma gdist_self (w : V → V → ℝ≥0∞) (s : V) : gdist w s s = 0 :=
  le_antisymm (by simpa [wcost, endpt] using gdist_le_of_walk w s ([] : List V)) (zero_le _)

omit [Fintype V] [DecidableEq V] in
/-- If all edges out of `S` have been relaxed, then the tentative distance of the endpoint
of a walk whose internal vertices lie in `S` is at most the current distance of its start
plus the weight of that walk. -/
lemma relax_walk {w : V → V → ℝ≥0∞} {S : Finset V} {d : V → ℝ≥0∞}
    (hrel : ∀ x ∈ S, ∀ y, d y ≤ d x + w x y) :
    ∀ (l : List V) (x : V), InS S x l → d (endpt x l) ≤ d x + wcost w x l := by
  intro l
  induction l with
  | nil => intro x _; simp [endpt, wcost]
  | cons a l ih =>
      rintro x ⟨hx, hrest⟩
      have h1 : d (endpt a l) ≤ d a + wcost w a l := ih a hrest
      have h2 : d a ≤ d x + w x a := hrel x hx a
      calc d (endpt x (a :: l)) = d (endpt a l) := rfl
        _ ≤ d a + wcost w a l := h1
        _ ≤ (d x + w x a) + wcost w a l := by gcongr
        _ = d x + wcost w x (a :: l) := by simp [wcost, add_assoc]

omit [Fintype V] [DecidableEq V] in
/-- Every walk leaving `S` has a prefix, of no greater weight, that stays inside `S`
until its endpoint, which lies outside `S`. -/
lemma exists_prefix_out {w : V → V → ℝ≥0∞} {S : Finset V} :
    ∀ (l : List V) (x : V), endpt x l ∉ S →
      ∃ l₁ : List V, InS S x l₁ ∧ endpt x l₁ ∉ S ∧ wcost w x l₁ ≤ wcost w x l := by
  intro l
  induction l with
  | nil => intro x hx; exact ⟨[], trivial, hx, le_rfl⟩
  | cons a l ih =>
      intro x hx
      by_cases hxS : x ∈ S
      · obtain ⟨l₁, h1, h2, h3⟩ := ih a hx
        refine ⟨a :: l₁, ⟨hxS, h1⟩, h2, ?_⟩
        simp only [wcost]
        gcongr
      · exact ⟨[], trivial, hxS, by simp [wcost]⟩

omit [Fintype V] [DecidableEq V] in
/-- Sanity check: the distance is bounded by the weight of a single edge. -/
lemma gdist_le_edge (w : V → V → ℝ≥0∞) (s t : V) : gdist w s t ≤ w s t := by
  simpa [endpt, wcost] using gdist_le_of_walk w s [t]

omit [Fintype V] [DecidableEq V] in
/-- Sanity check: if there are no edges at all, distinct vertices are at distance `⊤`. -/
lemma gdist_eq_top_of_no_edges (s t : V) (h : s ≠ t) :
    gdist (fun _ _ => (⊤ : ℝ≥0∞)) s t = ⊤ := by
  rw [gdist, eq_top_iff]
  refine le_sInf ?_
  rintro c ⟨l, hl, rfl⟩
  cases l with
  | nil => exact absurd hl h
  | cons a l => simp [wcost]

/-! ### The invariant is maintained -/

omit [Fintype V] in
lemma inv_init (w : V → V → ℝ≥0∞) (s : V) : Inv w s (init s).1 (init s).2 := by
  constructor
  · simp [init]
  · intro v
    by_cases hv : v = s
    · subst hv; simp [init, gdist_self]
    · simp [init, hv]
  · intro x hx; simp [init] at hx
  · intro x hx; simp [init] at hx
  · intro x hx; simp [init] at hx

lemma inv_step {w : V → V → ℝ≥0∞} {s : V} {p : Finset V × (V → ℝ≥0∞)}
    (h : Inv w s p.1 p.2) : Inv w s (step w p).1 (step w p).2 := by
  by_cases hne : (p.1ᶜ).Nonempty
  · rw [step, dif_pos hne]
    set S := p.1 with hS
    set d := p.2 with hd
    set u := argmin p.1ᶜ p.2 hne with hu
    have huS : u ∉ S := by
      have := argmin_mem p.1ᶜ p.2 hne
      simpa [hS] using this
    have hmin : ∀ y, y ∉ S → d u ≤ d y := by
      intro y hy
      exact argmin_le p.1ᶜ p.2 hne y (by simpa [hS] using hy)
    have hdu : d u = gdist w s u := by
      refine le_antisymm ?_ (h.ge u)
      refine le_sInf ?_
      rintro c ⟨l, hl, rfl⟩
      obtain ⟨l₁, hin, hout, hle⟩ :=
        exists_prefix_out (w := w) (S := S) l s (by rw [hl]; exact huS)
      calc d u ≤ d (endpt s l₁) := hmin _ hout
        _ ≤ d s + wcost w s l₁ := relax_walk h.relax l₁ s hin
        _ = wcost w s l₁ := by rw [h.zero, zero_add]
        _ ≤ wcost w s l := hle
    -- vertices already settled (and `u`) keep their distance
    have hkeep : ∀ x ∈ insert u S, min (d x) (d u + w u x) = d x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact min_eq_left le_self_add
      · exact min_eq_left ((h.order x hx u huS).trans le_self_add)
    have hdx : ∀ x ∈ insert u S, d x = gdist w s x := by
      intro x hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact hdu
      · exact h.visited x hx
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · show min (d s) (d u + w u s) = 0
      rw [h.zero]
      exact min_eq_left (zero_le _)
    · intro v
      show gdist w s v ≤ min (d v) (d u + w u v)
      refine le_min (h.ge v) ?_
      rw [hdu]
      exact gdist_triangle w s u v
    · intro x hx
      show min (d x) (d u + w u x) = gdist w s x
      rw [hkeep x hx, hdx x hx]
    · intro x hx y hy
      have hyS : y ∉ S := fun hc => hy (Finset.mem_insert_of_mem hc)
      have hxu : d x ≤ d u := by
        rcases Finset.mem_insert.mp hx with rfl | hx'
        · exact le_rfl
        · exact h.order x hx' u huS
      show min (d x) (d u + w u x) ≤ min (d y) (d u + w u y)
      rw [hkeep x hx]
      exact le_min (hxu.trans (hmin y hyS)) (hxu.trans le_self_add)
    · intro x hx y
      show min (d y) (d u + w u y) ≤ min (d x) (d u + w u x) + w x y
      rw [hkeep x hx]
      rcases Finset.mem_insert.mp hx with rfl | hx'
      · exact min_le_right _ _
      · exact (min_le_left _ _).trans (h.relax x hx' y)
  · rw [step, dif_neg hne]
    exact h

lemma inv_iterate (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) :
    Inv w s ((step w)^[k] (init s)).1 ((step w)^[k] (init s)).2 := by
  induction k with
  | zero => simpa using inv_init w s
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact inv_step ih

/-! ### Termination: after `card V` steps every vertex is settled -/

lemma card_iterate (w : V → V → ℝ≥0∞) (s : V) (k : ℕ) :
    ((step w)^[k] (init s)).1 = Finset.univ ∨ k ≤ ((step w)^[k] (init s)).1.card := by
  induction k with
  | zero => exact Or.inr (Nat.zero_le _)
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      set p := (step w)^[k] (init s) with hp
      by_cases hne : (p.1ᶜ).Nonempty
      · have hcard : k ≤ p.1.card := by
          rcases ih with hu | hc
          · exfalso
            rcases hne with ⟨x, hx⟩
            rw [Finset.mem_compl, hu] at hx
            exact hx (Finset.mem_univ x)
          · exact hc
        refine Or.inr ?_
        have hu : argmin p.1ᶜ p.2 hne ∉ p.1 := by
          have := argmin_mem p.1ᶜ p.2 hne
          simpa using this
        have : (step w p).1 = insert (argmin p.1ᶜ p.2 hne) p.1 := by
          rw [step, dif_pos hne]
        rw [this, Finset.card_insert_of_notMem hu]
        omega
      · have : p.1 = Finset.univ := by
          rw [Finset.not_nonempty_iff_eq_empty, Finset.compl_eq_empty_iff] at hne
          exact hne
        refine Or.inl ?_
        rw [step, dif_neg hne]
        exact this

lemma settled_all (w : V → V → ℝ≥0∞) (s : V) :
    ((step w)^[Fintype.card V] (init s)).1 = Finset.univ := by
  rcases card_iterate w s (Fintype.card V) with h | h
  · exact h
  · exact Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) h)

/-- **Dijkstra's algorithm is correct**: on a graph with nonnegative weights
(`ℝ≥0∞`-valued, with `⊤` denoting the absence of an edge), the algorithm returns, for
every vertex `v`, the infimum of the weights of all walks from the source `s` to `v`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s v : V) : dijkstra w s v = gdist w s v := by
  have hinv := inv_iterate w s (Fintype.card V)
  exact hinv.visited v (by rw [settled_all]; exact Finset.mem_univ v)

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

