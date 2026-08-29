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

/-!
We formalize Dijkstra's algorithm on a finite directed graph whose edge weights are
elements of `ℝ≥0∞` (`ENNReal`).  Using `ℝ≥0∞` encodes exactly the two features of the
setting Dijkstra's algorithm requires: weights are **nonnegative**, and a weight of `⊤`
models a missing edge (so unreachable vertices get distance `⊤`).

`CS.gdist w s v` is the true shortest-path distance: the infimum of the costs of all
walks from `s` to `v`.  `CS.dijkstra w s` is the output of the algorithm (the classical
loop: repeatedly select an unvisited vertex of minimal tentative distance, mark it
visited, and relax all of its outgoing edges).  The main theorem `CS.dijkstra_correct`
states that these agree.
-/

namespace CS

open Finset
open scoped ENNReal

section Defs

variable {V : Type*}

/-- `ReachesVia w S s v c` means: there is a walk from `s` to `v` of total weight `c`
all of whose vertices, except possibly the final one, lie in `S`. -/
inductive ReachesVia (w : V → V → ℝ≥0∞) (S : Finset V) (s : V) : V → ℝ≥0∞ → Prop
  | refl : ReachesVia w S s s 0
  | step {u v c} (hu : u ∈ S) (h : ReachesVia w S s u c) :
      ReachesVia w S s v (c + w u v)

/-- The infimum of the weights of walks from `s` to `v` with all intermediate vertices
in `S`. -/
noncomputable def distVia (w : V → V → ℝ≥0∞) (S : Finset V) (s v : V) : ℝ≥0∞ :=
  sInf {c | ReachesVia w S s v c}

/-- The shortest-path distance from `s` to `v`: the infimum of the weights of all walks
from `s` to `v` (`⊤` if `v` is unreachable). -/
noncomputable def gdist [Fintype V] (w : V → V → ℝ≥0∞) (s v : V) : ℝ≥0∞ :=
  distVia w Finset.univ s v

/-! ### Basic facts about `distVia` -/

theorem distVia_le {w : V → V → ℝ≥0∞} {S : Finset V} {s v : V} {c : ℝ≥0∞}
    (h : ReachesVia w S s v c) : distVia w S s v ≤ c :=
  sInf_le h

theorem le_distVia {w : V → V → ℝ≥0∞} {S : Finset V} {s v : V} {a : ℝ≥0∞}
    (h : ∀ c, ReachesVia w S s v c → a ≤ c) : a ≤ distVia w S s v :=
  le_sInf h

theorem ReachesVia.mono {w : V → V → ℝ≥0∞} {S T : Finset V} {s v : V} {c : ℝ≥0∞}
    (hST : S ⊆ T) (h : ReachesVia w S s v c) : ReachesVia w T s v c := by
  induction h with
  | refl => exact ReachesVia.refl
  | step hu _ ih => exact ih.step (hST hu)

theorem distVia_mono {w : V → V → ℝ≥0∞} {S T : Finset V} {s v : V} (hST : S ⊆ T) :
    distVia w T s v ≤ distVia w S s v :=
  le_distVia fun _ hc => distVia_le (hc.mono hST)

theorem distVia_self {w : V → V → ℝ≥0∞} {S : Finset V} {s : V} : distVia w S s s = 0 :=
  le_antisymm (distVia_le ReachesVia.refl) (zero_le _)

/-- The triangle inequality along a single edge leaving a vertex of `S`. -/
theorem distVia_step {w : V → V → ℝ≥0∞} {S : Finset V} {s u v : V} (hu : u ∈ S) :
    distVia w S s v ≤ distVia w S s u + w u v := by
  have h : distVia w S s u + w u v = ⨅ c ∈ {c | ReachesVia w S s u c}, c + w u v := by
    rw [distVia, ENNReal.sInf_add]
  rw [h]
  exact le_iInf₂ fun c hc => distVia_le (ReachesVia.step hu hc)

/-- With no intermediate vertices allowed, only the source is reachable (at cost `0`). -/
theorem distVia_empty [DecidableEq V] (w : V → V → ℝ≥0∞) (s v : V) :
    distVia w (∅ : Finset V) s v = if v = s then (0 : ℝ≥0∞) else (⊤ : ℝ≥0∞) := by
  by_cases h : v = s
  · subst h; simp [distVia_self]
  · rw [if_neg h, eq_top_iff]
    refine le_distVia fun c hc => ?_
    cases hc with
    | refl => exact absurd rfl h
    | step hu _ => simp at hu

/-! ### Walks as lists -/

/-- The total weight of the walk starting at `u` and visiting the vertices of `l` in
order. -/
noncomputable def walkCost (w : V → V → ℝ≥0∞) : V → List V → ℝ≥0∞
  | _, [] => 0
  | u, v :: l => w u v + walkCost w v l

theorem walkCost_append_singleton (w : V → V → ℝ≥0∞) (u : V) (l : List V) (x : V) :
    walkCost w u (l ++ [x]) = walkCost w u l + w (l.getLastD u) x := by
  induction l generalizing u with
  | nil => simp [walkCost]
  | cons a t ih =>
      show w u a + walkCost w a (t ++ [x])
          = (w u a + walkCost w a t) + w ((a :: t).getLastD u) x
      rw [ih, List.getLastD_cons, add_assoc]

end Defs

section Fin

variable {V : Type*} [Fintype V] [DecidableEq V]

omit [DecidableEq V] in
theorem gdist_le_distVia {w : V → V → ℝ≥0∞} {S : Finset V} {s v : V} :
    gdist w s v ≤ distVia w S s v :=
  distVia_mono (Finset.subset_univ S)

omit [DecidableEq V] in
theorem gdist_step {w : V → V → ℝ≥0∞} {s u v : V} :
    gdist w s v ≤ gdist w s u + w u v :=
  distVia_step (Finset.mem_univ u)

/-! ### The escape lemma -/

/-- Any walk from `s` either stays inside `S` (except for its last vertex), or else it
reaches, at some point, a vertex outside `S`, at a cost bounded by its total cost. -/
theorem escape (w : V → V → ℝ≥0∞) (S : Finset V) {s v : V} {c : ℝ≥0∞}
    (h : ReachesVia w Finset.univ s v c) :
    distVia w S s v ≤ c ∨ ∃ x ∉ S, distVia w S s x ≤ c := by
  induction h with
  | refl =>
      by_cases hs : s ∈ S
      · exact Or.inl (by simp [distVia_self])
      · exact Or.inr ⟨s, hs, by simp [distVia_self]⟩
  | @step u v c _ _ ih =>
      rcases ih with hl | ⟨x, hx, hxc⟩
      · by_cases hu : u ∈ S
        · exact Or.inl ((distVia_step hu).trans (by gcongr))
        · exact Or.inr ⟨u, hu, hl.trans le_self_add⟩
      · exact Or.inr ⟨x, hx, hxc.trans le_self_add⟩

/-- Greedy step: an unvisited vertex `u` minimizing the tentative distance already has
its true shortest-path distance as tentative distance. -/
theorem greedy {w : V → V → ℝ≥0∞} {S : Finset V} {s u : V}
    (hmin : ∀ x ∉ S, distVia w S s u ≤ distVia w S s x) :
    distVia w S s u = gdist w s u := by
  refine le_antisymm ?_ gdist_le_distVia
  refine le_distVia fun c hc => ?_
  rcases escape w S hc with h | ⟨x, hx, hxc⟩
  · exact h
  · exact (hmin x hx).trans hxc

/-- Relaxation: once the distances of all vertices of `S` are final, the
`insert u S`-restricted distances are obtained from the `S`-restricted ones by relaxing
the edges out of `u`. -/
theorem relax {w : V → V → ℝ≥0∞} {S : Finset V} {s u : V}
    (hS : ∀ x ∈ S, distVia w S s x = gdist w s x) (v : V) :
    distVia w (insert u S) s v = min (distVia w S s v) (distVia w S s u + w u v) := by
  refine le_antisymm ?_ ?_
  · refine le_min (distVia_mono (Finset.subset_insert u S)) ?_
    calc distVia w (insert u S) s v
        ≤ distVia w (insert u S) s u + w u v := distVia_step (Finset.mem_insert_self u S)
      _ ≤ distVia w S s u + w u v := by
          gcongr; exact distVia_mono (Finset.subset_insert u S)
  · refine le_distVia fun c hc => ?_
    have key : ∀ {v : V} {c : ℝ≥0∞}, ReachesVia w (insert u S) s v c →
        distVia w S s v ≤ c ∨ distVia w S s u + w u v ≤ c := by
      intro v c hc
      induction hc with
      | refl => exact Or.inl (by simp [distVia_self])
      | @step x v c hx hder ih =>
          rcases Finset.mem_insert.1 hx with rfl | hxS
          · have hxu : distVia w S s x ≤ c := by
              rcases ih with h | h
              · exact h
              · exact le_self_add.trans h
            exact Or.inr (by gcongr)
          · have hx' : distVia w S s x ≤ c := by
              rw [hS x hxS]
              exact distVia_le (hder.mono (Finset.subset_univ _))
            exact Or.inl ((distVia_step hxS).trans (by gcongr))
    rcases key hc with h | h
    · exact le_trans (min_le_left _ _) h
    · exact le_trans (min_le_right _ _) h

/-! ### `gdist` is the infimum of the costs of walks -/

omit [DecidableEq V] in
theorem reachesVia_univ_walk (w : V → V → ℝ≥0∞) (s : V) (l : List V) :
    ReachesVia w Finset.univ s (l.getLastD s) (walkCost w s l) := by
  induction l using List.reverseRecOn with
  | nil => simpa using ReachesVia.refl
  | append_singleton l x ih =>
      have h : (l ++ [x]).getLastD s = x := by simp
      rw [h, walkCost_append_singleton]
      exact ih.step (Finset.mem_univ _)

omit [DecidableEq V] in
theorem reachesVia_univ_iff_walk (w : V → V → ℝ≥0∞) (s v : V) (c : ℝ≥0∞) :
    ReachesVia w Finset.univ s v c ↔
      ∃ l : List V, l.getLastD s = v ∧ walkCost w s l = c := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], by simp [walkCost]⟩
    | @step u v c _ _ ih =>
        obtain ⟨l, hl, hc⟩ := ih
        exact ⟨l ++ [v], by simp, by rw [walkCost_append_singleton, hl, hc]⟩
  · rintro ⟨l, rfl, rfl⟩
    exact reachesVia_univ_walk w s l

omit [DecidableEq V] in
/-- The shortest-path distance is the infimum of the costs of all walks from `s` to
`v`, where a walk is presented as the list of vertices visited after `s`. -/
theorem gdist_eq_sInf_walkCost (w : V → V → ℝ≥0∞) (s v : V) :
    gdist w s v = sInf {c | ∃ l : List V, l.getLastD s = v ∧ walkCost w s l = c} := by
  rw [gdist, distVia]
  congr 1
  ext c
  exact reachesVia_univ_iff_walk w s v c

/-! ### The algorithm -/

/-- One iteration of Dijkstra's loop: pick an unvisited vertex `u` of minimal tentative
distance, mark it visited, and relax all edges out of `u`. -/
noncomputable def dijkstraStep (w : V → V → ℝ≥0∞)
    (p : Finset V × (V → ℝ≥0∞)) : Finset V × (V → ℝ≥0∞) :=
  if h : (p.1ᶜ).Nonempty then
    let u := Classical.choose (Finset.exists_min_image p.1ᶜ p.2 h)
    (insert u p.1, fun v => min (p.2 v) (p.2 u + w u v))
  else p

/-- The state of Dijkstra's algorithm after `n` iterations. -/
noncomputable def dijkstraAux (w : V → V → ℝ≥0∞) (s : V) : ℕ → Finset V × (V → ℝ≥0∞)
  | 0 => (∅, fun v => if v = s then 0 else ⊤)
  | n + 1 => dijkstraStep w (dijkstraAux w s n)

/-- Dijkstra's algorithm: run the loop once per vertex and return the tentative
distances. -/
noncomputable def dijkstra (w : V → V → ℝ≥0∞) (s : V) : V → ℝ≥0∞ :=
  (dijkstraAux w s (Fintype.card V)).2

/-- Specification of one loop iteration when there is still an unvisited vertex. -/
theorem dijkstraStep_spec (w : V → V → ℝ≥0∞) (p : Finset V × (V → ℝ≥0∞))
    (h : (p.1ᶜ).Nonempty) :
    ∃ u, u ∉ p.1 ∧ (∀ x ∉ p.1, p.2 u ≤ p.2 x) ∧
      dijkstraStep w p = (insert u p.1, fun v => min (p.2 v) (p.2 u + w u v)) := by
  obtain ⟨hmem, hmin⟩ := Classical.choose_spec (Finset.exists_min_image p.1ᶜ p.2 h)
  refine ⟨Classical.choose (Finset.exists_min_image p.1ᶜ p.2 h), by simpa using hmem,
    fun x hx => hmin x (by simpa using hx), ?_⟩
  simp only [dijkstraStep, dif_pos h]

/-- The loop invariant of Dijkstra's algorithm: tentative distances are exactly the
distances restricted to the visited set, and the visited vertices already carry their
true distances. -/
def Inv (w : V → V → ℝ≥0∞) (s : V) (p : Finset V × (V → ℝ≥0∞)) : Prop :=
  (∀ v, p.2 v = distVia w p.1 s v) ∧ (∀ x ∈ p.1, distVia w p.1 s x = gdist w s x)

theorem dijkstraAux_inv (w : V → V → ℝ≥0∞) (s : V) (n : ℕ) :
    Inv w s (dijkstraAux w s n) := by
  induction n with
  | zero =>
      refine ⟨fun v => ?_, fun x hx => absurd hx (by simp [dijkstraAux])⟩
      simp only [dijkstraAux, distVia_empty]
  | succ n ih =>
      obtain ⟨hd, hS⟩ := ih
      set p := dijkstraAux w s n with hp
      by_cases h : (p.1ᶜ).Nonempty
      · obtain ⟨u, hu, hmin, hstep⟩ := dijkstraStep_spec w p h
        have hmin' : ∀ x ∉ p.1, distVia w p.1 s u ≤ distVia w p.1 s x := by
          intro x hx
          have := hmin x hx
          rwa [hd u, hd x] at this
        have hgu : distVia w p.1 s u = gdist w s u := greedy hmin'
        have hrel := relax (u := u) hS
        have hnew : dijkstraAux w s (n + 1) =
            (insert u p.1, fun v => min (p.2 v) (p.2 u + w u v)) := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl, hstep]
        rw [hnew]
        constructor
        · intro v
          simp only [hrel v, hd v, hd u]
        · intro x hx
          rcases Finset.mem_insert.1 hx with rfl | hxS
          · rw [hrel x, min_eq_left le_self_add, hgu]
          · rw [hrel x, hS x hxS, min_eq_left]
            rw [hgu]
            exact gdist_step
      · have hnew : dijkstraAux w s (n + 1) = p := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl]
          simp only [dijkstraStep, dif_neg h]
        rw [hnew]
        exact ⟨hd, hS⟩

theorem dijkstraAux_card (w : V → V → ℝ≥0∞) (s : V) (n : ℕ) :
    (dijkstraAux w s n).1.card = min n (Fintype.card V) := by
  induction n with
  | zero => simp [dijkstraAux]
  | succ n ih =>
      set p := dijkstraAux w s n with hp
      by_cases h : (p.1ᶜ).Nonempty
      · obtain ⟨u, hu, -, hstep⟩ := dijkstraStep_spec w p h
        have hnew : (dijkstraAux w s (n + 1)).1 = insert u p.1 := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl, hstep]
        have hlt : p.1.card < Fintype.card V := by
          have : p.1 ≠ Finset.univ := by
            obtain ⟨x, hx⟩ := h
            intro hcon
            simp [hcon] at hx
          exact Finset.card_lt_card (lt_of_le_of_ne (Finset.subset_univ _) this)
        rw [ih] at hlt
        rw [hnew, Finset.card_insert_of_notMem hu, ih]
        omega
      · have hnew : (dijkstraAux w s (n + 1)).1 = p.1 := by
          rw [show dijkstraAux w s (n + 1) = dijkstraStep w p from rfl]
          simp only [dijkstraStep, dif_neg h]
        have huniv : p.1 = Finset.univ := by
          rw [Finset.not_nonempty_iff_eq_empty] at h
          simpa using congrArg (fun t : Finset V => tᶜ) h
        rw [huniv, Finset.card_univ] at ih
        rw [hnew, huniv, Finset.card_univ]
        omega

/-- **Correctness of Dijkstra's algorithm.**  On a finite directed graph with
nonnegative edge weights (weights valued in `ℝ≥0∞`, where `⊤` means "no edge"),
Dijkstra's algorithm computes, for every vertex `v`, the shortest-path distance from
the source `s` to `v`. -/
theorem dijkstra_correct (w : V → V → ℝ≥0∞) (s v : V) :
    dijkstra w s v = gdist w s v := by
  have hcard := dijkstraAux_card w s (Fintype.card V)
  have huniv : (dijkstraAux w s (Fintype.card V)).1 = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  obtain ⟨hd, -⟩ := dijkstraAux_inv w s (Fintype.card V)
  rw [dijkstra, hd v, huniv, gdist]

end Fin

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

