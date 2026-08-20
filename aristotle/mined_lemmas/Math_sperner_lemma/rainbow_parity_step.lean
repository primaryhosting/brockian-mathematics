import Mathlib
/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Math

open Finset

/-!
## Combinatorial data of a triangulated simplex with a Sperner colouring

We formalise a triangulated `n`-simplex combinatorially.  The vertices of the big simplex are
indexed by `Fin (n+1)`; a face of the big simplex is a nonempty `S : Finset (Fin (n+1))`.
The triangulation assigns to each such face `S` the finite set `cells S` of top-dimensional
simplices of the induced triangulation of the face `S`; a cell is a set of `|S|` vertices taken
from an ambient vertex set `V`.

`label : V → Fin (n+1)` is the colouring, and the Sperner condition is `label_mem`: a vertex
used in the triangulation of the face `S` receives a colour belonging to `S`.

`pseudomanifold` is the standard combinatorial property of a triangulation of a simplex: a
codimension-one face `F` of a cell of `S` lies in exactly two cells of `S`, unless it lies on the
boundary of `S` (that is, it is itself a cell of a proper face `T` of `S`), in which case it lies
in exactly one cell of `S`.
-/

/-- A combinatorial triangulated `n`-simplex, with a Sperner colouring, on the vertex set `V`. -/
structure SpernerTriangulation (n : ℕ) (V : Type*) [DecidableEq V] where
  /-- `cells S` are the top-dimensional simplices of the triangulation of the face `S`. -/
  cells : Finset (Fin (n + 1)) → Finset (Finset V)
  /-- The Sperner colouring of the vertices used by the triangulation. -/
  label : V → Fin (n + 1)
  /-- A cell of the triangulation of the face `S` has exactly `|S|` vertices. -/
  card_cell : ∀ S : Finset (Fin (n + 1)), ∀ C ∈ cells S, C.card = S.card
  /-- Sperner's condition: a vertex lying in the face `S` is coloured by a colour of `S`. -/
  label_mem : ∀ S : Finset (Fin (n + 1)), ∀ C ∈ cells S, ∀ v ∈ C, label v ∈ S
  /-- A vertex of the big simplex is triangulated by exactly one `0`-cell. -/
  vertex_cell : ∀ i : Fin (n + 1), (cells {i}).card = 1
  /-- The pseudomanifold property: an interior codimension-one face lies in exactly two cells,
  a boundary one in exactly one cell. -/
  pseudomanifold : ∀ S : Finset (Fin (n + 1)), 1 < S.card → ∀ F : Finset V,
      F.card + 1 = S.card → (∃ C ∈ cells S, F ⊆ C) →
      ((cells S).filter (fun C => F ⊆ C)).card = if ∃ T ⊂ S, F ∈ cells T then 1 else 2
  /-- A cell of a proper face of `S` is contained in some cell of `S`. -/
  face_subset : ∀ S T : Finset (Fin (n + 1)), T ⊂ S → ∀ F ∈ cells T, ∃ C ∈ cells S, F ⊆ C

namespace SpernerTriangulation

variable {n : ℕ} {V : Type*} [DecidableEq V]

/-- The rainbow ("fully coloured") cells of the triangulation of the face `S`: those cells whose
vertices realise all the colours of `S`. -/

lemma rainbow_parity_step (S : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) (hi₀ : i₀ ∈ S)
    (hcard : 1 < S.card) :
    (t.rainbow S).card % 2 = (t.rainbow (S.erase i₀)).card % 2 := by
  obtain ⟨k, hk⟩ : ∃ k, S.card = k + 1 := ⟨S.card - 1, by omega⟩
  set S' := S.erase i₀ with hS'def
  have hS'card : S'.card = k := by
    rw [hS'def, Finset.card_erase_of_mem hi₀, hk]
    omega
  have hS'ss : S' ⊂ S := Finset.erase_ssubset hi₀
  -- `D` is the set of all doors: codimension-one faces of cells of `S` coloured by `S'`.
  set D : Finset (Finset V) :=
    (t.cells S).biUnion (fun C => (C.powersetCard k).filter (fun F => F.image t.label = S'))
    with hDdef
  have hmemD : ∀ F : Finset V,
      F ∈ D ↔ ((∃ C ∈ t.cells S, F ⊆ C) ∧ F.card = k ∧ F.image t.label = S') := by
    intro F
    simp only [hDdef, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_powersetCard]
    constructor
    · rintro ⟨C, hC, ⟨hFC, hFcard⟩, himg⟩; exact ⟨⟨C, hC, hFC⟩, hFcard, himg⟩
    · rintro ⟨⟨C, hC, hFC⟩, hFcard, himg⟩; exact ⟨C, hC, ⟨hFC, hFcard⟩, himg⟩
  -- Double counting of the incidences (cell, door).
  have key : ∑ C ∈ t.cells S, (D.filter (fun F => F ⊆ C)).card
      = ∑ F ∈ D, ((t.cells S).filter (fun C => F ⊆ C)).card := by
    simp_rw [Finset.card_filter]
    exact Finset.sum_comm
  -- Left-hand side: count the doors of each cell.
  have hL : ∀ C ∈ t.cells S, (D.filter (fun F => F ⊆ C)).card
      = (if C.image t.label = S then 1 else 0)
        + 2 * (if C.image t.label = S' then 1 else 0) := by
    intro C hC
    have hDC : D.filter (fun F => F ⊆ C)
        = (C.powersetCard k).filter (fun F => F.image t.label = S') := by
      ext F
      simp only [Finset.mem_filter, hmemD, Finset.mem_powersetCard]
      constructor
      · rintro ⟨⟨_, hFcard, himg⟩, hFC⟩; exact ⟨⟨hFC, hFcard⟩, himg⟩
      · rintro ⟨⟨hFC, hFcard⟩, himg⟩; exact ⟨⟨⟨C, hC, hFC⟩, hFcard, himg⟩, hFC⟩
    rw [hDC, hS'def]
    exact card_doors_cell t.label C S i₀ hi₀ k hk (t.card_cell S C hC) (t.image_label_subset hC)
  -- Right-hand side: a door lies in one or two cells according to whether it is on the boundary.
  have hbd : ∀ F ∈ D, ((∃ T ⊂ S, F ∈ t.cells T) ↔ F ∈ t.rainbow S') := by
    intro F hF
    rw [hmemD] at hF
    obtain ⟨_, hFcard, himg⟩ := hF
    constructor
    · rintro ⟨T, hTS, hFT⟩
      have hTcard : F.card = T.card := t.card_cell T F hFT
      have hsub : S' ⊆ T := by
        rw [← himg]
        intro j hj
        obtain ⟨v, hv, rfl⟩ := Finset.mem_image.1 hj
        exact t.label_mem T F hFT v hv
      have hTeq : S' = T := Finset.eq_of_subset_of_card_le hsub (by omega)
      exact t.mem_rainbow.2 ⟨hTeq ▸ hFT, himg⟩
    · intro hF'
      exact ⟨S', hS'ss, (t.mem_rainbow.1 hF').1⟩
  have hR : ∀ F ∈ D, ((t.cells S).filter (fun C => F ⊆ C)).card
      = (if F ∈ t.rainbow S' then 1 else 0) + 2 * (if F ∈ t.rainbow S' then 0 else 1) := by
    intro F hF
    have hF' := hF
    rw [hmemD] at hF'
    obtain ⟨hex, hFcard, _⟩ := hF'
    rw [t.pseudomanifold S hcard F (by omega) hex]
    by_cases h : F ∈ t.rainbow S'
    · rw [if_pos ((hbd F hF).2 h)]; simp [h]
    · rw [if_neg (fun hc => h ((hbd F hF).1 hc))]; simp [h]
  -- Assemble the two counts.
  rw [Finset.sum_congr rfl hL, Finset.sum_congr rfl hR] at key
  have hLsum : ∑ C ∈ t.cells S, ((if C.image t.label = S then 1 else 0)
        + 2 * (if C.image t.label = S' then 1 else 0))
      = (t.rainbow S).card + 2 * ((t.cells S).filter (fun C => C.image t.label = S')).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.card_filter, ← Finset.card_filter]
    rfl
  have hDsub : t.rainbow S' ⊆ D := by
    intro F hF
    rw [t.mem_rainbow] at hF
    rw [hmemD]
    refine ⟨t.face_subset S S' hS'ss F hF.1, ?_, hF.2⟩
    rw [t.card_cell S' F hF.1, hS'card]
  have e1 : ∑ F ∈ D, (if F ∈ t.rainbow S' then 1 else 0) = (t.rainbow S').card := by
    rw [← Finset.card_filter, Finset.filter_mem_eq_inter, Finset.inter_eq_right.2 hDsub]
  have e2 : ∑ F ∈ D, (if F ∈ t.rainbow S' then 0 else 1)
      = (D.filter (fun F => F ∉ t.rainbow S')).card := by
    rw [Finset.card_filter]
    refine Finset.sum_congr rfl fun F _ => ?_
    by_cases h : F ∈ t.rainbow S' <;> simp [h]
  have hRsum : ∑ F ∈ D, ((if F ∈ t.rainbow S' then 1 else 0)
        + 2 * (if F ∈ t.rainbow S' then 0 else 1))
      = (t.rainbow S').card + 2 * (D.filter (fun F => F ∉ t.rainbow S')).card := by
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, e1, e2]
  rw [hLsum, hRsum] at key
  omega

/-- The base case: a vertex of the big simplex carries exactly one rainbow cell. -/
