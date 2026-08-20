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

lemma card_erase_doors_of_image_eq_erase (label : V → Fin (n + 1)) (C : Finset V)
    (S : Finset (Fin (n + 1))) (i₀ : Fin (n + 1)) (hi₀ : i₀ ∈ S) (hcard : C.card = S.card)
    (himg : C.image label = S.erase i₀) :
    (C.filter (fun v => (C.erase v).image label = S.erase i₀)).card = 2 := by
  set S' := S.erase i₀ with hS'
  have hS'card : S'.card + 1 = C.card := by
    rw [hS', Finset.card_erase_of_mem hi₀, hcard]
    have : 1 ≤ S.card := Finset.card_pos.2 ⟨i₀, hi₀⟩
    omega
  set fib : Fin (n + 1) → Finset V := fun j => C.filter (fun w => label w = j) with hfib
  have hmaps : Set.MapsTo label (C : Set V) (S' : Set (Fin (n + 1))) := by
    intro v hv
    rw [← himg]
    exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨v, hv, rfl⟩)
  have hsum : C.card = ∑ j ∈ S', (fib j).card := Finset.card_eq_sum_card_fiberwise hmaps
  have hone : ∀ j ∈ S', 1 ≤ (fib j).card := by
    intro j hj
    rw [← himg] at hj
    obtain ⟨w, hwC, hw⟩ := Finset.mem_image.1 hj
    exact Finset.card_pos.2 ⟨w, Finset.mem_filter.2 ⟨hwC, hw⟩⟩
  obtain ⟨j₀, hj₀S, hj₀⟩ : ∃ j ∈ S', 2 ≤ (fib j).card := by
    by_contra hcon
    push_neg at hcon
    have hall : ∑ j ∈ S', (fib j).card = ∑ j ∈ S', 1 := by
      refine Finset.sum_congr rfl fun j hj => ?_
      have := hone j hj
      have := hcon j hj
      omega
    rw [hall, Finset.sum_const, smul_eq_mul, mul_one] at hsum
    omega
  have hg : ∀ j ∈ S', (if j = j₀ then 2 else 1) = (fib j).card := by
    refine (Finset.sum_eq_sum_iff_of_le ?_).1 ?_
    · intro j hj
      by_cases h : j = j₀
      · subst h; rw [if_pos rfl]; exact hj₀
      · rw [if_neg h]; exact hone j hj
    · rw [← hsum, ← hS'card]
      have hsplit : ∑ j ∈ S', (if j = j₀ then 2 else 1)
          = ∑ j ∈ S', (1 + if j = j₀ then 1 else 0) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        by_cases h : j = j₀ <;> simp [h]
      rw [hsplit, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul, mul_one,
        Finset.sum_ite_eq' S' j₀ (fun _ => 1), if_pos hj₀S]
  have hfibj₀ : (fib j₀).card = 2 := by
    have := hg j₀ hj₀S
    rw [if_pos rfl] at this
    exact this.symm
  have hset : C.filter (fun v => (C.erase v).image label = S') = fib j₀ := by
    ext v
    simp only [hfib, Finset.mem_filter]
    constructor
    · rintro ⟨hvC, hv⟩
      refine ⟨hvC, ?_⟩
      by_contra hne
      have hlv : label v ∈ S' := hmaps hvC
      have h1 : (fib (label v)).card = 1 := by
        have := hg (label v) hlv
        rw [if_neg hne] at this
        exact this.symm
      have hmem : label v ∈ (C.erase v).image label := by rw [hv]; exact hlv
      obtain ⟨w, hwe, hw⟩ := Finset.mem_image.1 hmem
      obtain ⟨hwv, hwC⟩ := Finset.mem_erase.1 hwe
      have h2 : ({v, w} : Finset V) ⊆ fib (label v) := by
        intro x hx
        rcases Finset.mem_insert.1 hx with rfl | hx
        · exact Finset.mem_filter.2 ⟨hvC, rfl⟩
        · rw [Finset.mem_singleton] at hx
          subst hx
          exact Finset.mem_filter.2 ⟨hwC, hw⟩
      have h3 := Finset.card_le_card h2
      rw [h1, Finset.card_insert_of_notMem (by simp [Ne.symm hwv]), Finset.card_singleton] at h3
      omega
    · rintro ⟨hvC, hvlab⟩
      refine ⟨hvC, ?_⟩
      obtain ⟨w, hwfib, hwv⟩ :=
        Finset.exists_mem_ne (by rw [hfibj₀]; norm_num : 1 < (fib j₀).card) v
      obtain ⟨hwC, hw⟩ := Finset.mem_filter.1 hwfib
      apply Finset.Subset.antisymm
      · intro j hj
        obtain ⟨x, hxe, rfl⟩ := Finset.mem_image.1 hj
        exact hmaps (Finset.mem_erase.1 hxe).2
      · intro j hj
        rw [← himg] at hj
        obtain ⟨x, hxC, rfl⟩ := Finset.mem_image.1 hj
        by_cases hxv : x = v
        · subst hxv
          exact Finset.mem_image.2 ⟨w, Finset.mem_erase.2 ⟨hwv, hwC⟩, by rw [hw, hvlab]⟩
        · exact Finset.mem_image.2 ⟨x, Finset.mem_erase.2 ⟨hxv, hxC⟩, rfl⟩
  rw [hset, hfibj₀]

/-- Any other cell has no door. -/
