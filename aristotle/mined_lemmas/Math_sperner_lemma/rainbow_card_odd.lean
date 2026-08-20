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

theorem rainbow_card_odd (S : Finset (Fin (n + 1))) (hS : S.Nonempty) :
    Odd (t.rainbow S).card := by
  rw [Nat.odd_iff]
  induction hm : S.card using Nat.strong_induction_on generalizing S with
  | _ m ih =>
    match m, hm with
    | 0, hm => exact absurd (Finset.card_eq_zero.1 hm) (Finset.nonempty_iff_ne_empty.1 hS)
    | 1, hm =>
      obtain ⟨i, rfl⟩ := Finset.card_eq_one.1 hm
      rw [t.rainbow_vertex i]
    | (m + 2), hm =>
      obtain ⟨i₀, hi₀⟩ := hS
      rw [t.rainbow_parity_step S i₀ hi₀ (by omega)]
      refine ih (m + 1) (by omega) (S.erase i₀) ?_ ?_
      · rw [← Finset.card_pos, Finset.card_erase_of_mem hi₀, hm]
        omega
      · rw [Finset.card_erase_of_mem hi₀, hm]
        omega

end SpernerTriangulation

/-- **Sperner's lemma**: every Sperner colouring of a triangulated simplex has an odd number of
rainbow (fully coloured) cells. -/
