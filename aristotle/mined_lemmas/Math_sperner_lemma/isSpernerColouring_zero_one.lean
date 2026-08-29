import Mathlib

/-!
# Sperner Lemma
Category: Pure Mathematics
Target: Math.sperner_lemma
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Mathlib (as of this commit) contains *Sperner's theorem* on antichains
(`IsAntichain.sperner`) but **no** Sperner *lemma* about triangulated simplices;
`exact?`/`apply?`/`rw?` therefore have nothing to close this with, and the whole
development below is built from scratch.

## Formalisation

We work with the **barycentric subdivision** of a simplex.  Let `A : Finset α` be the
vertex set of a simplex `Δ(A)` (so `Δ(A)` has dimension `A.card - 1`).  The vertices of
the barycentric subdivision of `Δ(A)` are the barycentres of the faces of `Δ(A)`, i.e.
the nonempty subsets `S ⊆ A`, and the top-dimensional cells are the maximal flags
`S₁ ⊊ S₂ ⊊ ⋯ ⊊ S_k = A` (with `|S_i| = i`).  Such a flag is the same thing as an
ordering `a₁, a₂, …, a_k` of `A` (take `S_i = {a₁, …, a_i}`), so we encode a cell as a
list `l` whose underlying multiset is `A.val` (see `Math.cells`).

A **Sperner colouring** assigns to each vertex `S` of the subdivision a colour
`c S ∈ S` (the barycentre of a face must get a colour of one of the vertices of that
face).  A cell is **rainbow** (or "completely labelled") when its `k` vertices carry
`k` pairwise distinct colours.  `Math.colorSeq c ∅ l` is the list of colours of the
vertices of the cell `l`, listed along the flag.

The main result, `Math.sperner_lemma`, states that the number of rainbow cells is odd.
The section "The flag of faces of a cell" at the end records the dictionary between a
cell `l` and the corresponding maximal flag `Math.flagOf l 0 ⊊ ⋯ ⊊ Math.flagOf l (k-1) = A`
of faces of `Δ(A)`, and checks that the colours of the cell are exactly the colours of
the barycentres of that flag.
-/

open Finset List

namespace Math

variable {α : Type*} [DecidableEq α]

/-! ### The colours along a flag -/

/-- `colorSeq c acc l` is the list of colours `c (acc ∪ {a₁,…,a_i})`, `i = 1 … |l|`,
of the vertices of the flag determined by the ordering `l = [a₁, …, a_n]`
(started from the face `acc`). -/

lemma isSpernerColouring_zero_one : ∀ S : Finset ℕ, S.Nonempty → S ⊆ ({0, 1} : Finset ℕ) →
    (if S = ({1} : Finset ℕ) then 1 else 0) ∈ S := by
  intro S hS hSA
  have h : S ∈ ({0, 1} : Finset ℕ).powerset := Finset.mem_powerset.mpr hSA
  fin_cases h <;> simp_all <;> decide

/-- The exact count in the worked example: one rainbow cell (which is odd, as
`Math.sperner_lemma` predicts). -/
example :
    (rainbowCells (fun S => if S = ({1} : Finset ℕ) then 1 else 0)
      ({0, 1} : Finset ℕ)).card = 1 := by
  rw [rainbowCells, cells_zero_one]
  decide

end Math

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

