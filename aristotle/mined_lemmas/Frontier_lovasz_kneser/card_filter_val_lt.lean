import Mathlib
/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
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

namespace Frontier

/-! ## The Kneser graph -/

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are disjoint. -/

lemma card_filter_val_lt (n L : ℕ) (h : L ≤ n) :
    (Finset.univ.filter (fun y : Fin n => (y : ℕ) < L)).card = L := by
  have himg : (Finset.univ.filter (fun y : Fin n => (y : ℕ) < L)).image Fin.val
      = Finset.range L := by
    ext x
    simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_range]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, lt_of_lt_of_le hx h⟩, hx, rfl⟩
  rw [← Finset.card_image_of_injective _ Fin.val_injective, himg, Finset.card_range]

/-! ## The upper bound `χ(KG_{n,k}) ≤ n - 2k + 2` -/

/-- The standard colouring bound: the Kneser graph `KG_{n,k}` is `(n - 2k + 2)`-colourable.

A `k`-set `S` is coloured by `min (min S) (n - 2k + 1)`.  Two disjoint sets cannot share a
colour `< n - 2k + 1` since then they would share their smallest element, and they cannot both
get the colour `n - 2k + 1` since then they would both be contained in the last `2k - 1`
elements. -/
