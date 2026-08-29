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

theorem kneser_one_chromaticNumber (n : ℕ) (hn : 2 ≤ n) :
    (kneserGraph n 1).chromaticNumber = (n : ℕ∞) := by
  refine le_antisymm ?_ (kneser_one_chromaticNumber_ge n)
  have h := kneser_colorable n 1 le_rfl hn
  have he : n - 2 * 1 + 2 = n := by omega
  rw [he] at h
  exact h.chromaticNumber_le

/-! ## The odd Kneser graph `KG_{2k+1,k}` -/

section Odd

variable (k : ℕ)

/-- The cyclic arc `{i, i+1, …, i+k-1}` (indices mod `2k+1`) inside `Fin (2k+1)`. -/
