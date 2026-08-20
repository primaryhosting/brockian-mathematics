/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring immediately after the import.)

import Mathlib

/-!
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Frontier

open Finset SimpleGraph

/-- The vertex type of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) : Type := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
two of them being adjacent when they are disjoint.  (For `k ≥ 1` disjointness already forces
the two vertices to be distinct; the explicit `s ≠ t` only serves to make the relation
irreflexive in the degenerate case `k = 0`.) -/

theorem card_cyclicInterval (k i : ℕ) : (cyclicInterval k i).card = k := by
  rw [cyclicInterval, Finset.card_image_of_injOn, Finset.card_range]
  intro x hx y hy hxy
  simp only [Finset.mem_coe, Finset.mem_range] at hx hy
  have h : (i + x) % (2 * k + 1) = (i + y) % (2 * k + 1) := congrArg Fin.val hxy
  have h2 : x % (2 * k + 1) = y % (2 * k + 1) := Nat.ModEq.add_left_cancel' i h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2

/-- Two cyclic intervals of length `k` starting `k` apart are disjoint inside `Fin (2k+1)`. -/
