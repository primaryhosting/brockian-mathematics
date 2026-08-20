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

theorem disjoint_cyclicInterval (k i : ℕ) :
    Disjoint (cyclicInterval k i) (cyclicInterval k (i + k)) := by
  rw [Finset.disjoint_left]
  rintro x hx hy
  simp only [cyclicInterval, Finset.mem_image, Finset.mem_range] at hx hy
  obtain ⟨a, ha, hae⟩ := hx
  obtain ⟨b, hb, hbe⟩ := hy
  have h : (i + a) % (2 * k + 1) = (i + (k + b)) % (2 * k + 1) := by
    have h' := congrArg Fin.val (hae.trans hbe.symm)
    simpa [Nat.add_assoc] using h'
  have h2 : a % (2 * k + 1) = (k + b) % (2 * k + 1) := Nat.ModEq.add_left_cancel' i h
  rw [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at h2
  omega

