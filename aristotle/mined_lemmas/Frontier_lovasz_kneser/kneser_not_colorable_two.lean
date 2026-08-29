/-
# Lovasz Kneser
Category: Frontier Abel
Target: Frontier.lovasz_kneser
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

/-- The vertices of the Kneser graph `KG_{n,k}`: the `k`-element subsets of `Fin n`. -/
abbrev KneserVertex (n k : ℕ) := {s : Finset (Fin n) // s.card = k}

/-- The Kneser graph `KG_{n,k}`: vertices are the `k`-element subsets of an `n`-element set,
and two of them are adjacent when they are distinct and disjoint.  (For `k ≥ 1` the
distinctness condition is automatic; it is included only so that the relation is
irreflexive also in the degenerate case `k = 0`.) -/

theorem kneser_not_colorable_two (k : ℕ) (hk : 1 ≤ k) :
    ¬ (kneserGraph (2 * k + 1) k).Colorable 2 := by
  rintro ⟨C⟩
  set g : ℕ → Fin 2 := fun t => C (cyclicVertex k (t * k)) with hg
  have hstep : ∀ t, g t ≠ g (t + 1) := by
    intro t
    have ht : (t + 1) * k = t * k + k := by ring
    simpa [hg, ht] using C.valid (cyclicVertex_adj k (t * k) hk)
  have key : ∀ x y z : Fin 2, x ≠ y → y ≠ z → x = z := by decide
  have heven : ∀ t, g (2 * t) = g 0 := by
    intro t
    induction t with
    | zero => rfl
    | succ m ih =>
      have h1 : 2 * (m + 1) = (2 * m + 1) + 1 := by ring
      rw [h1, ← ih]
      exact (key _ _ _ (hstep (2 * m)) (hstep (2 * m + 1))).symm
  have hlast : g (2 * k + 1) = g 0 := by
    have hv : cyclicVertex k ((2 * k + 1) * k) = cyclicVertex k (0 * k) := by
      unfold cyclicVertex
      congr 1
      apply cyclicBlock_congr
      show ((2 * k + 1) * k) % (2 * k + 1) = (0 * k) % (2 * k + 1)
      simp [Nat.mul_mod_left, Nat.mul_comm]
    simp [hg, hv]
  exact hstep (2 * k) (by rw [heven k, ← hlast])

/-- For `n = 2k + 1` (with `k ≥ 1`) the chromatic number of the Kneser graph is `3`. -/
