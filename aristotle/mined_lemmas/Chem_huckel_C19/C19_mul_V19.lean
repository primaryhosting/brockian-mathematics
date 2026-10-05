import Mathlib

/-!
# Huckel C 19
Category: Chemistry
Target: Chem.huckel_C19
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to precede any module documentation, so the requested
header comment appears immediately after the single `import Mathlib` line.)
-/

open scoped BigOperators
open scoped Real

namespace Chem

open Complex Matrix SimpleGraph

/-- The adjacency matrix of the cycle graph `C₁₉`, i.e. the Hückel matrix of the
carbon skeleton of a 19-membered annulene (with `α = 0`, `β = 1`). -/

lemma C19_mul_V19 : C19 * V19 = V19 * D19 := by
  ext i k
  have h : ∑ j, C19 i j * evec (k : ℕ) j
      = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) * evec (k : ℕ) i := by
    have h0 := congrFun (C19_mulVec_evec (k : ℕ)) i
    simpa [Matrix.mulVec, dotProduct] using h0
  rw [Matrix.mul_apply, Matrix.mul_apply]
  calc ∑ j, C19 i j * V19 j k = ∑ j, C19 i j * evec (k : ℕ) j := by
        simp only [V19_apply]
    _ = ((2 * Real.cos (2 * Real.pi * k / 19) : ℝ) : ℂ) * evec (k : ℕ) i := h
    _ = ∑ j, V19 i j * D19 j k := by
        rw [← Matrix.mul_apply, D19, Matrix.mul_diagonal, V19_apply]
        ring

