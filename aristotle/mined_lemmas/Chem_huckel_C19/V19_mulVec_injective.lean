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

lemma V19_mulVec_injective {x y : Fin 19 → ℂ} (h : V19 *ᵥ x = V19 *ᵥ y) : x = y := by
  have := congrArg (fun z => V19⁻¹ *ᵥ z) h
  simpa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul V19 V19_isUnit_det] using this

/-- **Hückel theory for C₁₉.** A complex number `μ` is an eigenvalue of the adjacency
(Hückel) matrix of the cycle graph `C₁₉` if and only if `μ = 2 cos (2πk/19)` for some
`k ∈ {0, 1, …, 18}`. -/
