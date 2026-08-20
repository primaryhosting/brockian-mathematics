/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/

theorem boseModel_nontrivial :
    ∃ f, boseModel.field f ≠ 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro h
  have := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  simp [boseModel] at this

/-- In the model, the statistics is indeed the one predicted by the spin. -/
