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

theorem fermiModel_nontrivial : ∃ f, fermiModel.field f ≠ 0 := by
  refine ⟨fun _ => (0 : ℝ), ?_⟩
  intro hzero
  have hM : fieldMat (fun _ => (0 : ℝ)) = 0 := op_injective hzero
  have hentry := congrFun (congrFun hM 1) 0
  simp [fieldMat, cCoeff] at hentry

/-- The fermionic model has spin `1/2` and, in accordance with the spin–statistics
connection, Fermi statistics. -/
