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

theorem spacelike_example :
    Spacelike (fun _ => 0) (fun i => if i = 1 then 1 else 0) := by
  norm_num [Spacelike, minkowskiForm, show (3 : Fin 4) ≠ 1 by decide,
    show (2 : Fin 4) ≠ 1 by decide]

/-- A nontrivial model of the axioms: spin `0`, Bose statistics, nonzero field. -/
