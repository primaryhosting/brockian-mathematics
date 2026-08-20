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

def SpacelikeSeparated (A B : Set (Fin 4 → ℝ)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, Spacelike x y

/-! ## Statistics -/

/-- The two possible statistics of a relativistic field. -/
inductive Statistics
  | bose
  | fermi
  deriving DecidableEq, Repr

/-- The commutation sign attached to a statistics: `+1` for bosons (commutators),
`-1` for fermions (anticommutators). -/
