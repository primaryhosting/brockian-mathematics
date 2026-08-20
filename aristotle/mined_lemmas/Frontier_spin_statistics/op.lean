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

noncomputable def op (M : Matrix (Fin 2) (Fin 2) ℂ) : Hf →L[ℂ] Hf :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M

