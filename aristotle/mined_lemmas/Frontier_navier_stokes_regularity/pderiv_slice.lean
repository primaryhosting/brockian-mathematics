import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command of a
module, so the mandated header comment is placed immediately after the import.
-/

open scoped BigOperators ContDiff

namespace Frontier

namespace NavierStokes

/-- Points/vectors of `ℝ³`. -/
abbrev Vec := Fin 3 → ℝ

/-- The `i`-th partial derivative of a scalar field on `ℝ³`. -/

lemma pderiv_slice (F : Vec → ℝ) (i : Fin 3) (x : Vec) (h : DifferentiableAt ℝ F x) :
    HasDerivAt (fun s => F (Function.update x i s)) (pderiv F i x) (x i) := by
  have hu : HasDerivAt (fun s : ℝ => Function.update x i s) (Pi.single i 1) (x i) :=
    hasDerivAt_update x i (x i)
  have h2 : HasFDerivAt F (fderiv ℝ F x) (Function.update x i (x i)) := by
    simpa using h.hasFDerivAt
  simpa [pderiv, Function.comp] using h2.comp_hasDerivAt (x i) hu

/-- A field that does not depend on its `i`-th coordinate has vanishing `i`-th partial
derivative. -/
