import Mathlib

/-!
# Navier Stokes Regularity
Category: Frontier — Moonshot
Target: Frontier.navier_stokes_regularity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ContDiff BigOperators

namespace Frontier

/-- The physical space `ℝ³`, as the space of `3`-tuples of reals. -/
abbrev Vec : Type := Fin 3 → ℝ

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The `i`-th partial derivative of a (vector- or scalar-valued) field on `ℝ³`. -/

noncomputable def energy (u : ℝ → Vec → Vec) (t : ℝ) : ℝ := ∫ x, ∑ i, (u t x i) ^ 2

/-- Admissible initial data: a smooth, compactly supported, divergence-free vector field.
(The Clay problem allows Schwartz data; compactly supported data is the natural smooth
subclass used here.) -/
