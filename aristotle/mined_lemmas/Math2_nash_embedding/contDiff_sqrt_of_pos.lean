import Mathlib

/-!
# Nash Embedding
Category: Frontier Math
Target: Math2.nash_embedding
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` lines to precede every other command, including the module
-- docstring above; the requested header is otherwise reproduced verbatim.)

open scoped ContDiff
open Topology

namespace Math2

/-! ## The canonical linear isometry `ℝ →L[ℝ] ℝ¹`

We realise the target Euclidean space as `EuclideanSpace ℝ (Fin N)`.  For the construction
below only `N = 1` is needed, so we set up the canonical map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`
and record its basic properties. -/

/-- The canonical continuous linear map `ℝ →L[ℝ] EuclideanSpace ℝ (Fin 1)`,
sending `a` to the constant family `fun _ => a`. -/

lemma contDiff_sqrt_of_pos {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g) (hpos : ∀ x, 0 < g x) :
    ContDiff ℝ ∞ fun x => Real.sqrt (g x) := by
  rw [contDiff_iff_contDiffAt]
  exact fun x => hg.contDiffAt.sqrt (ne_of_gt (hpos x))

/-- A function whose derivative everywhere equals a smooth function is smooth. -/
