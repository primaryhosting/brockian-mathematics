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

lemma space3_injective : Function.Injective space3 := by
  intro a b hab
  have h0 : space3 a 0 = space3 b 0 := by rw [hab]
  have h1 : space3 a 1 = space3 b 1 := by rw [hab]
  have h2 : space3 a 2 = space3 b 2 := by rw [hab]
  simp only [space3_apply_zero, space3_apply_one, space3_apply_two] at h0 h1 h2
  exact Prod.ext h0 (Prod.ext h1 h2)

/-- **Nash embedding for rotationally symmetric surfaces.**
Let `h : ℝ → ℝ` be smooth, positive, with `|h'| < 1`.  Then the (generally curved) Riemannian
metric `du² + h(u)² dv²` on `ℝ²` is induced by a smooth map into a Euclidean space `ℝ^N`
which is injective on the strip `ℝ × (0, 2π)` (on all of `ℝ²` the map is only an immersion,
because the metric is `2π`-periodic in `v`). -/
