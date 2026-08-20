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

lemma contDiff_of_hasDerivAt {F a : ℝ → ℝ} (ha : ContDiff ℝ ∞ a)
    (h : ∀ x, HasDerivAt F (a x) x) : ContDiff ℝ ∞ F := by
  have hd : deriv F = a := funext fun x => (h x).deriv
  rw [contDiff_infty_iff_deriv]
  exact ⟨fun x => (h x).differentiableAt, by rw [hd]; exact ha⟩

/-- A continuous strictly monotone function `ℝ → ℝ` is a topological embedding. -/
