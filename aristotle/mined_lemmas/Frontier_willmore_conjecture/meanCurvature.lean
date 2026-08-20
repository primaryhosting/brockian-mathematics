/-
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Willmore Conjecture
Category: Frontier — Fields Medal Work
Target: Frontier.willmore_conjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## Basic vector algebra in `ℝ³` -/

/-- Euclidean three-space, as a triple of reals. -/
abbrev R3 := ℝ × ℝ × ℝ

/-- The standard inner product on `ℝ³`. -/

noncomputable def meanCurvature (X : ℝ → ℝ → R3) (u v : ℝ) : ℝ :=
  let Xu := pd1 X u v
  let Xv := pd2 X u v
  let Xuu := pd1 (pd1 X) u v
  let Xuv := pd2 (pd1 X) u v
  let Xvv := pd2 (pd2 X) u v
  let E := dot3 Xu Xu
  let F := dot3 Xu Xv
  let G := dot3 Xv Xv
  let N := cross3 Xu Xv
  let W := nrm3 N
  ((dot3 Xuu N / W) * G - 2 * (dot3 Xuv N / W) * F + (dot3 Xvv N / W) * E) / (2 * (E * G - F * F))

/-- The Willmore energy `∫ H² dA` of a surface parametrized by the square `[0, 2π]²`. -/
