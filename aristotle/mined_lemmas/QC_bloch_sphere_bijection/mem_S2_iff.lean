import Mathlib

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

/-
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is
-- repeated as the module docstring below.)
import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QC

open Complex

/-- A (normalised) pure qubit state vector: a unit vector `(a, b)` in `ℂ²`,
representing `a|0⟩ + b|1⟩`. -/

lemma mem_S2_iff (x y z : ℝ) :
    (!₂[x, y, z] : EuclideanSpace ℝ (Fin 3)) ∈ S2 ↔ x ^ 2 + y ^ 2 + z ^ 2 = 1 := by
  rw [S2, mem_sphere_zero_iff_norm, EuclideanSpace.norm_eq, Real.sqrt_eq_one]
  simp [Fin.sum_univ_three, sq_abs]

/-- The Bloch vector of a state vector `(a, b)`. -/
