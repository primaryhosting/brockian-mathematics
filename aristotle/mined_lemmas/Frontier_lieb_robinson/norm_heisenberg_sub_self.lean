import Mathlib

/-!
# Lieb Robinson
Category: Frontier Physics
Target: Frontier.lieb_robinson
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

open NormedSpace

/-- In a complex Banach algebra, `exp (x + y) = exp x * exp y` for commuting `x`, `y`. -/

theorem norm_heisenberg_sub_self (H : 𝒜) (hH : IsSelfAdjoint H) (t : ℝ) (A : 𝒜) :
    ‖heisenberg H t A - A‖ ≤ 2 * ‖A‖ * (Real.exp (‖H‖ * |t|) - 1) := by
  set U := propagator H t with hU
  set V := propagator H (-t) with hV
  have hnV : ‖V‖ = 1 := norm_propagator H hH (-t)
  have hdecomp : U * A * V - A = (U - 1) * A * V + A * (V - 1) := by
    noncomm_ring
  have h1 : ‖(U - 1) * A * V‖ ≤ (Real.exp (‖H‖ * |t|) - 1) * ‖A‖ := by
    calc ‖(U - 1) * A * V‖ ≤ ‖(U - 1) * A‖ * ‖V‖ := norm_mul_le _ _
      _ ≤ (‖U - 1‖ * ‖A‖) * ‖V‖ := by gcongr; exact norm_mul_le _ _
      _ = ‖U - 1‖ * ‖A‖ := by rw [hnV]; ring
      _ ≤ (Real.exp (‖H‖ * |t|) - 1) * ‖A‖ :=
          mul_le_mul_of_nonneg_right (norm_propagator_sub_one H t) (norm_nonneg A)
  have h2 : ‖A * (V - 1)‖ ≤ ‖A‖ * (Real.exp (‖H‖ * |t|) - 1) := by
    calc ‖A * (V - 1)‖ ≤ ‖A‖ * ‖V - 1‖ := norm_mul_le _ _
      _ ≤ ‖A‖ * (Real.exp (‖H‖ * |t|) - 1) :=
          mul_le_mul_of_nonneg_left (by simpa using norm_propagator_sub_one H (-t))
            (norm_nonneg A)
  calc ‖heisenberg H t A - A‖ = ‖(U - 1) * A * V + A * (V - 1)‖ := by
        rw [heisenberg, ← hU, ← hV, hdecomp]
    _ ≤ ‖(U - 1) * A * V‖ + ‖A * (V - 1)‖ := norm_add_le _ _
    _ ≤ (Real.exp (‖H‖ * |t|) - 1) * ‖A‖ + ‖A‖ * (Real.exp (‖H‖ * |t|) - 1) := by
        exact add_le_add h1 h2
    _ = 2 * ‖A‖ * (Real.exp (‖H‖ * |t|) - 1) := by ring

/-- **Lieb–Robinson bound (base case).**
For observables `A`, `B` in a C⋆-algebra that commute at time zero (for instance because they
are supported on disjoint regions), the commutator of the Heisenberg-evolved observable
`τ_t(A) = e^{itH} A e^{-itH}` with `B` obeys
`‖[τ_t(A), B]‖ ≤ 2‖A‖‖B‖ · min 1 (2 (e^{‖H‖|t|} - 1))`.
The first entry of the minimum is the trivial bound; the second exhibits the effective light
cone: the commutator can only grow like `e^{v|t|} - 1` (i.e. linearly in `t` for short times)
with velocity `v = ‖H‖`, so it stays small until the elapsed time is of the order of the
inverse interaction strength. -/
