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

namespace Frontier

section Mixing

variable {V : Type*} [Fintype V]

/-- The bilinear form associated with a weight matrix `A : V → V → ℝ`. -/

lemma bil_smul_right (A : V → V → ℝ) (c : ℝ) (f g : V → ℝ) :
    bil A f (fun x => c * g x) = c * bil A f g := by
  unfold bil
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun v _ => ?_)
  ring

/-- Polarization bound: on the space orthogonal to the constants, `|bil A f g|` is bounded
by `lam * (‖f‖² + ‖g‖²) / 2`. -/
