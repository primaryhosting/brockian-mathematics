import Mathlib

/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

theorem isingZ_eq_sum_prod (m n : ℕ) [NeZero m] [NeZero n] (J β : ℝ) :
    isingZ m n J β
      = ∑ r : ZMod m → (ZMod n → Bool), ∏ i : ZMod m, transferMatrix n J β (r i) (r (i + 1)) := by
  rw [isingZ]
  refine Fintype.sum_equiv (Equiv.curry (ZMod m) (ZMod n) Bool) _ _ ?_
  intro σ
  show Real.exp (-β * isingEnergy m n J σ) = _
  simp only [transferMatrix, Matrix.of_apply, Equiv.curry_apply]
  rw [← Real.exp_sum, isingEnergy]
  congr 1
  rw [Fintype.sum_prod_type]
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun y _ => ?_))
  simp only [Function.curry_apply]
  ring

/-- **The transfer-matrix reduction of the 2D Ising model.**  For every lattice size and
every temperature, the partition function on the `m × n` torus is the trace of the `m`-th
power of the `2ⁿ × 2ⁿ` transfer matrix.  This is the exact identity on which Onsager's
solution rests. -/
