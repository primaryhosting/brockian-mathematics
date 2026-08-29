import Mathlib

/-!
# Bloch Sphere Bijection
Category: Quantum Computing
Target: QC.bloch_sphere_bijection
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

set_option grind.warning false

namespace QC

/-! ## Pure qubit states -/

/-- A pure state of a single qubit: a unit vector `a|0⟩ + b|1⟩` in `ℂ²`. -/
structure Qubit where
  /-- amplitude of `|0⟩` -/
  a : ℂ
  /-- amplitude of `|1⟩` -/
  b : ℂ
  /-- normalization -/
  norm_eq : ‖a‖ ^ 2 + ‖b‖ ^ 2 = 1

namespace Qubit

/-- Two qubit states are physically identical when they differ by a global phase. -/

theorem bloch_mem_sphere (v : Qubit) :
    (!₂[blochX v, blochY v, blochZ v] : EuclideanSpace ℝ (Fin 3)) ∈
      Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 := by
  have hs : v.a.re ^ 2 + v.a.im ^ 2 + (v.b.re ^ 2 + v.b.im ^ 2) = 1 := by
    have := v.norm_eq
    rw [Qubit.norm_a_sq, Qubit.norm_b_sq] at this
    linarith
  have key : blochX v ^ 2 + blochY v ^ 2 + blochZ v ^ 2 = 1 := by
    rw [blochX_eq, blochY_eq, blochZ, Qubit.norm_a_sq, Qubit.norm_b_sq]
    nlinarith [hs]
  simp only [Metric.mem_sphere, dist_zero_right, EuclideanSpace.norm_eq, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons, Real.norm_eq_abs, sq_abs]
  rw [key, Real.sqrt_one]

/-- The Bloch vector of a pure qubit state, as a point of `S²`. -/
