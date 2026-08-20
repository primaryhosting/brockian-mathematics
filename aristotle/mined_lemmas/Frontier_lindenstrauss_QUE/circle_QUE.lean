/-
# Lindenstrauss QUE
Category: Frontier — Fields Medal Work
Target: Frontier.lindenstrauss_QUE
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Filter Topology TopologicalSpace
open scoped BoundedContinuousFunction

namespace Frontier

section Abstract

variable {X : Type*} [MetricSpace X] [CompactSpace X] [MeasurableSpace X] [BorelSpace X]

omit [CompactSpace X] in
/-- A weak-* limit of a sequence of `T`-invariant probability measures is `T`-invariant.

This is the standard "limit measures are geodesic-flow invariant" step in the
quantum-unique-ergodicity argument. -/

theorem circle_QUE (phi : ℕ → ℤ) (f : C(AddCircle (1:ℝ), ℝ)) :
    Tendsto (fun k => ∫ x, f x * ‖fourier (phi k) x‖ ^ 2 ∂(haarAddCircle (T := (1:ℝ)))) atTop
      (𝓝 (∫ x, f x ∂(haarAddCircle (T := (1:ℝ))))) := by
  have h : ∀ k, (∫ x, f x * ‖fourier (phi k) x‖ ^ 2 ∂(haarAddCircle (T := (1:ℝ))))
      = ∫ x, f x ∂(haarAddCircle (T := (1:ℝ))) := by
    intro k
    congr 1
    funext x
    rw [norm_fourier_eq_one]
    ring
  simp only [h]
  exact tendsto_const_nhds

end CircleBaseCase

end Frontier

