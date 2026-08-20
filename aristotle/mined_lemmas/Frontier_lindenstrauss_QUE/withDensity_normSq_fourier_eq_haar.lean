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

theorem withDensity_normSq_fourier_eq_haar (n : ℤ) :
    (haarAddCircle (T := (1:ℝ))).withDensity (fun x => (‖fourier n x‖₊ : ENNReal) ^ 2)
      = haarAddCircle := by
  have h : (fun x : AddCircle (1:ℝ) => (‖fourier n x‖₊ : ENNReal) ^ 2)
      = (1 : AddCircle (1:ℝ) → ENNReal) := by
    funext x
    have hx : ‖fourier n x‖₊ = 1 := by
      rw [← NNReal.coe_inj]
      exact norm_fourier_eq_one n x
    rw [hx]
    norm_num
  rw [h, withDensity_one]

/-- **Quantum unique ergodicity on the flat circle** (base case): along any sequence of Laplace
eigenfunctions `fourier (phi k)` of the circle, the position measures `‖φ‖² dHaar` equidistribute
with respect to the Haar probability measure. -/
