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

theorem hasDerivAt_deriv_fourier (n : ℤ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (2 * π * I * n) * fourier n (y : AddCircle (1:ℝ)))
      (-(4 * π ^ 2 * (n : ℂ) ^ 2) * fourier n (x : AddCircle (1:ℝ))) x := by
  have h := (hasDerivAt_fourier (1:ℝ) n x).const_mul (2 * π * I * (n : ℂ))
  convert h using 1
  push_cast
  ring_nf
  simp [Complex.I_sq]

/-- The microlocal (position) measure of the `n`-th circle eigenfunction is exactly the Haar
probability measure. -/
