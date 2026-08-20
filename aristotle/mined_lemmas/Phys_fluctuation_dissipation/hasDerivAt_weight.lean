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

import Mathlib

/-!
# Fluctuation Dissipation
Category: Frontier Phys
Target: Phys.fluctuation_dissipation
Statement: The FDT relates linear response to equilibrium correlations.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

open Finset

variable {Ω : Type*} [Fintype Ω]

/-- Boltzmann weight of the state `w` at inverse temperature `beta` for the
Hamiltonian `E - f • A`, i.e. the unperturbed energy `E` perturbed by an external
field `f` coupled to the observable `A`. -/

lemma hasDerivAt_weight (beta : ℝ) (E A : Ω → ℝ) (f : ℝ) (w : Ω) :
    HasDerivAt (fun f => weight beta E A f w) (beta * A w * weight beta E A f w) f := by
  have h : HasDerivAt (fun f : ℝ => -beta * (E w - f * A w)) (beta * A w) f := by
    have h1 : HasDerivAt (fun y : ℝ => -beta * (E w - y * A w))
        (-beta * -(1 * A w)) f :=
      (((hasDerivAt_id f).mul_const (A w)).const_sub (E w)).const_mul (-beta)
    convert h1 using 1; ring
  have h2 := h.exp
  simpa [weight, mul_comm] using h2

