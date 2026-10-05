/-
# Subclass Obstruction Statement
Category: Brockian Conjecture
Target: Zeta23Obstruction.subclass_obstruction_statement
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Zeta23Obstruction

/-- A **fixed-kernel pointwise-discard certificate**.

Abstract model of the certificates in the subclass under consideration: the certificate is
determined by one *fixed* kernel `R : ℝ → ℝ`, together with a region `shallow` of the parameter
line on which the kernel is discarded pointwise, i.e. on which it is *assumed* nonnegative
(`h_pos`).  Nothing at all is assumed about `R` off `shallow`; in the intended application the
values of `R` off `shallow` are the values of its analytic continuation at the deep points. -/
structure Certificate where
  /-- The fixed kernel of the certificate. -/
  R : ℝ → ℝ
  /-- The region on which the kernel is discarded pointwise. -/
  shallow : Set ℝ
  /-- Pointwise discard: on the shallow region the kernel is nonnegative. -/
  h_pos : ∀ x ∈ shallow, 0 ≤ R x

/-- A **configuration** with `n` species: each species `i` sits at a point `z i` of the parameter
line and carries a nonnegative weight `w i`.  This is the finite-dimensional stand-in for the
configuration data that the certificate's linear charging chain is applied to. -/
structure Config (n : ℕ) where
  /-- Location of each species. -/
  z : Fin n → ℝ
  /-- Nonnegative weight (charge) of each species. -/
  w : Fin n → ℝ
  /-- Weights are nonnegative. -/
  hw : ∀ i, 0 ≤ w i

/-- **Per-species linear charging**: the certificate's linear functional evaluated on a
configuration, i.e. the weighted sum of the kernel values at the species' locations. -/

def ValidAgainstDeepPairs (C : Certificate) : Prop :=
  ∀ cfg : Config 2, IsDeepPair C cfg → TermwiseBound C cfg

/-- The charging functional is linear in the weights. -/
