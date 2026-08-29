/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- If the closed support of `f` lies in `(0, ∞)`, then `f` vanishes on a
punctured right neighbourhood of `0`. -/

theorem eventually_eq_zero_nhdsWithin_zero
    {f : ℝ → ℂ} (hf : tsupport f ⊆ Set.Ioi (0 : ℝ)) :
    ∀ᶠ x in nhdsWithin (0 : ℝ) (Set.Ioi 0), f x = 0 := by
  have h0 : (0 : ℝ) ∉ tsupport f := fun h => by simpa using hf h
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) :=
    (isClosed_tsupport f).isOpen_compl.mem_nhds h0
  filter_upwards [nhdsWithin_le_nhds hmem] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- A function with compact support vanishes eventually at `+∞`. -/
