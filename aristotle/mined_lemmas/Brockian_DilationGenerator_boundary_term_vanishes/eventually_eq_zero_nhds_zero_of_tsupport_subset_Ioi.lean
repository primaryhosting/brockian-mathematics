/-
# Boundary Term Vanishes
Category: Gate1 Operator
Target: Brockian.DilationGenerator.boundary_term_vanishes
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

namespace Brockian.DilationGenerator

/-- If `f` has compact support contained in `(0, ∞)`, then `f` vanishes on a whole
neighbourhood of `0` in `ℝ`. -/

theorem eventually_eq_zero_nhds_zero_of_tsupport_subset_Ioi
    {f : ℝ → ℂ} (hf0 : tsupport f ⊆ Set.Ioi 0) :
    ∀ᶠ x : ℝ in nhds 0, f x = 0 := by
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) :=
    (isClosed_tsupport f).isOpen_compl.mem_nhds (fun h => by simpa using hf0 h)
  filter_upwards [hmem] with x hx using image_eq_zero_of_notMem_tsupport hx

/-- If `f` has compact support, then `f` vanishes eventually along `atTop`. -/
