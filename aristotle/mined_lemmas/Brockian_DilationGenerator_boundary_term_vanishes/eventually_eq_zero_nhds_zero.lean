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

set_option grind.warning false

namespace Brockian
namespace DilationGenerator

/-- If `f` has its closed support inside `(0, ∞)`, then `f` vanishes on a
neighbourhood of `0`. -/

lemma eventually_eq_zero_nhds_zero {f : ℝ → ℂ} (hf0 : tsupport f ⊆ Set.Ioi 0) :
    ∀ᶠ x in nhds (0 : ℝ), f x = 0 := by
  have hmem : (tsupport f)ᶜ ∈ nhds (0 : ℝ) := by
    refine (isClosed_tsupport f).isOpen_compl.mem_nhds ?_
    intro hcon
    exact lt_irrefl (0 : ℝ) (hf0 hcon)
  filter_upwards [hmem] with x hx
  exact image_eq_zero_of_notMem_tsupport hx

/-- A compactly supported function vanishes eventually at `+∞`. -/
