/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

/-!
# The CPT theorem

We formalize the geometric core of the CPT theorem in the Wightman framework.

A Lorentz-invariant local quantum field theory has Wightman functions that continue
analytically to the extended tube and are there invariant under the identity component of the
*complex* Lorentz group `L₊(ℂ)`.  The decisive geometric fact — the content of the CPT theorem —
is that the total space-time inversion `-1` belongs to that identity component: it is reached
from the identity by a complex boost of rapidity `iπ` in the `(0,1)` plane combined with a
rotation by `π` in the `(2,3)` plane.  Consequently every such theory is invariant under
`x ↦ -x`, i.e. CPT invariant.
-/

namespace Phys

open Matrix

/-- Complexified Minkowski space-time: four complex coordinates. -/
abbrev CSpaceTime : Type := Fin 4 → ℂ

/-- The Minkowski metric `diag(1, -1, -1, -1)` on complexified space-time. -/

lemma cptPath_continuous : Continuous cptPath := by
  have hc : Continuous fun t : ℝ => ((Real.cos t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_cos
  have hs : Continuous fun t : ℝ => ((Real.sin t : ℝ) : ℂ) :=
    Complex.continuous_ofReal.comp Real.continuous_sin
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [cptPath] <;>
    first
      | exact continuous_const
      | exact hc
      | exact hs
      | exact hs.neg
      | exact continuous_const.mul hs

/-- **The total space-time inversion lies in the identity component of the complex Lorentz
group.**  This is the geometric heart of the CPT theorem. -/
