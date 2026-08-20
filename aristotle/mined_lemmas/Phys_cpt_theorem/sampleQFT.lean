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

noncomputable def sampleQFT : LocalQFT 1 where
  W := fun x => minkForm (x 0) (x 0)
  lorentz_invariant := by
    rintro L ⟨γ, -, hγL, -, hγ1⟩ x
    have hL : IsComplexLorentz L := hγ1 ▸ hγL 1
    simpa using minkForm_lorentz hL (x 0) (x 0)

