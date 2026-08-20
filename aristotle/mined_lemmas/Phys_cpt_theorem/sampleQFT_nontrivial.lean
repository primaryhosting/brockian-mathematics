/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
## Overview

We formalize the statement of the **CPT theorem** in the Wightman framework, in the
standard form due to Jost:

> for a Lorentz-invariant local quantum field theory, the (analytically continued)
> Wightman functions satisfy `W (x₁, …, xₙ) = W (-xₙ, …, -x₁)`.

The set-up is the following.

* Complexified Minkowski space is `Phys.CSpacetime = Fin 4 → ℂ`, equipped with the
  (bilinear, not sesquilinear) Minkowski form `Phys.minkowski`.
* The complex Lorentz group consists of the complex `4 × 4` matrices preserving that form;
  the *proper* complex Lorentz group `Phys.ProperComplexLorentz` additionally requires
  determinant `1`.
* A `Phys.LorentzQFT` packages the Wightman functions `W n` of a theory together with
  invariance of the analytically continued Wightman functions under the proper complex
  Lorentz group.  This invariance is the content of the Bargmann–Hall–Wightman theorem:
  Lorentz invariance of the theory, together with the spectrum condition (which provides
  the analytic continuation into the extended tube), upgrades invariance under the real
  restricted Lorentz group to invariance under `L₊(ℂ)`.
* Locality enters through *weak local commutativity* `Phys.WeakLocalCommutativity`
  (Jost's condition), and CPT invariance is the Jost relation `Phys.CPTInvariant`.

The mathematical core proved here is that the total spacetime reflection `x ↦ -x` — the
PT transformation — belongs to the proper complex Lorentz group, and indeed to its
identity component: `Phys.joinedIn_one_neg_one` exhibits an explicit continuous path
inside the group from the identity to `-1`, built from a complex boost of rapidity `iπ`
in the `(0,1)`-plane together with a rotation by `π` in the `(2,3)`-plane.  Since the
Wightman functions are invariant under this element, CPT invariance and weak local
commutativity are equivalent (`Phys.cpt_theorem`).
-/

namespace Phys

open Matrix

/-- Complexified Minkowski spacetime. -/
abbrev CSpacetime : Type := Fin 4 → ℂ

/-- The Minkowski metric with signature `(+,-,-,-)`, as a complex matrix. -/

theorem sampleQFT_nontrivial :
    sampleQFT.W 1 (fun _ => ![1, 0, 0, 0]) ≠ sampleQFT.W 1 (fun _ => 0) := by
  show (∑ i : Fin 1, ∑ j : Fin 1, minkowski _ _) ≠ ∑ i : Fin 1, ∑ j : Fin 1, minkowski _ _
  simp [minkowski, eta, dotProduct, Matrix.mulVec, Fin.sum_univ_four]

end Phys

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

