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

def ProperComplexLorentz : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  {L | IsComplexLorentz L ∧ L.det = 1}

/-- Complex Lorentz transformations preserve the Minkowski form. -/
