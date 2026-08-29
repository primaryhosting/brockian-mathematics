/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Phys

open Finset Matrix

/-- Complexified Minkowski space: four complex coordinates. -/
abbrev CMinkowski : Type := Fin 4 → ℂ

/-- The Minkowski metric signature `(+,-,-,-)`. -/

theorem cptInversion_connectedToIdentity : ConnectedToIdentity cptInversion := by
  refine ⟨fun t => cptPath (Real.pi * t), ?_, ?_, ?_, ?_⟩
  · exact cptPath_continuous.comp (by fun_prop)
  · simpa using cptPath_zero
  · simpa using cptPath_pi
  · intro t; exact cptPath_isComplexLorentz _

/--
**CPT theorem (statement form).**

A Lorentz-invariant local quantum field theory is CPT invariant.

Formalization: after analytic continuation (Wightman's construction, which uses locality,
the spectrum condition and real Lorentz invariance), the Wightman functions `W` of the
theory are invariant under the identity component of the *complex* Lorentz group.  This is
the hypothesis `hinv` below.  The CPT theorem is then the assertion that `W` is invariant
under total spacetime inversion `x ↦ -x`, the geometric content of the CPT operation; this
holds because `-1` belongs to the identity component of the complex Lorentz group
(`cptInversion_connectedToIdentity`), which is false for the real Lorentz group.
-/
