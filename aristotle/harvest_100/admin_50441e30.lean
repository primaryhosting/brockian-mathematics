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
def eta : Fin 4 → ℂ := ![1, -1, -1, -1]

/-- The (complex bilinear extension of the) Minkowski inner product. -/
noncomputable def mform (x y : CMinkowski) : ℂ := ∑ i, eta i * x i * y i

/-- A complex `4 × 4` matrix is a complex Lorentz transformation when it preserves
the complex bilinear extension of the Minkowski form. -/
def IsComplexLorentz (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ x y : CMinkowski, mform (L.mulVec x) (L.mulVec y) = mform x y

/-- `L` lies in the identity component of the complex Lorentz group: there is a continuous
path of complex Lorentz transformations joining the identity to `L`. -/
def ConnectedToIdentity (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ p : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
    Continuous p ∧ p 0 = 1 ∧ p 1 = L ∧ ∀ t, IsComplexLorentz (p t)

/-- The total spacetime inversion `x ↦ -x`, i.e. the (P·T) part of the CPT operation on
spacetime arguments. -/
def cptInversion : Matrix (Fin 4) (Fin 4) ℂ := -1

/-- A one-parameter family of complex Lorentz transformations: a complex boost with
imaginary rapidity in the `(0,1)`-plane combined with a rotation in the `(2,3)`-plane.
At `t = π` it equals total spacetime inversion `-1`. -/
noncomputable def cptPath (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![
    ![(Real.cos t : ℂ), Complex.I * (Real.sin t : ℂ), 0, 0],
    ![Complex.I * (Real.sin t : ℂ), (Real.cos t : ℂ), 0, 0],
    ![0, 0, (Real.cos t : ℂ), -(Real.sin t : ℂ)],
    ![0, 0, (Real.sin t : ℂ), (Real.cos t : ℂ)]]

lemma cptPath_mulVec (t : ℝ) (x : CMinkowski) :
    (cptPath t).mulVec x =
      ![(Real.cos t : ℂ) * x 0 + Complex.I * (Real.sin t : ℂ) * x 1,
        Complex.I * (Real.sin t : ℂ) * x 0 + (Real.cos t : ℂ) * x 1,
        (Real.cos t : ℂ) * x 2 - (Real.sin t : ℂ) * x 3,
        (Real.sin t : ℂ) * x 2 + (Real.cos t : ℂ) * x 3] := by
  funext i
  fin_cases i <;>
    (simp [Matrix.mulVec, cptPath, dotProduct, Fin.sum_univ_four]; try ring)

lemma cptPath_isComplexLorentz (t : ℝ) : IsComplexLorentz (cptPath t) := by
  intro x y
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have hs : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
    have := Real.sin_sq_add_cos_sq t
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) this
  simp only [mform, Fin.sum_univ_four, cptPath_mulVec, eta]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]
  linear_combination (x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3) * hs -
    ((Real.sin t : ℂ) ^ 2 * (x 0 * y 0 - x 1 * y 1)) * hI

lemma cptPath_zero : cptPath 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cptPath]

lemma cptPath_pi : cptPath Real.pi = cptInversion := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cptPath, cptInversion]

lemma cptPath_continuous : Continuous cptPath := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp only [cptPath, Matrix.of_apply] <;> simp <;> fun_prop

/-- **The group-theoretic heart of the CPT theorem**: total spacetime inversion `x ↦ -x`
lies in the identity component of the *complex* Lorentz group, even though it is not in the
identity component of the real Lorentz group. -/
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
theorem cpt_theorem {n : ℕ} (W : (Fin n → CMinkowski) → ℂ)
    (hinv : ∀ L : Matrix (Fin 4) (Fin 4) ℂ, ConnectedToIdentity L →
      ∀ x : Fin n → CMinkowski, W (fun k => L.mulVec (x k)) = W x) :
    ∀ x : Fin n → CMinkowski, W (fun k => -(x k)) = W x := by
  intro x
  have h := hinv cptInversion cptInversion_connectedToIdentity x
  simpa [cptInversion, Matrix.neg_mulVec, Matrix.one_mulVec] using h

/-- The hypothesis of `cpt_theorem` is not vacuous: the simplest Lorentz-invariant
two-point-style function, `x ↦ ⟨x₀, x₀⟩`, satisfies it. -/
theorem cpt_hypothesis_nonvacuous :
    ∀ L : Matrix (Fin 4) (Fin 4) ℂ, ConnectedToIdentity L →
      ∀ x : Fin 1 → CMinkowski,
        (fun z : Fin 1 → CMinkowski => mform (z 0) (z 0)) (fun k => L.mulVec (x k)) =
          (fun z : Fin 1 → CMinkowski => mform (z 0) (z 0)) x := by
  rintro L ⟨p, -, -, hp1, hL⟩ x
  have : IsComplexLorentz L := hp1 ▸ hL 1
  exact this (x 0) (x 0)

#print axioms Phys.cpt_theorem

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

