import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the algebraic core of the CPT theorem in the Wightman framework.

A (scalar) `n`-point Wightman function, analytically continued to complex Minkowski
space, is a function `W : (Fin n → (Fin 4 → ℂ)) → ℂ`.

* *Lorentz invariance* (together with analyticity of the Wightman functions, which is
  what allows the real proper orthochronous group to be replaced by the complex Lorentz
  group) is expressed as invariance of `W` under every complex Lorentz matrix that is
  connected to the identity by a continuous path inside the complex Lorentz group.
* *Locality* enters through weak local commutativity: at Jost points the Wightman
  function is invariant under total reversal of its arguments.
* *CPT invariance* is the statement `W (x₁, …, x_n) = W (-x_n, …, -x₁)`.

The mathematical content is `Phys.negOne_connectedToOne`: the total space-time inversion
`-1` lies in the identity component of the complex Lorentz group (this is false for the
*real* Lorentz group), witnessed by the explicit path

`t ↦ (complex boost by rapidity `i t` in the 01-plane) ⊕ (rotation by `t` in the 23-plane)`

which joins `1` (at `t = 0`) to `-1` (at `t = π`).
-/

namespace Phys

open Matrix Complex

/-- The Minkowski metric `diag (1, -1, -1, -1)`, as a complex matrix. -/
def minkowskiEta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0;
     0, -1, 0, 0;
     0, 0, -1, 0;
     0, 0, 0, -1]

/-- A complex `4 × 4` matrix is a complex Lorentz transformation if it preserves the
Minkowski form, `Mᵀ η M = η`. -/
def IsComplexLorentz (M : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  M.transpose * minkowskiEta * M = minkowskiEta

/-- `M` lies in the identity component of the complex Lorentz group: it is joined to the
identity by a continuous path of complex Lorentz transformations. -/
def ConnectedToOne (M : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ γ : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
    Continuous γ ∧ (∀ t, IsComplexLorentz (γ t)) ∧ γ 0 = 1 ∧ γ 1 = M

/-- The explicit one-parameter family: a boost with imaginary rapidity `t` in the
`(0,1)`-plane, together with a rotation by the angle `t` in the `(2,3)`-plane. -/
noncomputable def cptPath (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.cos t : ℂ), (Real.sin t : ℂ) * I, 0, 0;
     (Real.sin t : ℂ) * I, (Real.cos t : ℂ), 0, 0;
     0, 0, (Real.cos t : ℂ), -(Real.sin t : ℂ);
     0, 0, (Real.sin t : ℂ), (Real.cos t : ℂ)]

lemma cptPath_isComplexLorentz (t : ℝ) : IsComplexLorentz (cptPath t) := by
  have hpy : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
    have h : (Real.sin t) ^ 2 + (Real.cos t) ^ 2 = 1 := Real.sin_sq_add_cos_sq t
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) h
  have hI : (I : ℂ) ^ 2 = -1 := Complex.I_sq
  show (cptPath t).transpose * minkowskiEta * cptPath t = minkowskiEta
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ, cptPath, minkowskiEta, Matrix.transpose_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    · first
      | linear_combination -hpy
      | linear_combination hpy - (Real.sin t : ℂ) ^ 2 * hI
      | linear_combination -hpy + (Real.sin t : ℂ) ^ 2 * hI
      | ring1

lemma cptPath_zero : cptPath 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptPath]

lemma cptPath_pi : cptPath Real.pi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptPath]

lemma continuous_cptPath : Continuous cptPath := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [cptPath] <;> fun_prop

/-- **The total space-time inversion `-1` lies in the identity component of the complex
Lorentz group.** This is the group-theoretic heart of the CPT theorem. -/
theorem negOne_connectedToOne : ConnectedToOne (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨fun t => cptPath (Real.pi * t), ?_, ?_, ?_, ?_⟩
  · exact continuous_cptPath.comp (by fun_prop)
  · intro t; exact cptPath_isComplexLorentz _
  · simpa using cptPath_zero
  · simpa using cptPath_pi

/-- A (scalar) `n`-point Wightman function on complexified Minkowski space. -/
def Wightman (n : ℕ) : Type := (Fin n → (Fin 4 → ℂ)) → ℂ

/-- Lorentz invariance: `W` is invariant under all complex Lorentz transformations in the
identity component (this is the content of real Lorentz invariance combined with the
analyticity of the Wightman functions). -/
def LorentzInvariant {n : ℕ} (W : Wightman n) : Prop :=
  ∀ M : Matrix (Fin 4) (Fin 4) ℂ, ConnectedToOne M →
    ∀ x : Fin n → (Fin 4 → ℂ), W (fun i => M.mulVec (x i)) = W x

/-- Weak local commutativity, the form in which locality (spacelike commutativity of the
fields) is used in the CPT theorem: at Jost points the Wightman function is invariant
under reversing the order of its arguments. -/
def WeaklyLocal {n : ℕ} (W : Wightman n) : Prop :=
  ∀ x : Fin n → (Fin 4 → ℂ), W (fun i => x i.rev) = W x

/-- CPT invariance: `W (x₁, …, x_n) = W (-x_n, …, -x₁)`. -/
def CPTInvariant {n : ℕ} (W : Wightman n) : Prop :=
  ∀ x : Fin n → (Fin 4 → ℂ), W (fun i => -(x i.rev)) = W x

/-- **CPT theorem.** Any Lorentz-invariant local quantum field theory is CPT invariant:
if the Wightman functions are invariant under the identity component of the complex
Lorentz group and satisfy weak local commutativity, then they are invariant under the
CPT operation `x ↦ -x` combined with reversal of the arguments. -/
theorem cpt_theorem {n : ℕ} (W : Wightman n) (hL : LorentzInvariant W)
    (hloc : WeaklyLocal W) : CPTInvariant W := by
  intro x
  have h1 : W (fun i => (-1 : Matrix (Fin 4) (Fin 4) ℂ).mulVec (x i.rev))
      = W (fun i => x i.rev) := hL _ negOne_connectedToOne _
  have h2 : ∀ v : Fin 4 → ℂ, (-1 : Matrix (Fin 4) (Fin 4) ℂ).mulVec v = -v := by
    intro v
    simp [Matrix.neg_mulVec]
  simpa only [h2] using h1.trans (hloc x)

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

