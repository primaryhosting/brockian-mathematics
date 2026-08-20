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
def eta : Matrix (Fin 4) (Fin 4) ℂ :=
  !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

lemma eta_transpose : etaᵀ = eta := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [eta]

/-- A matrix belongs to the complex Lorentz group when it preserves the Minkowski form. -/
def IsComplexLorentz (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop := Lᵀ * eta * L = eta

/-- `L` lies in the identity component of the complex Lorentz group: it is joined to the
identity by a continuous path of complex Lorentz transformations. -/
def ConnectedToId (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ γ : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
    Continuous γ ∧ (∀ t, IsComplexLorentz (γ t)) ∧ γ 0 = 1 ∧ γ 1 = L

/-- The complex Lorentz transformation interpolating between the identity (`t = 0`) and the
total space-time inversion `-1` (`t = π`): a complex boost of rapidity `i t` in the `(0,1)`
plane together with a rotation by `t` in the `(2,3)` plane. -/
noncomputable def cptPath (t : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![(Real.cos t : ℂ), Complex.I * (Real.sin t : ℂ), 0, 0;
     Complex.I * (Real.sin t : ℂ), (Real.cos t : ℂ), 0, 0;
     0, 0, (Real.cos t : ℂ), -(Real.sin t : ℂ);
     0, 0, (Real.sin t : ℂ), (Real.cos t : ℂ)]

@[simp] lemma cptPath_zero : cptPath 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptPath]

@[simp] lemma cptPath_pi : cptPath Real.pi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptPath]

/-- Every matrix on the path is a complex Lorentz transformation. -/
lemma cptPath_isComplexLorentz (t : ℝ) : IsComplexLorentz (cptPath t) := by
  have hpy : (Real.sin t : ℂ) ^ 2 + (Real.cos t : ℂ) ^ 2 = 1 := by
    exact_mod_cast congrArg (fun r : ℝ => (r : ℂ)) (Real.sin_sq_add_cos_sq t)
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cptPath, eta, Matrix.mul_apply, Fin.sum_univ_four, Matrix.transpose_apply,
      -Complex.ofReal_cos, -Complex.ofReal_sin] <;>
    ring_nf <;>
    first
      | ring
      | linear_combination hpy
      | linear_combination -hpy
      | linear_combination hI * (Real.sin t : ℂ) ^ 2 + hpy
      | linear_combination -hI * (Real.sin t : ℂ) ^ 2 - hpy
      | linear_combination hI * (Real.sin t : ℂ) ^ 2 - hpy
      | linear_combination -hI * (Real.sin t : ℂ) ^ 2 + hpy

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
theorem neg_one_connectedToId : ConnectedToId (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨fun t => cptPath (Real.pi * t), ?_, fun t => cptPath_isComplexLorentz _, ?_, ?_⟩
  · exact cptPath_continuous.comp (by fun_prop)
  · simp
  · simp

/-- A (Wightman-style) local quantum field theory with `n`-point function `W`, defined on
complexified space-time.  Lorentz invariance of a local theory yields, via analytic
continuation of the Wightman functions into the extended tube, invariance under the identity
component of the complex Lorentz group; that is the hypothesis recorded here. -/
structure LocalQFT (n : ℕ) where
  /-- The `n`-point Wightman function on complexified space-time. -/
  W : (Fin n → CSpaceTime) → ℂ
  /-- Invariance under the identity component of the complex Lorentz group. -/
  lorentz_invariant :
    ∀ L : Matrix (Fin 4) (Fin 4) ℂ, ConnectedToId L →
      ∀ x : Fin n → CSpaceTime, W (fun k => L.mulVec (x k)) = W x

/-- CPT invariance: the `n`-point functions are unchanged under the total inversion `x ↦ -x`
(the combined action of charge conjugation, parity and time reversal on Wightman functions). -/
def IsCPTInvariant {n : ℕ} (T : LocalQFT n) : Prop :=
  ∀ x : Fin n → CSpaceTime, T.W (fun k => -(x k)) = T.W x

/-- **CPT theorem.**  Any Lorentz-invariant local quantum field theory is CPT invariant. -/
theorem cpt_theorem {n : ℕ} (T : LocalQFT n) : IsCPTInvariant T := by
  intro x
  have h := T.lorentz_invariant (-1) neg_one_connectedToId x
  simpa [Matrix.neg_mulVec, Matrix.one_mulVec] using h

/-! ### Non-vacuity: the hypotheses are satisfied by a non-constant theory -/

/-- The Minkowski bilinear form on complexified space-time. -/
noncomputable def minkForm (v w : CSpaceTime) : ℂ := v ⬝ᵥ (eta.mulVec w)

lemma minkForm_lorentz {L : Matrix (Fin 4) (Fin 4) ℂ} (hL : IsComplexLorentz L)
    (v w : CSpaceTime) : minkForm (L.mulVec v) (L.mulVec w) = minkForm v w := by
  unfold minkForm
  rw [Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose,
    Matrix.mulVec_mulVec, Matrix.transpose_mul, eta_transpose, Matrix.mul_assoc,
    ← Matrix.mul_assoc Lᵀ, hL, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    eta_transpose]

/-- The quadratic theory `x ↦ ⟨x₀, x₀⟩` is a Lorentz-invariant local theory. -/
noncomputable def sampleQFT : LocalQFT 1 where
  W := fun x => minkForm (x 0) (x 0)
  lorentz_invariant := by
    rintro L ⟨γ, -, hγL, -, hγ1⟩ x
    have hL : IsComplexLorentz L := hγ1 ▸ hγL 1
    simpa using minkForm_lorentz hL (x 0) (x 0)

theorem sampleQFT_not_constant :
    ¬ ∀ x y : Fin 1 → CSpaceTime, sampleQFT.W x = sampleQFT.W y := by
  intro h
  have := h (fun _ => ![1, 0, 0, 0]) (fun _ => ![0, 0, 0, 0])
  simp [sampleQFT, minkForm, eta, Matrix.mulVec, dotProduct, Fin.sum_univ_four] at this

end Phys

