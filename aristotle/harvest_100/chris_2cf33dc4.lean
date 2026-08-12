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
def eta : Matrix (Fin 4) (Fin 4) ℂ := !![1, 0, 0, 0; 0, -1, 0, 0; 0, 0, -1, 0; 0, 0, 0, -1]

/-- The (complex bilinear) Minkowski form on complexified Minkowski space. -/
noncomputable def minkowski (x y : CSpacetime) : ℂ := x ⬝ᵥ (eta *ᵥ y)

/-- A complex matrix is a complex Lorentz transformation if it preserves the Minkowski
metric, i.e. `Λᵀ η Λ = η`. -/
def IsComplexLorentz (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop := Lᵀ * eta * L = eta

/-- The proper complex Lorentz group `L₊(ℂ)`: complex Lorentz matrices of determinant `1`. -/
def ProperComplexLorentz : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  {L | IsComplexLorentz L ∧ L.det = 1}

/-- Complex Lorentz transformations preserve the Minkowski form. -/
theorem minkowski_mulVec {L : Matrix (Fin 4) (Fin 4) ℂ} (hL : IsComplexLorentz L)
    (x y : CSpacetime) : minkowski (L *ᵥ x) (L *ᵥ y) = minkowski x y := by
  unfold minkowski
  rw [Matrix.mulVec_mulVec, ← Matrix.vecMul_transpose, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hL]

theorem isComplexLorentz_one : IsComplexLorentz 1 := by
  simp [IsComplexLorentz]

/-- The total spacetime reflection (PT) is a complex Lorentz transformation. -/
theorem isComplexLorentz_neg_one : IsComplexLorentz (-1) := by
  simp [IsComplexLorentz]

/-- The total spacetime reflection has determinant `1` (spacetime is even-dimensional). -/
theorem det_neg_one : (-1 : Matrix (Fin 4) (Fin 4) ℂ).det = 1 := by
  rw [Matrix.det_neg]
  norm_num

/-- The total spacetime reflection `x ↦ -x` lies in the proper complex Lorentz group. -/
theorem neg_one_mem_properComplexLorentz :
    (-1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ ProperComplexLorentz :=
  ⟨isComplexLorentz_neg_one, det_neg_one⟩

/-! ### PT lies in the identity component of the complex Lorentz group -/

/-- A two-parameter family of complex Lorentz transformations: a boost of complex rapidity
`w` in the `(0,1)`-plane composed with a rotation by the angle `t` in the `(2,3)`-plane. -/
noncomputable def boostRot (w t : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![Complex.cosh w, Complex.sinh w, 0, 0;
     Complex.sinh w, Complex.cosh w, 0, 0;
     0, 0, Complex.cos t, -Complex.sin t;
     0, 0, Complex.sin t, Complex.cos t]

theorem isComplexLorentz_boostRot (w t : ℂ) : IsComplexLorentz (boostRot w t) := by
  have h1 := Complex.cosh_sq_sub_sinh_sq w
  have h2 := Complex.sin_sq_add_cos_sq t
  unfold IsComplexLorentz
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boostRot, eta, Matrix.mul_apply, Fin.sum_univ_four] <;>
    (try ring1) <;> (try linear_combination h1) <;> (try linear_combination -h1) <;>
    (try linear_combination -h2)

theorem det_boostRot (w t : ℂ) : (boostRot w t).det = 1 := by
  have h1 := Complex.cosh_sq_sub_sinh_sq w
  have h2 := Complex.sin_sq_add_cos_sq t
  simp [boostRot, Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove]
  linear_combination (Complex.sin t ^ 2 + Complex.cos t ^ 2) * h1 + h2

theorem boostRot_mem (w t : ℂ) : boostRot w t ∈ ProperComplexLorentz :=
  ⟨isComplexLorentz_boostRot w t, det_boostRot w t⟩

theorem boostRot_zero : boostRot 0 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostRot]

/-- At rapidity `iπ` and rotation angle `π` the family reaches the total reflection `-1`. -/
theorem boostRot_pi : boostRot ((Real.pi : ℂ) * Complex.I) (Real.pi : ℂ) = -1 := by
  have hc : Complex.cosh ((Real.pi : ℂ) * Complex.I) = -1 := by
    rw [Complex.cosh_mul_I]; simp
  have hs : Complex.sinh ((Real.pi : ℂ) * Complex.I) = 0 := by
    rw [Complex.sinh_mul_I]; simp
  ext i j
  fin_cases i <;> fin_cases j <;> simp [boostRot, hc, hs]

theorem continuous_boostRot_path :
    Continuous fun s : unitInterval =>
      boostRot ((Real.pi : ℂ) * Complex.I * (s : ℝ)) ((Real.pi : ℂ) * (s : ℝ)) := by
  refine continuous_pi fun i => continuous_pi fun j => ?_
  fin_cases i <;> fin_cases j <;> simp [boostRot] <;> fun_prop

/-- The explicit path from the identity to the total spacetime reflection inside the
complex Lorentz group. -/
noncomputable def ptPath : Path (1 : Matrix (Fin 4) (Fin 4) ℂ) (-1) where
  toFun := fun s => boostRot ((Real.pi : ℂ) * Complex.I * (s : ℝ)) ((Real.pi : ℂ) * (s : ℝ))
  continuous_toFun := continuous_boostRot_path
  source' := by simpa using boostRot_zero
  target' := by simpa using boostRot_pi

/-- **PT is connected to the identity**: the total spacetime reflection `x ↦ -x` lies in
the identity component of the proper complex Lorentz group.  (This is the reason the
Bargmann–Hall–Wightman analytic continuation makes the Wightman functions invariant
under PT, even though PT is not a real orthochronous Lorentz transformation.) -/
theorem joinedIn_one_neg_one : JoinedIn ProperComplexLorentz 1 (-1) :=
  ⟨ptPath, fun _ => boostRot_mem _ _⟩

/-! ### Wightman functions, locality and CPT -/

/-- A Lorentz-invariant local quantum field theory, described (as in the Wightman
framework) by its sequence of `n`-point functions on complexified Minkowski space.

The invariance axiom is invariance of the analytically continued Wightman functions under
the *proper complex* Lorentz group `L₊(ℂ)`, which is what Lorentz invariance of the theory
together with the spectrum condition yields, by the Bargmann–Hall–Wightman theorem. -/
structure LorentzQFT where
  /-- The `n`-point Wightman function, analytically continued to complex arguments. -/
  W : (n : ℕ) → (Fin n → CSpacetime) → ℂ
  /-- Invariance under the proper complex Lorentz group. -/
  lorentz_invariance : ∀ (n : ℕ) (L : Matrix (Fin 4) (Fin 4) ℂ), L ∈ ProperComplexLorentz →
    ∀ x : Fin n → CSpacetime, W n (fun i => L *ᵥ x i) = W n x

namespace LorentzQFT

/-- Wightman functions of a Lorentz-invariant theory are invariant under the total
spacetime reflection `x ↦ -x`. -/
theorem W_neg (Q : LorentzQFT) (n : ℕ) (x : Fin n → CSpacetime) :
    Q.W n (fun i => -x i) = Q.W n x := by
  have h := Q.lorentz_invariance n (-1) neg_one_mem_properComplexLorentz x
  simpa [Matrix.neg_mulVec] using h

end LorentzQFT

/-- **Weak local commutativity** (Jost's form of locality): the Wightman functions are
invariant under reversing the order of all their arguments. -/
def WeakLocalCommutativity (Q : LorentzQFT) : Prop :=
  ∀ (n : ℕ) (x : Fin n → CSpacetime), Q.W n (fun i => x i.rev) = Q.W n x

/-- **CPT invariance**, in the form of the Jost relation
`W (x₁, …, xₙ) = W (-xₙ, …, -x₁)`. -/
def CPTInvariant (Q : LorentzQFT) : Prop :=
  ∀ (n : ℕ) (x : Fin n → CSpacetime), Q.W n (fun i => -x i.rev) = Q.W n x

/-- **The CPT theorem.**  For a Lorentz-invariant quantum field theory (invariance of the
analytically continued Wightman functions under the proper complex Lorentz group),
locality in the form of weak local commutativity is equivalent to CPT invariance.

In particular, any Lorentz-invariant local quantum field theory is CPT invariant. -/
theorem cpt_theorem (Q : LorentzQFT) : WeakLocalCommutativity Q ↔ CPTInvariant Q := by
  constructor
  · intro hloc n x
    exact (Q.W_neg n (fun i => x i.rev)).trans (hloc n x)
  · intro hcpt n x
    exact (Q.W_neg n (fun i => x i.rev)).symm.trans (hcpt n x)

/-- The CPT theorem, stated as an implication: a Lorentz-invariant local quantum field
theory is CPT invariant. -/
theorem cpt_invariant_of_local (Q : LorentzQFT) (hloc : WeakLocalCommutativity Q) :
    CPTInvariant Q :=
  (cpt_theorem Q).mp hloc

/-! ### A nontrivial example

To check that the axioms above are not vacuous we exhibit a nonconstant Lorentz-invariant
system of `n`-point functions which is weakly local, and hence CPT invariant. -/

/-- A toy Lorentz-invariant system of `n`-point functions, `W n x = ∑ i j, ⟨x i, x j⟩`. -/
noncomputable def sampleQFT : LorentzQFT where
  W := fun n x => ∑ i : Fin n, ∑ j : Fin n, minkowski (x i) (x j)
  lorentz_invariance := by
    intro n L hL x
    simp [minkowski_mulVec hL.1]

theorem sampleQFT_weakLocal : WeakLocalCommutativity sampleQFT := by
  intro n x
  have key : ∀ f : Fin n → ℂ, ∑ i : Fin n, f i.rev = ∑ i, f i :=
    fun f => Equiv.sum_comp Fin.revPerm f
  show (∑ i : Fin n, ∑ j : Fin n, minkowski (x i.rev) (x j.rev)) = _
  exact (key fun i => ∑ j : Fin n, minkowski (x i) (x j.rev)).trans
    (Finset.sum_congr rfl fun i _ => key fun j => minkowski (x i) (x j))

theorem sampleQFT_cptInvariant : CPTInvariant sampleQFT :=
  cpt_invariant_of_local _ sampleQFT_weakLocal

/-- The example really is nonconstant: its two-point function is not identically zero. -/
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

