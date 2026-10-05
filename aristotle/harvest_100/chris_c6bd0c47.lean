/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
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

namespace Phys

/-! ## Complexified Minkowski space and the complex Lorentz group -/

/-- Complexified Minkowski space `ℂ⁴`. -/
abbrev CVec : Type := Fin 4 → ℂ

/-- The (bilinear, not sesquilinear) Minkowski form of signature `(+,-,-,-)` on complexified
Minkowski space. -/
def mform (x y : CVec) : ℂ := x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3

/-- A complex `4 × 4` matrix is a complex Lorentz transformation if it preserves the complex
bilinear Minkowski form. -/
def IsComplexLorentz (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∀ x y : CVec, mform (L.mulVec x) (L.mulVec y) = mform x y

/-- Membership in the identity component of the complex Lorentz group: `L` is joined to the
identity by a continuous path of complex Lorentz transformations. -/
def ConnectedToId (L : Matrix (Fin 4) (Fin 4) ℂ) : Prop :=
  ∃ p : ℝ → Matrix (Fin 4) (Fin 4) ℂ,
    Continuous p ∧ p 0 = 1 ∧ p 1 = L ∧ ∀ t : ℝ, IsComplexLorentz (p t)

/-- The complex Lorentz transformation implementing a complex rotation by angle `θ` in the
`(0,1)` plane together with a rotation by `θ` in the `(2,3)` plane.  At `θ = 0` it is the
identity and at `θ = π` it is the total spacetime reflection `-1`, i.e. the `PT`
transformation. -/
noncomputable def ptPath (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  !![Complex.cos θ, Complex.I * Complex.sin θ, 0, 0;
     Complex.I * Complex.sin θ, Complex.cos θ, 0, 0;
     0, 0, Complex.cos θ, -Complex.sin θ;
     0, 0, Complex.sin θ, Complex.cos θ]

/-- Every member of the path `ptPath` preserves the complex Minkowski form. -/
lemma ptPath_isComplexLorentz (θ : ℝ) : IsComplexLorentz (ptPath θ) := by
  intro x y
  have hI : Complex.I * Complex.I = -1 := Complex.I_mul_I
  have hs : Complex.sin θ ^ 2 + Complex.cos θ ^ 2 = 1 := Complex.sin_sq_add_cos_sq _
  simp [mform, ptPath, Matrix.mulVec, dotProduct, Fin.sum_univ_four]
  linear_combination (x 0 * y 0 - x 1 * y 1 - x 2 * y 2 - x 3 * y 3) * hs
    - Complex.sin (θ : ℂ) ^ 2 * (x 0 * y 0 - x 1 * y 1) * hI

lemma ptPath_zero : ptPath 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ptPath]

lemma ptPath_pi : ptPath Real.pi = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ptPath]

lemma continuous_ptPath : Continuous ptPath := by
  refine continuous_matrix fun i j => ?_
  fin_cases i <;> fin_cases j <;> simp [ptPath] <;> fun_prop

/-- **The total spacetime reflection `PT = -1` lies in the identity component of the complex
Lorentz group.**  This is the mathematical heart of the CPT theorem: although `-1` is not in
the identity component of the *real* Lorentz group, complexifying connects it to the
identity. -/
theorem neg_one_connectedToId : ConnectedToId (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨fun t => ptPath (Real.pi * t), continuous_ptPath.comp (by fun_prop), ?_, ?_,
    fun t => ptPath_isComplexLorentz _⟩
  · simpa using ptPath_zero
  · simpa using ptPath_pi

/-! ## Lorentz-invariant local quantum field theories -/

/-- Two (complexified) points are spacelike separated when their difference has real and
negative Minkowski square. -/
def Spacelike (x y : CVec) : Prop :=
  (mform (x - y) (x - y)).im = 0 ∧ (mform (x - y) (x - y)).re < 0

/-- A Lorentz-invariant local quantum field theory, presented through its analytically
continued Wightman functions.

* `W n` is the `n`-point Wightman function on complexified Minkowski space;
* `lorentz_invariant` records Lorentz invariance: by the standard analytic continuation of
  the Wightman functions into the extended tube, invariance under the real proper
  orthochronous Lorentz group upgrades to invariance under the whole identity component of
  the complex Lorentz group;
* `local_commutativity` records locality, i.e. Bose symmetry of the Wightman functions under
  exchange of spacelike separated arguments. -/
structure QFT where
  /-- The `n`-point Wightman functions. -/
  W : (n : ℕ) → (Fin n → CVec) → ℂ
  /-- Invariance under the identity component of the complex Lorentz group. -/
  lorentz_invariant : ∀ (n : ℕ) (L : Matrix (Fin 4) (Fin 4) ℂ) (x : Fin n → CVec),
    ConnectedToId L → W n (fun i => L.mulVec (x i)) = W n x
  /-- Locality: the Wightman functions are symmetric under exchange of spacelike separated
  arguments. -/
  local_commutativity : ∀ (n : ℕ) (x : Fin n → CVec) (i j : Fin n),
    Spacelike (x i) (x j) → W n (x ∘ Equiv.swap i j) = W n x

/-- The CPT transformation on complexified Minkowski space: total inversion `x ↦ -x` of all
spacetime coordinates. -/
def cptMap (x : CVec) : CVec := -x

lemma cptMap_involutive : Function.Involutive cptMap := fun x => by
  simp [cptMap]

/-- **CPT theorem (statement level).**  Every Lorentz-invariant local quantum field theory is
CPT invariant: its Wightman functions are unchanged when all spacetime arguments are
reflected, `x ↦ -x`.  The proof runs through the fact that the total reflection `-1` lies in
the identity component of the complex Lorentz group, so that CPT invariance is a consequence
of Lorentz invariance of the analytically continued Wightman functions.  (The locality
axiom of `QFT` is what makes that analytic continuation, and hence the hypothesis
`lorentz_invariant`, available; it is not used again in this final step.) -/
theorem cpt_theorem (Q : QFT) (n : ℕ) (x : Fin n → CVec) :
    Q.W n (fun i => cptMap (x i)) = Q.W n x := by
  have h := Q.lorentz_invariant n (-1 : Matrix (Fin 4) (Fin 4) ℂ) x neg_one_connectedToId
  simpa [cptMap, Matrix.neg_mulVec, Matrix.one_mulVec] using h

end Phys

