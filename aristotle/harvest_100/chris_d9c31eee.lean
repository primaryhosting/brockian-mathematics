/-
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean 4 requires `import` to be the first command, so the header above is a plain
-- block comment; the identical module docstring is repeated below.)

import Mathlib

/-!
# Cpt Theorem
Category: Frontier Phys
Target: Phys.cpt_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped Real
open Matrix

namespace Phys

/-! ## The complexified Lorentz group

The mathematical heart of the CPT theorem (Jost's theorem) is the following fact: the total
inversion `-1` of Minkowski spacetime, which is *not* in the identity component of the real
Lorentz group, *is* reachable inside the **complex** Lorentz group `L(ℂ) = O(1,3;ℂ)`.  Indeed

  `diag(-1,-1,-1,-1) = diag(-1,-1,1,1) · diag(1,1,-1,-1)`,

where the second factor is the real rotation by `π` about the `x`-axis (an element of the
proper orthochronous group `L₊↑`) and the first factor is the value at rapidity `iπ` of the
family of boosts in the `(0,1)`–plane analytically continued to imaginary rapidity.

This is why a Lorentz-invariant theory whose Wightman functions possess the standard analytic
continuation in the boost parameter is automatically invariant under total inversion. -/

/-- The Minkowski metric `diag(1,-1,-1,-1)` on complexified spacetime `ℂ⁴`. -/
def minkowskiMetric : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.diagonal ![1, -1, -1, -1]

/-- The **proper complex Lorentz group** `L₊(ℂ)`: complex `4 × 4` matrices preserving the
Minkowski form and of determinant one. -/
def ProperComplexLorentz : Set (Matrix (Fin 4) (Fin 4) ℂ) :=
  {Λ | Λᵀ * minkowskiMetric * Λ = minkowskiMetric ∧ Λ.det = 1}

/-- The real Minkowski metric `diag(1,-1,-1,-1)`. -/
def minkowskiMetricReal : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, -1, -1, -1]

/-- The **proper orthochronous (real) Lorentz group** `L₊↑`: real Lorentz matrices with
determinant one that preserve the direction of time. -/
def ProperOrthochronousLorentz : Set (Matrix (Fin 4) (Fin 4) ℝ) :=
  {Λ | Λᵀ * minkowskiMetricReal * Λ = minkowskiMetricReal ∧ Λ.det = 1 ∧ 1 ≤ Λ 0 0}

/-! ### Complexified boosts in the `(0,1)`–plane -/

/-- The complexified boost in the `(0,1)`–plane with parameters `(c, s)`; for `c² + s² = 1`
this is a complex Lorentz transformation.  Taking `c = cosh ζ`, `s = -i sinh ζ` gives the
ordinary real boost of rapidity `ζ`, while `c = cos θ`, `s = sin θ` gives its analytic
continuation to the imaginary rapidity `iθ`. -/
def boost01 (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![c, Complex.I * s, 0, 0],
              ![Complex.I * s, c, 0, 0],
              ![0, 0, 1, 0],
              ![0, 0, 0, 1]]

theorem boost01_preserves_metric (c s : ℂ) (h : s ^ 2 + c ^ 2 = 1) :
    (boost01 c s)ᵀ * minkowskiMetric * boost01 c s = minkowskiMetric := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [boost01, minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply, Matrix.transpose_apply] <;>
    first
      | ring1
      | linear_combination h - s ^ 2 * hI
      | linear_combination -h + s ^ 2 * hI

theorem boost01_det (c s : ℂ) (h : s ^ 2 + c ^ 2 = 1) : (boost01 c s).det = 1 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have e : ((1 : Fin 4).succAbove (2 : Fin 3)) = 3 := by decide
  rw [show (boost01 c s).det = _ from Matrix.det_succ_row_zero _]
  simp [boost01, Matrix.det_fin_three, Fin.sum_univ_succ, e]
  linear_combination h - s ^ 2 * hI

theorem boost01_mem (c s : ℂ) (h : s ^ 2 + c ^ 2 = 1) :
    boost01 c s ∈ ProperComplexLorentz :=
  ⟨boost01_preserves_metric c s h, boost01_det c s h⟩

/-- The boost in the `(0,1)`–plane analytically continued to the **imaginary rapidity** `iθ`.
For real `θ` this is a genuine element of the complex Lorentz group, and `imagBoost 0 = 1`. -/
noncomputable def imagBoost (θ : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  boost01 ((Real.cos θ : ℝ) : ℂ) ((Real.sin θ : ℝ) : ℂ)

theorem imagBoost_mem (θ : ℝ) : imagBoost θ ∈ ProperComplexLorentz := by
  refine boost01_mem _ _ ?_
  have : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this

theorem imagBoost_zero : imagBoost 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [imagBoost, boost01]

/-- At imaginary rapidity `iπ` the boost becomes `diag(-1,-1,1,1)`: it inverts time together
with the `x`-axis. -/
theorem imagBoost_pi : imagBoost π = Matrix.diagonal ![-1, -1, 1, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [imagBoost, boost01]

/-! ### The rotation by `π` about the `x`-axis -/

/-- Rotation by `π` about the `x`-axis, `diag(1,1,-1,-1)`; a real proper orthochronous
Lorentz transformation. -/
def spaceRotationPi : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal ![1, 1, -1, -1]

theorem spaceRotationPi_mem : spaceRotationPi ∈ ProperOrthochronousLorentz := by
  refine ⟨?_, ?_, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [spaceRotationPi, minkowskiMetricReal, Matrix.mul_apply, Matrix.diagonal_apply]
  · rw [spaceRotationPi, Matrix.det_diagonal]
    simp [Fin.prod_univ_four]
  · simp [spaceRotationPi]

/-- **The factorisation underlying CPT.**  The total spacetime inversion is the product of the
imaginary-rapidity boost `imagBoost π` and the real rotation by `π` about the `x`-axis. -/
theorem imagBoost_pi_mul_spaceRotationPi :
    imagBoost π * spaceRotationPi.map (fun a : ℝ => (a : ℂ)) = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [imagBoost_pi, spaceRotationPi, Matrix.mul_apply, Matrix.diagonal_apply]

/-- Acting on a spacetime point, the imaginary boost at rapidity `iπ` followed by the rotation
by `π` is exactly the total inversion `x ↦ -x`. -/
theorem imagBoost_pi_spaceRotationPi_mulVec (v : Fin 4 → ℂ) :
    imagBoost π *ᵥ (spaceRotationPi.map (fun a : ℝ => (a : ℂ)) *ᵥ v) = -v := by
  rw [Matrix.mulVec_mulVec, imagBoost_pi_mul_spaceRotationPi, Matrix.neg_mulVec,
    Matrix.one_mulVec]

/-! ### Jost's lemma: `-1` lies in the identity component of `L₊(ℂ)`

The factorisation above is the computational core.  The following two results record its
geometric meaning: the total inversion is a proper complex Lorentz transformation, and it is
connected to the identity *inside* the complex Lorentz group — which is false for the real
Lorentz group. -/

/-- The `(0,1)`–boost and `(2,3)`–rotation combined into a single one-parameter family, used
to connect `1` to `-1` inside `L₊(ℂ)`. -/
def cptFamily (c s : ℂ) : Matrix (Fin 4) (Fin 4) ℂ :=
  Matrix.of ![![c, Complex.I * s, 0, 0],
              ![Complex.I * s, c, 0, 0],
              ![0, 0, c, -s],
              ![0, 0, s, c]]

theorem cptFamily_preserves_metric (c s : ℂ) (h : s ^ 2 + c ^ 2 = 1) :
    (cptFamily c s)ᵀ * minkowskiMetric * cptFamily c s = minkowskiMetric := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [cptFamily, minkowskiMetric, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.diagonal_apply, Matrix.transpose_apply] <;>
    first
      | ring1
      | linear_combination h - s ^ 2 * hI
      | linear_combination -h + s ^ 2 * hI
      | linear_combination -h

theorem cptFamily_det (c s : ℂ) (h : s ^ 2 + c ^ 2 = 1) : (cptFamily c s).det = 1 := by
  have hI : Complex.I ^ 2 = -1 := Complex.I_sq
  have e : ((1 : Fin 4).succAbove (2 : Fin 3)) = 3 := by decide
  rw [show (cptFamily c s).det = _ from Matrix.det_succ_row_zero _]
  simp [cptFamily, Matrix.det_fin_three, Fin.sum_univ_succ, e]
  linear_combination (c ^ 2 + s ^ 2) * h - s ^ 2 * (s ^ 2 + c ^ 2) * hI + h

theorem cptFamily_mem (c s : ℂ) (h : s ^ 2 + c ^ 2 = 1) :
    cptFamily c s ∈ ProperComplexLorentz :=
  ⟨cptFamily_preserves_metric c s h, cptFamily_det c s h⟩

theorem cptFamily_one_zero : cptFamily 1 0 = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptFamily]

theorem cptFamily_negOne_zero : cptFamily (-1) 0 = -1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [cptFamily]

/-- The total inversion of spacetime is a proper complex Lorentz transformation. -/
theorem negOne_mem_properComplexLorentz :
    (-1 : Matrix (Fin 4) (Fin 4) ℂ) ∈ ProperComplexLorentz := by
  have := cptFamily_mem (-1) 0 (by norm_num)
  rwa [cptFamily_negOne_zero] at this

theorem continuous_cptPath :
    Continuous fun t : ℝ =>
      cptFamily ((Real.cos (π * t) : ℝ) : ℂ) ((Real.sin (π * t) : ℝ) : ℂ) := by
  apply continuous_matrix
  intro i j
  fin_cases i <;> fin_cases j <;> simp only [cptFamily, Matrix.of_apply] <;> norm_num <;>
    fun_prop

/-- **Jost's key lemma.**  The total spacetime inversion `-1` can be joined to the identity by
a continuous path lying entirely inside the proper complex Lorentz group. -/
theorem joinedIn_one_negOne :
    JoinedIn ProperComplexLorentz 1 (-1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  refine ⟨⟨⟨fun t => cptFamily ((Real.cos (π * (t : ℝ)) : ℝ) : ℂ)
      ((Real.sin (π * (t : ℝ)) : ℝ) : ℂ),
      continuous_cptPath.comp continuous_subtype_val⟩, ?_, ?_⟩, ?_⟩
  · simp [cptFamily_one_zero]
  · simp [cptFamily_negOne_zero]
  · intro t
    refine cptFamily_mem _ _ ?_
    have : Real.sin (π * (t : ℝ)) ^ 2 + Real.cos (π * (t : ℝ)) ^ 2 = 1 :=
      Real.sin_sq_add_cos_sq _
    exact_mod_cast congrArg (fun x : ℝ => (x : ℂ)) this

/-! ## Wightman theories and the CPT theorem -/

/-- A point of complexified Minkowski spacetime. -/
abbrev CPoint := Fin 4 → ℂ

/-- A **Lorentz-invariant local quantum field theory**, presented through its `n`-point
Wightman function `W`, analytically continued to complexified Minkowski spacetime.

The three axioms are the standard ingredients of the Wightman formulation of the CPT theorem:

* `lorentz_invariance` — relativistic invariance: `W` is invariant under the real proper
  orthochronous Lorentz group `L₊↑`;
* `boost_analytic_continuation` — the consequence of the spectral condition: the invariance
  of `W` under boosts in the `(0,1)`–plane persists after analytic continuation of the
  rapidity to imaginary values (this is the one-parameter core of the Bargmann–Hall–Wightman
  analyticity argument);
* `weak_local_commutativity` — locality in Jost's form: `W` is unchanged when the order of its
  arguments is reversed. -/
structure LorentzInvariantLocalQFT (n : ℕ) where
  /-- The `n`-point Wightman function, analytically continued to complex arguments. -/
  W : (Fin n → CPoint) → ℂ
  /-- Relativistic invariance under the real proper orthochronous Lorentz group `L₊↑`. -/
  lorentz_invariance :
    ∀ Λ ∈ ProperOrthochronousLorentz, ∀ x : Fin n → CPoint,
      W (fun i => (Λ.map (fun a : ℝ => (a : ℂ))) *ᵥ x i) = W x
  /-- Invariance under `(0,1)`–boosts continued to imaginary rapidity. -/
  boost_analytic_continuation :
    ∀ θ : ℝ, ∀ x : Fin n → CPoint, W (fun i => imagBoost θ *ᵥ x i) = W x
  /-- Weak local commutativity (locality). -/
  weak_local_commutativity :
    ∀ x : Fin n → CPoint, W (fun i => x (Fin.rev i)) = W x

/-- **The CPT theorem.**  In any Lorentz-invariant local quantum field theory the Wightman
functions are invariant under the CPT transformation: total inversion of all spacetime
arguments combined with reversal of their order,

  `W(-x_n, …, -x₁) = W(x₁, …, x_n)`.

The proof factors the total inversion as an imaginary-rapidity boost times a real rotation by
`π`, applies relativistic invariance to the rotation and the analytic continuation to the
boost, and finally uses weak local commutativity to undo the reversal of the arguments. -/
theorem cpt_theorem {n : ℕ} (T : LorentzInvariantLocalQFT n) (x : Fin n → CPoint) :
    T.W (fun i => -x (Fin.rev i)) = T.W x := by
  set R : Matrix (Fin 4) (Fin 4) ℂ := spaceRotationPi.map (fun a : ℝ => (a : ℂ)) with hR
  have hboost := T.boost_analytic_continuation π (fun i => R *ᵥ x (Fin.rev i))
  have hrot := T.lorentz_invariance spaceRotationPi spaceRotationPi_mem
    (fun i => x (Fin.rev i))
  have hinv : ∀ i, imagBoost π *ᵥ (R *ᵥ x (Fin.rev i)) = -x (Fin.rev i) := fun i =>
    imagBoost_pi_spaceRotationPi_mulVec _
  simp only [hinv] at hboost
  rw [hboost, hR, hrot, T.weak_local_commutativity]

/-- The axioms above are consistent: constant Wightman functions satisfy all three of them, so
`cpt_theorem` is not vacuously true. -/
def constantQFT (n : ℕ) (z : ℂ) : LorentzInvariantLocalQFT n where
  W := fun _ => z
  lorentz_invariance := by intro _ _ _; rfl
  boost_analytic_continuation := by intro _ _; rfl
  weak_local_commutativity := by intro _; rfl

instance (n : ℕ) : Nonempty (LorentzInvariantLocalQFT n) := ⟨constantQFT n 0⟩

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

