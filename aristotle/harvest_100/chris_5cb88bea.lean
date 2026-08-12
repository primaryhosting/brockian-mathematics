/-
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Spin Statistics
Category: Frontier Physics
Target: Frontier.spin_statistics
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexConjugate
open scoped InnerProductSpace

namespace Frontier

/-! ## Minkowski geometry -/

/-- The Minkowski bilinear form on `ℝ⁴` with signature `(+,-,-,-)`. -/
def minkowskiForm (x y : Fin 4 → ℝ) : ℝ :=
  x 0 * y 0 - (x 1 * y 1 + x 2 * y 2 + x 3 * y 3)

/-- Two spacetime points are spacelike separated when their difference has
negative Minkowski square. -/
def Spacelike (x y : Fin 4 → ℝ) : Prop :=
  minkowskiForm (x - y) (x - y) < 0

/-- Two regions of spacetime are spacelike separated when every point of the first
is spacelike separated from every point of the second. -/
def SpacelikeSeparated (A B : Set (Fin 4 → ℝ)) : Prop :=
  ∀ x ∈ A, ∀ y ∈ B, Spacelike x y

/-! ## Statistics -/

/-- The two possible statistics of a relativistic field. -/
inductive Statistics
  | bose
  | fermi
  deriving DecidableEq, Repr

/-- The commutation sign attached to a statistics: `+1` for bosons (commutators),
`-1` for fermions (anticommutators). -/
def Statistics.sign : Statistics → ℂ
  | .bose => 1
  | .fermi => -1

/-- The statistics predicted by the spin–statistics connection for a field of
spin `s`, where `twiceSpin = 2s`: integer spin is Bose, half-integer spin is Fermi. -/
def statisticsOfSpin (twiceSpin : ℕ) : Statistics :=
  if Even twiceSpin then Statistics.bose else Statistics.fermi

theorem statisticsOfSpin_sign (n : ℕ) : (statisticsOfSpin n).sign = (-1 : ℂ) ^ n := by
  unfold statisticsOfSpin
  by_cases h : Even n
  · rw [if_pos h, Statistics.sign, h.neg_one_pow]
  · rw [if_neg h, Statistics.sign, (Nat.not_even_iff_odd.1 h).neg_one_pow]

theorem Statistics.eq_of_sign_eq {a b : Statistics} (h : a.sign = b.sign) : a = b := by
  cases a <;> cases b <;> first
    | rfl
    | (exfalso; simp [Statistics.sign] at h; norm_num at h)

/-! ## Wightman-type field data

A `WightmanField` packages the structural input of the spin–statistics theorem in the
Wightman framework: a Hilbert space of states with a vacuum vector, a family of smeared
field operators indexed by test functions together with their adjoints and (spacetime)
supports, a spin and a statistics, and the following properties.

* `locality` : at spacelike separation the fields obey the (anti)commutation relation
  dictated by their statistics.
* `jost` : *weak local commutativity*. At spacelike separation (Jost points) the analytic
  continuation of the two-point function relates the two orderings by the factor
  `(-1)^{2s}`.  This is the consequence of Lorentz covariance (equivalently PCT) and of
  the analyticity of the Wightman functions in the extended tube.
* `analytic` : *uniqueness of analytic continuation*. If the two-point function
  `⟪Ω, φ(g)^* φ(f) Ω⟫` vanishes for all spacelike separated configurations, then it
  vanishes identically, in particular at coincident arguments.
* `separating` : *Reeh–Schlieder*. The vacuum is separating for the field operators.
-/
structure WightmanField (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (TF : Type*) where
  /-- The spacetime support of a smeared field. -/
  supp : TF → Set (Fin 4 → ℝ)
  /-- The smeared field operator. -/
  field : TF → (H →L[ℂ] H)
  /-- The adjoint of the smeared field operator. -/
  fieldAdj : TF → (H →L[ℂ] H)
  /-- `fieldAdj f` is the adjoint of `field f`. -/
  adj_spec : ∀ f x y, ⟪fieldAdj f x, y⟫_ℂ = ⟪x, field f y⟫_ℂ
  /-- The vacuum vector. -/
  vacuum : H
  /-- Twice the spin of the field. -/
  twiceSpin : ℕ
  /-- The statistics with which the field is quantized. -/
  stat : Statistics
  /-- Locality: the fields (anti)commute at spacelike separation according to `stat`. -/
  locality : ∀ f g, SpacelikeSeparated (supp f) (supp g) →
      (field f) ∘L (fieldAdj g) = stat.sign • ((fieldAdj g) ∘L (field f))
  /-- Weak local commutativity at Jost points, from Lorentz covariance. -/
  jost : ∀ f g, SpacelikeSeparated (supp f) (supp g) →
      ⟪vacuum, (field f) (fieldAdj g vacuum)⟫_ℂ
        = (-1 : ℂ) ^ twiceSpin * ⟪vacuum, (fieldAdj g) (field f vacuum)⟫_ℂ
  /-- Uniqueness of analytic continuation for the two-point function. -/
  analytic : (∀ f g, SpacelikeSeparated (supp f) (supp g) →
        ⟪vacuum, (fieldAdj g) (field f vacuum)⟫_ℂ = 0) →
      ∀ f, ⟪vacuum, (fieldAdj f) (field f vacuum)⟫_ℂ = 0
  /-- Reeh–Schlieder: the vacuum is separating. -/
  separating : ∀ f, field f vacuum = 0 → field f = 0

namespace WightmanField

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {TF : Type*}
  (Φ : WightmanField H TF)

/-- Positivity: the vacuum expectation value `⟪Ω, φ(f)^* φ(f) Ω⟫` is the squared norm of
`φ(f) Ω`. -/
theorem vev_normalOrder (f : TF) :
    ⟪Φ.vacuum, (Φ.fieldAdj f) (Φ.field f Φ.vacuum)⟫_ℂ
      = (‖Φ.field f Φ.vacuum‖ : ℂ) ^ 2 := by
  have h := Φ.adj_spec f (Φ.field f Φ.vacuum) Φ.vacuum
  have h2 : ⟪Φ.vacuum, (Φ.fieldAdj f) (Φ.field f Φ.vacuum)⟫_ℂ
      = conj ⟪(Φ.fieldAdj f) (Φ.field f Φ.vacuum), Φ.vacuum⟫_ℂ := by
    rw [← inner_conj_symm]
  rw [h2, h, inner_self_eq_norm_sq_to_K]
  simp

/-- The vacuum expectation value of the `ε`-(anti)commutator, evaluated using locality. -/
theorem vev_locality {f g : TF} (h : SpacelikeSeparated (Φ.supp f) (Φ.supp g)) :
    ⟪Φ.vacuum, (Φ.field f) (Φ.fieldAdj g Φ.vacuum)⟫_ℂ
      = Φ.stat.sign * ⟪Φ.vacuum, (Φ.fieldAdj g) (Φ.field f Φ.vacuum)⟫_ℂ := by
  have := congrArg (fun A : H →L[ℂ] H => A Φ.vacuum) (Φ.locality f g h)
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_smul', Pi.smul_apply] at this
  rw [this, inner_smul_right]

/-- **Wrong statistics forces triviality.**  If a field of spin `s` is quantized with the
statistics *opposite* to the one predicted by the spin–statistics connection, then all its
smeared field operators vanish. -/
theorem trivial_of_wrong_statistics (hwrong : Φ.stat ≠ statisticsOfSpin Φ.twiceSpin)
    (f : TF) : Φ.field f = 0 := by
  -- The sign of the actual statistics differs from `(-1)^{2s}`.
  have hsign : Φ.stat.sign ≠ (-1 : ℂ) ^ Φ.twiceSpin := by
    intro h
    exact hwrong (Statistics.eq_of_sign_eq (by rw [h, statisticsOfSpin_sign]))
  -- Locality plus weak local commutativity kill the two-point function at spacelike
  -- separation.
  have hvanish : ∀ f g : TF, SpacelikeSeparated (Φ.supp f) (Φ.supp g) →
      ⟪Φ.vacuum, (Φ.fieldAdj g) (Φ.field f Φ.vacuum)⟫_ℂ = 0 := by
    intro f g h
    have h1 := Φ.vev_locality h
    have h2 := Φ.jost f g h
    have h3 : (Φ.stat.sign - (-1 : ℂ) ^ Φ.twiceSpin)
        * ⟪Φ.vacuum, (Φ.fieldAdj g) (Φ.field f Φ.vacuum)⟫_ℂ = 0 := by
      rw [sub_mul, ← h1, ← h2, sub_self]
    rcases mul_eq_zero.1 h3 with h4 | h4
    · exact absurd (sub_eq_zero.1 h4) hsign
    · exact h4
  -- Analytic continuation to coincident arguments, then positivity.
  have hzero := Φ.analytic hvanish f
  rw [Φ.vev_normalOrder f] at hzero
  have : ‖Φ.field f Φ.vacuum‖ = 0 := by
    have : ((‖Φ.field f Φ.vacuum‖ : ℂ)) ^ 2 = 0 := hzero
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    exact_mod_cast this
  exact Φ.separating f (by simpa using norm_eq_zero.1 this)

end WightmanField

/-- **The spin–statistics connection.**  A relativistic quantum field satisfying the
Wightman-type axioms packaged in `WightmanField` — locality with respect to its statistics,
weak local commutativity at Jost points, analyticity of the two-point function, and the
Reeh–Schlieder property of the vacuum — which is not identically zero must be quantized
with the statistics dictated by its spin: integer spin fields are bosons (they commute at
spacelike separation) and half-integer spin fields are fermions (they anticommute). -/
theorem spin_statistics {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    {TF : Type*} (Φ : WightmanField H TF) (hnontrivial : ∃ f, Φ.field f ≠ 0) :
    Φ.stat = statisticsOfSpin Φ.twiceSpin := by
  by_contra hwrong
  obtain ⟨f, hf⟩ := hnontrivial
  exact hf (Φ.trivial_of_wrong_statistics hwrong f)

/-! ## Non-vacuity

We exhibit a model of the axioms carrying a nonzero field, so that the hypotheses of
`Frontier.spin_statistics` are consistent and the theorem is not vacuous.  The model has
one-dimensional state space `ℂ`, test functions indexed by spacetime points, and the
identity operator as field; it is a spin-`0`, Bose model.
-/

/-- Two distinct points of a spacelike hyperplane are spacelike separated. -/
theorem spacelike_example :
    Spacelike (fun _ => 0) (fun i => if i = 1 then 1 else 0) := by
  norm_num [Spacelike, minkowskiForm, show (3 : Fin 4) ≠ 1 by decide,
    show (2 : Fin 4) ≠ 1 by decide]

/-- A nontrivial model of the axioms: spin `0`, Bose statistics, nonzero field. -/
def boseModel : WightmanField ℂ (Fin 4 → ℝ) where
  supp x := {x}
  field _ := ContinuousLinearMap.id ℂ ℂ
  fieldAdj _ := ContinuousLinearMap.id ℂ ℂ
  adj_spec _ _ _ := rfl
  vacuum := 1
  twiceSpin := 0
  stat := Statistics.bose
  locality _ _ _ := by simp [Statistics.sign]
  jost _ _ _ := by simp
  analytic h := by
    exfalso
    have := h (fun _ => 0) (fun i => if i = 1 then 1 else 0)
      (by rintro x rfl y rfl; exact spacelike_example)
    simp at this
  separating _ h := by
    exfalso
    simpa using congrArg (fun z : ℂ => z) h

theorem boseModel_nontrivial :
    ∃ f, boseModel.field f ≠ 0 := by
  refine ⟨fun _ => 0, ?_⟩
  intro h
  have := congrArg (fun A : ℂ →L[ℂ] ℂ => A 1) h
  simp [boseModel] at this

/-- In the model, the statistics is indeed the one predicted by the spin. -/
theorem boseModel_statistics :
    boseModel.stat = statisticsOfSpin boseModel.twiceSpin :=
  spin_statistics boseModel boseModel_nontrivial

/-! ### A nontrivial fermionic model

We also exhibit a *fermionic* model (`twiceSpin = 1`, Fermi statistics) with a nonzero
field, so that the axioms are consistent for half-integer spin as well.  The state space is
`ℂ²`, the field at a point `x` is the operator with matrix `!![0, d x; c x, 0]`, and the
coefficient functions `c`, `d` are supported on two timelike lines, chosen so that the
coefficient vectors at spacelike separated points are orthogonal.
-/

namespace FermiModel

open Matrix

/-- The two-dimensional state space of the model. -/
abbrev Hf := EuclideanSpace ℂ (Fin 2)

/-- The operator on `ℂ²` attached to a `2 × 2` matrix. -/
noncomputable def op (M : Matrix (Fin 2) (Fin 2) ℂ) : Hf →L[ℂ] Hf :=
  Matrix.toEuclideanCLM (𝕜 := ℂ) M

theorem op_adj (M : Matrix (Fin 2) (Fin 2) ℂ) (x y : Hf) :
    ⟪op Mᴴ x, y⟫_ℂ = ⟪x, op M y⟫_ℂ := by
  have h : op Mᴴ = ContinuousLinearMap.adjoint (op M) := by
    rw [op, op, ← ContinuousLinearMap.star_eq_adjoint, ← map_star]
    rfl
  rw [h, ContinuousLinearMap.adjoint_inner_left]

theorem op_comp (M N : Matrix (Fin 2) (Fin 2) ℂ) : op M ∘L op N = op (M * N) := by
  rw [op, op, op, ← ContinuousLinearMap.mul_def, ← map_mul]

theorem op_neg (M : Matrix (Fin 2) (Fin 2) ℂ) : op (-M) = - op M := by
  rw [op, op, map_neg]

theorem op_entry (M : Matrix (Fin 2) (Fin 2) ℂ) (i j : Fin 2) :
    ⟪(EuclideanSpace.single i (1 : ℂ)), (op M) (EuclideanSpace.single j (1 : ℂ))⟫_ℂ = M i j := by
  rw [EuclideanSpace.inner_single_left]
  simp [op, Matrix.mulVec, dotProduct]

theorem op_injective {M : Matrix (Fin 2) (Fin 2) ℂ} (h : op M = 0) : M = 0 := by
  ext i j
  have hij := op_entry M i j
  rw [h] at hij
  simpa using hij.symm

/-- The vacuum vector. -/
noncomputable def vac : Hf := EuclideanSpace.single 0 (1 : ℂ)

/-- The first coefficient function: `1` on the two chosen timelike lines, `0` elsewhere. -/
noncomputable def cCoeff (x : Fin 4 → ℝ) : ℂ :=
  if x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 then 1
  else if x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0 then 1 else 0

/-- The second coefficient function: `1` on the first line, `-1` on the second, `0`
elsewhere. -/
noncomputable def dCoeff (x : Fin 4 → ℝ) : ℂ :=
  if x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 then 1
  else if x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0 then -1 else 0

/-- The matrix of the field at a spacetime point. -/
noncomputable def fieldMat (x : Fin 4 → ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![0, dCoeff x; cCoeff x, 0]

/-- Points with equal spatial coordinates are never spacelike separated. -/
theorem not_spacelike_of_spatial_eq {x y : Fin 4 → ℝ}
    (h1 : x 1 = y 1) (h2 : x 2 = y 2) (h3 : x 3 = y 3) : ¬ Spacelike x y := by
  simp only [Spacelike, minkowskiForm, Pi.sub_apply, h1, h2, h3, not_lt]
  nlinarith [sq_nonneg (x 0 - y 0)]

/-- The coefficient vectors at spacelike separated points are orthogonal. -/
theorem coeff_orthogonal {x y : Fin 4 → ℝ} (h : Spacelike x y) :
    cCoeff x * conj (cCoeff y) + dCoeff x * conj (dCoeff y) = 0 := by
  unfold cCoeff dCoeff
  by_cases hx1 : x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0 <;>
    by_cases hx2 : x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0 <;>
    by_cases hy1 : y 1 = 0 ∧ y 2 = 0 ∧ y 3 = 0 <;>
    by_cases hy2 : y 1 = 1 ∧ y 2 = 0 ∧ y 3 = 0 <;>
    simp only [hx1, hx2, hy1, hy2, if_false] <;>
    first
      | (exact absurd h (not_spacelike_of_spatial_eq (by rw [hx1.1, hy1.1])
          (by rw [hx1.2.1, hy1.2.1]) (by rw [hx1.2.2, hy1.2.2])))
      | (exact absurd h (not_spacelike_of_spatial_eq (by rw [hx2.1, hy2.1])
          (by rw [hx2.2.1, hy2.2.1]) (by rw [hx2.2.2, hy2.2.2])))
      | norm_num

theorem fieldMat_conjTranspose (x : Fin 4 → ℝ) :
    (fieldMat x)ᴴ = !![0, conj (cCoeff x); conj (dCoeff x), 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [fieldMat]

theorem fieldMat_mul_adj (x y : Fin 4 → ℝ) :
    fieldMat x * (fieldMat y)ᴴ
      = !![dCoeff x * conj (dCoeff y), 0; 0, cCoeff x * conj (cCoeff y)] := by
  rw [fieldMat_conjTranspose, fieldMat, Matrix.mul_fin_two]
  norm_num

theorem adj_mul_fieldMat (x y : Fin 4 → ℝ) :
    (fieldMat y)ᴴ * fieldMat x
      = !![conj (cCoeff y) * cCoeff x, 0; 0, conj (dCoeff y) * dCoeff x] := by
  rw [fieldMat_conjTranspose, fieldMat, Matrix.mul_fin_two]
  norm_num

/-- At spacelike separation the matrices of the model anticommute. -/
theorem fieldMat_anticomm {x y : Fin 4 → ℝ} (h : Spacelike x y) :
    fieldMat x * (fieldMat y)ᴴ + (fieldMat y)ᴴ * fieldMat x = 0 := by
  have ho := coeff_orthogonal h
  rw [fieldMat_mul_adj, adj_mul_fieldMat]
  ext i j
  fin_cases i <;> fin_cases j <;> simp <;> linear_combination ho

theorem vev_op (M : Matrix (Fin 2) (Fin 2) ℂ) : ⟪vac, (op M) vac⟫_ℂ = M 0 0 :=
  op_entry M 0 0

theorem dCoeff_eq_zero_of_cCoeff_eq_zero {x : Fin 4 → ℝ} (h : cCoeff x = 0) : dCoeff x = 0 := by
  unfold cCoeff at h
  unfold dCoeff
  by_cases h1 : x 1 = 0 ∧ x 2 = 0 ∧ x 3 = 0
  · rw [if_pos h1] at h; norm_num at h
  · by_cases h2 : x 1 = 1 ∧ x 2 = 0 ∧ x 3 = 0
    · rw [if_neg h1, if_pos h2] at h; norm_num at h
    · rw [if_neg h1, if_neg h2]

/-- A nontrivial model of the Wightman-type axioms with `twiceSpin = 1` and Fermi
statistics. -/
noncomputable def fermiModel : WightmanField Hf (Fin 4 → ℝ) where
  supp x := {x}
  field x := op (fieldMat x)
  fieldAdj x := op ((fieldMat x)ᴴ)
  adj_spec x u v := op_adj (fieldMat x) u v
  vacuum := vac
  twiceSpin := 1
  stat := Statistics.fermi
  locality x y h := by
    have ha := fieldMat_anticomm (h x rfl y rfl)
    have key : fieldMat x * (fieldMat y)ᴴ = -((fieldMat y)ᴴ * fieldMat x) :=
      eq_neg_of_add_eq_zero_left ha
    rw [op_comp, op_comp, Statistics.sign, neg_one_smul, key, op_neg]
  jost x y h := by
    have ho := coeff_orthogonal (h x rfl y rfl)
    have h1 : (op (fieldMat x)) ((op ((fieldMat y)ᴴ)) vac)
        = (op (fieldMat x * (fieldMat y)ᴴ)) vac := by
      rw [← op_comp]; rfl
    have h2 : (op ((fieldMat y)ᴴ)) ((op (fieldMat x)) vac)
        = (op ((fieldMat y)ᴴ * fieldMat x)) vac := by
      rw [← op_comp]; rfl
    rw [h1, h2, vev_op, vev_op, fieldMat_mul_adj, adj_mul_fieldMat]
    norm_num
    linear_combination ho
  analytic h := by
    exfalso
    have hx : cCoeff (fun _ => (0 : ℝ)) = 1 := by norm_num [cCoeff]
    have hy : cCoeff (fun i => if i = 1 then (1 : ℝ) else 0) = 1 := by
      norm_num [cCoeff, show (3 : Fin 4) ≠ 1 by decide, show (2 : Fin 4) ≠ 1 by decide]
    have hval := h (fun _ => (0 : ℝ)) (fun i => if i = 1 then 1 else 0)
      (by rintro u rfl v rfl; exact spacelike_example)
    have h2 : (op ((fieldMat (fun i => if i = 1 then (1 : ℝ) else 0))ᴴ))
        ((op (fieldMat (fun _ => (0 : ℝ)))) vac)
        = (op ((fieldMat (fun i => if i = 1 then (1 : ℝ) else 0))ᴴ
            * fieldMat (fun _ => (0 : ℝ)))) vac := by
      rw [← op_comp]; rfl
    rw [h2, vev_op, adj_mul_fieldMat] at hval
    norm_num [hx, hy] at hval
  separating x h := by
    have hc : cCoeff x = 0 := by
      have hentry := op_entry (fieldMat x) 1 0
      rw [show (EuclideanSpace.single 0 (1 : ℂ) : Hf) = vac from rfl, h] at hentry
      simp only [inner_zero_right] at hentry
      simpa [fieldMat] using hentry.symm
    have hd : dCoeff x = 0 := dCoeff_eq_zero_of_cCoeff_eq_zero hc
    have hM : fieldMat x = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [fieldMat, hc, hd]
    rw [show op (fieldMat x) = op 0 by rw [hM], op, map_zero]

theorem fermiModel_nontrivial : ∃ f, fermiModel.field f ≠ 0 := by
  refine ⟨fun _ => (0 : ℝ), ?_⟩
  intro hzero
  have hM : fieldMat (fun _ => (0 : ℝ)) = 0 := op_injective hzero
  have hentry := congrFun (congrFun hM 1) 0
  simp [fieldMat, cCoeff] at hentry

/-- The fermionic model has spin `1/2` and, in accordance with the spin–statistics
connection, Fermi statistics. -/
theorem fermiModel_statistics :
    fermiModel.stat = statisticsOfSpin fermiModel.twiceSpin :=
  spin_statistics fermiModel fermiModel_nontrivial

end FermiModel

end Frontier

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

