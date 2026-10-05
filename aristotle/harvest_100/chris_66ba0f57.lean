import Mathlib

/-!
# Class Number Formula
Category: Frontier Math
Target: Math2.class_number_formula
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Math2

open Filter Topology NumberField NumberField.InfinitePlace NumberField.Units

/--
**The analytic class number formula (Dirichlet class number formula).**

For a number field `K`, the Dedekind zeta function `ζ_K` has a simple pole at `s = 1` whose
residue is
`(2 ^ r₁ * (2π) ^ r₂ * R_K * h_K) / (w_K * √|d_K|)`,
where `r₁` (resp. `r₂`) is the number of real (resp. complex) places of `K`, `R_K` is the
regulator, `h_K` the class number, `w_K` the number of roots of unity in `K` and `d_K` the
discriminant.  This is expressed as the limit of `(s - 1) * ζ_K(s)` as `s → 1⁺` along the reals.
-/
theorem class_number_formula (K : Type*) [Field K] [NumberField K] :
    Tendsto (fun s : ℝ ↦ (s - 1) * NumberField.dedekindZeta K s) (𝓝[>] 1)
      (𝓝 ((2 ^ nrRealPlaces K * (2 * Real.pi) ^ nrComplexPlaces K *
            NumberField.Units.regulator K * NumberField.classNumber K) /
          (NumberField.Units.torsionOrder K * Real.sqrt |NumberField.discr K|))) := by
  simpa [NumberField.dedekindZeta_residue_def] using
    NumberField.tendsto_sub_one_mul_dedekindZeta_nhdsGT K

/-! ### A concrete instance: the field `ℚ` -/

open NumberField.Units.dirichletUnitTheorem in
/-- `ℚ` has exactly one infinite place. -/
theorem card_infinitePlace_rat : Fintype.card (InfinitePlace ℚ) = 1 := by
  rw [NumberField.InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces,
    IsTotallyReal.nrComplexPlaces_eq_zero, ← IsTotallyReal.finrank]
  simp

/-- `ℚ` has exactly one real place. -/
theorem nrRealPlaces_rat : nrRealPlaces ℚ = 1 := by
  rw [← IsTotallyReal.finrank]; simp

open NumberField.Units.dirichletUnitTheorem in
/-- Since `ℚ` has a single infinite place, the index set of the regulator matrix is empty. -/
theorem isEmpty_infinitePlace_rat : IsEmpty {w : InfinitePlace ℚ // w ≠ w₀} :=
  have h : Subsingleton (InfinitePlace ℚ) :=
    Fintype.card_le_one_iff_subsingleton.mp card_infinitePlace_rat.le
  ⟨fun x => x.2 (@Subsingleton.elim _ h _ _)⟩

/-- The regulator of `ℚ` is `1` (the unit rank of `ℚ` is zero). -/
theorem regulator_rat : NumberField.Units.regulator ℚ = 1 := by
  haveI := isEmpty_infinitePlace_rat
  simp [NumberField.Units.regulator_eq_det', Matrix.det_isEmpty]

/-- The number of roots of unity of `ℚ` is `2`, namely `±1`. -/
theorem torsionOrder_rat : NumberField.Units.torsionOrder ℚ = 2 :=
  NumberField.Units.torsionOrder_eq_two_of_odd_finrank (K := ℚ) (by simp)

/--
The class number formula for `K = ℚ`: the residue at `s = 1` of the Riemann zeta function
(the Dedekind zeta function of `ℚ`) is `1`.  Indeed `r₁ = 1`, `r₂ = 0`, `R = 1`, `h = 1`,
`w = 2` and `d = 1`, so the residue is `2 / 2 = 1`.
-/
theorem class_number_formula_rat :
    Tendsto (fun s : ℝ ↦ (s - 1) * NumberField.dedekindZeta ℚ s) (𝓝[>] 1) (𝓝 1) := by
  have h := class_number_formula ℚ
  rw [nrRealPlaces_rat, IsTotallyReal.nrComplexPlaces_eq_zero, regulator_rat, torsionOrder_rat,
    Rat.classNumber_eq, Rat.numberField_discr] at h
  convert h using 2
  norm_num

end Math2

