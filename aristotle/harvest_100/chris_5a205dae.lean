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

/-
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open NormedSpace

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- Exponential of a sum of commuting elements of a real Banach algebra. -/
theorem exp_add_of_commute' {x y : 𝔸} (h : Commute x y) :
    exp (x + y) = exp x * exp y := by
  refine exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h ?_ ?_ <;>
    simp [expSeries_radius_eq_top ℝ 𝔸]

/-- `exp (t • X)` is invertible, with inverse `exp (t • (-X))`. -/
theorem exp_smul_mul_exp_neg_smul (X : 𝔸) (t : ℝ) : exp (t • X) * exp (t • (-X)) = 1 := by
  rw [← exp_add_of_commute'
    (Commute.smul_right (Commute.smul_left (Commute.neg_right (Commute.refl X)) t) t)]
  simp

/-- If the commutator `C = AB - BA` commutes with `A`, then
`exp (tA) B = (B + t C) exp (tA)`; i.e. conjugation by `exp (tA)` shifts `B` by `t C`. -/
theorem exp_smul_mul_eq {A B : 𝔸} (hA : Commute A (A * B - B * A)) (t : ℝ) :
    exp (t • A) * B = (B + t • (A * B - B * A)) * exp (t • A) := by
  set C := A * B - B * A with hC
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => exp (s • (-A)) * ((B + s • C) * exp (s • A))) 0 s := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => exp (s • (-A))) (exp (t • (-A)) * (-A)) t :=
      hasDerivAt_exp_smul_const (-A) t
    have h2 : HasDerivAt (fun s : ℝ => B + s • C) C t := by
      simpa using ((hasDerivAt_id t).smul_const C).const_add B
    have h3 : HasDerivAt (fun s : ℝ => exp (s • A)) (exp (t • A) * A) t :=
      hasDerivAt_exp_smul_const A t
    have h := h1.mul (h2.mul h3)
    convert h using 1
    simp only [Pi.mul_apply]
    set E := exp (t • A)
    set F := exp (t • (-A))
    have e1 : E * A = A * E := ((Commute.refl A).smul_left t).exp_left
    have e2 : C * (E * A) = A * (C * E) := by rw [e1, ← mul_assoc, ← hA.eq, mul_assoc]
    have key : F * (-A) * ((B + t • C) * E) + F * (C * E + (B + t • C) * (E * A))
        = F * ((-(A * B) + B * A + C) * E) + t • (F * (C * (E * A)) - F * (A * (C * E))) := by
      rw [e1]; noncomm_ring; module
    rw [key, e2, hC]; simp
  have hconst := is_const_of_deriv_eq_zero
    (f := fun s : ℝ => exp (s • (-A)) * ((B + s • C) * exp (s • A)))
    (fun s => (hderiv s).differentiableAt) (fun s => (hderiv s).deriv) t 0
  simp only [zero_smul, exp_zero, one_mul, mul_one] at hconst
  have h2 := congrArg (fun x => exp (t • A) * x) hconst
  simp only [← mul_assoc, exp_smul_mul_exp_neg_smul A t, one_mul] at h2
  simpa using h2.symm

/-- The auxiliary function `t ↦ exp (-(t²/2) C) exp (-t (A+B)) exp (tA) exp (tB)`
has vanishing derivative when the commutator `C = AB - BA` is central. -/
theorem hasDerivAt_bch_aux {A B : 𝔸} (hA : Commute A (A * B - B * A))
    (hB : Commute B (A * B - B * A)) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((-(s ^ 2 / 2)) • (A * B - B * A)) *
        (exp (s • (-(A + B))) * (exp (s • A) * exp (s • B)))) 0 t := by
  set C := A * B - B * A with hC
  have hg : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-t) t := by
    simpa using ((hasDerivAt_pow 2 t).div_const 2).neg
  have hu : HasDerivAt (fun s : ℝ => exp ((-(s ^ 2 / 2)) • C))
      ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C)) t := by
    have hf : HasDerivAt (fun s : ℝ => exp (s • C)) (exp ((-(t ^ 2 / 2)) • C) * C)
        (-(t ^ 2 / 2)) := hasDerivAt_exp_smul_const C _
    simpa [Function.comp_def] using hf.scomp t hg
  have hv : HasDerivAt (fun s : ℝ => exp (s • (-(A + B))))
      (exp (t • (-(A + B))) * (-(A + B))) t := hasDerivAt_exp_smul_const _ t
  have hp : HasDerivAt (fun s : ℝ => exp (s • A)) (exp (t • A) * A) t :=
    hasDerivAt_exp_smul_const A t
  have hq : HasDerivAt (fun s : ℝ => exp (s • B)) (exp (t • B) * B) t :=
    hasDerivAt_exp_smul_const B t
  have h := hu.mul (hv.mul (hp.mul hq))
  convert h using 1
  simp only [Pi.mul_apply]
  set u := exp ((-(t ^ 2 / 2)) • C)
  set v := exp (t • (-(A + B)))
  set p := exp (t • A)
  set q := exp (t • B)
  have hpA : p * A = A * p := ((Commute.refl A).smul_left t).exp_left
  have hqB : q * B = B * q := ((Commute.refl B).smul_left t).exp_left
  have hpB : p * B = (B + t • C) * p := exp_smul_mul_eq hA t
  have hCv : C * v = v * C := by
    have hnAB : Commute (-(A + B)) C := (hA.add_left hB).neg_left
    exact ((hnAB.smul_left t).exp_left).symm.eq
  have t1 : ((-t) • (u * C)) * (v * (p * q)) = u * (v * ((-t) • (C * (p * q)))) := by
    have h : u * C * (v * (p * q)) = u * (v * (C * (p * q))) := by
      rw [mul_assoc, ← mul_assoc C v, hCv, mul_assoc]
    rw [smul_mul_assoc, h, mul_smul_comm, mul_smul_comm]
  have t3 : (p * A) * q = A * (p * q) := by rw [hpA, mul_assoc]
  have t4 : p * (q * B) = B * (p * q) + t • (C * (p * q)) := by
    calc p * (q * B) = (p * B) * q := by rw [hqB, mul_assoc]
      _ = ((B + t • C) * p) * q := by rw [hpB]
      _ = B * (p * q) + t • (C * (p * q)) := by simp [add_mul, mul_assoc]
  rw [t1, t3, t4]
  have expand : u * ((v * (-(A + B))) * (p * q) +
        v * (A * (p * q) + (B * (p * q) + t • (C * (p * q)))))
      = u * (v * (t • (C * (p * q)))) := by
    rw [mul_assoc v (-(A + B)) (p * q)]
    congr 1
    rw [← mul_add]
    congr 1
    noncomm_ring
  rw [expand, ← mul_add, ← mul_add]
  simp

/-- **Baker–Campbell–Hausdorff, special case.**  If the commutator `C = AB - BA`
of two elements of a real Banach algebra is central (it commutes with both `A` and `B`),
then `exp A * exp B = exp (A + B + ½ [A, B])`. -/
theorem bcH_special {A B : 𝔸} (hA : Commute A (A * B - B * A))
    (hB : Commute B (A * B - B * A)) :
    exp A * exp B = exp (A + B + (2⁻¹ : ℝ) • (A * B - B * A)) := by
  set C := A * B - B * A with hC
  have hconst := is_const_of_deriv_eq_zero
    (f := fun s : ℝ =>
      exp ((-(s ^ 2 / 2)) • C) * (exp (s • (-(A + B))) * (exp (s • A) * exp (s • B))))
    (fun s => (hasDerivAt_bch_aux hA hB s).differentiableAt)
    (fun s => (hasDerivAt_bch_aux hA hB s).deriv) 1 0
  norm_num at hconst
  have hneg : (-B + -A) = -(A + B) := by abel
  rw [hneg] at hconst
  have h1 : exp ((2⁻¹ : ℝ) • C) * exp (-((1 / 2 : ℝ) • C)) = 1 := by
    have := exp_smul_mul_exp_neg_smul C (2⁻¹ : ℝ)
    simpa [smul_neg] using this
  have h2 : exp (A + B) * exp (-(A + B)) = 1 := by
    simpa using exp_smul_mul_exp_neg_smul (A + B) 1
  have step1 : exp (-(A + B)) * exp A * exp B = exp ((2⁻¹ : ℝ) • C) := by
    have h := congrArg (fun x => exp ((2⁻¹ : ℝ) • C) * x) hconst
    simp only [← mul_assoc, h1, one_mul, mul_one] at h
    exact h
  have step2 : exp A * exp B = exp (A + B) * exp ((2⁻¹ : ℝ) • C) := by
    have h := congrArg (fun x => exp (A + B) * x) step1
    simp only [← mul_assoc, h2, one_mul] at h
    exact h
  rw [step2, ← exp_add_of_commute' ((hA.add_left hB).smul_right (2⁻¹ : ℝ))]

/-! ### Non-vacuity: the Heisenberg (canonical commutation) example

The hypotheses of `bcH_special` are satisfiable with a nonzero commutator: take the
`3 × 3` nilpotent matrices `A = E₀₁`, `B = E₁₂`, whose commutator `E₀₂` is central. -/

section Heisenberg

open scoped Matrix.Norms.Operator

/-- The matrix `E₀₁`. -/
noncomputable def heisA : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![![0, 1, 0], ![0, 0, 0], ![0, 0, 0]]

/-- The matrix `E₁₂`. -/
noncomputable def heisB : Matrix (Fin 3) (Fin 3) ℝ := Matrix.of ![![0, 0, 0], ![0, 0, 1], ![0, 0, 0]]

theorem heis_commutator : heisA * heisB - heisB * heisA
    = Matrix.of ![![0, 0, 1], ![0, 0, 0], ![0, 0, 0]] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisA, heisB]

theorem heis_commutator_ne_zero : heisA * heisB - heisB * heisA ≠ 0 := by
  rw [heis_commutator]
  intro h
  have h02 := congrFun (congrFun h 0) 2
  simp at h02

theorem heis_commute_left : Commute heisA (heisA * heisB - heisB * heisA) := by
  rw [heis_commutator]
  show heisA * _ = _ * heisA
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisA]

theorem heis_commute_right : Commute heisB (heisA * heisB - heisB * heisA) := by
  rw [heis_commutator]
  show heisB * _ = _ * heisB
  ext i j
  fin_cases i <;> fin_cases j <;> simp [heisB]

/-- The BCH special case, applied to the Heisenberg pair (a genuinely noncommuting instance). -/
theorem bcH_special_heisenberg :
    exp heisA * exp heisB = exp (heisA + heisB + (2⁻¹ : ℝ) • (heisA * heisB - heisB * heisA)) :=
  bcH_special heis_commute_left heis_commute_right

end Heisenberg

end QPhys

