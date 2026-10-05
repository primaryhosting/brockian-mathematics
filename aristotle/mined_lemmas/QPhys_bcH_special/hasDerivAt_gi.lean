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

import Mathlib
/-!
# Bc H Special
Category: Quantum Physics
Target: QPhys.bcH_special
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open NormedSpace

namespace QPhys

section

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

noncomputable local instance instNormedAlgebraRatOfReal : NormedAlgebra ℚ 𝔸 :=
  NormedAlgebra.restrictScalars ℚ ℝ 𝔸

omit [CompleteSpace 𝔸] in
/-- A function `ℝ → 𝔸` with everywhere-vanishing derivative is constant. -/

theorem hasDerivAt_gi (A B C : 𝔸) (hAC : Commute A C) (hBC : Commute B C) (t : ℝ) :
    HasDerivAt (fun s : ℝ => exp ((-s) • (A + B)) * exp ((-(s ^ 2 / 2)) • C))
      (-((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B + t • C))) t := by
  have hABC : Commute (A + B) C := hAC.add_left hBC
  have hp := hasDerivAt_exp_neg_smul (A + B) t
  have hinner : HasDerivAt (fun s : ℝ => -(s ^ 2 / 2)) (-t) t := by
    have : HasDerivAt (fun s : ℝ => s ^ 2 / 2) t t := by
      simpa using ((hasDerivAt_pow 2 t).div_const 2)
    simpa using this.neg
  have hq : HasDerivAt (fun s : ℝ => exp ((-(s ^ 2 / 2)) • C))
      ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C)) t := by
    have h := (hasDerivAt_exp_smul_const (𝕂 := ℝ) C (-(t ^ 2 / 2))).scomp t hinner
    simp only [Function.comp_def] at h
    exact h
  have hcomm : Commute (A + B) (exp ((-(t ^ 2 / 2)) • C)) :=
    (hABC.smul_right (-(t ^ 2 / 2))).exp_right
  have h := hp.mul hq
  have e1 : (exp ((-t) • (A + B)) * (A + B)) * exp ((-(t ^ 2 / 2)) • C)
      = (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B) := by
    rw [mul_assoc, hcomm.eq, ← mul_assoc]
  have e2 : exp ((-t) • (A + B)) * ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C))
      = (-t) • ((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * C) := by
    rw [mul_smul_comm, mul_assoc]
  have heq : -(exp ((-t) • (A + B)) * (A + B)) * exp ((-(t ^ 2 / 2)) • C) +
      exp ((-t) • (A + B)) * ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C))
      = -((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B + t • C)) := by
    have e3 : (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B + t • C)
        = (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * (A + B)
          + t • ((exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) * C) := by
      rw [mul_add (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C)) (A + B) (t • C),
        mul_smul_comm]
    rw [neg_mul, e1, e2, e3, neg_add,
      neg_smul t (exp ((-t) • (A + B)) * exp ((-(t ^ 2 / 2)) • C) * C)]
  rw [← heq]
  exact h

/-- **Special case of the Baker–Campbell–Hausdorff formula.**
If the commutator `C = AB - BA` commutes with both `A` and `B` (in particular if it is central),
then `e^A e^B = e^{A + B + ½ [A,B]}`. -/
