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
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- written as a plain block comment; the module docstring below repeats it.)

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

/-- `ℚ`-algebra structure obtained by restricting scalars from `ℝ`; needed to use the
Mathlib API for the exponential in a Banach algebra. -/
noncomputable local instance ratAlgebraOfReal : NormedAlgebra ℚ 𝔸 :=
  NormedAlgebra.restrictScalars ℚ ℝ 𝔸

/-- `exp (t • X)` and `exp (t • (-X))` are inverse to each other. -/

theorem bcH_of_commute (A B : 𝔸) (hAC : Commute A (A * B - B * A))
    (hBC : Commute B (A * B - B * A)) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) := by
  set C := A * B - B * A with hC
  have hCAB : Commute C (A + B) := (hAC.symm).add_right (hBC.symm)
  set g : ℝ → 𝔸 := fun u =>
    exp ((u ^ 2 / 2) • (-C)) * (exp (u • (-(A + B))) * (exp (u • A) * exp (u • B))) with hg
  have hd : ∀ u : ℝ, HasDerivAt g 0 u := by
    intro u
    have dP : HasDerivAt (fun s : ℝ => exp ((s ^ 2 / 2) • (-C)))
        (u • (exp ((u ^ 2 / 2) • (-C)) * (-C))) u := by
      have hfd : HasDerivAt (fun s : ℝ => s ^ 2 / 2) u u := by
        simpa using ((hasDerivAt_pow 2 u).div_const 2)
      simpa [Function.comp] using
        (hasDerivAt_exp_smul_const (𝕂 := ℝ) (-C) (u ^ 2 / 2)).scomp u hfd
    have dQ : HasDerivAt (fun s : ℝ => exp (s • (-(A + B))))
        (exp (u • (-(A + B))) * (-(A + B))) u := hasDerivAt_exp_smul_const _ _
    have dR : HasDerivAt (fun s : ℝ => exp (s • A)) (exp (u • A) * A) u :=
      hasDerivAt_exp_smul_const _ _
    have dS : HasDerivAt (fun s : ℝ => exp (s • B)) (exp (u • B) * B) u :=
      hasDerivAt_exp_smul_const _ _
    have h := dP.mul (dQ.mul (dR.mul dS))
    convert h using 1
    simp only [Pi.mul_apply]
    set P := exp ((u ^ 2 / 2) • (-C))
    set Q := exp (u • (-(A + B)))
    set R := exp (u • A)
    set S := exp (u • B)
    have hQC : C * Q = Q * C := ((hCAB.neg_right).smul_right u).exp_right
    have hRA : R * A = A * R := ((Commute.refl A).smul_left u).exp_left
    have hSB : S * B = B * S := ((Commute.refl B).smul_left u).exp_left
    have hRB : R * B = (B + u • C) * R := exp_smul_mul_eq A B hAC u
    rw [hRA, hSB]
    rw [show R * (B * S) = ((B + u • C) * R) * S by rw [← mul_assoc, hRB]]
    rw [show (u • (P * (-C))) * (Q * (R * S)) = u • (-(P * (Q * (C * (R * S))))) by
      rw [smul_mul_assoc, mul_neg, neg_mul, mul_assoc, ← mul_assoc C Q, hQC, mul_assoc]]
    symm
    noncomm_ring
    module
  have hconst : g 1 = g 0 :=
    is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) 1 0
  have h0 : g 0 = 1 := by simp [hg]
  have h1 : exp ((1 / 2 : ℝ) • (-C)) * (exp (-(A + B)) * (exp A * exp B)) = 1 := by
    simpa [hg] using hconst.trans h0
  have hinvC : exp ((1 / 2 : ℝ) • C) * exp ((1 / 2 : ℝ) • (-C)) = 1 :=
    exp_smul_mul_exp_smul_neg C (1 / 2)
  have hinvAB : exp (A + B) * exp (-(A + B)) = 1 := by
    simpa using exp_smul_mul_exp_smul_neg (A + B) 1
  have step1 : exp (-(A + B)) * (exp A * exp B) = exp ((1 / 2 : ℝ) • C) := by
    calc exp (-(A + B)) * (exp A * exp B)
        = (exp ((1 / 2 : ℝ) • C) * exp ((1 / 2 : ℝ) • (-C)))
            * (exp (-(A + B)) * (exp A * exp B)) := by rw [hinvC, one_mul]
      _ = exp ((1 / 2 : ℝ) • C)
            * (exp ((1 / 2 : ℝ) • (-C)) * (exp (-(A + B)) * (exp A * exp B))) := by
            rw [mul_assoc]
      _ = exp ((1 / 2 : ℝ) • C) := by rw [h1, mul_one]
  calc exp A * exp B
      = (exp (A + B) * exp (-(A + B))) * (exp A * exp B) := by rw [hinvAB, one_mul]
    _ = exp (A + B) * (exp (-(A + B)) * (exp A * exp B)) := by rw [mul_assoc]
    _ = exp (A + B) * exp ((1 / 2 : ℝ) • C) := by rw [step1]
    _ = exp (A + B + (1 / 2 : ℝ) • C) :=
        (exp_add_of_commute ((hCAB.symm).smul_right (1 / 2))).symm

/-- **BCH special case.**  In a Banach algebra, if the commutator `[A, B] = AB - BA` is central,
then `exp A * exp B = exp (A + B + ½ [A, B])`. -/
