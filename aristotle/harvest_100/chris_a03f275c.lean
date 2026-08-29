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
theorem exp_smul_mul_exp_smul_neg (X : 𝔸) (t : ℝ) : exp (t • X) * exp (t • (-X)) = 1 := by
  rw [← exp_add_of_commute ((((Commute.refl X).neg_right).smul_left t).smul_right t)]
  simp

/-- If the commutator `C = AB - BA` commutes with `A`, then
`exp (t • A) * B = (B + t • C) * exp (t • A)`; equivalently `exp(tA) B exp(-tA) = B + t C`. -/
theorem exp_smul_mul_eq (A B : 𝔸) (hAC : Commute A (A * B - B * A)) (t : ℝ) :
    exp (t • A) * B = (B + t • (A * B - B * A)) * exp (t • A) := by
  set C := A * B - B * A with hC
  have hAM : ∀ u : ℝ, A * (B + u • C) = (B + u • C) * A + C := by
    intro u
    simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hAC.eq]
    rw [hC]; abel
  set f : ℝ → 𝔸 := fun u => exp (u • (-A)) * ((B + u • C) * exp (u • A)) with hf
  have hd : ∀ u : ℝ, HasDerivAt f 0 u := by
    intro u
    have dP : HasDerivAt (fun s : ℝ => exp (s • (-A))) (exp (u • (-A)) * (-A)) u :=
      hasDerivAt_exp_smul_const _ _
    have dM : HasDerivAt (fun s : ℝ => B + s • C) C u := by
      simpa using ((hasDerivAt_id u).smul_const C).const_add B
    have dR : HasDerivAt (fun s : ℝ => exp (s • A)) (exp (u • A) * A) u :=
      hasDerivAt_exp_smul_const _ _
    have h := dP.mul (dM.mul dR)
    have hRA : exp (u • A) * A = A * exp (u • A) := ((Commute.refl A).smul_left u).exp_left
    convert h using 1
    simp only [Pi.mul_apply]
    set P := exp (u • (-A))
    set R := exp (u • A)
    have hzero : -(A * (B + u • C)) + C + (B + u • C) * A = 0 := by rw [hAM u]; abel
    have key : (P * (-A)) * ((B + u • C) * R) + P * (C * R + (B + u • C) * (R * A))
        = P * ((-(A * (B + u • C)) + C + (B + u • C) * A) * R) := by
      rw [hRA]
      noncomm_ring
      module
    rw [key, hzero, zero_mul, mul_zero]
  have hconst : f t = f 0 :=
    is_const_of_deriv_eq_zero (fun u => (hd u).differentiableAt) (fun u => (hd u).deriv) t 0
  have h0 : f 0 = B := by simp [hf]
  have ht : exp (t • (-A)) * ((B + t • C) * exp (t • A)) = B := hconst.trans h0
  calc exp (t • A) * B
      = exp (t • A) * (exp (t • (-A)) * ((B + t • C) * exp (t • A))) := by rw [ht]
    _ = (exp (t • A) * exp (t • (-A))) * ((B + t • C) * exp (t • A)) := by rw [mul_assoc]
    _ = (B + t • C) * exp (t • A) := by rw [exp_smul_mul_exp_smul_neg, one_mul]

/-- **Special case of the Baker–Campbell–Hausdorff formula.**  If the commutator
`C = AB - BA` commutes with both `A` and `B` (in particular if it is central), then
`exp A * exp B = exp (A + B + ½ C)`. -/
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
theorem bcH_special (A B : 𝔸) (hcentral : ∀ X : 𝔸, Commute (A * B - B * A) X) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) :=
  bcH_of_commute A B (hcentral A).symm (hcentral B).symm

end

end QPhys

