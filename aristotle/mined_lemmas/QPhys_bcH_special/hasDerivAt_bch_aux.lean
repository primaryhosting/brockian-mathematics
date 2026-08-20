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
