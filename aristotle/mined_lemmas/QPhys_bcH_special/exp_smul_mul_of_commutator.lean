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

open NormedSpace

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

omit [CompleteSpace 𝔸] in
/-- A function `ℝ → 𝔸` with everywhere vanishing derivative is constant. -/

theorem exp_smul_mul_of_commutator (X Y c : 𝔸) (hc : X * Y - Y * X = c) (hX : Commute X c)
    (t : ℝ) : exp (t • X) * Y = (Y + t • c) * exp (t • X) := by
  have hXz : ∀ s : ℝ, X * (Y + s • c) = (Y + s • c) * X + c := by
    intro s
    rw [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, hX.eq, ← hc]
    abel
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => exp (u • (-X)) * (Y + u • c) * exp (u • X)) 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • (-X))) ((-X) * exp (s • (-X))) s :=
      hasDerivAt_exp_smul_const' (-X) s
    have h2 : HasDerivAt (fun u : ℝ => Y + u • c) c s := by
      simpa using ((hasDerivAt_id s).smul_const c).const_add Y
    have h3 : HasDerivAt (fun u : ℝ => exp (u • X)) (exp (s • X) * X) s :=
      hasDerivAt_exp_smul_const X s
    have hmain := (h1.mul h2).mul h3
    have hcomm1 : Commute X (exp (s • (-X))) :=
      (((Commute.refl X).neg_right).smul_right s).exp_right
    have hcomm2 : Commute X (exp (s • X)) := ((Commute.refl X).smul_right s).exp_right
    have := aux_alg_conj X (Y + s • c) c (exp (s • (-X))) (exp (s • X)) hcomm1 hcomm2 (hXz s)
    rw [← this]
    exact hmain
  have key : exp (t • (-X)) * (Y + t • c) * exp (t • X) = Y := by
    have := const_of_hasDerivAt_zero hderiv t 0
    simpa using this
  have hinv : exp (t • X) * exp (t • (-X)) = 1 := by
    rw [smul_neg, ← exp_add_of_commute_real (Commute.refl _).neg_right]
    simp
  calc exp (t • X) * Y = exp (t • X) * (exp (t • (-X)) * (Y + t • c) * exp (t • X)) := by
        rw [key]
    _ = (exp (t • X) * exp (t • (-X))) * ((Y + t • c) * exp (t • X)) := by
        simp [mul_assoc]
    _ = (Y + t • c) * exp (t • X) := by rw [hinv, one_mul]

/-- Auxiliary noncommutative algebra identity used for the derivative of the
interpolating path `t ↦ e^{-t(A+B)} e^{tA} e^{tB}`. -/
