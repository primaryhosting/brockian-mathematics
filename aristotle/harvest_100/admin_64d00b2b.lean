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
theorem const_of_hasDerivAt_zero {f : ℝ → 𝔸} (h : ∀ t, HasDerivAt f 0 t) (a b : ℝ) :
    f a = f b :=
  is_const_of_deriv_eq_zero (fun t => (h t).differentiableAt) (fun t => (h t).deriv) a b

/-- `exp (x + y) = exp x * exp y` for commuting elements of a real Banach algebra. -/
theorem exp_add_of_commute_real {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball (𝕂 := ℝ) h
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

/-- Auxiliary noncommutative algebra identity used to show that the conjugation
function has vanishing derivative. -/
theorem aux_alg_conj {R : Type*} [Ring R] (X z c e₁ e₂ : R) (h₁ : Commute X e₁)
    (h₂ : Commute X e₂) (hz : X * z = z * X + c) :
    (((-X) * e₁) * z + e₁ * c) * e₂ + (e₁ * z) * (e₂ * X) = 0 := by
  have e1X : (-X) * e₁ * z = -(e₁ * (X * z)) := by
    rw [neg_mul, h₁.eq]; noncomm_ring
  rw [e1X, hz, ← h₂.eq]
  noncomm_ring

/-- **Hadamard's lemma** in the case of a commutator `c = [X, Y]` commuting with `X`:
`e^{tX} Y = (Y + t c) e^{tX}`. -/
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
theorem aux_alg_bch {R : Type*} [Ring R] (A B K q r s : R)
    (f1 : q * A = (A + K) * q) (f2 : r * B = (B + K) * r) (f3 : q * B = (B - K) * q)
    (f4 : K * q = q * K) :
    ((-(A + B)) * q * r + q * (A * r)) * s + (q * r) * (B * s) = K * (q * r * s) := by
  have e1 : q * (A * r) = (A + K) * q * r := by rw [← mul_assoc, f1]
  have e3 : q * (B + K) = B * q := by rw [mul_add, ← f4, f3]; noncomm_ring
  have e2 : (q * r) * (B * s) = (B * q * r) * s := by
    rw [mul_assoc q r, ← mul_assoc r B, f2, ← mul_assoc, ← mul_assoc, e3]
  rw [e1, e2]
  noncomm_ring

/-- The Baker-Campbell-Hausdorff formula in the special case of a central commutator:
if `[A, B]` commutes with both `A` and `B`, then `e^A e^B = e^{A + B + ½[A,B]}`. -/
theorem bcH_special (A B : 𝔸) (hA : Commute A (A * B - B * A)) (hB : Commute B (A * B - B * A)) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) := by
  set C := A * B - B * A with hC
  have hAB : Commute (A + B) C := hA.add_left hB
  have hcomm1 : Commute (-(A + B)) C := hAB.neg_left
  -- the derivative of the interpolating path `t ↦ e^{-t(A+B)} e^{tA} e^{tB}`
  have hMderiv : ∀ t : ℝ,
      HasDerivAt (fun u : ℝ => exp (u • (-(A + B))) * exp (u • A) * exp (u • B))
        ((t • C) * (exp (t • (-(A + B))) * exp (t • A) * exp (t • B))) t := by
    intro t
    have h1 : HasDerivAt (fun u : ℝ => exp (u • (-(A + B))))
        ((-(A + B)) * exp (t • (-(A + B)))) t := hasDerivAt_exp_smul_const' _ t
    have h2 : HasDerivAt (fun u : ℝ => exp (u • A)) (A * exp (t • A)) t :=
      hasDerivAt_exp_smul_const' A t
    have h3 : HasDerivAt (fun u : ℝ => exp (u • B)) (B * exp (t • B)) t :=
      hasDerivAt_exp_smul_const' B t
    have hmain := (h1.mul h2).mul h3
    have hc1 : (-(A + B)) * A - A * (-(A + B)) = C := by rw [hC]; noncomm_ring
    have hc3 : (-(A + B)) * B - B * (-(A + B)) = -C := by rw [hC]; noncomm_ring
    have f1 := exp_smul_mul_of_commutator (-(A + B)) A C hc1 hcomm1 t
    have f2 := exp_smul_mul_of_commutator A B C hC.symm hA t
    have f3 := exp_smul_mul_of_commutator (-(A + B)) B (-C) hc3 hcomm1.neg_right t
    have f3' : exp (t • (-(A + B))) * B = (B - t • C) * exp (t • (-(A + B))) := by
      rw [f3, smul_neg, sub_eq_add_neg]
    have f4 : (t • C) * exp (t • (-(A + B))) = exp (t • (-(A + B))) * (t • C) :=
      ((hcomm1.symm.smul_left t).smul_right t).exp_right
    have halg := aux_alg_bch A B (t • C) (exp (t • (-(A + B)))) (exp (t • A)) (exp (t • B))
      f1 f2 f3' f4
    rw [← halg]
    exact hmain
  -- the compensating factor `t ↦ e^{-t²[A,B]/2}`
  have hPderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => exp ((-(u ^ 2 / 2)) • C))
      ((-t) • (exp ((-(t ^ 2 / 2)) • C) * C)) t := by
    intro t
    have hs : HasDerivAt (fun u : ℝ => -(u ^ 2 / 2)) (-t) t := by
      simpa using ((hasDerivAt_pow 2 t).div_const 2).neg
    have hg : HasDerivAt (fun v : ℝ => exp (v • C)) (exp ((-(t ^ 2 / 2)) • C) * C)
        (-(t ^ 2 / 2)) := hasDerivAt_exp_smul_const C _
    simpa [Function.comp_def] using hg.scomp t hs
  have hvderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ => exp ((-(u ^ 2 / 2)) • C) *
      (exp (u • (-(A + B))) * exp (u • A) * exp (u • B))) 0 t := by
    intro t
    have := (hPderiv t).mul (hMderiv t)
    convert this using 1
    simp [mul_assoc]
  have hv : exp ((-(1 / 2 : ℝ)) • C) * (exp (-(A + B)) * exp A * exp B) = 1 := by
    have h := const_of_hasDerivAt_zero hvderiv 1 0
    rw [show ((1 : ℝ) ^ 2 / 2) = 1 / 2 by norm_num,
      show ((0 : ℝ) ^ 2 / 2) = 0 by norm_num] at h
    simpa only [one_smul, zero_smul, neg_zero, exp_zero, one_mul, mul_one] using h
  -- conclude
  have hinvC : exp ((1 / 2 : ℝ) • C) * exp ((-(1 / 2 : ℝ)) • C) = 1 := by
    rw [← exp_add_of_commute_real ((Commute.refl C).smul_left _ |>.smul_right _), ← add_smul,
      add_neg_cancel, zero_smul, exp_zero]
  have hX : exp (-(A + B)) * exp A * exp B = exp ((1 / 2 : ℝ) • C) := by
    calc exp (-(A + B)) * exp A * exp B
        = exp ((1 / 2 : ℝ) • C) * (exp ((-(1 / 2 : ℝ)) • C) *
            (exp (-(A + B)) * exp A * exp B)) := by
          rw [← mul_assoc, hinvC, one_mul]
      _ = exp ((1 / 2 : ℝ) • C) := by rw [hv, mul_one]
  have hinvAB : exp (A + B) * exp (-(A + B)) = 1 := by
    rw [← exp_add_of_commute_real (Commute.refl _).neg_right, add_neg_cancel, exp_zero]
  calc exp A * exp B = (exp (A + B) * exp (-(A + B))) * (exp A * exp B) := by
        rw [hinvAB, one_mul]
    _ = exp (A + B) * (exp (-(A + B)) * exp A * exp B) := by simp [mul_assoc]
    _ = exp (A + B) * exp ((1 / 2 : ℝ) • C) := by rw [hX]
    _ = exp (A + B + (1 / 2 : ℝ) • C) := (exp_add_of_commute_real (hAB.smul_right _)).symm

end QPhys

