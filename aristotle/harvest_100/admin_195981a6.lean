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

open NormedSpace

namespace QPhys

variable {𝔸 : Type*} [NormedRing 𝔸] [NormedAlgebra ℝ 𝔸] [CompleteSpace 𝔸]

/-- `exp` turns sums of commuting elements into products (specialization of
`NormedSpace.exp_add_of_commute_of_mem_ball` to a real Banach algebra). -/
theorem exp_add_comm {x y : 𝔸} (h : Commute x y) : exp (x + y) = exp x * exp y :=
  exp_add_of_commute_of_mem_ball h ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)
    ((expSeries_radius_eq_top ℝ 𝔸).symm ▸ edist_lt_top _ _)

theorem exp_mul_exp_neg (x : 𝔸) : exp x * exp (-x) = 1 := by
  rw [← exp_add_comm (Commute.refl x).neg_right]; simp

theorem exp_neg_mul_exp (x : 𝔸) : exp (-x) * exp x = 1 := by
  rw [← exp_add_comm (Commute.refl x).neg_left]; simp

/-- If the commutator `D = Y * X - X * Y` commutes with `Y`, then
`exp (t • Y) * X = (X + t • D) * exp (t • Y)`. -/
theorem exp_smul_mul_eq (X Y : 𝔸) (h : Commute Y (Y * X - X * Y)) (t : ℝ) :
    exp (t • Y) * X = (X + t • (Y * X - X * Y)) * exp (t • Y) := by
  set D := Y * X - X * Y with hD
  have hcomm : ∀ s : ℝ, Commute (exp (s • Y)) D := fun s => (h.smul_left s).exp_left
  have hexpY : ∀ s : ℝ, Commute Y (exp (s • Y)) := fun s =>
    ((Commute.refl Y).smul_right s).exp_right
  have hexpnY : ∀ s : ℝ, Commute Y (exp (s • (-Y))) := fun s =>
    (((Commute.refl Y).neg_right).smul_right s).exp_right
  have hinv : ∀ s : ℝ, exp (s • Y) * exp (s • (-Y)) = 1 := by
    intro s
    rw [← exp_add_comm (((Commute.refl Y).neg_right.smul_right s).smul_left s)]
    simp
  have hinv' : ∀ s : ℝ, exp (s • (-Y)) * exp (s • Y) = 1 := by
    intro s
    rw [← exp_add_comm (((Commute.refl Y).neg_left.smul_right s).smul_left s)]
    simp
  have hderiv : ∀ s : ℝ,
      HasDerivAt (fun u : ℝ => exp (u • Y) * X * exp (u • (-Y)) - u • D) 0 s := by
    intro s
    have h1 : HasDerivAt (fun u : ℝ => exp (u • Y)) (Y * exp (s • Y)) s :=
      hasDerivAt_exp_smul_const' Y s
    have h2 : HasDerivAt (fun u : ℝ => exp (u • (-Y))) (exp (s • (-Y)) * (-Y)) s :=
      hasDerivAt_exp_smul_const (-Y) s
    have h4 := ((h1.mul_const X).mul h2).sub ((hasDerivAt_id s).smul_const D)
    convert h4 using 1
    have e1 : Y * exp (s • Y) = exp (s • Y) * Y := (hexpY s).eq
    have e2 : exp (s • (-Y)) * (-Y) = (-Y) * exp (s • (-Y)) := ((hexpnY s).neg_left).eq.symm
    have e3 : exp (s • Y) * D = D * exp (s • Y) := (hcomm s).eq
    have expand : Y * exp (s • Y) * X * exp (s • (-Y))
        + exp (s • Y) * X * (exp (s • (-Y)) * (-Y)) - (1 : ℝ) • D
        = exp (s • Y) * D * exp (s • (-Y)) - D := by
      rw [e1, e2, hD, one_smul]; noncomm_ring
    rw [expand, e3, mul_assoc, hinv s, mul_one, sub_self]
  have key : ∀ s : ℝ, exp (s • Y) * X * exp (s • (-Y)) - s • D = X := by
    intro s
    have hc := is_const_of_deriv_eq_zero
      (f := fun u : ℝ => exp (u • Y) * X * exp (u • (-Y)) - u • D)
      (fun u => (hderiv u).differentiableAt) (fun u => (hderiv u).deriv) s 0
    simpa using hc
  have h6 : exp (t • Y) * X * exp (t • (-Y)) = X + t • D := sub_eq_iff_eq_add.mp (key t)
  calc exp (t • Y) * X = exp (t • Y) * X * exp (t • (-Y)) * exp (t • Y) := by
        rw [mul_assoc (exp (t • Y) * X), hinv' t, mul_one]
    _ = (X + t • D) * exp (t • Y) := by rw [h6]

/-- **Baker–Campbell–Hausdorff, special case.** If the commutator `[A, B] = A * B - B * A`
commutes with both `A` and `B` (in particular, if it is central), then
`exp A * exp B = exp (A + B + ½ [A, B])`. -/
theorem bcH_special (A B : 𝔸) (hA : Commute A (A * B - B * A))
    (hB : Commute B (A * B - B * A)) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) := by
  set C := A * B - B * A with hC
  have hderiv : ∀ t : ℝ, HasDerivAt (fun u : ℝ =>
      exp (u • A) * exp (u • B) * exp ((u ^ 2 / 2) • (-C)) * exp (u • (-(A + B)))) 0 t := by
    intro t
    have d2 : HasDerivAt (fun u : ℝ => exp (u • A)) (A * exp (t • A)) t :=
      hasDerivAt_exp_smul_const' A t
    have d3 : HasDerivAt (fun u : ℝ => exp (u • B)) (exp (t • B) * B) t :=
      hasDerivAt_exp_smul_const B t
    have hq : HasDerivAt (fun u : ℝ => u ^ 2 / 2) t t := by
      simpa using (hasDerivAt_pow 2 t).div_const 2
    have d4 : HasDerivAt (fun u : ℝ => exp ((u ^ 2 / 2) • (-C)))
        (t • (exp ((t ^ 2 / 2) • (-C)) * (-C))) t := by
      simpa [Function.comp] using (hasDerivAt_exp_smul_const (-C) (t ^ 2 / 2)).scomp t hq
    have d5 : HasDerivAt (fun u : ℝ => exp (u • (-(A + B))))
        ((-(A + B)) * exp (t • (-(A + B)))) t :=
      hasDerivAt_exp_smul_const' (-(A + B)) t
    have h := ((d2.mul d3).mul d4).mul d5
    convert h using 1
    simp only [Pi.mul_apply]
    set p := exp (t • A) with hp
    set q := exp (t • B) with hqdef
    set r := exp ((t ^ 2 / 2) • (-C)) with hr
    set s := exp (t • (-(A + B))) with hs
    have hpA : ∀ x : 𝔸, p * (A * x) = A * (p * x) := fun x => by
      rw [← mul_assoc, ← (((Commute.refl A).smul_right t).exp_right : Commute A p).eq, mul_assoc]
    have hrA : ∀ x : 𝔸, r * (A * x) = A * (r * x) := fun x => by
      rw [← mul_assoc,
        ← ((hA.neg_right.smul_right (t ^ 2 / 2)).exp_right : Commute A r).eq, mul_assoc]
    have hqB : ∀ x : 𝔸, q * (B * x) = B * (q * x) := fun x => by
      rw [← mul_assoc, ← (((Commute.refl B).smul_right t).exp_right : Commute B q).eq, mul_assoc]
    have hrB : ∀ x : 𝔸, r * (B * x) = B * (r * x) := fun x => by
      rw [← mul_assoc,
        ← ((hB.neg_right.smul_right (t ^ 2 / 2)).exp_right : Commute B r).eq, mul_assoc]
    have hpC : ∀ x : 𝔸, p * (C * x) = C * (p * x) := fun x => by
      rw [← mul_assoc, ← ((hA.symm.smul_right t).exp_right : Commute C p).eq, mul_assoc]
    have hqC : ∀ x : 𝔸, q * (C * x) = C * (q * x) := fun x => by
      rw [← mul_assoc, ← ((hB.symm.smul_right t).exp_right : Commute C q).eq, mul_assoc]
    have hrC : ∀ x : 𝔸, r * (C * x) = C * (r * x) := fun x => by
      rw [← mul_assoc,
        ← (((Commute.refl C).neg_right.smul_right (t ^ 2 / 2)).exp_right : Commute C r).eq,
        mul_assoc]
    have hBC : Commute B (B * A - A * B) := by
      have he : B * A - A * B = -C := by rw [hC]; noncomm_ring
      rw [he]; exact hB.neg_right
    have hqA0 : q * A = (A - t • C) * q := by
      have := exp_smul_mul_eq A B hBC t
      rw [hqdef]
      rw [this]
      have he : B * A - A * B = -C := by rw [hC]; noncomm_ring
      rw [he, smul_neg, ← sub_eq_add_neg]
    have hqA : ∀ x : 𝔸, q * (A * x) = A * (q * x) - t • (C * (q * x)) := fun x => by
      rw [← mul_assoc, hqA0]
      simp [sub_mul, mul_assoc]
    simp only [mul_assoc, mul_sub, mul_add, add_mul, mul_neg, neg_mul, smul_neg,
      smul_mul_assoc, mul_smul_comm, hpA, hrA, hqB, hrB, hpC, hqC, hrC, hqA]
    abel
  have hF1 : exp A * exp B * exp (-((1 / 2 : ℝ) • C)) * exp (-(A + B)) = 1 := by
    have hconst := is_const_of_deriv_eq_zero
      (f := fun u : ℝ =>
        exp (u • A) * exp (u • B) * exp ((u ^ 2 / 2) • (-C)) * exp (u • (-(A + B))))
      (fun u => (hderiv u).differentiableAt) (fun u => (hderiv u).deriv) 1 0
    simpa [smul_neg] using hconst
  have hcomm2 : Commute (A + B) ((1 / 2 : ℝ) • C) := (hA.add_left hB).smul_right _
  have step : exp A * exp B * exp (-((1 / 2 : ℝ) • C)) * exp (-(A + B)) * exp (A + B) *
      exp ((1 / 2 : ℝ) • C) = exp A * exp B := by
    rw [mul_assoc (exp A * exp B * exp (-((1 / 2 : ℝ) • C))), exp_neg_mul_exp, mul_one,
      mul_assoc, exp_neg_mul_exp, mul_one]
  calc exp A * exp B
      = exp A * exp B * exp (-((1 / 2 : ℝ) • C)) * exp (-(A + B)) * exp (A + B) *
          exp ((1 / 2 : ℝ) • C) := step.symm
    _ = exp (A + B) * exp ((1 / 2 : ℝ) • C) := by rw [hF1, one_mul]
    _ = exp (A + B + (1 / 2 : ℝ) • C) := (exp_add_comm hcomm2).symm

/-- **Baker–Campbell–Hausdorff, special case**, stated with the literal hypothesis that the
commutator `[A, B] = A * B - B * A` is central: `exp A * exp B = exp (A + B + ½ [A, B])`. -/
theorem bcH_special_of_central (A B : 𝔸) (h : ∀ x : 𝔸, Commute x (A * B - B * A)) :
    exp A * exp B = exp (A + B + (1 / 2 : ℝ) • (A * B - B * A)) :=
  bcH_special A B (h A) (h B)

end QPhys

