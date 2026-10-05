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
