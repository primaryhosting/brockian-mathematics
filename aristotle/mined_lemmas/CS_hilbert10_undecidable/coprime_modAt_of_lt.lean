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
The moduli `1 + (i+1)q` used to code finite sequences, and the Chinese remainder theorem
for them.
-/
import RequestProject.H10.Arith

open Dioph Finset

namespace H10

/-- The `i`-th modulus of the Chinese remainder coding with parameter `q`. -/

theorem coprime_modAt_of_lt {q n a b : ℕ} (hq : (n + 1).factorial ∣ q)
    (hab : a < b) (hbn : b ≤ n) : Nat.Coprime (modAt q a) (modAt q b) := by
  set d := Nat.gcd (modAt q a) (modAt q b) with hd
  have hda : d ∣ modAt q a := Nat.gcd_dvd_left _ _
  have hdb : d ∣ modAt q b := Nat.gcd_dvd_right _ _
  have hsub : modAt q a - (a+1) * q = 1 := by simp [modAt]
  have hdiff : d ∣ (b - a) * q := by
    have h1 : modAt q b - modAt q a = (b - a) * q := by
      simp only [modAt]
      have h2 : (b + 1) * q - (a + 1) * q = (b - a) * q := by
        rw [← Nat.sub_mul]
        congr 1
        omega
      omega
    rw [← h1]
    exact Nat.dvd_sub hdb hda
  have hcop_dq : Nat.Coprime d q := by
    have h1 : Nat.gcd d q ∣ modAt q a := (Nat.gcd_dvd_left d q).trans hda
    have h2 : Nat.gcd d q ∣ (a+1) * q := Dvd.dvd.mul_left (Nat.gcd_dvd_right d q) _
    have h3 : Nat.gcd d q ∣ 1 := by rw [← hsub]; exact Nat.dvd_sub h1 h2
    exact Nat.eq_one_of_dvd_one h3
  have hdba : d ∣ b - a := hcop_dq.dvd_of_dvd_mul_right hdiff
  have hdq : d ∣ q := hdba.trans ((Nat.dvd_factorial (by omega) (by omega)).trans hq)
  have hd1 : d ∣ 1 := by
    rw [← hsub]
    exact Nat.dvd_sub hda (Dvd.dvd.mul_left hdq _)
  exact Nat.eq_one_of_dvd_one hd1

/-- Distinct moduli are coprime, provided `q` is divisible by `(n+1)!`. -/
