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
# AKS core: the introspective-numbers argument

This file contains the mathematical heart of the Agrawal–Kayal–Saxena primality test.
-/

namespace AKS

open Polynomial

section Introspective

variable {p : ℕ} [hp : Fact p.Prime]

/-- `m` is *introspective* for the polynomial `f` (with respect to `r`-th roots of unity in the
field `F` of characteristic `p`) if `f(y)^m = f(y^m)` for every `r`-th root of unity `y ∈ F`. -/

lemma pow_mul_pow_injective {n P q : ℕ} (hP : P.Prime) (hn : 2 ≤ n) (hqp : q * P = n)
    (hnpow : ∀ k, n ≠ P ^ k) {i₁ j₁ i₂ j₂ : ℕ} (h : q ^ i₁ * P ^ j₁ = q ^ i₂ * P ^ j₂) :
    i₁ = i₂ ∧ j₁ = j₂ := by
  have hn0 : n ≠ 0 := by omega
  have hq0 : q ≠ 0 := by rintro rfl; simp at hqp; omega
  set v := n.factorization P with hv
  set u := n / P ^ v with hu
  have hu_eq : P ^ v * u = n := Nat.ordProj_mul_ordCompl_eq_self n P
  have hpu : ¬ P ∣ u := Nat.not_dvd_ordCompl hP hn0
  have hu0 : u ≠ 0 := by
    intro h0; rw [h0, mul_zero] at hu_eq; omega
  have hu2 : 2 ≤ u := by
    rcases Nat.lt_or_ge u 2 with h' | h'
    · interval_cases u
      · omega
      · exact absurd (by simpa using hu_eq.symm) (hnpow v)
    · exact h'
  obtain ⟨c, hc_prime, hc_dvd⟩ := Nat.exists_prime_and_dvd (n := u) (by omega)
  have hcP : c ≠ P := by rintro rfl; exact hpu hc_dvd
  have hun : u ∣ n := ⟨P ^ v, by rw [← hu_eq]; ring⟩
  have hcq : c ∣ q := by
    have hcn : c ∣ q * P := by rw [hqp]; exact hc_dvd.trans hun
    exact ((Nat.coprime_primes hc_prime hP).mpr hcP).dvd_of_dvd_mul_right hcn
  have hw : 0 < q.factorization c := hc_prime.factorization_pos_of_dvd hq0 hcq
  have hPc : P.factorization c = 0 := by
    rw [hP.factorization]
    simp [Ne.symm hcP]
  have key : ∀ i j : ℕ, (q ^ i * P ^ j).factorization c = i * q.factorization c := by
    intro i j
    rw [Nat.factorization_mul (pow_ne_zero _ hq0) (pow_ne_zero _ hP.pos.ne')]
    simp [Nat.factorization_pow, hPc]
  have h1 : i₁ * q.factorization c = i₂ * q.factorization c := by
    rw [← key i₁ j₁, ← key i₂ j₂, h]
  have hi : i₁ = i₂ := Nat.eq_of_mul_eq_mul_right hw h1
  subst hi
  refine ⟨rfl, ?_⟩
  have := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (pow_ne_zero _ hq0)) h
  exact Nat.pow_right_injective hP.two_le this

