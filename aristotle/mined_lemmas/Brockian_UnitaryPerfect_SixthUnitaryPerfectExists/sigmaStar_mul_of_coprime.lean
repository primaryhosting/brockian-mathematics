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
/-!
# Sixth Unitary Perfect Exists
Category: Brockian Conjecture
Target: Brockian.UnitaryPerfect.SixthUnitaryPerfectExists
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-/

import Mathlib

/-!
# Sixth Unitary Perfect Exists

(The header block above is repeated here as a module docstring: Lean requires `import`
commands to precede any doc comment, so the file-opening header is an ordinary comment.)

Unitary divisors, the unitary divisor sum `σ*`, unitary perfect numbers, verification of the
five known unitary perfect numbers, the fact that no odd number `> 1` is unitary perfect, and
a reduction of the open "sixth unitary perfect number" problem.
-/

namespace Brockian.UnitaryPerfect

open Finset

/-- The unitary divisors of `n`: the divisors `d ∣ n` with `gcd (d, n / d) = 1`. -/

theorem sigmaStar_mul_of_coprime {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (h : Nat.Coprime m n) :
    sigmaStar (m * n) = sigmaStar m * sigmaStar n := by
  rw [sigmaStar, sigmaStar, sigmaStar, Finset.sum_mul_sum, ← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun p : ℕ × ℕ => p.1 * p.2)
    (j := fun d => (Nat.gcd d m, Nat.gcd d n)) ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, mem_unitaryDivisors] at hp
    obtain ⟨⟨ha, hax, -⟩, ⟨hb, hby, -⟩⟩ := hp
    refine mem_unitaryDivisors.2 ⟨mul_dvd_mul ha hb, ?_, by positivity⟩
    have hdiv : m * n / (a * b) = (m / a) * (n / b) := (Nat.div_mul_div_comm ha hb).symm
    rw [hdiv]
    have h1 : Nat.Coprime a (n / b) :=
      (h.coprime_dvd_left ha).coprime_dvd_right (Nat.div_dvd_of_dvd hb)
    have h2 : Nat.Coprime b (m / a) :=
      ((h.symm).coprime_dvd_left hb).coprime_dvd_right (Nat.div_dvd_of_dvd ha)
    exact Nat.Coprime.mul_left (hax.mul_right h1) (h2.mul_right hby)
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    obtain ⟨hdvd, hcop, -⟩ := hd
    have hkey : Nat.gcd d m * Nat.gcd d n = d :=
      (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hdvd
    have h1 : Nat.gcd d m ∣ m := Nat.gcd_dvd_right d m
    have h2 : Nat.gcd d n ∣ n := Nat.gcd_dvd_right d n
    have hd1 : Nat.gcd d m ∣ d := Dvd.intro _ hkey
    have hd2 : Nat.gcd d n ∣ d := Dvd.intro_left _ hkey
    have hdiv : m * n / d = (m / Nat.gcd d m) * (n / Nat.gcd d n) := by
      rw [Nat.div_mul_div_comm h1 h2, hkey]
    simp only [Finset.mem_product, mem_unitaryDivisors]
    refine ⟨⟨h1, ?_, hm.ne'⟩, ⟨h2, ?_, hn.ne'⟩⟩
    · refine (hcop.coprime_dvd_left hd1).coprime_dvd_right ?_
      rw [hdiv]; exact Dvd.intro _ rfl
    · refine (hcop.coprime_dvd_left hd2).coprime_dvd_right ?_
      rw [hdiv]; exact Dvd.intro_left _ rfl
  · rintro ⟨a, b⟩ hp
    simp only [Finset.mem_product, mem_unitaryDivisors] at hp
    obtain ⟨⟨ha, -, -⟩, ⟨hb, -, -⟩⟩ := hp
    have hbm : Nat.Coprime b m := (h.symm).coprime_dvd_left hb
    have ham : Nat.Coprime a n := h.coprime_dvd_left ha
    have e1 : Nat.gcd (a * b) m = a := by
      rw [Nat.Coprime.gcd_mul_right_cancel a hbm, Nat.gcd_eq_left ha]
    have e2 : Nat.gcd (a * b) n = b := by
      rw [Nat.Coprime.gcd_mul_left_cancel b ham, Nat.gcd_eq_left hb]
    simp [e1, e2]
  · intro d hd
    rw [mem_unitaryDivisors] at hd
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).mpr hd.1
  · intro p _; rfl

