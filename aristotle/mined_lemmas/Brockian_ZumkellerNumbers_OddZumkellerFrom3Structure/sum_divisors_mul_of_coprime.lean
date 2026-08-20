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
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Odd Zumkeller From 3 Structure
Category: Brockian Conjecture
Target: Brockian.ZumkellerNumbers.OddZumkellerFrom3Structure
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

namespace Brockian
namespace ZumkellerNumbers

/-- A positive natural number `n` is a *Zumkeller number* if the set of its divisors can be
split into two parts having the same sum. -/

theorem sum_divisors_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) (hm : m ≠ 0) (hn : n ≠ 0)
    (g : ℕ → ℤ) :
    ∑ k ∈ (m * n).divisors, g k = ∑ d ∈ m.divisors, ∑ e ∈ n.divisors, g (d * e) := by
  rw [← Finset.sum_product']
  refine (Finset.sum_nbij' (i := fun p : ℕ × ℕ => p.1 * p.2) (j := fun k => (k.gcd m, k.gcd n))
    ?_ ?_ ?_ ?_ ?_).symm
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product, Nat.mem_divisors] at hde
    simp only [Nat.mem_divisors]
    exact ⟨Nat.mul_dvd_mul hde.1.1 hde.2.1, by positivity⟩
  · intro k _
    simp only [Finset.mem_product, Nat.mem_divisors]
    exact ⟨⟨Nat.gcd_dvd_right k m, hm⟩, ⟨Nat.gcd_dvd_right k n, hn⟩⟩
  · rintro ⟨d, e⟩ hde
    simp only [Finset.mem_product, Nat.mem_divisors] at hde
    have h1 : (d * e).gcd m = d := by
      rw [Nat.Coprime.gcd_mul_right_cancel d (Nat.Coprime.coprime_dvd_left hde.2.1 h.symm)]
      exact Nat.gcd_eq_left hde.1.1
    have h2 : (d * e).gcd n = e := by
      rw [mul_comm, Nat.Coprime.gcd_mul_right_cancel e (Nat.Coprime.coprime_dvd_left hde.1.1 h)]
      exact Nat.gcd_eq_left hde.2.1
    simp [h1, h2]
  · intro k hk
    simp only [Nat.mem_divisors] at hk
    exact (Nat.gcd_mul_gcd_eq_iff_dvd_mul_of_coprime h).2 hk.1
  · rintro ⟨d, e⟩ _
    rfl

/-- Zumkeller numbers are stable under multiplication by a coprime factor. -/
