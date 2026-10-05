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
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Riesel Problem
Category: Brockian Conjecture
Target: Brockian.RieselCovering.RieselProblem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RieselCovering

/-- A *Riesel number* is an odd natural number `k` such that `k * 2 ^ n - 1` is never prime
for `n ≥ 1`. -/

lemma exists_small_prime_dvd (n : ℕ) :
    ∃ p : ℕ, p.Prime ∧ p ≤ 241 ∧ p ∣ 509203 * 2 ^ n - 1 := by
  obtain ⟨r, hr, hrlt⟩ : ∃ r, n % 24 = r ∧ r < 24 :=
    ⟨n % 24, rfl, Nat.mod_lt _ (by norm_num)⟩
  interval_cases r
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 0 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 1 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 2 n (by decide) hr (by norm_num)⟩
  · exact ⟨241, by norm_num, by norm_num, dvd_of_dvd_residue 241 3 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 4 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 5 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 6 n (by decide) hr (by norm_num)⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_of_dvd_residue 13 7 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 8 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 9 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 10 n (by decide) hr (by norm_num)⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_of_dvd_residue 7 11 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 12 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 13 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 14 n (by decide) hr (by norm_num)⟩
  · exact ⟨17, by norm_num, by norm_num, dvd_of_dvd_residue 17 15 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 16 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 17 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 18 n (by decide) hr (by norm_num)⟩
  · exact ⟨13, by norm_num, by norm_num, dvd_of_dvd_residue 13 19 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 20 n (by decide) hr (by norm_num)⟩
  · exact ⟨5, by norm_num, by norm_num, dvd_of_dvd_residue 5 21 n (by decide) hr (by norm_num)⟩
  · exact ⟨3, by norm_num, by norm_num, dvd_of_dvd_residue 3 22 n (by decide) hr (by norm_num)⟩
  · exact ⟨7, by norm_num, by norm_num, dvd_of_dvd_residue 7 23 n (by decide) hr (by norm_num)⟩

/-- **The Riesel problem**: `509203` is a Riesel number, i.e. it is odd and
`509203 * 2 ^ n - 1` is composite for every `n ≥ 1`.  The proof uses Riesel's covering
system `{3, 5, 7, 13, 17, 241}`, whose primes all satisfy `2 ^ 24 ≡ 1`: for each residue
`r = n % 24` one of them divides `509203 * 2 ^ n - 1`. -/
