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

theorem sixth_exists_iff :
    (∃ n, IsUnitaryPerfect n ∧ n ∉ knownUnitaryPerfect) ↔
      (∃ a m : ℕ, 1 ≤ a ∧ Odd m ∧ 0 < m ∧
        (2 ^ a + 1) * sigmaStar m = 2 ^ (a + 1) * m ∧ 2 ^ a * m ∉ knownUnitaryPerfect) := by
  constructor
  · rintro ⟨n, hn, hnot⟩
    have hn0 : n ≠ 0 := hn.1.ne'
    have hn1 : 1 < n := by
      rcases Nat.lt_or_ge n 2 with h | h
      · interval_cases n
        · omega
        · exfalso
          have := hn.2
          rw [sigmaStar_one] at this
          omega
      · omega
    set a := n.factorization 2 with hadef
    set m := n / 2 ^ a with hmdef
    have hsplit : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
    have ha : 1 ≤ a :=
      Nat.prime_two.factorization_pos_of_dvd hn0 (even_of_unitaryPerfect hn hn1).two_dvd
    have hm0 : 0 < m := Nat.ordCompl_pos 2 hn0
    have hmodd : Odd m := by
      have h2 : ¬ (2 ∣ m) := Nat.not_dvd_ordCompl Nat.prime_two hn0
      exact Nat.odd_iff.2 (by omega)
    refine ⟨a, m, ha, hmodd, hm0, ?_, ?_⟩
    · exact (unitaryPerfect_two_pow_mul_iff ha hmodd hm0).1 (by rwa [hsplit])
    · rwa [hsplit]
  · rintro ⟨a, m, ha, hmodd, hm0, hrel, hnot⟩
    exact ⟨2 ^ a * m, (unitaryPerfect_two_pow_mul_iff ha hmodd hm0).2 hrel, hnot⟩

/-- **Sixth unitary perfect number (conditional).**

Whether a sixth unitary perfect number exists is an open problem, so the statement is proved
here in conditional (reduced) form: given `a ≥ 1` and an odd `m ≥ 1` satisfying the
"odd part" equation `(2 ^ a + 1) σ*(m) = 2 ^ (a+1) m`, with `2 ^ a * m` different from the five
known unitary perfect numbers, a sixth unitary perfect number exists.

By `sixth_exists_iff` this hypothesis is not merely sufficient but also necessary, so the
reduction loses nothing: the search for a sixth unitary perfect number is exactly the search
for such a pair `(a, m)`. -/
