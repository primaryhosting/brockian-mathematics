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

/-!
# Erdos Straus Conjecture
Category: Brockian Conjecture
Target: Brockian.ErdosStraus.ErdosStrausConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.ErdosStraus

/-- `IsErdosStrausRepresentable n` says that `4 / n` is a sum of three positive unit fractions,
`4 / n = 1 / x + 1 / y + 1 / z`, written here in the equivalent denominator-cleared form
`4 * (x * y * z) = n * (y * z + x * z + x * y)` with `x, y, z > 0`.
(The three denominators are not required to be distinct.) -/

theorem exists_prime_dvd : ∀ n : Nat, 2 ≤ n → ∃ p : Nat, IsPrimeNat p ∧ p ∣ n := by
  intro n
  induction n using Nat.strongRecOn with
  | _ n ih =>
    intro hn
    by_cases hp : ∀ d : Nat, d ∣ n → d = 1 ∨ d = n
    · exact ⟨n, ⟨hn, hp⟩, Nat.dvd_refl n⟩
    · obtain ⟨d, hdvd, hd1, hdn⟩ : ∃ d, d ∣ n ∧ d ≠ 1 ∧ d ≠ n := by grind
      have hd0 : d ≠ 0 := by
        intro h
        subst h
        have := Nat.eq_zero_of_zero_dvd hdvd
        omega
      have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdvd
      have hd2 : 2 ≤ d := by omega
      obtain ⟨p, hp, hpd⟩ := ih d (by omega) hd2
      exact ⟨p, hp, Nat.dvd_trans hpd hdvd⟩

/-- Representability passes from a divisor to its multiples. -/
