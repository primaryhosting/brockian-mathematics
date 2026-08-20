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
# Polignac Conjecture
Category: Brockian Conjecture
Target: Brockian.PolignacPrimes.PolignacConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (The header above is a plain block comment rather than a module docstring `/-! ... -/`
-- because Lean 4 requires `import` commands to precede every other command, including
-- module docstrings.)

import Mathlib

/-!
# Polignac Conjecture

De Polignac's conjecture states that for every positive even number `n` there are infinitely
many pairs of *consecutive* primes `p < q` with `q - p = n`.  This is an open problem (the case
`n = 2` is the twin prime conjecture), so what is proved here is a *conditional reduction*:
Polignac's conjecture is derived from Dickson's conjecture on simultaneous primality of
linear forms.

The derivation is the classical one.  Given an even `n ≥ 2`, one chooses for each `j` with
`0 < j < n` a distinct prime `q j > n`, sets `Q = ∏ q j` and uses the Chinese Remainder Theorem
to find `a` with `q j ∣ a + j` for all such `j`.  The pair of linear forms `a + Q x`,
`(a + n) + Q x` is then admissible, so Dickson's conjecture produces arbitrarily large `x`
making both forms prime; and every intermediate value `a + Q x + j` (`0 < j < n`) is divisible
by the prime `q j`, which is smaller than it, hence composite.  So the two primes are
consecutive with difference exactly `n`.
-/

namespace Brockian
namespace PolignacPrimes

open Finset
open scoped Function

/-- `p` and `q` are consecutive primes: both are prime, `p < q`, and no prime lies strictly
between them. -/

theorem PolignacConjecture (H : DicksonConjecture) (n : ℕ) (hn : Even n) (hn0 : 0 < n) (N : ℕ) :
    ∃ p : ℕ, N < p ∧ IsConsecutivePrimePair p (p + n) := by
  have hn2 : 2 ≤ n := by
    obtain ⟨m, rfl⟩ := hn
    omega
  obtain ⟨a, Q, hQ0, hint, hdvd⟩ := exists_residue_class n
  set A : Fin 2 → ℕ := ![a, a + n] with hA
  set B : Fin 2 → ℕ := ![Q, Q] with hB
  have hBpos : ∀ i, 0 < B i := by
    intro i
    fin_cases i <;> simpa [hB] using hQ0
  have hadm : ∀ r : ℕ, r.Prime → ∃ x : ℕ, ∀ i, ¬ (r ∣ A i + B i * x) := by
    intro r hr
    by_cases hrQ : r ∣ Q
    · refine ⟨0, ?_⟩
      intro i
      obtain ⟨h1, h2⟩ := hdvd r hr hrQ
      fin_cases i <;> simpa [hA, hB] using ‹_›
    · obtain ⟨x, hx1, hx2⟩ := exists_not_dvd_of_not_dvd (a := a) hr hrQ hn
      refine ⟨x, ?_⟩
      intro i
      fin_cases i
      · simpa [hA, hB] using hx1
      · simpa [hA, hB] using hx2
  obtain ⟨x, hxbig, hprime⟩ := H 2 A B hBpos hadm (N + Q + 1)
  refine ⟨a + Q * x, ?_, ?_⟩
  · have : x ≤ Q * x := Nat.le_mul_of_pos_left x hQ0
    omega
  · have hQx : Q < Q * x := by
      calc Q < x := by omega
        _ ≤ Q * x := Nat.le_mul_of_pos_left x hQ0
    have hp0 : Nat.Prime (a + Q * x) := by simpa [hA, hB] using hprime 0
    have hp1 : Nat.Prime (a + Q * x + n) := by
      have h1 := hprime 1
      simp only [hA, hB, Matrix.cons_val_one, Matrix.cons_val_fin_one] at h1
      have he : a + n + Q * x = a + Q * x + n := by ring
      rwa [he] at h1
    refine ⟨hp0, hp1, by omega, ?_⟩
    intro r hr1 hr2 hrp
    obtain ⟨s, hs, hsQ, hsdvd⟩ := hint (r - (a + Q * x)) (by omega) (by omega)
    have hsr : s ∣ r := by
      have hre : r = a + (r - (a + Q * x)) + Q * x := by omega
      rw [hre]
      exact hsdvd.add (hsQ.mul_right x)
    have hsle : s ≤ Q := Nat.le_of_dvd hQ0 hsQ
    have := (Nat.Prime.eq_one_or_self_of_dvd hrp s hsr).resolve_left hs.one_lt.ne'
    omega

/-- Restatement of the conditional Polignac conjecture as an infinitude statement: conditional
on Dickson's conjecture, for every positive even `n` infinitely many primes `p` are such that
`p` and `p + n` are consecutive primes. -/
