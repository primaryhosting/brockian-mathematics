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

theorem exists_residue_class (n : ℕ) :
    ∃ a Q : ℕ, 0 < Q ∧
      (∀ j, 0 < j → j < n → ∃ r, r.Prime ∧ r ∣ Q ∧ r ∣ a + j) ∧
      (∀ r : ℕ, r.Prime → r ∣ Q → ¬ r ∣ a ∧ ¬ r ∣ (a + n)) := by
  classical
  set q : ℕ → ℕ := fun j => Nat.nth Nat.Prime (n + j) with hq
  have hqp : ∀ j, (q j).Prime := fun j => Nat.prime_nth_prime (n + j)
  have hqgt : ∀ j, n < q j := by
    intro j
    have := Nat.add_two_le_nth_prime (n + j)
    simp only [hq]
    omega
  have hqinj : Function.Injective q := by
    intro i j hij
    have := (Nat.nth_injective Nat.infinite_setOf_prime) hij
    omega
  have hs : ∀ i ∈ Finset.Ico 1 n, q i ≠ 0 := fun i _ => (hqp i).pos.ne'
  have pp : Set.Pairwise ((Finset.Ico 1 n : Finset ℕ) : Set ℕ) (Nat.Coprime on q) := by
    intro i _ j _ hij
    exact (Nat.coprime_primes (hqp i) (hqp j)).mpr (fun h => hij (hqinj h))
  obtain ⟨a, ha⟩ := Nat.chineseRemainderOfFinset (fun j => q j - j) q (Finset.Ico 1 n) hs pp
  have hdvd : ∀ j ∈ Finset.Ico 1 n, q j ∣ a + j := by
    intro j hjt
    have hjn : j < n := (Finset.mem_Ico.mp hjt).2
    have h := (ha j hjt).add_right j
    rw [Nat.sub_add_cancel (le_of_lt (lt_trans hjn (hqgt j)))] at h
    exact (Nat.modEq_zero_iff_dvd).mp (h.trans ((Nat.modEq_zero_iff_dvd).mpr dvd_rfl))
  refine ⟨a, ∏ j ∈ Finset.Ico 1 n, q j, Finset.prod_pos (fun i _ => (hqp i).pos), ?_, ?_⟩
  · intro j hj0 hjn
    have hjt : j ∈ Finset.Ico 1 n := Finset.mem_Ico.mpr ⟨hj0, hjn⟩
    exact ⟨q j, hqp j, Finset.dvd_prod_of_mem q hjt, hdvd j hjt⟩
  · intro r hr hrQ
    obtain ⟨j, hjt, hrj⟩ := (Nat.Prime.prime hr).exists_mem_finset_dvd hrQ
    have hrq : r = q j := (Nat.prime_dvd_prime_iff_eq hr (hqp j)).mp hrj
    have hj0 := Finset.mem_Ico.mp hjt
    have hd := hdvd j hjt
    subst hrq
    have hgt := hqgt j
    refine ⟨?_, ?_⟩
    · intro hcon
      have h1 : q j ∣ j := by simpa using Nat.dvd_sub hd hcon
      have := Nat.le_of_dvd (by omega) h1
      omega
    · intro hcon
      have h1 : q j ∣ n - j := by simpa [Nat.add_sub_add_left] using Nat.dvd_sub hcon hd
      have := Nat.le_of_dvd (by omega) h1
      omega

/-- **Polignac's conjecture**, conditional on Dickson's conjecture: for every positive even `n`
there are arbitrarily large primes `p` such that `p` and `p + n` are consecutive primes. -/
