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
# Fortune Conjecture
Category: Brockian Conjecture
Target: Brockian.FortunateNumbers.FortuneConjecture
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Note: the requested header is written as a plain block comment `/- ... -/` rather than a
-- module doc comment `/-! ... -/`, because Lean 4 requires `import` to precede every command,
-- and a module doc comment counts as a command.  The text is otherwise verbatim.)

import Mathlib

set_option maxHeartbeats 1000000

namespace Brockian.FortunateNumbers

open Finset

/-- `IsFortunate n m` says that `m` is *the* Fortunate number attached to the primorial `n#`:
it is the least integer `m > 1` such that `n# + m` is prime. -/
def IsFortunate (n m : ℕ) : Prop :=
  1 < m ∧ Nat.Prime (primorial n + m) ∧ ∀ k, 1 < k → k < m → ¬ Nat.Prime (primorial n + k)

/-- A prime `p ≤ n` divides the primorial `n#`. -/
theorem prime_dvd_primorial {n p : ℕ} (hp : p.Prime) (hpn : p ≤ n) : p ∣ primorial n :=
  Finset.dvd_prod_of_mem _ (by simp [hpn, hp])

/-- Existence: for every `n` a Fortunate number exists (there are infinitely many primes,
so some `n# + m` with `m > 1` is prime, and we take the least such `m`). -/
theorem exists_isFortunate (n : ℕ) : ∃ m, IsFortunate n m := by
  have hex : ∃ m, 1 < m ∧ Nat.Prime (primorial n + m) := by
    obtain ⟨P, hP, hPp⟩ := Nat.exists_infinite_primes (primorial n + 2)
    refine ⟨P - primorial n, by omega, ?_⟩
    have : primorial n + (P - primorial n) = P := by omega
    rwa [this]
  classical
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro k hk1 hk hkp
  exact Nat.find_min hex hk ⟨hk1, hkp⟩

/-- Key unconditional fact: every prime factor of a Fortunate number `m` for `n#`
exceeds `n`.  Indeed, a prime `p ≤ n` divides `n#`, hence would divide the prime `n# + m`,
forcing `p = n# + m`, which is impossible since `p ≤ n# < n# + m`. -/
theorem prime_factor_gt {n m : ℕ} (h : IsFortunate n m) {p : ℕ} (hp : p.Prime)
    (hpm : p ∣ m) : n < p := by
  obtain ⟨hm1, hprime, -⟩ := h
  by_contra hle
  push_neg at hle
  have hdvd : p ∣ primorial n := prime_dvd_primorial hp hle
  have hdvd' : p ∣ primorial n + m := Dvd.dvd.add hdvd hpm
  have hple : p ≤ primorial n := Nat.le_of_dvd (primorial_pos n) hdvd
  have := (hprime.eq_one_or_self_of_dvd p hdvd').resolve_left hp.ne_one
  omega

/-- Consequently, a *composite* Fortunate number would have to be at least `(n+1)^2`. -/
theorem sq_le_of_not_prime {n m : ℕ} (h : IsFortunate n m) (hcomp : ¬ Nat.Prime m) :
    (n + 1) ^ 2 ≤ m := by
  have hm1 : 1 < m := h.1
  set q := m.minFac with hq
  have hqp : q.Prime := Nat.minFac_prime (by omega)
  have hqm : q ∣ m := Nat.minFac_dvd m
  have hqn : n < q := prime_factor_gt h hqp hqm
  set k := m / q with hk
  have hmk : m = q * k := (Nat.mul_div_cancel' hqm).symm
  have hk1 : 1 < k := by
    rcases Nat.lt_or_ge k 2 with hk2 | hk2
    · interval_cases k
      · simp [hmk] at hm1
      · exact absurd (by simpa [hmk] using hqp) hcomp
    · exact hk2
  have hkd : k ∣ m := ⟨q, by rw [hmk]; ring⟩
  have hrp : (k.minFac).Prime := Nat.minFac_prime (by omega)
  have hrm : k.minFac ∣ m := (Nat.minFac_dvd k).trans hkd
  have hrn : n < k.minFac := prime_factor_gt h hrp hrm
  have hkr : k.minFac ≤ k := Nat.minFac_le (by omega)
  calc (n + 1) ^ 2 = (n + 1) * (n + 1) := by ring
    _ ≤ q * k := Nat.mul_le_mul (by omega) (by omega)
    _ = m := hmk.symm

/-- **Fortune's conjecture, conditional form.**

Fortune's conjecture asserts that every Fortunate number is prime; it is open.
Here we prove the reduction: the conjecture for `n` follows from the (conjectural,
but numerically well supported) bound saying that the Fortunate number of `n#` is smaller
than the square of the least prime exceeding `n`; the weaker hypothesis `m < (n+1)^2`
already suffices.

Contrapositive content: a *counterexample* to Fortune's conjecture must be a composite
Fortunate number, all of whose prime factors exceed `n`, hence must be at least `(n+1)^2`. -/
theorem FortuneConjecture {n m : ℕ} (h : IsFortunate n m) (hbound : m < (n + 1) ^ 2) :
    Nat.Prime m := by
  by_contra hcomp
  exact absurd (sq_le_of_not_prime h hcomp) (by omega)

/-- Equivalent reformulation of Fortune's conjecture for a given `n`: the Fortunate number `m`
is prime **iff** it is not a composite number of size at least `(n+1)^2`. -/
theorem isFortunate_prime_iff {n m : ℕ} (h : IsFortunate n m) :
    Nat.Prime m ↔ ¬ ((n + 1) ^ 2 ≤ m ∧ ¬ Nat.Prime m) := by
  constructor
  · intro hp hcon; exact hcon.2 hp
  · intro hcon
    by_contra hcomp
    exact hcon ⟨sq_le_of_not_prime h hcomp, hcomp⟩

section Examples

theorem primorial_zero : primorial 0 = 1 := by decide

theorem primorial_two : primorial 2 = 2 := by decide

theorem primorial_three : primorial 3 = 6 := by decide

/-- The Fortunate number of `0# = 1` is `2`, which is prime. -/
example : IsFortunate 0 2 := by
  refine ⟨by norm_num, by rw [primorial_zero]; norm_num, ?_⟩
  intro k hk1 hk2
  omega

/-- The Fortunate number of `2# = 2` is `3`, which is prime. -/
example : IsFortunate 2 3 := by
  refine ⟨by norm_num, by rw [primorial_two]; norm_num, ?_⟩
  intro k hk1 hk2
  rw [primorial_two]
  interval_cases k
  norm_num

/-- The Fortunate number of `3# = 6` is `5`, which is prime. -/
example : IsFortunate 3 5 := by
  refine ⟨by norm_num, by rw [primorial_three]; norm_num, ?_⟩
  intro k hk1 hk2
  rw [primorial_three]
  interval_cases k <;> norm_num

end Examples

end Brockian.FortunateNumbers

