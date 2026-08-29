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
