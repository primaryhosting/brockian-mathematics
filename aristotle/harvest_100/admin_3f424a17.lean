import Mathlib

/-!
# Goldbach Wheel K 2 1327
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_1327
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- Note: Lean 4 requires `import` commands to precede every other command,
-- including module documentation, so the header block above sits just after
-- the single `import Mathlib` line.

set_option maxHeartbeats 4000000
set_option maxRecDepth 100000
set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Brockian

/-! ### A kernel-friendly primality test

`Nat.decidablePrime` performs `Θ(n)` trial divisions and is far too slow for
kernel reduction on a few hundred numbers, so we use a small trial-division
test up to `√n` (with fuel) together with a soundness proof. -/

/-- `trialAux n f d` checks that no `e` with `d ≤ e` and `e * e ≤ n` divides `n`,
using `f` units of fuel; it returns `false` when the fuel runs out. -/
def trialAux (n : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | (f + 1), d => if n < d * d then true else if n % d == 0 then false else trialAux n f (d + 1)

/-- A Boolean primality test, sound by `isPrimeB_sound`, fast under kernel reduction
for `n < 1600` (fuel `40` covers all trial divisors up to `√n`). -/
def isPrimeB (n : ℕ) : Bool := 2 ≤ n && trialAux n 40 2

theorem trialAux_sound (n : ℕ) :
    ∀ f d, trialAux n f d = true → ∀ e, d ≤ e → e * e ≤ n → ¬ e ∣ n := by
  intro f
  induction f with
  | zero => intro d h; simp [trialAux] at h
  | succ f ih =>
    intro d h e hde hee hdvd
    rw [trialAux] at h
    by_cases h1 : n < d * d
    · exact absurd hee (by nlinarith [Nat.mul_le_mul hde hde])
    · simp only [h1, if_false] at h
      by_cases h2 : n % d == 0
      · simp [h2] at h
      · simp only [h2] at h
        rcases eq_or_lt_of_le hde with rfl | hlt
        · simp only [beq_iff_eq] at h2
          exact h2 (Nat.mod_eq_zero_of_dvd hdvd)
        · exact ih (d + 1) h e hlt hee hdvd

theorem isPrimeB_sound {n : ℕ} (h : isPrimeB n = true) : Nat.Prime n := by
  rw [isPrimeB, Bool.and_eq_true, decide_eq_true_eq] at h
  refine Nat.prime_def_le_sqrt.mpr ⟨h.1, fun m hm hms => ?_⟩
  exact trialAux_sound n 40 2 h.2 m hm (Nat.le_sqrt.mp hms)

/-! ### The prime data

`primeMask` is the bitmask of the primes below `1328`: bit `p` is set iff `p` is
prime.  `wheelSpokes` is the set of "spokes" of the Goldbach wheel, i.e. the small
primes that are allowed as the smaller summand. -/

/-- Bitmask of the primes `< 1328`. -/
def primeMask : ℕ :=
  2986793699354964966835927301217008259302263430909374666791341132234264811227334778053757846503498762062113181585587619060298442378116277488631156256376434239092036059285253544964719249140638915200534050206672277004701076777703965152156178915501541779626784833344371752025088121305545633374745450164679680261221317007399539577353874566270292751940695716555300979884638300668247903401038629556206577836

/-- The spokes of the wheel: the primes up to `73`.  Every even `n` with
`4 ≤ n ≤ 1327` has a Goldbach representation whose smaller summand is a spoke. -/
def wheelSpokes : List ℕ :=
  [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73]

theorem primeMask_sound_bool :
    (List.range 1328).all (fun n => !(primeMask.testBit n) || isPrimeB n) = true := by decide

/-- Every bit set in `primeMask` below `1328` marks a prime. -/
theorem prime_of_testBit {n : ℕ} (hn : n < 1328) (h : primeMask.testBit n = true) :
    Nat.Prime n := by
  have := List.all_eq_true.mp primeMask_sound_bool n (List.mem_range.mpr hn)
  simp only [h, Bool.not_true, Bool.false_or] at this
  exact isPrimeB_sound this

/-- The wheel computation: for every even `n = 2 * i + 4` with `i < 662` there is a spoke
`p` with `2 * p ≤ n` such that both `p` and `n - p` are prime (as recorded by `primeMask`). -/
theorem wheel_check :
    (List.range 662).all (fun i =>
      wheelSpokes.any (fun p =>
        decide (2 * p ≤ 2 * i + 4) && primeMask.testBit p && primeMask.testBit (2 * i + 4 - p)))
      = true := by decide

/-- **Goldbach wheel, K = 2, modulus 1327.**
Every even number `n` with `4 ≤ n ≤ 1327` is the sum of two primes `p ≤ q`. -/
theorem GoldbachWheelK2_1327 (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1327) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ p ≤ q ∧ p + q = n := by
  obtain ⟨k, hk⟩ := he
  -- write `n = 2 * i + 4`
  obtain ⟨i, hi, rfl⟩ : ∃ i : ℕ, i < 662 ∧ n = 2 * i + 4 := ⟨k - 2, by omega, by omega⟩
  have hrow := List.all_eq_true.mp wheel_check i (List.mem_range.mpr hi)
  obtain ⟨p, hp, hcond⟩ := List.any_eq_true.mp hrow
  rw [Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hcond
  obtain ⟨⟨hle, hbp⟩, hbq⟩ := hcond
  have hp1 : Nat.Prime p := prime_of_testBit (by omega) hbp
  have hq1 : Nat.Prime (2 * i + 4 - p) := prime_of_testBit (by omega) hbq
  exact ⟨p, 2 * i + 4 - p, hp1, hq1, by omega, by omega⟩

end Brockian

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

