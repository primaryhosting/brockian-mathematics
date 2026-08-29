/-
  Brockian/FortunateNumbers.lean — FORTUNATE NUMBERS & FORTUNE'S CONJECTURE.

  For a primorial P (the product of the first primes), the *Fortunate number*
  is the smallest m > 1 for which P + m is prime. Reo Fortune conjectured
  (still OPEN) that every Fortunate number is prime.

  This module records CONCRETE, machine-checked instances:

    P =   2  →  m = 3    (2 + 3   = 5   prime; 2 + 2 = 4   composite)
    P =   6  →  m = 5    (6 + 5   = 11  prime; 6 + {2,3,4}   = 8,9,10   composite)
    P =  30  →  m = 7    (30 + 7  = 37  prime; 30 + {2..6}   = 32..36   composite)
    P = 210  →  m = 13   (210 + 13 = 223 prime; 210 + {2..12} = 212..222 composite)

  The four bases 2, 6, 30, 210 are exactly Mathlib's `primorial` at 2, 3, 5, 7
  (identities recorded below). Each of the four Fortunate numbers 3, 5, 7, 13
  is prime — the small-case evidence FOR Fortune's conjecture.

  Fortune's conjecture itself is stored as an UNPROVEN `def` (`FortuneConjecture`).
  It is never asserted or proved here: it remains open.

  Mathlib note: the primorial lives at the ROOT namespace as `primorial`
  (`primorial n = ∏ p ∈ Finset.range (n+1) with p.Prime, p`); there is no
  `Nat.primorial`. So `primorial 2 = 2`, `primorial 3 = 6`, `primorial 5 = 30`,
  `primorial 7 = 210`.
-/
import Mathlib

set_option autoImplicit false

namespace Brockian.FortunateNumbers

/-- `m` is the Fortunate number for base `P`: the smallest integer `> 1` with
`P + m` prime. -/
def FortunateFor (P m : ℕ) : Prop :=
  1 < m ∧ (P + m).Prime ∧ ∀ k : ℕ, 1 < k → k < m → ¬ (P + k).Prime

/-- Fortune's conjecture (OPEN): every Fortunate number, taken over a primorial
base `P = primorial n`, is prime. Recorded as an UNPROVEN `def` — never asserted,
never proved. -/
def FortuneConjecture : Prop :=
  ∀ n P m : ℕ, P = primorial n → FortunateFor P m → m.Prime

/-! ### (1) Flagship — concrete Fortunate numbers -/

/-- `P = 2`: the Fortunate number is `3` (`2+3 = 5` prime, `2+2 = 4` composite). -/
theorem fortunate_2 : FortunateFor 2 3 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-- `P = 6`: the Fortunate number is `5` (`6+5 = 11` prime, `6+{2,3,4}` composite). -/
theorem fortunate_6 : FortunateFor 6 5 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-- `P = 30`: the Fortunate number is `7` (`30+7 = 37` prime, `30+{2..6}` composite). -/
theorem fortunate_30 : FortunateFor 30 7 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-- `P = 210`: the Fortunate number is `13` (`210+13 = 223` prime,
`210+{2..12} = 212..222` all composite). -/
theorem fortunate_210 : FortunateFor 210 13 := by
  refine ⟨by norm_num, by norm_num, ?_⟩
  intro k hk hk'
  interval_cases k <;> norm_num

/-! ### (2) The Fortunate numbers are prime (Fortune's conjecture, small cases) -/

/-- Each concrete Fortunate number `3, 5, 7, 13` is prime — the evidence for
Fortune's conjecture in the recorded cases. -/
theorem fortunate_values_prime :
    (3 : ℕ).Prime ∧ (5 : ℕ).Prime ∧ (7 : ℕ).Prime ∧ (13 : ℕ).Prime := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> norm_num

/-! ### (3) Primorial identities — tie the bases to Mathlib's `primorial` -/

/-- `primorial 2 = 2`. -/
theorem primorial_2 : primorial 2 = 2 := by decide

/-- `primorial 3 = 6`. -/
theorem primorial_3 : primorial 3 = 6 := by decide

/-- `primorial 5 = 30`. -/
theorem primorial_5 : primorial 5 = 30 := by decide

/-- `primorial 7 = 210`. -/
theorem primorial_7 : primorial 7 = 210 := by decide

theorem fortunateFor_coprime {P m : ℕ} (hP : 0 < P) (h : FortunateFor P m) :
    Nat.Coprime m P := by
  obtain ⟨hm, hp, -⟩ := h
  have hd : Nat.gcd m P ∣ P + m :=
    Nat.dvd_add (Nat.gcd_dvd_right m P) (Nat.gcd_dvd_left m P)
  rcases hp.eq_one_or_self_of_dvd _ hd with h1 | h2
  · exact h1
  · have hle : Nat.gcd m P ≤ m := Nat.le_of_dvd (by omega) (Nat.gcd_dvd_left m P)
    omega

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
theorem fortunateFor_unique {P m m' : ℕ} (h : FortunateFor P m) (h' : FortunateFor P m') :
    m = m' := by
  obtain ⟨hm, hp, hmin⟩ := h
  obtain ⟨hm', hp', hmin'⟩ := h'
  rcases lt_trichotomy m m' with hlt | heq | hgt
  · exact absurd hp (hmin' m hm hlt)
  · exact heq
  · exact absurd hp' (hmin m' hm' hgt)

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
theorem fortunateFor_odd_of_even_base {P m : ℕ} (hP : 0 < P) (hE : Even P)
    (h : FortunateFor P m) : Odd m := by
  obtain ⟨hm, hp, -⟩ := h
  obtain ⟨t, ht⟩ := hE
  have hodd : Odd (P + m) := hp.odd_of_ne_two (by omega)
  obtain ⟨s, hs⟩ := hodd
  exact ⟨s - t, by omega⟩

theorem fortunateFor_not_dvd_base_prime {P m p : ℕ} (hP : 0 < P) (h : FortunateFor P m)
    (hp : p.Prime) (hpP : p ∣ P) : ¬ p ∣ m := by
  obtain ⟨hm, hprime, -⟩ := h
  intro hpm
  have hdvd : p ∣ P + m := Nat.dvd_add hpP hpm
  have hpe : p = P + m := ((Nat.Prime.eq_one_or_self_of_dvd hprime p hdvd).resolve_left
    hp.ne_one)
  have hle : p ≤ m := Nat.le_of_dvd (by omega) hpm
  omega

end Brockian.FortunateNumbers
