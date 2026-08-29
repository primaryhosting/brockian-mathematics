/-!
# Goldbach Wheel K 2 947
Category: Brockian Corpus
Target: Brockian.GoldbachWheelK2_947
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxRecDepth 100000

namespace Brockian

/-- Elementary primality predicate: `p` is at least `2` and its only divisors are `1` and `p`. -/
def IsPrimeNat (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- Trial division search: `noDivFrom n fuel d` is `true` when no `e` with `d ≤ e`,
`e * e ≤ n` (reachable within `fuel` steps) divides `n`. -/
def noDivFrom (n : Nat) : Nat → Nat → Bool
  | 0, _ => true
  | fuel + 1, d => if n < d * d then true else if n % d == 0 then false else noDivFrom n fuel (d + 1)

/-- Boolean primality test by trial division up to the square root. -/
def isPrimeB (n : Nat) : Bool := (2 ≤ n) && noDivFrom n n 2

/-- Search for a representation `n = p + q` with `p` prime and `q` prime, trying `p = 2, 3, …`. -/
def hasRepAux (n : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, p =>
      if n < p then false
      else if isPrimeB p && isPrimeB (n - p) then true
      else hasRepAux n fuel (p + 1)

/-- `hasRep n` is `true` when the search finds a representation of `n` as a sum of two primes. -/
def hasRep (n : Nat) : Bool := hasRepAux n (n + 1) 2

theorem noDivFrom_spec (n : Nat) :
    ∀ fuel d e, noDivFrom n fuel d = true → d ≤ e → e < d + fuel → e * e ≤ n → n % e ≠ 0 := by
  intro fuel
  induction fuel with
  | zero => intro d e _ h1 h2 _; omega
  | succ f ih =>
    intro d e h hde helt hee
    rw [noDivFrom] at h
    split at h
    · rename_i hlt
      have : d * d ≤ e * e := Nat.mul_le_mul hde hde
      omega
    · rename_i hge
      split at h
      · exact absurd h (by simp)
      · rename_i hmod
        rw [beq_iff_eq] at hmod
        rcases Nat.eq_or_lt_of_le hde with rfl | hlt
        · exact hmod
        · exact ih (d + 1) e h hlt (by omega) hee

theorem isPrimeB_spec {n : Nat} (h : isPrimeB n = true) : IsPrimeNat n := by
  rw [isPrimeB, Bool.and_eq_true] at h
  obtain ⟨h2, hnd⟩ := h
  have hn2 : 2 ≤ n := by simpa using h2
  have key : ∀ e, 2 ≤ e → e * e ≤ n → n % e ≠ 0 := by
    intro e he2 hee
    have hle : e ≤ e * e := Nat.le_mul_of_pos_right e (by omega)
    exact noDivFrom_spec n n 2 e hnd he2 (by omega) hee
  refine ⟨hn2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmn : m = n
  · exact Or.inr hmn
  exfalso
  obtain ⟨k, hk⟩ := hm
  have hm0 : m ≠ 0 := by
    intro h0; subst h0; simp at hk; omega
  have hk0 : k ≠ 0 := by
    intro h0; subst h0; simp at hk; omega
  have hk1 : k ≠ 1 := by
    intro h1; subst h1; simp at hk; exact hmn hk.symm
  have hm2 : 2 ≤ m := by omega
  have hk2 : 2 ≤ k := by omega
  rcases Nat.le_total m k with hmk | hkm
  · have hmm : m * m ≤ n := by
      calc m * m ≤ m * k := Nat.mul_le_mul_left m hmk
        _ = n := hk.symm
    exact key m hm2 hmm (by rw [hk]; exact Nat.mul_mod_right m k)
  · have hkk : k * k ≤ n := by
      calc k * k ≤ m * k := Nat.mul_le_mul_right k hkm
        _ = n := hk.symm
    exact key k hk2 hkk (by rw [hk]; exact Nat.mul_mod_left m k)

theorem hasRepAux_spec (n : Nat) :
    ∀ fuel p, hasRepAux n fuel p = true →
      ∃ a b, isPrimeB a = true ∧ isPrimeB b = true ∧ a + b = n := by
  intro fuel
  induction fuel with
  | zero => intro p h; exact absurd h (by simp [hasRepAux])
  | succ f ih =>
    intro p h
    rw [hasRepAux] at h
    split at h
    · exact absurd h (by simp)
    · rename_i hpn
      split at h
      · rename_i hpr
        rw [Bool.and_eq_true] at hpr
        exact ⟨p, n - p, hpr.1, hpr.2, by omega⟩
      · exact ih (p + 1) h

theorem hasRep_spec {n : Nat} (h : hasRep n = true) :
    ∃ p q, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  obtain ⟨a, b, ha, hb, hab⟩ := hasRepAux_spec n (n + 1) 2 h
  exact ⟨a, b, isPrimeB_spec ha, isPrimeB_spec hb, hab⟩

/-- **Goldbach wheel, `K = 2`, modulus `947`.**
Every even `n` with `4 ≤ n ≤ 947` is a sum of two primes. -/
theorem GoldbachWheelK2_947 (n : Nat) (heven : n % 2 = 0) (h4 : 4 ≤ n) (hle : n ≤ 947) :
    ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = n := by
  have H : ∀ m < 948, m % 2 = 0 → 4 ≤ m → hasRep m = true := by decide
  exact hasRep_spec (H n (by omega) heven h4)

/-- Sanity check that the hypotheses of the theorem are satisfiable. -/
example : ∃ p q : Nat, IsPrimeNat p ∧ IsPrimeNat q ∧ p + q = 946 :=
  GoldbachWheelK2_947 946 rfl (by omega) (by omega)

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

