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
# Cullen Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.CullenWoodall.CullenPrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
Note on the header: Lean 4 requires `import` to be the very first command of a file, so the
header above is a plain block comment (`/- ... -/`) rather than a module docstring (`/-! ... -/`);
its text is otherwise verbatim.

## Contents

* Cullen numbers `C n = n * 2 ^ n + 1` and Woodall numbers `W n = n * 2 ^ n - 1`.
* `CullenPrimeInfinitude` / `WoodallPrimeInfinitude`: Lean-checked *conditional reductions* of the
  (open) infinitude conjectures to the corresponding unboundedness hypotheses, together with
  `cullenPrimeConjecture_iff_unbounded` / `woodallPrimeConjecture_iff_unbounded`.
* Unconditional partial results: explicit arithmetic progressions of composite Cullen numbers
  (`p ∣ C (p - 2 + k * p * (p - 1))` for every odd prime `p`), the companion Woodall divisibility
  `p ∣ W ((p - 1) ^ 2)`, and the resulting infinitude of composite Cullen and Woodall numbers.

Nothing about Cullen or Woodall numbers is currently available in Mathlib; the arithmetic input
used here is Fermat's little theorem in the form `ZMod.pow_card_sub_one_eq_one`, together with
`Nat.exists_infinite_primes` and `Set.infinite_of_forall_exists_gt`.
-/

namespace Brockian.CullenWoodall

/-! ## Cullen numbers -/

/-- The `n`-th Cullen number `C n = n * 2 ^ n + 1`. -/
def cullen (n : ℕ) : ℕ := n * 2 ^ n + 1

/-- `n` indexes a *Cullen prime* when the `n`-th Cullen number is prime. -/
def IsCullenPrime (n : ℕ) : Prop := Nat.Prime (cullen n)

@[simp] theorem cullen_zero : cullen 0 = 1 := rfl

theorem cullen_strictMono : StrictMono cullen := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h2 : (0:ℕ) < 2 ^ n := Nat.two_pow_pos n
  have h : n * 2 ^ n < (n + 1) * 2 ^ (n + 1) :=
    calc n * 2 ^ n < (n + 1) * 2 ^ n :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.lt_succ_self n) (le_refl _) h2
      _ ≤ (n + 1) * 2 ^ (n + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
  simpa [cullen] using h

theorem cullen_injective : Function.Injective cullen := cullen_strictMono.injective

theorem lt_cullen (n : ℕ) : n < cullen n := by
  have : n ≤ n * 2 ^ n := Nat.le_mul_of_pos_right _ (Nat.two_pow_pos n)
  simpa [cullen] using Nat.lt_succ_of_le this

/-- For `n ≥ 2` the Cullen number `C n` exceeds `n + 2`; used to show that a prime dividing
`C n` is a *proper* divisor. -/
theorem add_two_lt_cullen {n : ℕ} (hn : 2 ≤ n) : n + 2 < cullen n := by
  have h4 : (4:ℕ) ≤ 2 ^ n := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmul : n * 4 ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h4
  simp only [cullen]
  omega

/-! ## The Cullen prime conjecture and its conditional reduction -/

/-- The Cullen prime conjecture: there are infinitely many `n` with `n * 2 ^ n + 1` prime.
This is an open problem; `CullenPrimeInfinitude` below is the corresponding conditional
reduction. -/
def CullenPrimeConjecture : Prop := {n : ℕ | IsCullenPrime n}.Infinite

/-- **Conditional reduction of the Cullen prime infinitude conjecture.**

The unconditional statement (there are infinitely many Cullen primes) is an open problem.
What is proved here is its reduction to an *unboundedness* hypothesis: if for every bound `N`
there is an index `n > N` for which the Cullen number `n * 2 ^ n + 1` is prime, then the set of
Cullen prime indices is infinite, the conjecture `CullenPrimeConjecture` holds, and the set of
Cullen primes themselves is an infinite set of primes. -/
theorem CullenPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (cullen n)) :
    {n : ℕ | IsCullenPrime n}.Infinite ∧ CullenPrimeConjecture ∧
      {p : ℕ | p.Prime ∧ ∃ n, cullen n = p}.Infinite := by
  have hinf : {n : ℕ | IsCullenPrime n}.Infinite := by
    refine Set.infinite_of_forall_exists_gt (fun a => ?_)
    obtain ⟨n, hn, hp⟩ := h a
    exact ⟨n, hp, hn⟩
  refine ⟨hinf, hinf, ?_⟩
  have himg : (cullen '' {n : ℕ | IsCullenPrime n}).Infinite :=
    hinf.image cullen_injective.injOn
  refine himg.mono ?_
  rintro p ⟨n, hn, rfl⟩
  exact ⟨hn, n, rfl⟩

/-- The Cullen prime conjecture is *equivalent* to the unboundedness hypothesis used in
`CullenPrimeInfinitude`. -/
theorem cullenPrimeConjecture_iff_unbounded :
    CullenPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (cullen n) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    exact (CullenPrimeInfinitude h).1

/-! ## Unconditional partial results for Cullen numbers

For every odd prime `p` and every `k`, the index `n = (p - 2) + k * p * (p - 1)` satisfies
`n ≡ -2 (mod p)` and `2 ^ n ≡ 2 ^ (p - 2) (mod p)`, whence
`C n ≡ -2 * 2 ^ (p - 2) + 1 = 1 - 2 ^ (p - 1) ≡ 0 (mod p)`
by Fermat's little theorem.  So each odd prime `p` kills a whole arithmetic progression of
Cullen numbers, and infinitely many Cullen numbers are composite. -/

theorem prime_dvd_cullen_progression {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (k : ℕ) :
    p ∣ cullen (p - 2 + k * (p * (p - 1))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using h
  have hferm : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  set n := p - 2 + k * (p * (p - 1)) with hn
  have hcast : ((cullen n : ℕ) : ZMod p) = 0 := by
    have hidx : ((n : ℕ) : ZMod p) = -2 := by
      have hsub : ((p - 2 : ℕ) : ZMod p) = -2 := by
        rw [Nat.cast_sub (by omega : 2 ≤ p), ZMod.natCast_self]
        push_cast
        ring
      have : ((n : ℕ) : ZMod p) = ((p - 2 : ℕ) : ZMod p) + k * ((p : ZMod p) * ((p - 1 : ℕ))) := by
        rw [hn]; push_cast; ring
      rw [this, hsub, ZMod.natCast_self]
      ring
    have hpow : (2 : ZMod p) ^ n = 2 ^ (p - 2) := by
      have hsplit : n = (p - 2) + (p - 1) * (k * p) := by
        rw [hn]; ring
      rw [hsplit, pow_add, pow_mul, hferm, one_pow, mul_one]
    have hexp : (2 : ZMod p) * 2 ^ (p - 2) = 2 ^ (p - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have hkey : (-2 : ZMod p) * 2 ^ (p - 2) = -(2 ^ (p - 1)) := by
      rw [← hexp]; ring
    have : ((cullen n : ℕ) : ZMod p) = ((n : ℕ) : ZMod p) * 2 ^ n + 1 := by
      simp [cullen]
    rw [this, hidx, hpow, hkey, hferm]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

/-- For every odd prime `p`, the prime `p` divides the Cullen number `C (p - 2)`. -/
theorem prime_dvd_cullen_sub_two {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ cullen (p - 2) := by
  simpa using prime_dvd_cullen_progression hp hp2 0

/-- Every Cullen number in the progression `C ((p - 2) + k * p * (p - 1))`, for `p` a prime
`≥ 5`, is composite. -/
theorem cullen_progression_not_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (k : ℕ) :
    ¬ IsCullenPrime (p - 2 + k * (p * (p - 1))) := by
  intro hprime
  set n := p - 2 + k * (p * (p - 1)) with hn
  have hn2 : 2 ≤ n := by omega
  have hdvd : p ∣ cullen n := prime_dvd_cullen_progression hp (by omega) k
  have hlt : p < cullen n := lt_of_le_of_lt (by omega) (add_two_lt_cullen hn2)
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

theorem cullen_sub_two_not_prime {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) :
    ¬ IsCullenPrime (p - 2) := by
  simpa using cullen_progression_not_prime hp hp5 0

/-- Infinitely many Cullen numbers are composite. -/
theorem infinite_cullen_not_prime : {n : ℕ | ¬ IsCullenPrime n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun a => ?_)
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max 5 (a + 3))
  refine ⟨p - 2, cullen_sub_two_not_prime hp (le_trans (le_max_left _ _) hple), ?_⟩
  have : a + 3 ≤ p := le_trans (le_max_right _ _) hple
  omega

/-! ## Woodall numbers

The companion family `W n = n * 2 ^ n - 1`, whose prime infinitude is open as well. -/

/-- The `n`-th Woodall number `W n = n * 2 ^ n - 1` (natural subtraction; `W 0 = 0`). -/
def woodall (n : ℕ) : ℕ := n * 2 ^ n - 1

/-- `n` indexes a *Woodall prime* when the `n`-th Woodall number is prime. -/
def IsWoodallPrime (n : ℕ) : Prop := Nat.Prime (woodall n)

theorem woodall_strictMono : StrictMono woodall := by
  apply strictMono_nat_of_lt_succ
  intro n
  have h : n * 2 ^ n < (n + 1) * 2 ^ (n + 1) :=
    calc n * 2 ^ n < (n + 1) * 2 ^ n :=
          Nat.mul_lt_mul_of_lt_of_le (Nat.lt_succ_self n) (le_refl _) (Nat.two_pow_pos n)
      _ ≤ (n + 1) * 2 ^ (n + 1) :=
          Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ n))
  have h2 : 2 ≤ (n + 1) * 2 ^ (n + 1) := by
    have : (2:ℕ) ≤ 2 ^ (n + 1) := Nat.one_lt_two_pow (by omega)
    calc (2:ℕ) ≤ 2 ^ (n + 1) := this
      _ ≤ (n + 1) * 2 ^ (n + 1) := Nat.le_mul_of_pos_left _ (by omega)
  simp only [woodall]
  omega

theorem woodall_injective : Function.Injective woodall := woodall_strictMono.injective

theorem lt_woodall {n : ℕ} (hn : 2 ≤ n) : n < woodall n := by
  have h4 : (4:ℕ) ≤ 2 ^ n := by
    calc (4:ℕ) = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have hmul : n * 4 ≤ n * 2 ^ n := Nat.mul_le_mul_left _ h4
  simp only [woodall]
  omega

/-- The Woodall prime conjecture: there are infinitely many `n` with `n * 2 ^ n - 1` prime.
This is open as well. -/
def WoodallPrimeConjecture : Prop := {n : ℕ | IsWoodallPrime n}.Infinite

/-- **Conditional reduction of the Woodall prime infinitude conjecture**, in exact analogy with
`CullenPrimeInfinitude`. -/
theorem WoodallPrimeInfinitude
    (h : ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (woodall n)) :
    {n : ℕ | IsWoodallPrime n}.Infinite ∧ WoodallPrimeConjecture ∧
      {p : ℕ | p.Prime ∧ ∃ n, woodall n = p}.Infinite := by
  have hinf : {n : ℕ | IsWoodallPrime n}.Infinite := by
    refine Set.infinite_of_forall_exists_gt (fun a => ?_)
    obtain ⟨n, hn, hp⟩ := h a
    exact ⟨n, hp, hn⟩
  refine ⟨hinf, hinf, ?_⟩
  have himg : (woodall '' {n : ℕ | IsWoodallPrime n}).Infinite :=
    hinf.image woodall_injective.injOn
  refine himg.mono ?_
  rintro p ⟨n, hn, rfl⟩
  exact ⟨hn, n, rfl⟩

theorem woodallPrimeConjecture_iff_unbounded :
    WoodallPrimeConjecture ↔ ∀ N : ℕ, ∃ n : ℕ, N < n ∧ Nat.Prime (woodall n) := by
  constructor
  · intro h N
    obtain ⟨n, hn, hlt⟩ := h.exists_gt N
    exact ⟨n, hlt, hn⟩
  · intro h
    exact (WoodallPrimeInfinitude h).1

/-! For an odd prime `p`, the index `n = (p - 1) ^ 2` satisfies `n ≡ 1 (mod p)` and
`2 ^ n = (2 ^ (p - 1)) ^ (p - 1) ≡ 1 (mod p)`, so `W n = n * 2 ^ n - 1 ≡ 0 (mod p)`. -/
theorem prime_dvd_woodall_sq {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    p ∣ woodall ((p - 1) ^ 2) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have h2ne : (2 : ZMod p) ≠ 0 := by
    have h : ((2 : ℕ) : ZMod p) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      intro hd
      have := Nat.le_of_dvd (by norm_num) hd
      omega
    simpa using h
  have hferm : (2 : ZMod p) ^ (p - 1) = 1 := ZMod.pow_card_sub_one_eq_one h2ne
  set n := (p - 1) ^ 2 with hn
  have hone : (1:ℕ) ≤ n * 2 ^ n := by
    have h1 : 1 ≤ n := by
      have : 2 ≤ p - 1 := by omega
      calc (1:ℕ) ≤ 2 ^ 2 := by norm_num
        _ ≤ (p - 1) ^ 2 := Nat.pow_le_pow_left this 2
    exact Nat.mul_pos h1 (Nat.two_pow_pos n)
  have hcast : ((woodall n : ℕ) : ZMod p) = 0 := by
    have hidx : ((n : ℕ) : ZMod p) = 1 := by
      have hsub : ((p - 1 : ℕ) : ZMod p) = -1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ p), ZMod.natCast_self]
        push_cast
        ring
      rw [hn]
      push_cast [hsub]
      ring
    have hpow : (2 : ZMod p) ^ n = 1 := by
      have : n = (p - 1) * (p - 1) := by rw [hn]; ring
      rw [this, pow_mul, hferm, one_pow]
    have hw : ((woodall n : ℕ) : ZMod p) = ((n : ℕ) : ZMod p) * 2 ^ n - 1 := by
      simp only [woodall]
      rw [Nat.cast_sub hone]
      push_cast
      ring
    rw [hw, hidx, hpow]
    ring
  exact (ZMod.natCast_eq_zero_iff _ _).mp hcast

theorem woodall_sq_not_prime {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) :
    ¬ IsWoodallPrime ((p - 1) ^ 2) := by
  intro hprime
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  set n := (p - 1) ^ 2 with hn
  have hpn : p ≤ n := by
    have h1 : p - 1 + 1 = p := by omega
    have h2 : 2 ≤ p - 1 := by omega
    have : (p - 1) * 2 ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_left _ h2
    have hsq : n = (p - 1) * (p - 1) := by rw [hn]; ring
    omega
  have hn2 : 2 ≤ n := by omega
  have hdvd : p ∣ woodall n := prime_dvd_woodall_sq hp hp2
  have hlt : p < woodall n := lt_of_le_of_lt hpn (lt_woodall hn2)
  rcases hprime.eq_one_or_self_of_dvd p hdvd with h | h
  · omega
  · omega

/-- Infinitely many Woodall numbers are composite. -/
theorem infinite_woodall_not_prime : {n : ℕ | ¬ IsWoodallPrime n}.Infinite := by
  refine Set.infinite_of_forall_exists_gt (fun a => ?_)
  obtain ⟨p, hple, hp⟩ := Nat.exists_infinite_primes (max 3 (a + 2))
  have h3 : 3 ≤ p := le_trans (le_max_left _ _) hple
  have ha : a + 2 ≤ p := le_trans (le_max_right _ _) hple
  refine ⟨(p - 1) ^ 2, woodall_sq_not_prime hp (by omega), ?_⟩
  have hsq : (p - 1) ^ 2 = (p - 1) * (p - 1) := by ring
  have : (p - 1) * 2 ≤ (p - 1) * (p - 1) := Nat.mul_le_mul_left _ (by omega)
  omega

end Brockian.CullenWoodall

