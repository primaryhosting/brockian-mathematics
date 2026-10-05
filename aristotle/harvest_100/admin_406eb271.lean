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
# Goldbach Covariance Transfer
Category: Brockian Conjecture
Target: Brockian.GoldbachComb.GoldbachCovarianceTransfer
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option autoImplicit false

namespace Brockian.GoldbachComb

/-! ## Primality (self-contained, no imports) -/

/-- `IsPrime p` : `p` is at least `2` and has no divisors other than `1` and `p`. -/
def IsPrime (p : Nat) : Prop := 2 ≤ p ∧ ∀ m, m ∣ p → m = 1 ∨ m = p

/-- A boolean primality test by trial division. -/
def primeB (n : Nat) : Bool :=
  (2 ≤ n) && (List.range n).all (fun m => (m < 2) || !(n % m == 0))

theorem isPrime_of_primeB {p : Nat} (h : primeB p = true) : IsPrime p := by
  simp only [primeB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, Bool.or_eq_true,
    Bool.not_eq_true', beq_eq_false_iff_ne, List.mem_range] at h
  obtain ⟨h2, hall⟩ := h
  refine ⟨h2, ?_⟩
  intro m hm
  by_cases hm1 : m = 1
  · exact Or.inl hm1
  by_cases hmp : m = p
  · exact Or.inr hmp
  exfalso
  have hp0 : 0 < p := by omega
  have hmle : m ≤ p := Nat.le_of_dvd hp0 hm
  have hmlt : m < p := by omega
  obtain ⟨k, rfl⟩ := hm
  have hmod : m * k % m = 0 := Nat.mul_mod_right m k
  have h3 := hall m hmlt
  simp [hmod] at h3
  have hm0 : m = 0 := by omega
  subst hm0
  simp at h2

/-! ## The Goldbach counting function -/

/-- The list of `p ≤ n` such that both `p` and `n - p` pass the primality test. -/
def goldbachPairs (n : Nat) : List Nat :=
  (List.range (n + 1)).filter (fun p => primeB p && primeB (n - p))

/-- `goldbachCount n` is the number of Goldbach representations `n = p + q`
(ordered pairs of primes), as an integer. -/
def goldbachCount (n : Nat) : Int := (goldbachPairs n).length

/-- `GoldbachRep n` : `n` is a sum of two primes. -/
def GoldbachRep (n : Nat) : Prop := ∃ p q, IsPrime p ∧ IsPrime q ∧ p + q = n

theorem goldbachCount_nonneg (n : Nat) : 0 ≤ goldbachCount n := by
  simp [goldbachCount]

/-- A nonzero Goldbach count witnesses a Goldbach representation. -/
theorem goldbachRep_of_count_ne_zero {n : Nat} (h : goldbachCount n ≠ 0) : GoldbachRep n := by
  have hne : goldbachPairs n ≠ [] := by
    intro hnil
    apply h
    simp [goldbachCount, hnil]
  obtain ⟨p, hp⟩ := List.exists_mem_of_ne_nil _ hne
  simp only [goldbachPairs, List.mem_filter, List.mem_range, Bool.and_eq_true] at hp
  obtain ⟨hlt, hp1, hp2⟩ := hp
  refine ⟨p, n - p, isPrime_of_primeB hp1, isPrime_of_primeB hp2, ?_⟩
  omega

/-! ## Sums and covariance over a finite index list -/

/-- Sum of `f` over the index list `S`. -/
def lsum (S : List Nat) (f : Nat → Int) : Int := (S.map f).sum

/-- The (unnormalized) covariance of `f` and `g` over `S`:
`|S| * ∑ f g - (∑ f) * (∑ g)`, i.e. `|S|²` times the empirical covariance. -/
def cov (S : List Nat) (f g : Nat → Int) : Int :=
  (S.length : Int) * lsum S (fun n => f n * g n) - lsum S f * lsum S g

/-- Indicator of the Goldbach failure set. -/
def failInd (n : Nat) : Int := if goldbachCount n = 0 then 1 else 0

theorem failInd_nonneg (n : Nat) : 0 ≤ failInd n := by
  unfold failInd; split <;> omega

theorem lsum_nil (f : Nat → Int) : lsum [] f = 0 := rfl

theorem lsum_cons (a : Nat) (S : List Nat) (f : Nat → Int) :
    lsum (a :: S) f = f a + lsum S f := rfl

theorem lsum_zero (S : List Nat) : lsum S (fun _ => 0) = 0 := by
  induction S with
  | nil => rfl
  | cons a S ih => rw [lsum_cons, ih]; rfl

theorem lsum_nonneg {S : List Nat} {f : Nat → Int} (hf : ∀ n ∈ S, 0 ≤ f n) : 0 ≤ lsum S f := by
  induction S with
  | nil => exact Int.le_refl 0
  | cons a S ih =>
      rw [lsum_cons]
      have h1 : 0 ≤ f a := hf a (List.mem_cons_self ..)
      have h2 : 0 ≤ lsum S f := ih (fun n hn => hf n (List.mem_cons_of_mem _ hn))
      omega

/-- A sum of nonnegative terms vanishes only if every term vanishes. -/
theorem eq_zero_of_lsum_eq_zero {S : List Nat} {f : Nat → Int}
    (hf : ∀ n ∈ S, 0 ≤ f n) (hsum : lsum S f = 0) : ∀ n ∈ S, f n = 0 := by
  induction S with
  | nil => intro n hn; cases hn
  | cons a S ih =>
      rw [lsum_cons] at hsum
      have h1 : 0 ≤ f a := hf a (List.mem_cons_self ..)
      have hS : ∀ n ∈ S, 0 ≤ f n := fun n hn => hf n (List.mem_cons_of_mem _ hn)
      have h2 : 0 ≤ lsum S f := lsum_nonneg hS
      have hfa : f a = 0 := by omega
      have htail : lsum S f = 0 := by omega
      intro n hn
      rcases List.mem_cons.mp hn with rfl | hn
      · exact hfa
      · exact ih hS htail n hn

/-! ## The covariance transfer identity -/

/-- **Covariance transfer.** Over any index list `S`, the covariance of the Goldbach
counting function with the indicator of the Goldbach-failure set is exactly minus the
product of their totals: the counting function is supported off the failure set, so all
of the covariance comes from the mean term. -/
theorem cov_goldbachCount_failInd (S : List Nat) :
    cov S goldbachCount failInd = -(lsum S goldbachCount * lsum S failInd) := by
  have hpt : (fun n => goldbachCount n * failInd n) = (fun _ => (0 : Int)) := by
    funext n
    by_cases h : goldbachCount n = 0
    · simp [h]
    · simp [failInd, h]
  simp [cov, hpt, lsum_zero]

/-- **Goldbach Covariance Transfer.**

Let `S` be any finite list of natural numbers on which the Goldbach counting function has
positive total mass. If the (unnormalized) empirical covariance over `S` between the
Goldbach counting function and the indicator of the Goldbach-failure set vanishes, then
Goldbach's property holds at every `n ∈ S`: each such `n` is a sum of two primes.

This is a Lean-checked conditional reduction: a covariance hypothesis on a finite window
`S` transfers to the full two-primes statement on that window. -/
theorem GoldbachCovarianceTransfer (S : List Nat)
    (hpos : 0 < lsum S goldbachCount)
    (hcov : cov S goldbachCount failInd = 0) :
    ∀ n ∈ S, GoldbachRep n := by
  have hid := cov_goldbachCount_failInd S
  rw [hcov] at hid
  have hprod : lsum S goldbachCount * lsum S failInd = 0 := by omega
  have hfail : lsum S failInd = 0 := by
    rcases Int.mul_eq_zero.mp hprod with h | h
    · omega
    · exact h
  intro n hn
  have hzero := eq_zero_of_lsum_eq_zero (fun m _ => failInd_nonneg m) hfail n hn
  have hcount : goldbachCount n ≠ 0 := by
    intro h
    simp [failInd, h] at hzero
  exact goldbachRep_of_count_ne_zero hcount

/-! ## Non-vacuity: the hypotheses are satisfiable -/

example : 0 < lsum [4] goldbachCount := by decide

example : cov [4] goldbachCount failInd = 0 := by decide

example : GoldbachRep 4 := GoldbachCovarianceTransfer [4] (by decide) (by decide) 4 (by simp)

/-- The transfer applied to a concrete window of even numbers. -/
example : ∀ n ∈ [4, 6, 8, 10, 12, 14, 16, 18, 20, 22, 24, 26, 28, 30], GoldbachRep n :=
  GoldbachCovarianceTransfer _ (by decide) (by decide)

end Brockian.GoldbachComb

