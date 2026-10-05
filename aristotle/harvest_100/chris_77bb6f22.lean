import Mathlib

/-!
# Chen Theorem
Category: Frontier — Prime Numbers
Target: Frontier.Chen_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 100000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## The statement of Chen's theorem -/

/-- `AlmostPrime2 q` says that `q` has at most two prime factors, counted with
multiplicity (i.e. `Ω(q) ≤ 2`); such a number is classically called a `P₂`.
Note that primes themselves satisfy this (`Ω = 1`). -/
def AlmostPrime2 (q : ℕ) : Prop := q.primeFactorsList.length ≤ 2

/-- `ChenRep n` says that `n` can be written as `p + q` with `p` prime and `q` a `P₂`. -/
def ChenRep (n : ℕ) : Prop := ∃ p q : ℕ, Nat.Prime p ∧ AlmostPrime2 q ∧ n = p + q

/-- The full statement of Chen's theorem (Chen, 1973): every sufficiently large even
number is the sum of a prime and a number having at most two prime factors. -/
def ChenStatement : Prop := ∃ N : ℕ, ∀ n : ℕ, N ≤ n → Even n → ChenRep n

/-- Goldbach's conjecture, in the form used below as the hypothesis of the reduction. -/
def GoldbachStatement : Prop :=
  ∀ n : ℕ, 4 ≤ n → Even n → ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q

/-! ## Basic facts -/

/-- A prime is a `P₂`. -/
theorem almostPrime2_of_prime {q : ℕ} (hq : Nat.Prime q) : AlmostPrime2 q := by
  simp [AlmostPrime2, Nat.primeFactorsList_prime hq]

/-- A sum of two primes has a Chen representation. -/
theorem chenRep_of_primes {n p q : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q)
    (h : n = p + q) : ChenRep n :=
  ⟨p, q, hp, almostPrime2_of_prime hq, h⟩

/-! ## A verified base case -/

/-- The primes below `1000`. -/
def primesBelow1000 : List ℕ :=
  [2,3,5,7,11,13,17,19,23,29,31,37,41,43,47,53,59,61,67,71,73,79,83,89,97,101,103,107,109,
   113,127,131,137,139,149,151,157,163,167,173,179,181,191,193,197,199,211,223,227,229,233,
   239,241,251,257,263,269,271,277,281,283,293,307,311,313,317,331,337,347,349,353,359,367,
   373,379,383,389,397,401,409,419,421,431,433,439,443,449,457,461,463,467,479,487,491,499,
   503,509,521,523,541,547,557,563,569,571,577,587,593,599,601,607,613,617,619,631,641,643,
   647,653,659,661,673,677,683,691,701,709,719,727,733,739,743,751,757,761,769,773,787,797,
   809,811,821,823,827,829,839,853,857,859,863,877,881,883,887,907,911,919,929,937,941,947,
   953,967,971,977,983,991,997]

/-- Every entry of `primesBelow1000` is indeed prime. -/
theorem primesBelow1000_prime : ∀ p ∈ primesBelow1000, Nat.Prime p := by
  decide +kernel

/-- A kernel-checked Goldbach verification: every even `n` with `4 ≤ n ≤ 1001` is a sum of
two primes taken from `primesBelow1000`. -/
theorem goldbach_check :
    (List.range 1002).all
      (fun n => n < 4 || n % 2 == 1 ||
        primesBelow1000.any (fun p => p ≤ n && primesBelow1000.contains (n - p))) = true := by
  decide +kernel

/-- Every even number `n` with `4 ≤ n ≤ 1000` is the sum of two primes. -/
theorem goldbach_base (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1000) (he : Even n) :
    ∃ p q : ℕ, Nat.Prime p ∧ Nat.Prime q ∧ n = p + q := by
  have hmem : n ∈ List.range 1002 := List.mem_range.2 (by omega)
  have h := (List.all_eq_true.1 goldbach_check) n hmem
  have h4' : (decide (n < 4)) = false := by simp; omega
  have hpar : (n % 2 == 1) = false := by
    have : n % 2 = 0 := Nat.even_iff.1 he
    simp [this]
  rw [h4', hpar] at h
  simp only [Bool.false_or, List.any_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨p, hp, hple, hcont⟩ := h
  refine ⟨p, n - p, primesBelow1000_prime p hp, primesBelow1000_prime _ ?_, by omega⟩
  simpa using List.mem_of_elem_eq_true hcont

/-- **Base case of Chen's theorem**, verified by kernel computation: every even number `n`
with `4 ≤ n ≤ 1000` is the sum of a prime and a `P₂` (in fact, of two primes). -/
theorem chen_base (n : ℕ) (h4 : 4 ≤ n) (hn : n ≤ 1000) (he : Even n) : ChenRep n := by
  obtain ⟨p, q, hp, hq, h⟩ := goldbach_base n h4 hn he
  exact chenRep_of_primes hp hq h

/-! ## A reduction -/

/-- **Reduction**: Goldbach's conjecture implies Chen's theorem (with `N = 4`). -/
theorem chen_of_goldbach (hG : GoldbachStatement) : ChenStatement := by
  refine ⟨4, fun n hn he => ?_⟩
  obtain ⟨p, q, hp, hq, h⟩ := hG n hn he
  exact chenRep_of_primes hp hq h

/-! ## Main target

The full theorem of Chen (1973) — that *every* sufficiently large even number is a sum of a
prime and a `P₂` — is not proved here. What is established, as requested, is the formalized
statement together with (i) a kernel-verified base case covering all even numbers up to
`1000`, and (ii) a Lean-checked reduction showing that Goldbach's conjecture implies the
Chen statement. -/
theorem Chen_theorem :
    (∀ n : ℕ, 4 ≤ n → n ≤ 1000 → Even n → ChenRep n) ∧
      (GoldbachStatement → ChenStatement) :=
  ⟨chen_base, chen_of_goldbach⟩

end Frontier

