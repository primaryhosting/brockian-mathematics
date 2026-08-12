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
# Mersenne Prime Infinitude
Category: Brockian Conjecture
Target: Brockian.MersennePerfect.MersennePrimeInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` lines to precede any module docstring `/-! ... -/`, so the
-- header above is written as a plain block comment; its text is otherwise verbatim.)
import Mathlib
import Archive.Wiedijk100Theorems.PerfectNumbers

/-!
The infinitude of Mersenne primes is a famous open problem, so what is established here is a
Lean-checked **conditional reduction**: the set of Mersenne primes is infinite **if and only if**
the set of even perfect numbers is infinite.  The main target
`Brockian.MersennePerfect.MersennePrimeInfinitude` is the substantive direction: from the
infinitude of even perfect numbers one obtains infinitely many primes `p` with `2 ^ p - 1` prime.

The bridge is the Euclid–Euler theorem (available in Mathlib's archive as
`Theorems100.Nat.even_and_perfect_iff`).
-/

namespace Brockian.MersennePerfect

/-- `p` is a *Mersenne exponent* when `mersenne p = 2 ^ p - 1` is prime. -/
def MersenneExponent (p : ℕ) : Prop := (mersenne p).Prime

/-- `n` is an even perfect number. -/
def EvenPerfect (n : ℕ) : Prop := Even n ∧ n.Perfect

/-- The set of Mersenne exponents. -/
def mersenneExponents : Set ℕ := {p | MersenneExponent p}

/-- The set of even perfect numbers. -/
def evenPerfects : Set ℕ := {n | EvenPerfect n}

/-- The Euclid–Euler theorem, restated in the vocabulary of this file. -/
theorem evenPerfect_iff {n : ℕ} :
    EvenPerfect n ↔ ∃ k : ℕ, MersenneExponent (k + 1) ∧ n = 2 ^ k * mersenne (k + 1) :=
  Theorems100.Nat.even_and_perfect_iff

/-- The Euclid map `k ↦ 2 ^ k * (2 ^ (k + 1) - 1)` is strictly monotone. -/
theorem strictMono_euclidMap : StrictMono fun k : ℕ => 2 ^ k * mersenne (k + 1) := by
  intro a b hab
  have h1 : (2 : ℕ) ^ a < 2 ^ b := Nat.pow_lt_pow_right (by norm_num) hab
  have h2 : mersenne (a + 1) < mersenne (b + 1) :=
    strictMono_mersenne (by omega)
  exact Nat.mul_lt_mul_of_lt_of_lt h1 h2

/-- The Euclid map is injective. -/
theorem injective_euclidMap : Function.Injective fun k : ℕ => 2 ^ k * mersenne (k + 1) :=
  strictMono_euclidMap.injective

/-- Zero is not a Mersenne exponent, since `mersenne 0 = 0`. -/
theorem mersenneExponent_ne_zero {p : ℕ} (hp : MersenneExponent p) : p ≠ 0 := by
  rintro rfl
  exact Nat.not_prime_zero (by simpa [MersenneExponent, mersenne] using hp)

/-- A Mersenne exponent is itself prime. -/
theorem prime_of_mersenneExponent {p : ℕ} (hp : MersenneExponent p) : p.Prime :=
  Nat.Prime.of_mersenne hp

/-- Every even perfect number is the image, under the Euclid map, of a shifted Mersenne
exponent. -/
theorem evenPerfects_subset_image :
    evenPerfects ⊆ (fun k : ℕ => 2 ^ k * mersenne (k + 1)) '' {k : ℕ | MersenneExponent (k + 1)} := by
  intro n hn
  obtain ⟨k, hk, rfl⟩ := evenPerfect_iff.1 hn
  exact ⟨k, hk, rfl⟩

/-- Conversely, the Euclid map sends shifted Mersenne exponents to even perfect numbers. -/
theorem image_subset_evenPerfects :
    (fun k : ℕ => 2 ^ k * mersenne (k + 1)) '' {k : ℕ | MersenneExponent (k + 1)} ⊆
      evenPerfects := by
  rintro n ⟨k, hk, rfl⟩
  exact evenPerfect_iff.2 ⟨k, hk, rfl⟩

/-- If there are infinitely many even perfect numbers, then there are infinitely many
Mersenne exponents. -/
theorem infinite_mersenneExponents_of_infinite_evenPerfects
    (h : evenPerfects.Infinite) : mersenneExponents.Infinite := by
  intro hfin
  apply h
  have hshift : {k : ℕ | MersenneExponent (k + 1)} = (fun k : ℕ => k + 1) ⁻¹' mersenneExponents :=
    rfl
  have hK : {k : ℕ | MersenneExponent (k + 1)}.Finite := by
    rw [hshift]
    exact hfin.preimage (Set.injOn_of_injective (fun a b hab => by omega))
  exact (hK.image _).subset evenPerfects_subset_image

/-- If there are infinitely many Mersenne exponents, then there are infinitely many
even perfect numbers. -/
theorem infinite_evenPerfects_of_infinite_mersenneExponents
    (h : mersenneExponents.Infinite) : evenPerfects.Infinite := by
  have hsub : mersenneExponents ⊆ (fun k : ℕ => k + 1) '' {k : ℕ | MersenneExponent (k + 1)} := by
    intro p hp
    refine ⟨p - 1, ?_, ?_⟩
    · have := mersenneExponent_ne_zero hp
      simpa [Set.mem_setOf_eq, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.2 this)] using hp
    · have := mersenneExponent_ne_zero hp
      show p - 1 + 1 = p
      omega
  have hK : {k : ℕ | MersenneExponent (k + 1)}.Infinite := by
    intro hfin
    exact h ((hfin.image _).subset hsub)
  exact (hK.image (Set.injOn_of_injective injective_euclidMap)).mono image_subset_evenPerfects

/-- **Main conditional reduction.**  The set of Mersenne primes is infinite if and only if the
set of even perfect numbers is infinite. -/
theorem infinite_mersenneExponents_iff :
    mersenneExponents.Infinite ↔ evenPerfects.Infinite :=
  ⟨infinite_evenPerfects_of_infinite_mersenneExponents,
    infinite_mersenneExponents_of_infinite_evenPerfects⟩

/-- **Mersenne Prime Infinitude (conditional).**  If there are infinitely many even perfect
numbers, then there are infinitely many primes `p` for which the Mersenne number `2 ^ p - 1`
is prime.  (The unconditional statement is a well-known open problem.) -/
theorem MersennePrimeInfinitude (h : {n : ℕ | Even n ∧ n.Perfect}.Infinite) :
    {p : ℕ | p.Prime ∧ (mersenne p).Prime}.Infinite := by
  have h' : evenPerfects.Infinite := h
  have := infinite_mersenneExponents_of_infinite_evenPerfects h'
  refine Set.Infinite.mono ?_ this
  intro p hp
  exact ⟨prime_of_mersenneExponent hp, hp⟩

/-- A concrete unconditional partial result: `2, 3, 5, 7, 13` are Mersenne exponents, so there
are at least five Mersenne primes. -/
theorem five_mersenneExponents :
    ∀ p ∈ ({2, 3, 5, 7, 13} : Finset ℕ), MersenneExponent p := by
  intro p hp
  fin_cases hp <;>
    · rw [MersenneExponent, show mersenne = fun n => 2 ^ n - 1 from rfl]
      norm_num

end Brockian.MersennePerfect

#print axioms Brockian.MersennePerfect.MersennePrimeInfinitude
#print axioms Brockian.MersennePerfect.infinite_mersenneExponents_iff
#print axioms Brockian.MersennePerfect.five_mersenneExponents

