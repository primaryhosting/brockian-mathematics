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
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` before any command, including a module docstring, so the header
-- above is repeated verbatim as the module docstring immediately after the import.)

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RuthAaronPairs

/-! ## The sum-of-prime-factors function -/

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 0 = sopfr 1 = 0`). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- `n` is a *Ruth–Aaron pair* (more precisely, the smaller member of one) when `n ≥ 2` and
`n` and `n + 1` have the same sum of prime factors, counted with multiplicity. -/
def IsRuthAaronPair (n : ℕ) : Prop := 2 ≤ n ∧ sopfr n = sopfr (n + 1)

@[simp] lemma sopfr_one : sopfr 1 = 0 := by simp [sopfr]

lemma sopfr_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    sopfr (m * n) = sopfr m + sopfr n := by
  unfold sopfr
  rw [(Nat.perm_primeFactorsList_mul hm hn).sum_eq, List.sum_append]

lemma sopfr_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

/-- The sum of prime factors of a product of a list of primes is the sum of that list. -/
lemma sopfr_prod_primes : ∀ l : List ℕ, (∀ p ∈ l, Nat.Prime p) → sopfr l.prod = l.sum
  | [], _ => by simp
  | p :: l, h => by
      have hp : Nat.Prime p := h p (by simp)
      have hl : ∀ q ∈ l, Nat.Prime q := fun q hq => h q (by simp [hq])
      have hprod : l.prod ≠ 0 := by
        refine List.prod_ne_zero ?_
        intro h0
        exact (hl 0 h0).ne_zero rfl
      simp only [List.prod_cons, List.sum_cons]
      rw [sopfr_mul hp.ne_zero hprod, sopfr_prime hp, sopfr_prod_primes l hl]

/-! ## Small Ruth–Aaron pairs -/

theorem isRuthAaronPair_8 : IsRuthAaronPair 8 := by
  refine ⟨by norm_num, ?_⟩
  have h8 : (8 : ℕ) = [2, 2, 2].prod := by norm_num
  have h9 : (8 + 1 : ℕ) = [3, 3].prod := by norm_num
  rw [h9, h8, sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num),
    sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num)]
  norm_num

theorem isRuthAaronPair_15 : IsRuthAaronPair 15 := by
  refine ⟨by norm_num, ?_⟩
  have h1 : (15 : ℕ) = [3, 5].prod := by norm_num
  have h2 : (15 + 1 : ℕ) = [2, 2, 2, 2].prod := by norm_num
  rw [h2, h1, sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num),
    sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num)]
  norm_num

theorem isRuthAaronPair_77 : IsRuthAaronPair 77 := by
  refine ⟨by norm_num, ?_⟩
  have h1 : (77 : ℕ) = [7, 11].prod := by norm_num
  have h2 : (77 + 1 : ℕ) = [2, 3, 13].prod := by norm_num
  rw [h2, h1, sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num),
    sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num)]
  norm_num

theorem isRuthAaronPair_948 : IsRuthAaronPair 948 := by
  refine ⟨by norm_num, ?_⟩
  have h1 : (948 : ℕ) = [2, 2, 3, 79].prod := by norm_num
  have h2 : (948 + 1 : ℕ) = [13, 73].prod := by norm_num
  rw [h2, h1, sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num),
    sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num)]
  norm_num

/-! ## A parametric family of Ruth–Aaron pairs

For every `k` one has the polynomial identity

`4 * (k + 1) * (12 * k ^ 2 + 15 * k + 1) + 1 = (4 * k + 5) * (12 * k ^ 2 + 12 * k + 1)`

and the two sides have matching sums of prime factors as soon as `k + 1`, `4 * k + 5`,
`12 * k ^ 2 + 15 * k + 1` and `12 * k ^ 2 + 12 * k + 1` are all prime, because

`4 + (k + 1) + (12 * k ^ 2 + 15 * k + 1) = (4 * k + 5) + (12 * k ^ 2 + 12 * k + 1)`.
-/

/-- The candidate Ruth–Aaron number attached to a parameter `k`. -/
def familyMember (k : ℕ) : ℕ := 4 * (k + 1) * (12 * k ^ 2 + 15 * k + 1)

lemma familyMember_succ_eq (k : ℕ) :
    familyMember k + 1 = (4 * k + 5) * (12 * k ^ 2 + 12 * k + 1) := by
  unfold familyMember; ring

/-- The parameter `k = 2` produces the Ruth–Aaron pair `948`, `949`. -/
theorem familyMember_two : familyMember 2 = 948 := by norm_num [familyMember]

/-- **Key unconditional step.** If the four numbers `k + 1`, `4 * k + 5`,
`12 * k ^ 2 + 15 * k + 1`, `12 * k ^ 2 + 12 * k + 1` are all prime, then
`4 * (k + 1) * (12 * k ^ 2 + 15 * k + 1)` is a Ruth–Aaron number. -/
theorem isRuthAaronPair_familyMember {k : ℕ} (h1 : Nat.Prime (k + 1))
    (h2 : Nat.Prime (4 * k + 5)) (h3 : Nat.Prime (12 * k ^ 2 + 15 * k + 1))
    (h4 : Nat.Prime (12 * k ^ 2 + 12 * k + 1)) : IsRuthAaronPair (familyMember k) := by
  constructor
  · unfold familyMember; nlinarith [sq_nonneg k]
  · have hfour : sopfr 4 = 4 := by
      have h : (4 : ℕ) = [2, 2].prod := by norm_num
      rw [h, sopfr_prod_primes _ (by intro p hp; fin_cases hp <;> norm_num)]
      norm_num
    have hn : sopfr (familyMember k) = 4 + (k + 1) + (12 * k ^ 2 + 15 * k + 1) := by
      unfold familyMember
      rw [show 4 * (k + 1) * (12 * k ^ 2 + 15 * k + 1)
            = 4 * ((k + 1) * (12 * k ^ 2 + 15 * k + 1)) by ring,
        sopfr_mul (by norm_num) (Nat.mul_ne_zero h1.ne_zero h3.ne_zero),
        sopfr_mul h1.ne_zero h3.ne_zero, hfour, sopfr_prime h1, sopfr_prime h3]
      ring
    have hn1 : sopfr (familyMember k + 1) = (4 * k + 5) + (12 * k ^ 2 + 12 * k + 1) := by
      rw [familyMember_succ_eq, sopfr_mul h2.ne_zero h4.ne_zero, sopfr_prime h2, sopfr_prime h4]
    rw [hn, hn1]; ring

lemma familyMember_strictMono : StrictMono familyMember := by
  refine strictMono_nat_of_lt_succ fun k => ?_
  unfold familyMember
  nlinarith [sq_nonneg k, Nat.zero_le k]

/-! ## The Schinzel-type hypothesis and the conditional infinitude theorem -/

/-- The set of parameters `k` for which the four polynomial values
`k + 1`, `4 * k + 5`, `12 * k ^ 2 + 15 * k + 1`, `12 * k ^ 2 + 12 * k + 1` are all prime.
Each such `k` yields a Ruth–Aaron pair, by `isRuthAaronPair_familyMember`. -/
def admissibleParams : Set ℕ :=
  {k : ℕ | Nat.Prime (k + 1) ∧ Nat.Prime (4 * k + 5) ∧ Nat.Prime (12 * k ^ 2 + 15 * k + 1) ∧
    Nat.Prime (12 * k ^ 2 + 12 * k + 1)}

/-- A Schinzel/Bateman–Horn-type hypothesis: the four irreducible integer polynomials
`k + 1`, `4 * k + 5`, `12 * k ^ 2 + 15 * k + 1`, `12 * k ^ 2 + 12 * k + 1`
are simultaneously prime for infinitely many `k`.  (Smallest witnesses: `k = 2`, giving the
Ruth–Aaron pair `948 = 2 ^ 2 * 3 * 79`, `949 = 13 * 73`, and `k = 42`, giving
`3749428 = 2 ^ 2 * 43 * 21799`, `3749429 = 173 * 21673`.) -/
def SimultaneousPrimeHypothesis : Prop := admissibleParams.Infinite

/-- `k = 2` is admissible: it produces the Ruth–Aaron pair `948`, `949`. -/
theorem two_mem_admissibleParams : 2 ∈ admissibleParams := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> norm_num

/-- `k = 42` is admissible: it produces the Ruth–Aaron pair `3749428`, `3749429`. -/
theorem fortyTwo_mem_admissibleParams : 42 ∈ admissibleParams := by
  refine ⟨by norm_num, by norm_num, ?_, ?_⟩ <;> norm_num

/-- **Conditional Ruth–Aaron infinitude.** Granting the Schinzel-type simultaneous primality
hypothesis above, there are infinitely many `n` with `sopfr n = sopfr (n + 1)`, i.e. infinitely
many Ruth–Aaron pairs. -/
theorem RuthAaronInfinitude (H : SimultaneousPrimeHypothesis) :
    {n : ℕ | IsRuthAaronPair n}.Infinite := by
  have himg := H.image (familyMember_strictMono.injective.injOn)
  refine himg.mono ?_
  rintro _ ⟨k, ⟨h1, h2, h3, h4⟩, rfl⟩
  exact isRuthAaronPair_familyMember h1 h2 h3 h4

end Brockian.RuthAaronPairs

