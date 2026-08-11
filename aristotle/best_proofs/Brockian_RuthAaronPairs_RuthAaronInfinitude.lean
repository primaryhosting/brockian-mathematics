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

import Mathlib

/-!
# Ruth Aaron Infinitude
Category: Brockian Conjecture
Target: Brockian.RuthAaronPairs.RuthAaronInfinitude
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Brockian.RuthAaronPairs

/-- `sopfr n` is the sum of the prime factors of `n`, counted with multiplicity
(`sopfr 0 = sopfr 1 = 0`). -/
def sopfr (n : ℕ) : ℕ := (Nat.primeFactorsList n).sum

/-- A *Ruth–Aaron pair* is a pair of consecutive integers `n, n+1` (with `n ≥ 2`) whose
sums of prime factors, counted with multiplicity, agree. -/
def IsRuthAaronPair (n : ℕ) : Prop := 2 ≤ n ∧ sopfr n = sopfr (n + 1)

@[simp] lemma sopfr_one : sopfr 1 = 0 := by simp [sopfr]

lemma sopfr_prime {p : ℕ} (hp : p.Prime) : sopfr p = p := by
  simp [sopfr, Nat.primeFactorsList_prime hp]

/-- `sopfr` is completely additive. -/
lemma sopfr_mul {m n : ℕ} (hm : m ≠ 0) (hn : n ≠ 0) :
    sopfr (m * n) = sopfr m + sopfr n := by
  have h := (Nat.perm_primeFactorsList_mul hm hn).sum_eq
  simpa [sopfr] using h

/-! ## The construction

For `a ≥ 1` put `k := sopfr (a+1) - sopfr a` (assumed to be a genuine natural difference,
i.e. `sopfr (a+1) = sopfr a + k`), and set
`p := (a+1) * k + 1`, `q := a * k + 1`.
Then `a * p + 1 = (a+1) * q`, and if `p` and `q` are both prime then `n := a * p` is a
Ruth–Aaron pair, since
`sopfr (a * p) = sopfr a + p` and `sopfr ((a+1) * q) = sopfr a + k + a*k + 1 = sopfr a + p`.
-/

/-- The data of a "seed" for the construction of a Ruth–Aaron pair. -/
def RuthAaronSeed (a k : ℕ) : Prop :=
  1 ≤ a ∧ sopfr (a + 1) = sopfr a + k ∧ Nat.Prime ((a + 1) * k + 1) ∧ Nat.Prime (a * k + 1)

/-- The key algebraic identity behind the construction. -/
lemma succ_mul_seed (a k : ℕ) : a * ((a + 1) * k + 1) + 1 = (a + 1) * (a * k + 1) := by
  ring

/-- **Construction lemma.** Every seed produces a Ruth–Aaron pair. -/
theorem isRuthAaronPair_of_seed {a k : ℕ} (h : RuthAaronSeed a k) :
    IsRuthAaronPair (a * ((a + 1) * k + 1)) := by
  obtain ⟨ha, hk, hp, hq⟩ := h
  set p := (a + 1) * k + 1 with hpdef
  set q := a * k + 1 with hqdef
  have ha0 : a ≠ 0 := by omega
  have ha1 : a + 1 ≠ 0 := by omega
  have hp0 : p ≠ 0 := hp.pos.ne'
  have hq0 : q ≠ 0 := hq.pos.ne'
  refine ⟨?_, ?_⟩
  · have h2 : 2 ≤ p := hp.two_le
    calc 2 = 1 * 2 := by ring
    _ ≤ a * p := Nat.mul_le_mul ha h2
  · rw [succ_mul_seed a k, sopfr_mul ha0 hp0, sopfr_mul ha1 hq0,
      sopfr_prime hp, sopfr_prime hq, hk]
    simp only [hpdef, hqdef]
    ring

/-- The Dickson/Schinzel-type hypothesis under which we obtain infinitely many Ruth–Aaron
pairs: there are arbitrarily large `a` for which the pair of linear forms attached to
`k = sopfr (a+1) - sopfr a` takes prime values simultaneously. -/
def RuthAaronSeedsUnbounded : Prop := ∀ N : ℕ, ∃ a k : ℕ, N ≤ a ∧ RuthAaronSeed a k

/-- **Main theorem (conditional).** If seeds occur with arbitrarily large `a`, then there
are infinitely many Ruth–Aaron pairs. -/
theorem RuthAaronInfinitude (H : RuthAaronSeedsUnbounded) :
    {n : ℕ | IsRuthAaronPair n}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨a, k, haN, hseed⟩ := H (N + 1)
  refine ⟨a * ((a + 1) * k + 1), isRuthAaronPair_of_seed hseed, ?_⟩
  have h2 : 1 ≤ (a + 1) * k + 1 := hseed.2.2.1.one_lt.le.trans' (by omega)
  calc N < a := by omega
  _ = a * 1 := by ring
  _ ≤ a * ((a + 1) * k + 1) := Nat.mul_le_mul_left a h2

/-! ## Unconditional examples

The construction is not vacuous: the seed `a = 1, k = 2` produces the smallest Ruth–Aaron
pair `(5, 6)`, and we record a few further pairs directly. -/

lemma sopfr_prime_mul {p m : ℕ} (hp : p.Prime) (hm : m ≠ 0) :
    sopfr (p * m) = p + sopfr m := by
  rw [sopfr_mul hp.pos.ne' hm, sopfr_prime hp]

lemma ruthAaronSeed_one_two : RuthAaronSeed 1 2 :=
  ⟨le_refl 1, by rw [sopfr_prime Nat.prime_two, sopfr_one], by norm_num, by norm_num⟩

/-- The smallest Ruth–Aaron pair, `(5, 6)`, produced by the seed `a = 1, k = 2`. -/
lemma isRuthAaronPair_five : IsRuthAaronPair 5 := by
  have h := isRuthAaronPair_of_seed ruthAaronSeed_one_two
  norm_num at h
  exact h

/-- A nontrivial seed: `a = 12`, `k = sopfr 13 - sopfr 12 = 13 - 7 = 6`, with
`13 * 6 + 1 = 79` and `12 * 6 + 1 = 73` both prime. -/
lemma ruthAaronSeed_twelve_six : RuthAaronSeed 12 6 := by
  refine ⟨by norm_num, ?_, by norm_num, by norm_num⟩
  rw [show (12 + 1 : ℕ) = 13 from rfl, show (12 : ℕ) = 2 * (2 * 3) from rfl,
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 13), sopfr_prime (by norm_num : Nat.Prime 3)]

/-- The Ruth–Aaron pair `(948, 949)` produced by the seed `a = 12, k = 6`:
`948 = 2^2 · 3 · 79` and `949 = 13 · 73`, both with prime factor sum `86`. -/
lemma isRuthAaronPair_948 : IsRuthAaronPair 948 := by
  have h := isRuthAaronPair_of_seed ruthAaronSeed_twelve_six
  norm_num at h
  exact h

/-- `(8, 9)` : `2+2+2 = 3+3`. -/
lemma isRuthAaronPair_eight : IsRuthAaronPair 8 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (8 : ℕ) = 2 * (2 * 2) from rfl, show (8 + 1 : ℕ) = 3 * 3 from rfl,
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 3) (by norm_num),
    sopfr_prime Nat.prime_two, sopfr_prime (by norm_num : Nat.Prime 3)]

/-- `(15, 16)` : `3+5 = 2+2+2+2`. -/
lemma isRuthAaronPair_fifteen : IsRuthAaronPair 15 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (15 : ℕ) = 3 * 5 from rfl, show (15 + 1 : ℕ) = 2 * (2 * (2 * 2)) from rfl,
    sopfr_prime_mul (by norm_num : Nat.Prime 3) (by norm_num),
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime Nat.prime_two, sopfr_prime (by norm_num : Nat.Prime 5)]

/-- `(77, 78)` : `7+11 = 2+3+13`. -/
lemma isRuthAaronPair_seventySeven : IsRuthAaronPair 77 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (77 : ℕ) = 7 * 11 from rfl, show (77 + 1 : ℕ) = 2 * (3 * 13) from rfl,
    sopfr_prime_mul (by norm_num : Nat.Prime 7) (by norm_num),
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 3) (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 11), sopfr_prime (by norm_num : Nat.Prime 13)]

/-- `(714, 715)` : the Ruth–Aaron pair, `2+3+7+17 = 5+11+13 = 29`. -/
lemma isRuthAaronPair_sevenHundredFourteen : IsRuthAaronPair 714 := by
  refine ⟨by norm_num, ?_⟩
  rw [show (714 : ℕ) = 2 * (3 * (7 * 17)) from rfl,
    show (714 + 1 : ℕ) = 5 * (11 * 13) from rfl,
    sopfr_prime_mul Nat.prime_two (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 3) (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 7) (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 5) (by norm_num),
    sopfr_prime_mul (by norm_num : Nat.Prime 11) (by norm_num),
    sopfr_prime (by norm_num : Nat.Prime 17), sopfr_prime (by norm_num : Nat.Prime 13)]

end Brockian.RuthAaronPairs

#print axioms Brockian.RuthAaronPairs.RuthAaronInfinitude
#print axioms Brockian.RuthAaronPairs.isRuthAaronPair_of_seed
#print axioms Brockian.RuthAaronPairs.isRuthAaronPair_948

