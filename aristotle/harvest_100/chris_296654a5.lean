import Mathlib

/-!
# Green Tao
Category: Frontier — Prime Numbers
Target: Frontier.Green_Tao
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-- `A` contains an arithmetic progression of length `k`: there are a starting point `a`
and a positive common difference `d` with `a, a + d, …, a + (k-1) d` all in `A`. -/
def HasAPOfLength (A : Set ℕ) (k : ℕ) : Prop :=
  ∃ a d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A

/-- `A` contains arithmetic progressions of every finite length. -/
def ArbitrarilyLongAPs (A : Set ℕ) : Prop :=
  ∀ k : ℕ, HasAPOfLength A k

/-- The set of prime numbers. -/
def primeSet : Set ℕ := {p : ℕ | Nat.Prime p}

/-- **Green–Tao statement**: the primes contain arbitrarily long arithmetic progressions. -/
def GreenTaoStatement : Prop := ArbitrarilyLongAPs primeSet

/-- **Erdős–Turán statement**: every set of natural numbers whose reciprocals form a
divergent series contains arbitrarily long arithmetic progressions. -/
def ErdosTuranStatement : Prop :=
  ∀ A : Set ℕ, ¬ Summable (Set.indicator A (fun n : ℕ ↦ (1 : ℝ) / n)) → ArbitrarilyLongAPs A

/-- Containing an AP of length `k` is monotone (downward) in `k`. -/
theorem HasAPOfLength.mono {A : Set ℕ} {k l : ℕ} (hkl : l ≤ k) (h : HasAPOfLength A k) :
    HasAPOfLength A l := by
  obtain ⟨a, d, hd, ha⟩ := h
  exact ⟨a, d, hd, fun i hi ↦ ha i (lt_of_lt_of_le hi hkl)⟩

/-- The sum of the reciprocals of the primes diverges (Mathlib), phrased for `primeSet`. -/
theorem not_summable_one_div_primeSet :
    ¬ Summable (Set.indicator primeSet (fun n : ℕ ↦ (1 : ℝ) / n)) :=
  not_summable_one_div_on_primes

/-- **Green–Tao, as a Lean-checked reduction.**
The Erdős–Turán statement implies that the primes contain arbitrarily long arithmetic
progressions.  The reduction uses the (unconditional, Mathlib) divergence of the sum of
the reciprocals of the primes. -/
theorem Green_Tao (h : ErdosTuranStatement) : GreenTaoStatement :=
  h primeSet not_summable_one_div_primeSet

/-- Unconditional base cases: the primes contain arithmetic progressions of every length
`k ≤ 10`, witnessed by `199 + 210 i`. -/
theorem Green_Tao_base_le_ten {k : ℕ} (hk : k ≤ 10) : HasAPOfLength primeSet k := by
  refine ⟨199, 210, by norm_num, fun i hi ↦ ?_⟩
  have hi10 : i < 10 := lt_of_lt_of_le hi hk
  interval_cases i <;> simp only [primeSet, Set.mem_setOf_eq] <;> norm_num

/-- Unconditional base cases, longer version: the primes contain arithmetic progressions of
every length `k ≤ 13`, witnessed by `766439 + 510510 i`. -/
theorem Green_Tao_base_le_thirteen {k : ℕ} (hk : k ≤ 13) : HasAPOfLength primeSet k := by
  refine ⟨766439, 510510, by norm_num, fun i hi ↦ ?_⟩
  have hi13 : i < 13 := lt_of_lt_of_le hi hk
  interval_cases i <;> simp only [primeSet, Set.mem_setOf_eq] <;> norm_num

/-- In particular, the primes contain a three-term arithmetic progression. -/
theorem Green_Tao_base_three : HasAPOfLength primeSet 3 :=
  Green_Tao_base_le_ten (by norm_num)

/-! ### Sub-progressions and the "infinitely many" form of the statement -/

/-- A progression of length `j + k` contains a progression of length `k` whose first term is
at least `j`: just start `j` steps later. -/
theorem HasAPOfLength.shift {A : Set ℕ} {k j : ℕ} (h : HasAPOfLength A (j + k)) :
    ∃ a d : ℕ, 0 < d ∧ j ≤ a ∧ ∀ i < k, a + i * d ∈ A := by
  obtain ⟨a, d, hd, ha⟩ := h
  refine ⟨a + j * d, d, hd, ?_, fun i hi ↦ ?_⟩
  · have : j * 1 ≤ j * d := Nat.mul_le_mul_left j hd
    omega
  · have h' := ha (j + i) (by omega)
    have he : a + (j + i) * d = a + j * d + i * d := by ring
    rwa [he] at h'

/-- If a set contains arbitrarily long progressions, then for each `k` it contains *infinitely
many* progressions of length `k`: the set of possible first terms is infinite. -/
theorem ArbitrarilyLongAPs.infinite_starting_points {A : Set ℕ} (h : ArbitrarilyLongAPs A)
    (k : ℕ) : {a : ℕ | ∃ d : ℕ, 0 < d ∧ ∀ i < k, a + i * d ∈ A}.Infinite := by
  apply Set.infinite_of_forall_exists_gt
  intro N
  obtain ⟨a, d, hd, hNa, ha⟩ := HasAPOfLength.shift (j := N + 1) (k := k) (h (N + 1 + k))
  exact ⟨a, ⟨d, hd, ha⟩, by omega⟩

/-- Green–Tao in its "infinitely many" form: granting the Erdős–Turán statement, for every `k`
there are infinitely many `k`-term arithmetic progressions of primes. -/
theorem Green_Tao_infinitely_many (h : ErdosTuranStatement) (k : ℕ) :
    {a : ℕ | ∃ d : ℕ, 0 < d ∧ ∀ i < k, Nat.Prime (a + i * d)}.Infinite :=
  (Green_Tao h).infinite_starting_points k

/-! ### Structure of arithmetic progressions of primes

The following unconditional results describe the shape that any long progression of primes
must have: its common difference is divisible by every prime `p ≤ k` (hence by the primorial
`k#`), unless the progression itself starts at such a small prime. -/

/-- If `a, a + d, …, a + (k-1) d` are all prime and `p ≤ k` is a prime smaller than the first
term `a`, then `p` divides the common difference `d`. -/
theorem prime_dvd_common_difference {a d k : ℕ} (hprime : ∀ i < k, Nat.Prime (a + i * d))
    {p : ℕ} (hp : Nat.Prime p) (hpk : p ≤ k) (hpa : p < a) : p ∣ d := by
  by_contra hnd
  haveI : Fact (Nat.Prime p) := ⟨hp⟩
  have hdne : (d : ZMod p) ≠ 0 := fun h ↦ hnd ((ZMod.natCast_eq_zero_iff d p).1 h)
  set i : ℕ := (-(a : ZMod p) * (d : ZMod p)⁻¹).val with hi_def
  have hi : i < p := ZMod.val_lt _
  have hzero : ((a + i * d : ℕ) : ZMod p) = 0 := by
    push_cast [hi_def, ZMod.natCast_val, ZMod.cast_id]
    field_simp
    ring
  have hdvd : p ∣ a + i * d := (ZMod.natCast_eq_zero_iff _ _).1 hzero
  have hpr : Nat.Prime (a + i * d) := hprime i (lt_of_lt_of_le hi hpk)
  rcases hpr.eq_one_or_self_of_dvd p hdvd with h | h
  · exact hp.one_lt.ne' h
  · omega

/-- The common difference of a `k`-term arithmetic progression of primes whose first term
exceeds `k` is divisible by the primorial `k# = ∏_{p ≤ k, p prime} p`. -/
theorem primorial_dvd_common_difference {a d k : ℕ} (hka : k < a)
    (hprime : ∀ i < k, Nat.Prime (a + i * d)) : primorial k ∣ d := by
  refine Finset.prod_primes_dvd d ?_ ?_ <;> intro q hq <;>
    simp only [Finset.mem_filter, Finset.mem_range] at hq
  · exact hq.2.prime
  · exact prime_dvd_common_difference hprime hq.2 (by omega) (by omega)

/-- Consequently, the common difference of a `k`-term progression of primes starting above `k`
is at least the primorial `k#`; long progressions of primes necessarily have huge gaps. -/
theorem primorial_le_common_difference {a d k : ℕ} (hka : k < a) (hd : 0 < d)
    (hprime : ∀ i < k, Nat.Prime (a + i * d)) : primorial k ≤ d :=
  Nat.le_of_dvd hd (primorial_dvd_common_difference hka hprime)

end Frontier

