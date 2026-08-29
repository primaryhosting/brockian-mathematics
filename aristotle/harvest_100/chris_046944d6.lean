/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Dependency graph

The goal of this file is to decompose Pollack's theorem (*the set of betrothed,
a.k.a. quasi-amicable, numbers has asymptotic density zero*) into small,
independently reusable pieces, and to prove every piece of the decomposition
that is currently within reach.  The remaining, genuinely analytic, node is
isolated as an explicit hypothesis of the main reduction theorem — it is *not*
assumed anywhere else in the file, and no axiom is added.

```
                      density_zero_reduction            (proved, conditional)
                                 ▲
                                 │
        count_betrothed_le_two_mul_count_witness        (proved)
                ▲                              ▲
                │                              │
   smaller_mem_quasiAmicableWitness     partner_injOn_betrothed   (proved)
                ▲                              ▲
                │                              │
        IsBetrothedPair.symm / partner_eq / sigma1 lemmas         (proved)

   hypothesis node (open, supplied as an argument):
        HasDensityZero quasiAmicableWitness
        i.e.  #{m ≤ x : 2m+1 < σ(m) and σ(σ(m)-m-1) = σ(m)} = o(x)
```

The hypothesis node is *weaker* than Pollack's theorem in the sense that it is a
statement about a set defined by a purely `σ`-arithmetic condition (no
existential quantifier over partners), which is the shape that the
Erdős-type machinery for amicable numbers is usually applied to.  The reduction
theorem shows that density zero for that set already implies density zero for
the full set of betrothed numbers, by
* observing that the smaller member of a betrothed pair lies in that set, and
* showing that the partner map is injective on the betrothed numbers and sends
  the larger member of a pair to the smaller one, which is below it.

Supporting reusable material proved here:
* a small toolkit for asymptotic density zero (`HasDensityZero`): monotonicity,
  closure under unions, finite sets, and a comparison criterion;
* elementary structure theory of betrothed numbers: uniqueness of the partner,
  the smaller member is abundant, the larger member is deficient, betrothed
  numbers are composite;
* every nondeficient number has a primitive nondeficient divisor (the entry
  point to Erdős' method).
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

set_option grind.warning false

namespace Brockian
namespace BetrothedNumbers

open Filter Topology Finset

/-! ## Sum-of-divisors basics -/

/-- `sigma1 n` is the sum of the divisors of `n`. -/
def sigma1 (n : ℕ) : ℕ := ∑ d ∈ n.divisors, d

lemma sigma1_zero : sigma1 0 = 0 := by simp [sigma1]

lemma sigma1_one : sigma1 1 = 1 := by decide

/-- For `n ≥ 1` the number `n` itself is a divisor, so `n ≤ σ(n)`. -/
lemma self_le_sigma1 {n : ℕ} (hn : 0 < n) : n ≤ sigma1 n := by
  refine Finset.single_le_sum (f := fun d => d) (fun i _ => Nat.zero_le i) ?_
  exact Nat.mem_divisors_self n hn.ne'

/-- For `n ≥ 2` both `1` and `n` are divisors, so `n + 1 ≤ σ(n)`. -/
lemma succ_le_sigma1 {n : ℕ} (hn : 1 < n) : n + 1 ≤ sigma1 n := by
  have hsub : ({1, n} : Finset ℕ) ⊆ n.divisors := by
    intro d hd
    simp only [Finset.mem_insert, Finset.mem_singleton] at hd
    rcases hd with rfl | rfl
    · exact Nat.one_mem_divisors.2 (by omega)
    · exact Nat.mem_divisors_self d (by omega)
  have hcalc : ∑ d ∈ ({1, n} : Finset ℕ), d ≤ sigma1 n :=
    Finset.sum_le_sum_of_subset hsub
  have : ∑ d ∈ ({1, n} : Finset ℕ), d = 1 + n := by
    rw [Finset.sum_insert (by simp; omega), Finset.sum_singleton]
  omega

/-- A prime has `σ(p) = p + 1`. -/
lemma sigma1_prime {p : ℕ} (hp : p.Prime) : sigma1 p = p + 1 := by
  simp [sigma1, Nat.Prime.divisors hp, Finset.sum_pair hp.one_lt.ne, Nat.add_comm]

/-! ## Betrothed (quasi-amicable) numbers -/

/-- `IsBetrothedPair m n` says that `(m, n)` is a betrothed (quasi-amicable)
pair: `m ≠ n` are positive and `σ(m) = σ(n) = m + n + 1`. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ sigma1 m = m + n + 1 ∧ sigma1 n = m + n + 1

/-- A number is betrothed if it belongs to some betrothed pair. -/
def IsBetrothed (n : ℕ) : Prop := ∃ m, IsBetrothedPair n m

/-- The set of betrothed numbers. -/
def betrothedSet : Set ℕ := {n | IsBetrothed n}

/-- The smallest betrothed pair, `(48, 75)`: this witnesses that the notion is
not vacuous. -/
example : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;> decide

lemma IsBetrothedPair.symm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  exact ⟨hn, hm, hmn.symm, by omega, by omega⟩

lemma IsBetrothedPair.isBetrothed {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothed m := ⟨n, h⟩

/-- The partner of a betrothed number is recovered from `σ`. -/
def partner (n : ℕ) : ℕ := sigma1 n - n - 1

lemma partner_eq {m n : ℕ} (h : IsBetrothedPair m n) : partner m = n := by
  obtain ⟨-, -, -, h1, -⟩ := h
  simp only [partner, h1]
  omega

/-- The partner of a betrothed number is unique. -/
lemma partner_unique {m n n' : ℕ} (h : IsBetrothedPair m n) (h' : IsBetrothedPair m n') :
    n = n' := by
  rw [← partner_eq h, ← partner_eq h']

/-- In a betrothed pair the smaller member is abundant. -/
lemma abundant_of_smaller {m n : ℕ} (h : IsBetrothedPair m n) (hlt : m < n) :
    2 * m < sigma1 m := by
  obtain ⟨-, -, -, h1, -⟩ := h
  omega

/-- In a betrothed pair the larger member is deficient (`σ(n) ≤ 2n`). -/
lemma deficient_of_larger {m n : ℕ} (h : IsBetrothedPair m n) (hlt : m < n) :
    sigma1 n ≤ 2 * n := by
  obtain ⟨-, -, -, -, h2⟩ := h
  omega

/-- A betrothed number is not prime. -/
lemma not_prime_of_isBetrothed {n : ℕ} (h : IsBetrothed n) : ¬ n.Prime := by
  rintro hp
  obtain ⟨m, hm, hn, hmn, h1, h2⟩ := h
  rw [sigma1_prime hp] at h1
  omega

/-- A betrothed number is bigger than `1`. -/
lemma one_lt_of_isBetrothed {n : ℕ} (h : IsBetrothed n) : 1 < n := by
  obtain ⟨m, hm, hn, hmn, h1, h2⟩ := h
  rcases Nat.lt_or_ge n 2 with h' | h'
  · have hn1 : n = 1 := by omega
    subst hn1
    rw [sigma1_one] at h1
    omega
  · omega

/-! ## The witness set

The set of numbers satisfying the `σ`-condition enjoyed by the *smaller* member
of a betrothed pair.  It is defined without any existential quantifier over
partners, which makes it the natural target for analytic estimates. -/

/-- `quasiAmicableWitness` is the set of `m > 0` with `2m + 1 < σ(m)` and
`σ(σ(m) - m - 1) = σ(m)`.  Every smaller member of a betrothed pair lies in it. -/
def quasiAmicableWitness : Set ℕ :=
  {m | 0 < m ∧ 2 * m + 1 < sigma1 m ∧ sigma1 (sigma1 m - m - 1) = sigma1 m}

lemma smaller_mem_quasiAmicableWitness {m n : ℕ} (h : IsBetrothedPair m n) (hlt : m < n) :
    m ∈ quasiAmicableWitness := by
  obtain ⟨hm, hn, hmn, h1, h2⟩ := h
  refine ⟨hm, by omega, ?_⟩
  have : sigma1 m - m - 1 = n := by omega
  rw [this, h2, h1]

/-! ## A toolkit for asymptotic density zero -/

/-- The number of elements of `S` that are at most `x`. -/
noncomputable def countUpTo (S : Set ℕ) (x : ℕ) : ℕ :=
  ((Finset.range (x + 1)).filter (fun n => n ∈ S)).card

/-- `S` has asymptotic density zero. -/
def HasDensityZero (S : Set ℕ) : Prop :=
  Tendsto (fun x : ℕ => (countUpTo S x : ℝ) / (x : ℝ)) atTop (𝓝 0)

lemma countUpTo_mono {S T : Set ℕ} (h : S ⊆ T) (x : ℕ) : countUpTo S x ≤ countUpTo T x := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, h hn.2⟩

lemma countUpTo_union_le (S T : Set ℕ) (x : ℕ) :
    countUpTo (S ∪ T) x ≤ countUpTo S x + countUpTo T x := by
  classical
  refine le_trans (Finset.card_le_card ?_) (Finset.card_union_le _ _)
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_union, Set.mem_union] at hn ⊢
  tauto

lemma countUpTo_le_card_of_finite {S : Set ℕ} (hS : S.Finite) (x : ℕ) :
    countUpTo S x ≤ hS.toFinset.card := by
  apply Finset.card_le_card
  intro n hn
  simp only [Finset.mem_filter] at hn
  simpa using hn.2

/-- Comparison criterion: if the counting function of `S` is bounded by a
constant multiple of the counting function of a density-zero set, then `S` has
density zero. -/
lemma hasDensityZero_of_le_const_mul {S T : Set ℕ} (c : ℕ)
    (hc : ∀ x, countUpTo S x ≤ c * countUpTo T x) (hT : HasDensityZero T) :
    HasDensityZero S := by
  have h2 : Tendsto (fun x : ℕ => (c : ℝ) * ((countUpTo T x : ℝ) / (x : ℝ))) atTop (𝓝 0) := by
    simpa using hT.const_mul (c : ℝ)
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) h2
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    rw [← mul_div_assoc]
    gcongr
    exact_mod_cast hc x

lemma HasDensityZero.mono {S T : Set ℕ} (h : S ⊆ T) (hT : HasDensityZero T) :
    HasDensityZero S :=
  hasDensityZero_of_le_const_mul 1 (fun x => by simpa using countUpTo_mono h x) hT

lemma hasDensityZero_union {S T : Set ℕ} (hS : HasDensityZero S) (hT : HasDensityZero T) :
    HasDensityZero (S ∪ T) := by
  have h2 : Tendsto
      (fun x : ℕ => (countUpTo S x : ℝ) / (x : ℝ) + (countUpTo T x : ℝ) / (x : ℝ))
      atTop (𝓝 0) := by simpa using hS.add hT
  refine squeeze_zero (fun x => by positivity) (fun x => ?_) h2
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    rw [← add_div]
    gcongr
    exact_mod_cast countUpTo_union_le S T x

lemma hasDensityZero_of_finite {S : Set ℕ} (hS : S.Finite) : HasDensityZero S := by
  refine squeeze_zero (fun x => by positivity) (fun x => ?_)
    (tendsto_const_div_atTop_nhds_zero_nat (hS.toFinset.card : ℝ))
  rcases Nat.eq_zero_or_pos x with rfl | hx
  · simp
  · have hx' : (0 : ℝ) < (x : ℝ) := by exact_mod_cast hx
    gcongr
    exact_mod_cast countUpTo_le_card_of_finite hS x

/-! ## Primitive nondeficient numbers

Erdős' method for amicable numbers enters through primitive nondeficient
numbers; the following existence lemma is the elementary entry point. -/

/-- `n` is nondeficient if `2n ≤ σ(n)`. -/
def Nondeficient (n : ℕ) : Prop := 2 * n ≤ sigma1 n

/-- `n` is primitive nondeficient if it is nondeficient but no proper divisor is. -/
def PrimitiveNondeficient (n : ℕ) : Prop :=
  Nondeficient n ∧ ∀ d, d ∣ n → d < n → ¬ Nondeficient d

/-- Every nondeficient number has a primitive nondeficient divisor. -/
lemma exists_primitiveNondeficient_dvd {n : ℕ} (hn : Nondeficient n) (hpos : 0 < n) :
    ∃ d, d ∣ n ∧ PrimitiveNondeficient d := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    by_cases hprim : ∀ d, d ∣ n → d < n → ¬ Nondeficient d
    · exact ⟨n, dvd_rfl, ⟨hn, hprim⟩⟩
    · push_neg at hprim
      obtain ⟨d, hdvd, hlt, hd⟩ := hprim
      have hdpos : 0 < d := by
        rcases Nat.eq_zero_or_pos d with rfl | h
        · simp [Nondeficient, sigma1_zero] at hd
          omega
        · exact h
      obtain ⟨e, he, hprime⟩ := ih d hlt hd hdpos
      exact ⟨e, he.trans hdvd, hprime⟩

/-! ## The reduction -/

/-- The partner map is injective on betrothed numbers. -/
lemma partner_injOn_betrothed : Set.InjOn partner betrothedSet := by
  rintro a ha b hb hab
  obtain ⟨m, hm⟩ := ha
  obtain ⟨m', hm'⟩ := hb
  have h1 : partner a = m := partner_eq hm
  have h2 : partner b = m' := partner_eq hm'
  have hmm : m = m' := by rw [← h1, ← h2, hab]
  subst hmm
  obtain ⟨-, -, -, -, ha2⟩ := hm
  obtain ⟨-, -, -, -, hb2⟩ := hm'
  omega

/-- The key counting inequality: betrothed numbers up to `x` are at most twice
the number of witnesses up to `x`. -/
lemma count_betrothed_le_two_mul_count_witness (x : ℕ) :
    countUpTo betrothedSet x ≤ 2 * countUpTo quasiAmicableWitness x := by
  classical
  set W : Finset ℕ := (Finset.range (x + 1)).filter (fun n => n ∈ quasiAmicableWitness) with hW
  set B : Finset ℕ := (Finset.range (x + 1)).filter (fun n => n ∈ betrothedSet) with hB
  have hsplit :
      (B.filter (fun n => n ∈ quasiAmicableWitness)).card +
        (B.filter (fun n => ¬ n ∈ quasiAmicableWitness)).card = B.card :=
    Finset.card_filter_add_card_filter_not _
  have h1 : (B.filter (fun n => n ∈ quasiAmicableWitness)).card ≤ W.card := by
    apply Finset.card_le_card
    intro n hn
    simp only [hB, hW, Finset.mem_filter] at hn ⊢
    exact ⟨hn.1.1, hn.2⟩
  have h2 : (B.filter (fun n => ¬ n ∈ quasiAmicableWitness)).card ≤ W.card := by
    refine Finset.card_le_card_of_injOn partner ?_ ?_
    · intro n hn
      simp only [hB, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_range] at hn
      obtain ⟨⟨hnx, hnb⟩, hnw⟩ := hn
      obtain ⟨m, hpair⟩ := hnb
      have hmn : m < n := by
        rcases lt_trichotomy n m with h | h | h
        · exact absurd (smaller_mem_quasiAmicableWitness hpair h) hnw
        · exact absurd h hpair.2.2.1
        · exact h
      have hp : partner n = m := partner_eq hpair
      simp only [hW, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_range]
      refine ⟨by omega, ?_⟩
      rw [hp]
      exact smaller_mem_quasiAmicableWitness hpair.symm hmn
    · intro a ha b hb hab
      simp only [hB, Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_filter,
        Finset.mem_range] at ha hb
      exact partner_injOn_betrothed ha.1.2 hb.1.2 hab
  have : B.card ≤ 2 * W.card := by omega
  simpa [countUpTo, hB, hW, two_mul] using this

/--
**Density zero reduction for betrothed numbers.**

If the (purely `σ`-arithmetically defined) set

`quasiAmicableWitness = {m | 0 < m ∧ 2m + 1 < σ(m) ∧ σ(σ(m) - m - 1) = σ(m)}`

has asymptotic density zero, then the set of betrothed (quasi-amicable) numbers
has asymptotic density zero.

This is the reduction step of Pollack's theorem: it removes the existential
quantifier over partners and the two-sided nature of a betrothed pair, leaving
exactly one analytic node — the density of the witness set — as the remaining
dependency.
-/
theorem density_zero_reduction (h : HasDensityZero quasiAmicableWitness) :
    HasDensityZero betrothedSet :=
  hasDensityZero_of_le_const_mul 2 count_betrothed_le_two_mul_count_witness h

end BetrothedNumbers
end Brockian

