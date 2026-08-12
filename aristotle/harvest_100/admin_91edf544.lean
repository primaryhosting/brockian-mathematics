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
# Goldbach From Spectral Model
Category: Brockian (Open Discharge)
Target: Brockian.GoldbachSchema.goldbach_from_spectral_model
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat

namespace Brockian.GoldbachSchema

open Finset Complex

/-- The primes below `n`, i.e. the support of the spectral model at level `n`. -/
def primesBelow (n : ℕ) : Finset ℕ := (Finset.range n).filter Nat.Prime

/-- The standard additive character `e(1/n)`: a primitive `n`-th root of unity. -/
noncomputable def zeta (n : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

/-- The prime exponential sum `S_n(j) = ∑_{p < n, p prime} e(pj/n)`. -/
noncomputable def spectralSum (n j : ℕ) : ℂ := ∑ p ∈ primesBelow n, zeta n ^ (p * j)

/-- The spectral (circle-method) main term at level `n`: `∑_{j < n} S_n(j)^2`. -/
noncomputable def spectralMain (n : ℕ) : ℂ := ∑ j ∈ Finset.range n, spectralSum n j ^ 2

/-- The number of ordered representations `n = p + q` with `p`, `q` prime. -/
def goldbachCount (n : ℕ) : ℕ :=
  ((primesBelow n ×ˢ primesBelow n).filter (fun pq => pq.1 + pq.2 = n)).card

/-- The spectral positivity (non-vanishing) predicate of the model at level `n`. -/
def SpectralPositivity (n : ℕ) : Prop := spectralMain n ≠ 0

/-- Goldbach's conjecture: every even `n ≥ 4` is a sum of two primes. -/
def GoldbachConjecture : Prop :=
  ∀ n : ℕ, Even n → 4 ≤ n → ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n

/-! ### Orthogonality -/

theorem zeta_isPrimitiveRoot {n : ℕ} (hn : n ≠ 0) : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n hn

theorem zeta_pow_eq_one_iff {n : ℕ} (hn : n ≠ 0) (k : ℕ) :
    zeta n ^ k = 1 ↔ n ∣ k := (zeta_isPrimitiveRoot hn).pow_eq_one_iff_dvd k

/-- Orthogonality of the additive characters mod `n`. -/
theorem sum_zeta_pow (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    ∑ j ∈ Finset.range n, zeta n ^ (k * j) = if n ∣ k then (n : ℂ) else 0 := by
  by_cases h : n ∣ k
  · simp only [h, if_true]
    have hone : ∀ j ∈ Finset.range n, zeta n ^ (k * j) = 1 := by
      intro j _
      rw [pow_mul, (zeta_pow_eq_one_iff hn k).2 h, one_pow]
    rw [Finset.sum_congr rfl hone]
    simp
  · simp only [h, if_false]
    have hne : zeta n ^ k ≠ 1 := fun hc => h ((zeta_pow_eq_one_iff hn k).1 hc)
    have hgeom : ∑ j ∈ Finset.range n, (zeta n ^ k) ^ j
        = ((zeta n ^ k) ^ n - 1) / (zeta n ^ k - 1) := geom_sum_eq hne n
    rw [show ∑ j ∈ Finset.range n, zeta n ^ (k * j) = ∑ j ∈ Finset.range n, (zeta n ^ k) ^ j from
      Finset.sum_congr rfl (fun j _ => by rw [pow_mul]), hgeom, ← pow_mul, mul_comm k n, pow_mul,
      (zeta_isPrimitiveRoot hn).pow_eq_one, one_pow]
    simp

/-! ### The spectral identity -/

/-- The circle-method identity: the spectral main term counts ordered Goldbach
representations exactly. -/
theorem spectralMain_eq (n : ℕ) (hn : n ≠ 0) :
    spectralMain n = n * goldbachCount n := by
  have hfilter : (primesBelow n ×ˢ primesBelow n).filter (fun pq => n ∣ pq.1 + pq.2)
      = (primesBelow n ×ˢ primesBelow n).filter (fun pq => pq.1 + pq.2 = n) := by
    apply Finset.filter_congr
    intro pq hpq
    simp only [primesBelow, Finset.mem_product, Finset.mem_filter, Finset.mem_range] at hpq
    obtain ⟨⟨hp1, hp2⟩, hq1, hq2⟩ := hpq
    constructor
    · rintro ⟨c, hc⟩
      have := hp2.two_le
      have := hq2.two_le
      have hc2 : c < 2 := by nlinarith [hc]
      interval_cases c <;> omega
    · rintro rfl; exact dvd_rfl
  have hsq : ∀ j : ℕ, spectralSum n j ^ 2
      = ∑ pq ∈ primesBelow n ×ˢ primesBelow n, zeta n ^ ((pq.1 + pq.2) * j) := by
    intro j
    rw [sq, spectralSum, Finset.sum_mul_sum, Finset.sum_product]
    exact Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => by
      rw [← pow_add]; ring_nf
  rw [spectralMain, Finset.sum_congr rfl (fun j _ => hsq j), Finset.sum_comm,
    Finset.sum_congr rfl (fun pq (_ : pq ∈ primesBelow n ×ˢ primesBelow n) =>
      sum_zeta_pow n hn (pq.1 + pq.2)),
    Finset.sum_ite, Finset.sum_const, Finset.sum_const_zero, add_zero, nsmul_eq_mul,
    hfilter, goldbachCount, mul_comm]

theorem goldbachCount_ne_zero_iff (n : ℕ) :
    goldbachCount n ≠ 0 ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  rw [goldbachCount, ← Nat.pos_iff_ne_zero, Finset.card_pos]
  constructor
  · rintro ⟨pq, hpq⟩
    simp only [primesBelow, Finset.mem_filter, Finset.mem_product, Finset.mem_range] at hpq
    exact ⟨pq.1, pq.2, hpq.1.1.2, hpq.1.2.2, hpq.2⟩
  · rintro ⟨p, q, hp, hq, rfl⟩
    refine ⟨(p, q), ?_⟩
    have := hp.two_le
    have := hq.two_le
    simp only [primesBelow, Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    exact ⟨⟨⟨by omega, hp⟩, by omega, hq⟩, trivial⟩

/-- Faithfulness of the spectral model: at every level `n ≥ 1`, spectral positivity is
*equivalent* to the existence of a Goldbach representation of `n`. -/
theorem spectralPositivity_iff (n : ℕ) (hn : n ≠ 0) :
    SpectralPositivity n ↔ ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  rw [SpectralPositivity, spectralMain_eq n hn, ← goldbachCount_ne_zero_iff]
  simp [hn]

/-! ### Main result -/

/-- Spectral positivity at a level `n ≥ 4` yields a Goldbach representation of `n`,
with no further hypotheses. -/
theorem goldbach_of_spectralPositivity (n : ℕ) (h4 : 4 ≤ n) (h : SpectralPositivity n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n :=
  (spectralPositivity_iff n (by omega)).1 h

/-- **Goldbach from the spectral model**, unconditionally: the spectral non-vanishing
hypothesis of the model, imposed at every even level `n ≥ 4`, is *equivalent* to Goldbach's
conjecture. In particular the implication "spectral positivity ⟹ Goldbach" holds with no
extra hypotheses: the model-faithfulness hypothesis of the schema is discharged. -/
theorem goldbach_from_spectral_model :
    (∀ n : ℕ, Even n → 4 ≤ n → SpectralPositivity n) ↔ GoldbachConjecture := by
  constructor
  · intro h n he h4
    exact goldbach_of_spectralPositivity n h4 (h n he h4)
  · intro h n he h4
    exact (spectralPositivity_iff n (by omega)).2 (h n he h4)

/-!
The equivalence above pins down the exact strength of the spectral hypothesis: imposed at all
even levels `n ≥ 4` it is neither weaker nor stronger than Goldbach's conjecture itself, which
remains open. What is discharged unconditionally here is the *faithfulness* of the spectral
model (`spectralMain_eq`, `spectralPositivity_iff`), i.e. the bridging hypothesis of the schema:
no assumption is needed to pass from spectral non-vanishing to a Goldbach representation.
-/

/-! ### Unconditional non-vacuity of the model on a verified range -/

set_option maxRecDepth 40000 in
set_option maxHeartbeats 2000000 in
/-- Goldbach's conjecture, verified unconditionally for all even `n` with `4 ≤ n ≤ 100`. -/
theorem goldbach_le_hundred (n : ℕ) (hle : n ≤ 100) (he : Even n) (h4 : 4 ≤ n) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p + q = n := by
  have key : ∀ m ∈ Finset.range 101, Even m → 4 ≤ m →
      ∃ p ∈ Finset.range 101, ∃ q ∈ Finset.range 101, Nat.Prime p ∧ Nat.Prime q ∧ p + q = m := by
    decide
  obtain ⟨p, -, q, -, hp, hq, hpq⟩ := key n (Finset.mem_range.2 (by omega)) he h4
  exact ⟨p, q, hp, hq, hpq⟩

/-- The spectral model is unconditionally positive at every even level `4 ≤ n ≤ 100`. -/
theorem spectralPositivity_le_hundred (n : ℕ) (hle : n ≤ 100) (he : Even n) (h4 : 4 ≤ n) :
    SpectralPositivity n :=
  (spectralPositivity_iff n (by omega)).2 (goldbach_le_hundred n hle he h4)

end Brockian.GoldbachSchema

