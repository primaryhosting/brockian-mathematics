import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Brockian

/-- A finite set `H` of integers is *admissible* if for every prime `p` it fails to cover
all residue classes modulo `p`, i.e. some residue class mod `p` is missed by `H`.
This is the classical admissibility condition of the Hardy–Littlewood prime `k`-tuple
conjecture. -/
def Admissible (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ h ∈ H, (h : ZMod p) ≠ r

/-- The odd part of the arithmetic factor of the Hardy–Littlewood singular series for
prime pairs `(n, n + d)`: the product of `(p-1)/(p-2)` over the odd primes dividing `d`. -/
def singularFactor (d : ℕ) : ℚ :=
  ∏ p ∈ d.primeFactors.erase 2, ((p : ℚ) - 1) / ((p : ℚ) - 2)

/-- The Hardy–Littlewood singular series for the prime pair gap `d`, measured in units of
the twin prime constant `C₂`: it is `2 ∏_{p ∣ d, p odd} (p-1)/(p-2)` for even `d`, and `0`
for odd `d` (an odd gap forces one of the two numbers to be even). -/
def singularSeries (d : ℕ) : ℚ :=
  if Even d then 2 * singularFactor d else 0

section Admissibility

/-- For an odd prime `p`, a two element set of residues cannot cover `ZMod p`. -/
lemma exists_residue_ne_pair {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (a b : ZMod p) :
    ∃ r : ZMod p, a ≠ r ∧ b ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hcard : ({a, b} : Finset (ZMod p)).card < Fintype.card (ZMod p) := by
    have h1 : ({a, b} : Finset (ZMod p)).card ≤ 2 :=
      le_trans (Finset.card_insert_le _ _) (by simp)
    have h2 : Fintype.card (ZMod p) = p := ZMod.card p
    omega
  have hne : ({a, b} : Finset (ZMod p))ᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl]
    omega
  obtain ⟨r, hr⟩ := hne
  refine ⟨r, ?_, ?_⟩ <;> · rintro rfl; simp at hr

/-- An even natural number casts to `0` in `ZMod 2`. -/
lemma intCast_zmod_two_of_even (d : ℕ) (hd : Even d) : (((d : ℤ)) : ZMod 2) = 0 := by
  obtain ⟨k, hk⟩ := hd
  subst hk
  push_cast
  rw [← two_mul]
  simp [show ((2 : ZMod 2)) = 0 by decide]

/-- An odd natural number casts to `1` in `ZMod 2`. -/
lemma intCast_zmod_two_of_odd (d : ℕ) (hd : ¬ Even d) : (((d : ℤ)) : ZMod 2) = 1 := by
  obtain ⟨k, hk⟩ := Nat.not_even_iff_odd.mp hd
  subst hk
  push_cast
  simp [show ((2 : ZMod 2)) = 0 by decide]

/-- The pair `{0, d}` is admissible exactly when the gap `d` is even. -/
lemma admissible_pair_iff_even (d : ℕ) : Admissible {0, (d : ℤ)} ↔ Even d := by
  constructor
  · intro h
    by_contra hodd
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (by simp)
    have hd : (((d : ℤ)) : ZMod 2) ≠ r := hr _ (by simp)
    rw [intCast_zmod_two_of_odd d hodd] at hd
    rw [Int.cast_zero] at h0
    have hr2 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
    rcases hr2 r with rfl | rfl
    · exact h0 rfl
    · exact hd rfl
  · intro hd p hp
    by_cases hp2 : p = 2
    · subst hp2
      refine ⟨1, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · simp only [Int.cast_zero]; decide
      · rw [intCast_zmod_two_of_even d hd]; decide
    · obtain ⟨r, hr0, hrd⟩ := exists_residue_ne_pair hp hp2 0 ((d : ℤ) : ZMod p)
      refine ⟨r, ?_⟩
      intro h hh
      simp only [Finset.mem_insert, Finset.mem_singleton] at hh
      rcases hh with rfl | rfl
      · simpa using hr0
      · exact hrd

end Admissibility

section General

/-- The odd arithmetic factor of the singular series is always positive. -/
lemma singularFactor_pos (d : ℕ) : 0 < singularFactor d := by
  refine Finset.prod_pos ?_
  intro p hp
  have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
  have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have h3 : 3 ≤ p := by have := hpp.two_le; omega
  have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
  apply div_pos <;> linarith

/-- The singular series of an even gap is positive. -/
lemma singularSeries_pos_of_even {d : ℕ} (hd : Even d) : 0 < singularSeries d := by
  rw [singularSeries, if_pos hd]
  have := singularFactor_pos d
  linarith

/-- The singular series of an odd gap vanishes. -/
lemma singularSeries_eq_zero_of_odd {d : ℕ} (hd : ¬ Even d) : singularSeries d = 0 := by
  rw [singularSeries, if_neg hd]

end General

section Values

lemma primeFactors_1602 : (1602 : ℕ).primeFactors = {2, 3, 89} := by
  have h : (1602 : ℕ) = 2 * (3 ^ 2 * 89) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  decide

lemma primeFactors_1604 : (1604 : ℕ).primeFactors = {2, 401} := by
  have h : (1604 : ℕ) = 2 ^ 2 * 401 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

lemma primeFactors_1606 : (1606 : ℕ).primeFactors = {2, 11, 73} := by
  have h : (1606 : ℕ) = 2 * (11 * 73) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  decide

lemma primeFactors_1608 : (1608 : ℕ).primeFactors = {2, 3, 67} := by
  have h : (1608 : ℕ) = 2 ^ 3 * (3 * 67) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  decide

lemma primeFactors_1610 : (1610 : ℕ).primeFactors = {2, 5, 7, 23} := by
  have h : (1610 : ℕ) = 2 * (5 * (7 * 23)) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  decide

lemma singularSeries_1602 : singularSeries 1602 = 352 / 87 := by
  rw [singularSeries, if_pos (by decide), singularFactor, primeFactors_1602]
  norm_num [Finset.prod_insert, Finset.erase_insert_of_ne]

lemma singularSeries_1604 : singularSeries 1604 = 800 / 399 := by
  rw [singularSeries, if_pos (by decide), singularFactor, primeFactors_1604]
  norm_num [Finset.prod_insert, Finset.erase_insert_of_ne]

lemma singularSeries_1606 : singularSeries 1606 = 160 / 71 := by
  rw [singularSeries, if_pos (by decide), singularFactor, primeFactors_1606]
  norm_num [Finset.prod_insert, Finset.erase_insert_of_ne]

lemma singularSeries_1608 : singularSeries 1608 = 264 / 65 := by
  rw [singularSeries, if_pos (by decide), singularFactor, primeFactors_1608]
  norm_num [Finset.prod_insert, Finset.erase_insert_of_ne]

lemma singularSeries_1610 : singularSeries 1610 = 352 / 105 := by
  rw [singularSeries, if_pos (by decide), singularFactor, primeFactors_1610]
  norm_num [Finset.prod_insert, Finset.erase_insert_of_ne]

end Values

/-- **Admissible gaps and singular series values in the range `1602 ≤ d ≤ 1610`.**

* a gap `d` in this range is admissible (i.e. `{0, d}` is an admissible pair) precisely
  when `d` is even;
* every admissible gap in this range has positive singular series;
* the gap `d = 1608` strictly maximizes the singular series over the range, with value
  `264/65` (in units of the twin prime constant `C₂`). -/
theorem SingularSeriesGaps16021610 :
    (∀ d : ℕ, 1602 ≤ d → d ≤ 1610 → (Admissible {0, (d : ℤ)} ↔ Even d)) ∧
    (∀ d : ℕ, 1602 ≤ d → d ≤ 1610 → Even d → 0 < singularSeries d) ∧
    (∀ d : ℕ, 1602 ≤ d → d ≤ 1610 → Even d → d ≠ 1608 →
      singularSeries d < singularSeries 1608) ∧
    singularSeries 1608 = 264 / 65 := by
  refine ⟨fun d _ _ => admissible_pair_iff_even d, ?_, ?_, singularSeries_1608⟩
  · intro d _ _ he
    exact singularSeries_pos_of_even he
  · intro d h1 h2 he hne
    interval_cases d <;>
      first
        | (exfalso; revert he; decide)
        | (exact absurd rfl hne)
        | norm_num [singularSeries_1602, singularSeries_1604, singularSeries_1606,
            singularSeries_1608, singularSeries_1610]

end Brockian

