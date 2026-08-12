import Mathlib

set_option maxHeartbeats 200000

example (r : ZMod 2) (h0 : (0 : ZMod 2) ≠ r) (h1 : (1 : ZMod 2) ≠ r) : False := by
  fin_cases r <;> simp_all

example : ({2, 5, 29} : Finset ℕ).erase 2 = {5, 29} := by
  rw [Finset.erase_insert (by simp)]

example : (∏ p ∈ ({5, 29} : Finset ℕ), (((p : ℚ) - 1) / ((p : ℚ) - 2))) = 112 / 81 := by
  rw [Finset.prod_insert (by simp), Finset.prod_singleton]
  norm_num

example (g : ℕ) (hmod : g % 2 = 1) : (((g : ℤ)) : ZMod 2) = 1 := by
  push_cast
  rw [← ZMod.natCast_mod g 2, hmod]
  norm_num

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

namespace Brockian

/-- A finite set `H` of integers is *admissible* (in the sense of Hardy–Littlewood
prime constellations) if for every prime `p` the reductions of the elements of `H`
mod `p` do not cover all residue classes mod `p`. -/
def IsAdmissibleSet (H : Finset ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r

/-- A natural number `g` is an *admissible gap* if the pair `{0, g}` is admissible,
i.e. `{n, n + g}` is a candidate pattern for a pair of primes. -/
def IsAdmissibleGap (g : ℕ) : Prop := IsAdmissibleSet {0, (g : ℤ)}

/-- The odd part of the Hardy–Littlewood singular series for the pair `{0, g}`:
`∏_{p ∣ g, p odd prime} (p-1)/(p-2)`.  (The full singular series is
`2 C₂` times this factor.) -/
noncomputable def singularSeriesFactor (g : ℕ) : ℚ :=
  ∏ p ∈ g.primeFactors.erase 2, ((p : ℚ) - 1) / ((p : ℚ) - 2)

/-- A set of size smaller than `p` never covers all residues mod `p`. -/
lemma admissible_at_of_card_lt {p : ℕ} (hp : p.Prime) {H : Finset ℤ} (h : H.card < p) :
    ∃ r : ZMod p, ∀ x ∈ H, (x : ZMod p) ≠ r := by
  haveI : Fact p.Prime := ⟨hp⟩
  by_contra hc
  push_neg at hc
  have hsub : (Finset.univ : Finset (ZMod p)) ⊆ H.image (fun x : ℤ => (x : ZMod p)) := by
    intro r _
    obtain ⟨x, hx, hxr⟩ := hc r
    exact Finset.mem_image.2 ⟨x, hx, hxr⟩
  have hle := Finset.card_le_card hsub
  rw [Finset.card_univ, ZMod.card] at hle
  have h2 : (H.image (fun x : ℤ => (x : ZMod p))).card ≤ H.card := Finset.card_image_le
  omega

/-- A gap is admissible exactly when it is even. -/
theorem isAdmissibleGap_iff_even (g : ℕ) : IsAdmissibleGap g ↔ Even g := by
  constructor
  · intro h
    by_contra hodd
    rw [Nat.not_even_iff_odd] at hodd
    have hmod : g % 2 = 1 := Nat.odd_iff.mp hodd
    obtain ⟨r, hr⟩ := h 2 Nat.prime_two
    have h0 : ((0 : ℤ) : ZMod 2) ≠ r := hr 0 (Finset.mem_insert_self _ _)
    have hg : (((g : ℤ)) : ZMod 2) ≠ r := hr (g : ℤ) (by simp)
    have hgv : (((g : ℤ)) : ZMod 2) = 1 := by
      push_cast
      rw [← ZMod.natCast_mod g 2, hmod]
      norm_num
    rw [hgv] at hg
    simp only [Int.cast_zero] at h0
    fin_cases r <;> simp_all
  · intro heven p hp
    rcases eq_or_ne p 2 with rfl | hp2
    · refine ⟨1, ?_⟩
      intro x hx
      have hmod : g % 2 = 0 := Nat.even_iff.mp heven
      have hgv : (((g : ℤ)) : ZMod 2) = 0 := by
        push_cast
        rw [← ZMod.natCast_mod g 2, hmod]
        norm_num
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl
      · simpa using (by decide : (0 : ZMod 2) ≠ 1)
      · rw [hgv]; decide
    · refine admissible_at_of_card_lt hp ?_
      have hcard : ({0, (g : ℤ)} : Finset ℤ).card ≤ 2 := Finset.card_insert_le _ _ |>.trans (by simp)
      have : 3 ≤ p := by
        have := hp.two_le
        omega
      omega

/-- Every factor of the singular series is at least one, hence so is the product. -/
theorem one_le_singularSeriesFactor (g : ℕ) : 1 ≤ singularSeriesFactor g := by
  rw [singularSeriesFactor]
  calc (1 : ℚ) = ∏ _p ∈ (Nat.primeFactors g).erase 2, (1 : ℚ) := by simp
  _ ≤ ∏ p ∈ (Nat.primeFactors g).erase 2, ((p : ℚ) - 1) / ((p : ℚ) - 2) := by
      refine Finset.prod_le_prod (fun i _ => by norm_num) (fun p hp => ?_)
      have hp2 : p ≠ 2 := Finset.ne_of_mem_erase hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
      have h3 : 3 ≤ p := by have := hpp.two_le; omega
      have h3' : (3 : ℚ) ≤ (p : ℚ) := by exact_mod_cast h3
      rw [le_div_iff₀ (by linarith)]
      linarith

lemma primeFactors_1450 : Nat.primeFactors 1450 = {2, 5, 29} := by
  have h : (1450 : ℕ) = 2 * (5 ^ 2 * 29) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1452 : Nat.primeFactors 1452 = {2, 3, 11} := by
  have h : (1452 : ℕ) = 2 ^ 2 * (3 * 11 ^ 2) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1454 : Nat.primeFactors 1454 = {2, 727} := by
  have h : (1454 : ℕ) = 2 * 727 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1456 : Nat.primeFactors 1456 = {2, 7, 13} := by
  have h : (1456 : ℕ) = 2 ^ 4 * (7 * 13) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1458 : Nat.primeFactors 1458 = {2, 3} := by
  have h : (1458 : ℕ) = 2 * 3 ^ 6 := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num)]
  rfl

lemma primeFactors_1460 : Nat.primeFactors 1460 = {2, 5, 73} := by
  have h : (1460 : ℕ) = 2 ^ 2 * (5 * 73) := by norm_num
  rw [h, Nat.primeFactors_mul (by norm_num) (by norm_num),
    Nat.primeFactors_mul (by norm_num) (by norm_num), Nat.primeFactors_pow _ (by norm_num),
    Nat.Prime.primeFactors (by norm_num), Nat.Prime.primeFactors (by norm_num),
    Nat.Prime.primeFactors (by norm_num)]
  rfl

/-- **New admissible gap range.**  Every even number in the range `[1450, 1460]` is an
admissible gap, no odd number in that range is, and for each admissible gap in the range
the odd part of the Hardy–Littlewood singular series is the stated rational number
(in particular it exceeds `1`). -/
theorem SingularSeriesGaps14501460 :
    (∀ g ∈ Finset.Icc 1450 1460, (IsAdmissibleGap g ↔ Even g)) ∧
      singularSeriesFactor 1450 = 112 / 81 ∧
      singularSeriesFactor 1452 = 20 / 9 ∧
      singularSeriesFactor 1454 = 726 / 725 ∧
      singularSeriesFactor 1456 = 72 / 55 ∧
      singularSeriesFactor 1458 = 2 ∧
      singularSeriesFactor 1460 = 96 / 71 := by
  refine ⟨fun g _ => isAdmissibleGap_iff_even g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [singularSeriesFactor, primeFactors_1450, Finset.erase_insert (by simp),
      Finset.prod_insert (by simp), Finset.prod_singleton]
    norm_num
  · rw [singularSeriesFactor, primeFactors_1452, Finset.erase_insert (by simp),
      Finset.prod_insert (by simp), Finset.prod_singleton]
    norm_num
  · rw [singularSeriesFactor, primeFactors_1454, Finset.erase_insert (by simp),
      Finset.prod_singleton]
    norm_num
  · rw [singularSeriesFactor, primeFactors_1456, Finset.erase_insert (by simp),
      Finset.prod_insert (by simp), Finset.prod_singleton]
    norm_num
  · rw [singularSeriesFactor, primeFactors_1458, Finset.erase_insert (by simp),
      Finset.prod_singleton]
    norm_num
  · rw [singularSeriesFactor, primeFactors_1460, Finset.erase_insert (by simp),
      Finset.prod_insert (by simp), Finset.prod_singleton]
    norm_num

end Brockian

