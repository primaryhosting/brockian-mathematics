/-
# Density Zero Reduction
Category: Frontier — Betrothed Numbers
Target: Brockian.BetrothedNumbers.density_zero_reduction
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open Filter

/-!
# Density Zero Reduction for Betrothed (Quasi-Amicable) Numbers

Pollack's theorem asserts that the set of betrothed numbers has asymptotic density zero.  This
file decomposes that statement into Mathlib-sized pieces: it fixes the definitions, proves the
weakest reusable analytic-number-theory lemmas unconditionally, and then states and proves the
*reduction* theorem, which isolates exactly what analytic input is still missing.  No claim of
the unconditional density theorem is made.

## Dependency graph

```
properDivisorSum ── IsBetrothedPair ── betrothed
                                        │
                                        ├── isBetrothedPair_comm
                                        ├── betrothed_partner_unique
                                        ├── not_prime_of_betrothed   (uses
                                        │     Nat.sum_properDivisors_eq_one_iff_prime)
                                        ├── two_le_of_betrothed
                                        └── isBetrothedPair_48_75 ── betrothed_nonempty

sectionLe ── sectionLe_subset_Iic ── sectionLe_finite
     │                                    │
     └── countLe ─┬─ countLe_mono ────────┘
                  ├─ countLe_le_succ
                  ├─ countLe_union_le
                  ├─ countLe_le_ncard_of_finite
                  ├─ countLe_empty ── countLe_biUnion_le
                  └─ countLe_multiples_le ─┐
                                           ├── countLe_multiplesUnion_le
                    countLe_biUnion_le ────┘        │
                                                    │
HasDensityZero ── hasDensityZero_iff ─┬── HasDensityZero.subset            │
                                      ├── hasDensityZero_of_finite         │
                                      ├── HasDensityZero.union             │
                                      ├── hasDensityZero_of_countLe_div    │
                                      └── hasDensityZero_of_multiples_cover ┘
                                                    │
   HasDensityZero.subset + hasDensityZero_of_finite │
                     └── hasDensityZero_of_subset_union_finite
                                                    │
                                                    ▼
              density_zero_reduction                (main target)
              density_zero_reduction_of_div_bound   (variant, via the finite-perturbation
                                                     and `C x / f x` criteria)
              density_zero_reduction_of_multiples_cover
                                                    (variant, via the sifting criterion)
```

## What remains for the full theorem

The only unproved ingredient of Pollack's theorem is the construction of the covering family:
for each `ε > 0`, a set (or a finite set of moduli) capturing every betrothed number outside a
sparse remainder.  Feeding such a construction into `density_zero_reduction` (or one of its two
variants) yields `HasDensityZero betrothed`.
-/

namespace Brockian
namespace BetrothedNumbers

/-! ## Basic definitions -/

/-- The sum of the proper divisors of `n`, usually written `s(n) = σ(n) - n`. -/
def properDivisorSum (n : ℕ) : ℕ := ∑ d ∈ Nat.properDivisors n, d

/-- `m` and `n` form a *betrothed* (quasi-amicable) pair: both are positive, distinct, and
each is one less than the sum of the proper divisors of the other. -/
def IsBetrothedPair (m n : ℕ) : Prop :=
  0 < m ∧ 0 < n ∧ m ≠ n ∧ properDivisorSum m = n + 1 ∧ properDivisorSum n = m + 1

/-- The set of betrothed numbers: those belonging to some betrothed pair. -/
def betrothed : Set ℕ := {n | ∃ m, IsBetrothedPair m n}

/-- The elements of `A` lying in the interval `[0, x]`. -/
def sectionLe (A : Set ℕ) (x : ℕ) : Set ℕ := {n | n ∈ A ∧ n ≤ x}

/-- The number of elements of `A` in the interval `[0, x]`. -/
noncomputable def countLe (A : Set ℕ) (x : ℕ) : ℕ := (sectionLe A x).ncard

/-- A set of naturals has asymptotic density zero. -/
def HasDensityZero (A : Set ℕ) : Prop :=
  Tendsto (fun x : ℕ => (countLe A x : ℝ) / x) atTop (nhds 0)

/-! ## Elementary properties of the counting function -/

theorem sectionLe_subset_Iic (A : Set ℕ) (x : ℕ) : sectionLe A x ⊆ Set.Iic x := fun _ hn => hn.2

theorem sectionLe_finite (A : Set ℕ) (x : ℕ) : (sectionLe A x).Finite :=
  Set.Finite.subset (Set.finite_Iic x) (sectionLe_subset_Iic A x)

theorem sectionLe_mono {A B : Set ℕ} (h : A ⊆ B) (x : ℕ) : sectionLe A x ⊆ sectionLe B x :=
  fun _ hn => ⟨h hn.1, hn.2⟩

theorem countLe_mono {A B : Set ℕ} (h : A ⊆ B) (x : ℕ) : countLe A x ≤ countLe B x :=
  Set.ncard_le_ncard (sectionLe_mono h x) (sectionLe_finite B x)

theorem countLe_le_succ (A : Set ℕ) (x : ℕ) : countLe A x ≤ x + 1 := by
  have h1 : countLe A x ≤ (Set.Iic x).ncard :=
    Set.ncard_le_ncard (sectionLe_subset_Iic A x) (Set.finite_Iic x)
  have h2 : (Set.Iic x).ncard = x + 1 := Set.ncard_Iic_nat x
  omega

theorem countLe_union_le (A B : Set ℕ) (x : ℕ) :
    countLe (A ∪ B) x ≤ countLe A x + countLe B x := by
  have hsub : sectionLe (A ∪ B) x ⊆ sectionLe A x ∪ sectionLe B x := by
    rintro n ⟨h | h, hx⟩
    · exact Or.inl ⟨h, hx⟩
    · exact Or.inr ⟨h, hx⟩
  calc countLe (A ∪ B) x ≤ (sectionLe A x ∪ sectionLe B x).ncard :=
        Set.ncard_le_ncard hsub ((sectionLe_finite A x).union (sectionLe_finite B x))
    _ ≤ countLe A x + countLe B x :=
        Set.ncard_union_le _ _

/-- For a finite set `A`, the counting function is bounded by the cardinality of `A`. -/
theorem countLe_le_ncard_of_finite {A : Set ℕ} (hA : A.Finite) (x : ℕ) :
    countLe A x ≤ A.ncard :=
  Set.ncard_le_ncard (fun _ hn => hn.1) hA

/-- At most `x / d + 1` of the numbers in `[0, x]` are divisible by `d`. -/
theorem countLe_multiples_le (d x : ℕ) : countLe {n : ℕ | d ∣ n} x ≤ x / d + 1 := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · have hsub : sectionLe {n : ℕ | (0 : ℕ) ∣ n} x ⊆ ({0} : Set ℕ) := by
      rintro n ⟨hn, -⟩
      simpa using (zero_dvd_iff.1 hn)
    have h := Set.ncard_le_ncard hsub (Set.finite_singleton 0)
    simp only [Set.ncard_singleton] at h
    have : countLe {n : ℕ | (0 : ℕ) ∣ n} x = (sectionLe {n : ℕ | (0 : ℕ) ∣ n} x).ncard := rfl
    omega
  · have hsub : sectionLe {n : ℕ | d ∣ n} x ⊆ (fun k => d * k) '' (Set.Iic (x / d)) := by
      rintro n ⟨⟨k, rfl⟩, hle⟩
      exact ⟨k, (Nat.le_div_iff_mul_le hd).2 (by rw [Nat.mul_comm]; exact hle), rfl⟩
    have h1 : countLe {n : ℕ | d ∣ n} x ≤ ((fun k => d * k) '' (Set.Iic (x / d))).ncard :=
      Set.ncard_le_ncard hsub (Set.Finite.image _ (Set.finite_Iic _))
    have h2 : ((fun k => d * k) '' (Set.Iic (x / d))).ncard ≤ (Set.Iic (x / d)).ncard :=
      Set.ncard_image_le (Set.finite_Iic _)
    have h3 : (Set.Iic (x / d)).ncard = x / d + 1 := Set.ncard_Iic_nat _
    omega

theorem countLe_empty (x : ℕ) : countLe (∅ : Set ℕ) x = 0 := by
  have : sectionLe (∅ : Set ℕ) x = ∅ := by
    ext n; simp [sectionLe]
  simp [countLe, this]

/-- Subadditivity of the counting function over a finite union. -/
theorem countLe_biUnion_le (D : Finset ℕ) (g : ℕ → Set ℕ) (x : ℕ) :
    countLe (⋃ d ∈ D, g d) x ≤ ∑ d ∈ D, countLe (g d) x := by
  classical
  induction D using Finset.induction with
  | empty => simp [countLe_empty]
  | insert a D ha ih =>
      have hset : (⋃ d ∈ (insert a D : Finset ℕ), g d) = g a ∪ ⋃ d ∈ D, g d := by
        ext n; simp [Finset.mem_insert]
      rw [hset, Finset.sum_insert ha]
      exact le_trans (countLe_union_le _ _ x) (Nat.add_le_add_left ih _)

/-- The key sifting bound: the numbers up to `x` divisible by some element of a finite set `D`
number at most `x * ∑_{d ∈ D} 1/d + |D|`. -/
theorem countLe_multiplesUnion_le (D : Finset ℕ) (x : ℕ) :
    (countLe {n : ℕ | ∃ d ∈ D, d ∣ n} x : ℝ)
      ≤ (x : ℝ) * (∑ d ∈ D, (1 : ℝ) / d) + D.card := by
  classical
  have hset : {n : ℕ | ∃ d ∈ D, d ∣ n} = ⋃ d ∈ D, {n : ℕ | d ∣ n} := by
    ext n; simp
  have h1 : countLe {n : ℕ | ∃ d ∈ D, d ∣ n} x ≤ ∑ d ∈ D, countLe {n : ℕ | d ∣ n} x := by
    rw [hset]; exact countLe_biUnion_le D _ x
  have h2 : (∑ d ∈ D, countLe {n : ℕ | d ∣ n} x : ℝ) ≤ ∑ d ∈ D, ((x : ℝ) / d + 1) := by
    refine Finset.sum_le_sum ?_
    intro d _
    have hd : (countLe {n : ℕ | d ∣ n} x : ℝ) ≤ ((x / d : ℕ) : ℝ) + 1 := by
      exact_mod_cast countLe_multiples_le d x
    have : ((x / d : ℕ) : ℝ) ≤ (x : ℝ) / d := Nat.cast_div_le
    linarith
  have h3 : (∑ d ∈ D, ((x : ℝ) / d + 1)) = (x : ℝ) * (∑ d ∈ D, (1 : ℝ) / d) + D.card := by
    rw [Finset.sum_add_distrib, Finset.mul_sum]
    simp [div_eq_mul_inv, mul_comm]
  have h1' : (countLe {n : ℕ | ∃ d ∈ D, d ∣ n} x : ℝ)
      ≤ (∑ d ∈ D, countLe {n : ℕ | d ∣ n} x : ℝ) := by exact_mod_cast h1
  linarith [h1', h2, h3.le, h3.ge]

/-! ## Reusable density-zero criteria -/

/-- Density zero is equivalent to the "for every `ε > 0`, eventually `count ≤ ε x`" formulation. -/
theorem hasDensityZero_iff (A : Set ℕ) :
    HasDensityZero A ↔ ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (countLe A x : ℝ) ≤ ε * x := by
  unfold HasDensityZero
  constructor
  · intro h ε hε
    obtain ⟨N, hN⟩ := Metric.tendsto_atTop.1 h ε hε
    filter_upwards [eventually_ge_atTop N, eventually_ge_atTop 1] with x hxN hx1
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    have hd := hN x hxN
    rw [Real.dist_eq, sub_zero] at hd
    have h2 : (countLe A x : ℝ) / x < ε := lt_of_abs_lt hd
    have : (countLe A x : ℝ) = ((countLe A x : ℝ) / x) * x := by field_simp
    nlinarith
  · intro h
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hhalf : (0 : ℝ) < ε / 2 := by linarith
    obtain ⟨N, hN⟩ := (h (ε / 2) hhalf).exists_forall_of_atTop
    refine ⟨max N 1, fun x hx => ?_⟩
    have hx1 : 1 ≤ x := le_trans (le_max_right N 1) hx
    have hxN : N ≤ x := le_trans (le_max_left N 1) hx
    have hx0 : (0 : ℝ) < x := by exact_mod_cast hx1
    have hb := hN x hxN
    have hle : (countLe A x : ℝ) / x ≤ ε / 2 := by
      rw [div_le_iff₀ hx0]; exact hb
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)]
    linarith

/-- Density zero passes to subsets. -/
theorem HasDensityZero.subset {A B : Set ℕ} (hB : HasDensityZero B) (h : A ⊆ B) :
    HasDensityZero A := by
  rw [hasDensityZero_iff] at hB ⊢
  intro ε hε
  filter_upwards [hB ε hε] with x hx
  exact le_trans (by exact_mod_cast countLe_mono h x) hx

/-- Finite sets have density zero. -/
theorem hasDensityZero_of_finite {A : Set ℕ} (hA : A.Finite) : HasDensityZero A := by
  rw [hasDensityZero_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt ((A.ncard : ℝ) / ε)
  filter_upwards [eventually_ge_atTop N] with x hx
  have hxN : (N : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h1 : (countLe A x : ℝ) ≤ (A.ncard : ℝ) := by
    exact_mod_cast countLe_le_ncard_of_finite hA x
  have h2 : (A.ncard : ℝ) / ε < (x : ℝ) := lt_of_lt_of_le hN hxN
  rw [div_lt_iff₀ hε] at h2
  linarith

/-- A union of two density-zero sets has density zero. -/
theorem HasDensityZero.union {A B : Set ℕ} (hA : HasDensityZero A) (hB : HasDensityZero B) :
    HasDensityZero (A ∪ B) := by
  rw [hasDensityZero_iff] at hA hB ⊢
  intro ε hε
  have hε2 : (0 : ℝ) < ε / 2 := by linarith
  filter_upwards [hA (ε / 2) hε2, hB (ε / 2) hε2] with x hxA hxB
  have hcast : (countLe (A ∪ B) x : ℝ) ≤ (countLe A x : ℝ) + (countLe B x : ℝ) := by
    exact_mod_cast countLe_union_le A B x
  linarith

/-- Density zero only depends on the set up to a finite perturbation. -/
theorem hasDensityZero_of_subset_union_finite {A B F : Set ℕ} (hB : HasDensityZero B)
    (hF : F.Finite) (h : A ⊆ B ∪ F) : HasDensityZero A :=
  (hB.union (hasDensityZero_of_finite hF)).subset h

/-- A counting bound of the shape `count A x ≤ C * x / f x` with `f → ∞` gives density zero. -/
theorem hasDensityZero_of_countLe_div {A : Set ℕ} (C : ℝ) (f : ℕ → ℝ)
    (hf : Tendsto f atTop atTop)
    (hbound : ∀ᶠ x : ℕ in atTop, (countLe A x : ℝ) ≤ C * x / f x) :
    HasDensityZero A := by
  rw [hasDensityZero_iff]
  intro ε hε
  have hfpos : ∀ᶠ x : ℕ in atTop, max (C / ε) 1 < f x := hf.eventually_gt_atTop _
  filter_upwards [hbound, hfpos, eventually_ge_atTop 1] with x hx hfx _
  have hf1 : (1 : ℝ) < f x := lt_of_le_of_lt (le_max_right _ _) hfx
  have hf0 : (0 : ℝ) < f x := by linarith
  have hCf : C / ε < f x := lt_of_le_of_lt (le_max_left _ _) hfx
  have hxpos : (0 : ℝ) ≤ (x : ℝ) := by positivity
  rw [div_lt_iff₀ hε] at hCf
  have hdiv : C * x / f x ≤ ε * x := by
    rw [div_le_iff₀ hf0]
    nlinarith
  linarith

/-- Sifting criterion: a set that, for every `ε > 0`, can be covered by the multiples of the
elements of a finite set `D_ε` whose reciprocals sum to at most `ε / 2`, has density zero. -/
theorem hasDensityZero_of_multiples_cover {A : Set ℕ} (cover : ℝ → Finset ℕ)
    (hsub : ∀ ε : ℝ, 0 < ε → A ⊆ {n : ℕ | ∃ d ∈ cover ε, d ∣ n})
    (hsum : ∀ ε : ℝ, 0 < ε → ∑ d ∈ cover ε, (1 : ℝ) / d ≤ ε / 2) :
    HasDensityZero A := by
  rw [hasDensityZero_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ((cover ε).card : ℝ) / ε)
  filter_upwards [eventually_ge_atTop N] with x hx
  have hxR : (2 : ℝ) * ((cover ε).card : ℝ) / ε < (x : ℝ) :=
    lt_of_lt_of_le hN (by exact_mod_cast hx)
  rw [div_lt_iff₀ hε] at hxR
  have h0 : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hmono : (countLe A x : ℝ) ≤ (countLe {n : ℕ | ∃ d ∈ cover ε, d ∣ n} x : ℝ) := by
    exact_mod_cast countLe_mono (hsub ε hε) x
  have hbound := countLe_multiplesUnion_le (cover ε) x
  have hs := hsum ε hε
  nlinarith [hmono, hbound, hs]

/-! ## Elementary structure of betrothed numbers -/

theorem isBetrothedPair_comm {m n : ℕ} (h : IsBetrothedPair m n) : IsBetrothedPair n m :=
  ⟨h.2.1, h.1, (Ne.symm h.2.2.1), h.2.2.2.2, h.2.2.2.1⟩

/-- The partner of a betrothed number is uniquely determined. -/
theorem betrothed_partner_unique {m m' n : ℕ} (h : IsBetrothedPair m n)
    (h' : IsBetrothedPair m' n) : m = m' := by
  have h1 := h.2.2.2.2
  have h2 := h'.2.2.2.2
  omega

/-- Betrothed numbers are never prime. -/
theorem not_prime_of_betrothed {n : ℕ} (hn : n ∈ betrothed) : ¬ n.Prime := by
  obtain ⟨m, hm⟩ := hn
  intro hp
  have h1 : properDivisorSum n = 1 := Nat.sum_properDivisors_eq_one_iff_prime.2 hp
  have h2 : properDivisorSum n = m + 1 := hm.2.2.2.2
  have h3 := hm.1
  omega

/-- Betrothed numbers are at least `2`. -/
theorem two_le_of_betrothed {n : ℕ} (hn : n ∈ betrothed) : 2 ≤ n := by
  obtain ⟨m, hm⟩ := hn
  rcases Nat.lt_or_ge n 2 with h | h
  · interval_cases n
    · exact absurd hm.2.1 (by simp)
    · have h1 : properDivisorSum 1 = 0 := by decide
      have h2 := hm.2.2.2.2
      have h3 := hm.1
      omega
  · exact h

/-- `(48, 75)` is a betrothed pair, so the set of betrothed numbers is nonempty. -/
theorem isBetrothedPair_48_75 : IsBetrothedPair 48 75 := by
  refine ⟨by norm_num, by norm_num, by norm_num, ?_, ?_⟩ <;>
    simp only [properDivisorSum] <;> decide

theorem betrothed_nonempty : betrothed.Nonempty := ⟨75, 48, isBetrothedPair_48_75⟩

/-! ## The reduction

Pollack's theorem states that the set of betrothed numbers has asymptotic density zero.  The
following theorem is the *reduction* step: it isolates exactly the analytic input that remains
to be supplied, namely a family of covering sets `cover ε ⊇ betrothed` whose counting functions
are eventually bounded by `ε x`.  Given such a family, density zero follows. -/
theorem density_zero_reduction
    (cover : ℝ → Set ℕ)
    (hsub : ∀ ε : ℝ, 0 < ε → betrothed ⊆ cover ε)
    (hcount : ∀ ε : ℝ, 0 < ε → ∀ᶠ x : ℕ in atTop, (countLe (cover ε) x : ℝ) ≤ ε * x) :
    HasDensityZero betrothed := by
  rw [hasDensityZero_iff]
  intro ε hε
  filter_upwards [hcount ε hε] with x hx
  have hle : (countLe betrothed x : ℝ) ≤ (countLe (cover ε) x : ℝ) := by
    exact_mod_cast countLe_mono (hsub ε hε) x
  linarith

/-- A variant of the reduction where the cover is allowed finitely many exceptions and the
counting bound is given through an auxiliary function tending to infinity. -/
theorem density_zero_reduction_of_div_bound
    (E F : Set ℕ) (C : ℝ) (f : ℕ → ℝ)
    (hsub : betrothed ⊆ E ∪ F) (hF : F.Finite)
    (hf : Tendsto f atTop atTop)
    (hbound : ∀ᶠ x : ℕ in atTop, (countLe E x : ℝ) ≤ C * x / f x) :
    HasDensityZero betrothed :=
  hasDensityZero_of_subset_union_finite (hasDensityZero_of_countLe_div C f hf hbound) hF hsub

/-- The sifting form of the reduction, specialised to betrothed numbers. -/
theorem density_zero_reduction_of_multiples_cover
    (cover : ℝ → Finset ℕ)
    (hsub : ∀ ε : ℝ, 0 < ε → betrothed ⊆ {n : ℕ | ∃ d ∈ cover ε, d ∣ n})
    (hsum : ∀ ε : ℝ, 0 < ε → ∑ d ∈ cover ε, (1 : ℝ) / d ≤ ε / 2) :
    HasDensityZero betrothed :=
  hasDensityZero_of_multiples_cover cover hsub hsum

end BetrothedNumbers
end Brockian

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

