import RequestProject.CapExpand

/-!
# The Ellenberg–Gijswijt bound

Combining the slice-rank bound with the polynomial expansion gives
`|A| ≤ 3 · #{exponent vectors of degree ≤ 2n/3}` for every 3AP-free `A ⊆ 𝔽₃ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- In `𝔽₃ⁿ`, a 3AP-free set contains no nontrivial triple summing to zero. -/
lemma eq_of_sum_eq_zero {n : ℕ} {A : Finset (Fin n → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3)))
    {x y z : Fin n → ZMod 3} (hx : x ∈ A) (hy : y ∈ A) (hz : z ∈ A)
    (h : x + y + z = 0) : x = y ∧ y = z := by
  have hxy : x = y := by
    refine hA (by exact_mod_cast hx) (by exact_mod_cast hy) (by exact_mod_cast hz) ?_
    funext i
    have hi : x i + y i + z i = 0 := by simpa using congrFun h i
    have : (3 : ZMod 3) = 0 := by decide
    have hy3 : y i + y i = -y i := by
      have : y i + y i + y i = 0 := by
        have : (3 : ZMod 3) * y i = 0 := by rw [show (3:ZMod 3) = 0 from by decide]; ring
        linear_combination this
      linear_combination this
    simp only [Pi.add_apply]
    rw [hy3]
    linear_combination hi
  subst hxy
  refine ⟨rfl, ?_⟩
  funext i
  have hi : x i + x i + z i = 0 := by simpa using congrFun h i
  have h3 : x i + x i + x i = 0 := by
    have : (3 : ZMod 3) * x i = 0 := by rw [show (3:ZMod 3) = 0 from by decide]; ring
    linear_combination this
  linear_combination h3 - hi

/-- The zero-sum indicator is the diagonal indicator on a 3AP-free set. -/
lemma indicator_diag {n : ℕ} {A : Finset (Fin n → ZMod 3)}
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) (x y z : A) :
    (if x = y ∧ y = z then (1 : ZMod 3) else 0)
      = if (x : Fin n → ZMod 3) + (y : Fin n → ZMod 3) + (z : Fin n → ZMod 3) = 0
        then (1 : ZMod 3) else 0 := by
  by_cases h : (x : Fin n → ZMod 3) + (y : Fin n → ZMod 3) + (z : Fin n → ZMod 3) = 0
  · obtain ⟨h1, h2⟩ := eq_of_sum_eq_zero hA x.2 y.2 z.2 h
    rw [if_pos h, if_pos ⟨Subtype.ext h1, Subtype.ext h2⟩]
  · rw [if_neg h, if_neg]
    rintro ⟨rfl, rfl⟩
    apply h
    funext i
    have : (3 : ZMod 3) * (x : Fin n → ZMod 3) i = 0 := by
      rw [show (3:ZMod 3) = 0 from by decide]; ring
    simp only [Pi.add_apply, Pi.zero_apply]
    linear_combination this

/-- **The Ellenberg–Gijswijt bound.** -/
theorem capset_card_le {n : ℕ} (A : Finset (Fin n → ZMod 3))
    (hA : ThreeAPFree (A : Set (Fin n → ZMod 3))) :
    A.card ≤ 3 * (lowExp n).card := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have key := card_le_of_diag_decomp (F := ZMod 3) (X := A)
    (I₁ := (lowExp n : Finset (Exp n))) (I₂ := (lowExp n : Finset (Exp n)))
    (I₃ := (lowExp n : Finset (Exp n)))
    (f₁ := fun a x => mon n (a : Exp n) (x : Fin n → ZMod 3))
    (g₁ := fun a y z => S₁ n (a : Exp n) (y : Fin n → ZMod 3) (z : Fin n → ZMod 3))
    (f₂ := fun a y => mon n (a : Exp n) (y : Fin n → ZMod 3))
    (g₂ := fun a x z => S₂ n (a : Exp n) (x : Fin n → ZMod 3) (z : Fin n → ZMod 3))
    (f₃ := fun a z => mon n (a : Exp n) (z : Fin n → ZMod 3))
    (g₃ := fun a x y => S₃ n (a : Exp n) (x : Fin n → ZMod 3) (y : Fin n → ZMod 3))
    (by
      intro x y z
      rw [indicator_diag hA x y z, indicator_slices]
      congr 1
      · congr 1
        · exact (Finset.sum_coe_sort (lowExp n)
            (fun a => mon n a (x : Fin n → ZMod 3) * S₁ n a y z)).symm
        · exact (Finset.sum_coe_sort (lowExp n)
            (fun a => mon n a (y : Fin n → ZMod 3) * S₂ n a x z)).symm
      · exact (Finset.sum_coe_sort (lowExp n)
          (fun a => mon n a (z : Fin n → ZMod 3) * S₃ n a x y)).symm)
  simp only [Fintype.card_coe] at key
  omega

end CapSetAux

import RequestProject.SliceRank

/-!
# The Croot–Lev–Pach polynomial expansion for `𝔽₃ⁿ`

We expand the indicator function of `x + y + z = 0` on `(ZMod 3)ⁿ` into monomials and
group the resulting terms into three families of slices, each indexed by the set of
exponent vectors of degree at most `2n/3`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- Coefficients of the expansion of `1 - (u+v+w)^2` over `ZMod 3`. -/
def cf : Fin 3 × Fin 3 × Fin 3 → ZMod 3 := fun t =>
  match t with
  | (0, 0, 0) => 1
  | (2, 0, 0) => 2
  | (0, 2, 0) => 2
  | (0, 0, 2) => 2
  | (1, 1, 0) => 1
  | (0, 1, 1) => 1
  | (1, 0, 1) => 1
  | _ => 0

lemma cf_expand : ∀ u v w : ZMod 3, (if u + v + w = 0 then (1 : ZMod 3) else 0)
    = ∑ t : Fin 3 × Fin 3 × Fin 3, cf t * u ^ (t.1 : ℕ) * v ^ (t.2.1 : ℕ) * w ^ (t.2.2 : ℕ) := by
  decide

lemma cf_deg : ∀ t : Fin 3 × Fin 3 × Fin 3, cf t ≠ 0 →
    (t.1 : ℕ) + (t.2.1 : ℕ) + (t.2.2 : ℕ) ≤ 2 := by decide

variable (n : ℕ)

/-- Exponent vectors with all exponents `< 3`. -/
abbrev Exp := Fin n → Fin 3

/-- The (reduced) monomial attached to an exponent vector. -/
def mon (a : Exp n) (x : Fin n → ZMod 3) : ZMod 3 := ∏ i, x i ^ (a i : ℕ)

/-- The total degree of an exponent vector. -/
def deg (a : Exp n) : ℕ := ∑ i, (a i : ℕ)

/-- Index type for the terms of the triple expansion. -/
abbrev Idx := Fin n → Fin 3 × Fin 3 × Fin 3

/-- The coefficient of the term indexed by `g`. -/
def cprod (g : Idx n) : ZMod 3 := ∏ i, cf (g i)

def e₁ (g : Idx n) : Exp n := fun i => (g i).1
def e₂ (g : Idx n) : Exp n := fun i => (g i).2.1
def e₃ (g : Idx n) : Exp n := fun i => (g i).2.2

/-- The degree threshold `⌊2n/3⌋`. -/
def D0 : ℕ := 2 * n / 3

/-- Exponent vectors of degree at most `⌊2n/3⌋`. -/
def lowExp : Finset (Exp n) := univ.filter (fun a => deg n a ≤ D0 n)

variable {n}

lemma indicator_prod (x y z : Fin n → ZMod 3) :
    (if x + y + z = 0 then (1 : ZMod 3) else 0)
      = ∏ i, (if x i + y i + z i = 0 then (1 : ZMod 3) else 0) := by
  by_cases h : x + y + z = 0
  · rw [if_pos h]
    refine (Finset.prod_eq_one fun i _ => ?_).symm
    have : x i + y i + z i = 0 := by
      have := congrFun h i
      simpa using this
    rw [if_pos this]
  · rw [if_neg h]
    obtain ⟨i, hi⟩ := Function.ne_iff.mp h
    refine (Finset.prod_eq_zero (Finset.mem_univ i) ?_).symm
    have : x i + y i + z i ≠ 0 := by simpa using hi
    rw [if_neg this]

/-- The main expansion: the indicator of `x + y + z = 0` as a sum of products of monomials. -/
lemma indicator_expand (x y z : Fin n → ZMod 3) :
    (if x + y + z = 0 then (1 : ZMod 3) else 0)
      = ∑ g : Idx n, cprod n g * mon n (e₁ n g) x * mon n (e₂ n g) y * mon n (e₃ n g) z := by
  rw [indicator_prod]
  have step : ∀ i : Fin n, (if x i + y i + z i = 0 then (1 : ZMod 3) else 0)
      = ∑ t : Fin 3 × Fin 3 × Fin 3,
        cf t * x i ^ (t.1 : ℕ) * y i ^ (t.2.1 : ℕ) * z i ^ (t.2.2 : ℕ) :=
    fun i => cf_expand _ _ _
  rw [Finset.prod_congr rfl fun i _ => step i, Fintype.prod_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  simp only [cprod, mon, e₁, e₂, e₃]
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]

/-- Terms with a nonzero coefficient have total degree at most `2n`. -/
lemma deg_le_of_cprod_ne_zero (g : Idx n) (hg : cprod n g ≠ 0) :
    deg n (e₁ n g) + deg n (e₂ n g) + deg n (e₃ n g) ≤ 2 * n := by
  have hall : ∀ i : Fin n, cf (g i) ≠ 0 := by
    intro i hi
    exact hg (Finset.prod_eq_zero (Finset.mem_univ i) hi)
  have : deg n (e₁ n g) + deg n (e₂ n g) + deg n (e₃ n g)
      = ∑ i : Fin n, (((g i).1 : ℕ) + ((g i).2.1 : ℕ) + ((g i).2.2 : ℕ)) := by
    simp [deg, e₁, e₂, e₃, Finset.sum_add_distrib]
  rw [this]
  calc ∑ i : Fin n, (((g i).1 : ℕ) + ((g i).2.1 : ℕ) + ((g i).2.2 : ℕ))
      ≤ ∑ _i : Fin n, 2 := Finset.sum_le_sum fun i _ => cf_deg (g i) (hall i)
    _ = 2 * n := by simp [mul_comm]

variable (n)

/-- The three groups of terms. -/
def P₁ : Finset (Idx n) := univ.filter (fun g => deg n (e₁ n g) ≤ D0 n)
def P₂ : Finset (Idx n) :=
  univ.filter (fun g => ¬ deg n (e₁ n g) ≤ D0 n ∧ deg n (e₂ n g) ≤ D0 n)
def P₃ : Finset (Idx n) :=
  univ.filter (fun g => ¬ deg n (e₁ n g) ≤ D0 n ∧ ¬ deg n (e₂ n g) ≤ D0 n
    ∧ deg n (e₃ n g) ≤ D0 n)

/-- The first family of slice functions. -/
def S₁ (a : Exp n) (y z : Fin n → ZMod 3) : ZMod 3 :=
  ∑ g ∈ (P₁ n).filter (fun g => e₁ n g = a), cprod n g * mon n (e₂ n g) y * mon n (e₃ n g) z

/-- The second family of slice functions. -/
def S₂ (a : Exp n) (x z : Fin n → ZMod 3) : ZMod 3 :=
  ∑ g ∈ (P₂ n).filter (fun g => e₂ n g = a), cprod n g * mon n (e₁ n g) x * mon n (e₃ n g) z

/-- The third family of slice functions. -/
def S₃ (a : Exp n) (x y : Fin n → ZMod 3) : ZMod 3 :=
  ∑ g ∈ (P₃ n).filter (fun g => e₃ n g = a), cprod n g * mon n (e₁ n g) x * mon n (e₂ n g) y

variable {n}

/-- The slice decomposition of the indicator of `x + y + z = 0`. -/
theorem indicator_slices (x y z : Fin n → ZMod 3) :
    (if x + y + z = 0 then (1 : ZMod 3) else 0)
      = (∑ a ∈ lowExp n, mon n a x * S₁ n a y z)
        + (∑ a ∈ lowExp n, mon n a y * S₂ n a x z)
        + (∑ a ∈ lowExp n, mon n a z * S₃ n a x y) := by
  classical
  set F : Idx n → ZMod 3 :=
    fun g => cprod n g * mon n (e₁ n g) x * mon n (e₂ n g) y * mon n (e₃ n g) z with hF
  rw [indicator_expand x y z]
  -- split the total sum into the three groups
  have hsplit : ∑ g : Idx n, F g
      = (∑ g ∈ P₁ n, F g) + (∑ g ∈ P₂ n, F g) + (∑ g ∈ P₃ n, F g) := by
    have hd12 : Disjoint (P₁ n) (P₂ n) := by
      simp only [P₁, P₂, Finset.disjoint_filter]
      intro g _ h1 h2
      exact h2.1 h1
    have hd3 : Disjoint (P₁ n ∪ P₂ n) (P₃ n) := by
      rw [Finset.disjoint_union_left]
      constructor
      · simp only [P₁, P₃, Finset.disjoint_filter]
        intro g _ h1 h2
        exact h2.1 h1
      · simp only [P₂, P₃, Finset.disjoint_filter]
        intro g _ h1 h2
        exact h2.2.1 h1.2
    have hsub : P₁ n ∪ P₂ n ∪ P₃ n ⊆ univ := Finset.subset_univ _
    have hzero : ∀ g ∈ (univ : Finset (Idx n)), g ∉ P₁ n ∪ P₂ n ∪ P₃ n → F g = 0 := by
      intro g _ hg
      simp only [Finset.mem_union, P₁, P₂, P₃, Finset.mem_filter, Finset.mem_univ,
        true_and, not_or, not_and] at hg
      obtain ⟨⟨h1, h2⟩, h3⟩ := hg
      have hc : cprod n g = 0 := by
        by_contra hc
        have hle := deg_le_of_cprod_ne_zero g hc
        have hD : 3 * D0 n + 2 ≥ 2 * n := by
          have := Nat.lt_succ_of_le (Nat.le_refl (D0 n))
          unfold D0
          omega
        have hb2 := h2 h1
        have hb3 := (h3 h1) hb2
        unfold D0 at hD hb2 hb3 h1 hle
        omega
      rw [hF]
      simp [hc]
    rw [← Finset.sum_subset hsub hzero, Finset.sum_union hd3, Finset.sum_union hd12]
  rw [hsplit]
  congr 1
  congr 1
  · -- first group
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun g => e₁ n g) (t := lowExp n) (fun g hg => by
        simp only [lowExp, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [P₁] using hg) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S₁, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have : e₁ n g = a := (Finset.mem_filter.mp hg).2
    rw [hF]
    simp only
    rw [this]
    ring
  · -- second group
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun g => e₂ n g) (t := lowExp n) (fun g hg => by
        simp only [lowExp, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [P₂] using (Finset.mem_filter.mp hg).2.2) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S₂, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have : e₂ n g = a := (Finset.mem_filter.mp hg).2
    rw [hF]
    simp only
    rw [this]
    ring
  · -- third group
    rw [← Finset.sum_fiberwise_of_maps_to
      (g := fun g => e₃ n g) (t := lowExp n) (fun g hg => by
        simp only [lowExp, Finset.mem_filter, Finset.mem_univ, true_and]
        simpa [P₃] using (Finset.mem_filter.mp hg).2.2.2) F]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [S₃, Finset.mul_sum]
    refine Finset.sum_congr rfl fun g hg => ?_
    have : e₃ n g = a := (Finset.mem_filter.mp hg).2
    rw [hF]
    simp only
    rw [this]
    ring

end CapSetAux

/-
# Cap Set
Category: Frontier Math
Target: Math2.cap_set
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.CapCount

/-!
# Cap Set

The cap-set theorem: subsets of `𝔽₃ⁿ` with no three-term arithmetic progression have
size `o(3ⁿ)` (Croot–Lev–Pach / Ellenberg–Gijswijt).

Main results: `Math2.cap_set` and `Math2.capSetMax_isLittleO`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

/-- The exponential decay of the Ellenberg–Gijswijt bound relative to `3ⁿ`. -/
lemma eventually_bound (ε : ℝ) (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, (3 : ℝ) * ((lowExp n).card : ℝ) ≤ ε * 3 ^ n := by
  have hlim := tendsto_pow_atTop_nhds_zero_of_lt_one
    (r := (343 / 432 : ℝ)) (by norm_num) (by norm_num)
  rw [Metric.tendsto_atTop] at hlim
  obtain ⟨N, hN⟩ := hlim (ε ^ 3 / 27) (by positivity)
  refine ⟨N, fun n hn => ?_⟩
  have hsmall : (343 / 432 : ℝ) ^ n ≤ ε ^ 3 / 27 := by
    have := hN n hn
    rw [Real.dist_eq, sub_zero, abs_of_nonneg (by positivity)] at this
    linarith
  have hcube := lowExp_card_cube_le n
  have hkey : (3 * ((lowExp n).card : ℝ)) ^ 3 ≤ (ε * 3 ^ n) ^ 3 := by
    have h1 : (3 * ((lowExp n).card : ℝ)) ^ 3 = 27 * ((lowExp n).card : ℝ) ^ 3 := by ring
    have h2 : (ε * 3 ^ n) ^ 3 = ε ^ 3 * 27 ^ n := by
      rw [mul_pow, ← pow_mul, mul_comm n 3, pow_mul]
      norm_num
    have h3 : (27 : ℝ) ^ n * (343 / 432 : ℝ) ^ n = (343 / 16 : ℝ) ^ n := by
      rw [← mul_pow]
      norm_num
    have h27 : (0 : ℝ) < (27 : ℝ) ^ n := by positivity
    have h4 : 27 * ((lowExp n).card : ℝ) ^ 3 ≤ 27 * (343 / 16 : ℝ) ^ n := by linarith
    have h5 : (27 : ℝ) * (343 / 16 : ℝ) ^ n ≤ ε ^ 3 * 27 ^ n := by
      rw [← h3]
      have : (27 : ℝ) * ((27 : ℝ) ^ n * (343 / 432 : ℝ) ^ n)
          ≤ 27 * ((27 : ℝ) ^ n * (ε ^ 3 / 27)) := by
        have := mul_le_mul_of_nonneg_left hsmall (le_of_lt h27)
        linarith
      calc (27 : ℝ) * ((27 : ℝ) ^ n * (343 / 432 : ℝ) ^ n)
          ≤ 27 * ((27 : ℝ) ^ n * (ε ^ 3 / 27)) := this
        _ = ε ^ 3 * 27 ^ n := by ring
    rw [h1, h2]
    linarith
  have hnn : (0 : ℝ) ≤ ε * 3 ^ n := by positivity
  exact le_of_pow_le_pow_left₀ (by norm_num) hnn hkey

end CapSetAux

namespace Math2

open CapSetAux

/-- **The cap-set theorem** (Croot–Lev–Pach / Ellenberg–Gijswijt).

Subsets of `𝔽₃ⁿ` containing no three-term arithmetic progression have size `o(3ⁿ)`:
for every `ε > 0` there is an `N` such that for all `n ≥ N`, every 3AP-free subset `A`
of `(ZMod 3)ⁿ` satisfies `|A| ≤ ε · 3ⁿ`. -/
theorem cap_set : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N,
    ∀ A : Finset (Fin n → ZMod 3), ThreeAPFree (A : Set (Fin n → ZMod 3)) →
      (A.card : ℝ) ≤ ε * 3 ^ n := by
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_bound ε hε
  refine ⟨N, fun n hn A hA => ?_⟩
  have h1 : A.card ≤ 3 * (lowExp n).card := capset_card_le A hA
  have h2 : (A.card : ℝ) ≤ 3 * ((lowExp n).card : ℝ) := by
    exact_mod_cast h1
  exact h2.trans (hN n hn)

/-- The set of 3AP-free subsets of `𝔽₃ⁿ`. -/
def capSets (n : ℕ) : Finset (Finset (Fin n → ZMod 3)) :=
  (univ : Finset (Finset (Fin n → ZMod 3))).filter
    (fun A : Finset (Fin n → ZMod 3) => ThreeAPFree (A : Set (Fin n → ZMod 3)))

/-- The largest size of a 3AP-free subset of `𝔽₃ⁿ`. -/
def capSetMax (n : ℕ) : ℕ := (capSets n).sup Finset.card

/-- The cap-set theorem in asymptotic form: the maximal size of a 3AP-free subset of
`𝔽₃ⁿ` is `o(3ⁿ)`. -/
theorem capSetMax_isLittleO :
    (fun n => (capSetMax n : ℝ)) =o[Filter.atTop] (fun n => (3 : ℝ) ^ n) := by
  rw [Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := cap_set ε hε
  rw [Filter.eventually_atTop]
  refine ⟨N, fun n hn => ?_⟩
  have hne : (capSets n).Nonempty := by
    refine ⟨∅, ?_⟩
    simp [capSets, ThreeAPFree]
  obtain ⟨A, hAmem, hAeq⟩ := Finset.exists_mem_eq_sup _ hne Finset.card
  have hA : ThreeAPFree (A : Set (Fin n → ZMod 3)) := (mem_filter.mp hAmem).2
  have hbd := hN n hn A hA
  rw [capSetMax, hAeq, Real.norm_natCast,
    Real.norm_of_nonneg (by positivity : (0:ℝ) ≤ (3:ℝ) ^ n)]
  exact hbd

end Math2

import Mathlib

/-!
# Slice rank of the diagonal tensor

This file contains the linear-algebra core of the Croot–Lev–Pach / Ellenberg–Gijswijt
argument: if the diagonal tensor on a finite type `X` admits a decomposition into
`r₁ + r₂ + r₃` "slices", then `card X ≤ r₁ + r₂ + r₃`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

variable {F : Type*} [Field F] {X : Type*} [Fintype X] [DecidableEq X]

/-- The restriction of a submodule of functions `X → F` to a finset `S`. -/
def restrictMap (W : Submodule F (X → F)) (S : Finset X) : W →ₗ[F] (S → F) where
  toFun u := fun x => (u : X → F) (x : X)
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- A subspace `W` of `X → F` contains an element whose support has size at least
`finrank W`. -/
theorem exists_large_support (W : Submodule F (X → F)) :
    ∃ (S : Finset X) (u : X → F), u ∈ W ∧ (∀ x ∈ S, u x ≠ 0) ∧
      Module.finrank F W ≤ S.card := by
  classical
  set P : Finset X → Prop := fun S => ∀ c : X → F, ∃ u ∈ W, ∀ x ∈ S, u x = c x with hP
  have hne : ((univ : Finset (Finset X)).filter P).Nonempty := by
    refine ⟨∅, ?_⟩
    simp only [mem_filter, mem_univ, true_and, hP]
    exact fun c => ⟨0, W.zero_mem, by simp⟩
  obtain ⟨S, hSmem, hSmax⟩ :=
    Finset.exists_max_image ((univ : Finset (Finset X)).filter P) Finset.card hne
  have hPS : P S := (mem_filter.mp hSmem).2
  obtain ⟨u, huW, hu⟩ := hPS (fun _ => 1)
  refine ⟨S, u, huW, ?_, ?_⟩
  · intro x hx
    rw [hu x hx]
    exact one_ne_zero
  · -- maximality forces `finrank W ≤ S.card`
    by_contra hlt
    push_neg at hlt
    -- the restriction map to `S` is surjective, so its kernel is nontrivial
    have hsurj : Function.Surjective (restrictMap W S) := by
      intro c
      obtain ⟨v, hvW, hv⟩ := hPS (fun x => if hx : x ∈ S then c ⟨x, hx⟩ else 0)
      refine ⟨⟨v, hvW⟩, ?_⟩
      funext x
      simpa [restrictMap, x.2] using hv x x.2
    have hrange : LinearMap.range (restrictMap W S) = ⊤ :=
      LinearMap.range_eq_top.mpr hsurj
    have hfr : Module.finrank F (LinearMap.range (restrictMap W S))
        + Module.finrank F (LinearMap.ker (restrictMap W S)) = Module.finrank F W :=
      LinearMap.finrank_range_add_finrank_ker _
    have hrk : Module.finrank F (LinearMap.range (restrictMap W S)) = S.card := by
      rw [hrange, finrank_top]
      simp
    have hkerpos : Module.finrank F (LinearMap.ker (restrictMap W S)) ≠ 0 := by omega
    have hkerne : LinearMap.ker (restrictMap W S) ≠ ⊥ := fun hb => hkerpos (by
      rw [hb]; simp)
    obtain ⟨w, hwker, hw0⟩ := (Submodule.ne_bot_iff _).mp hkerne
    obtain ⟨w, hwmem⟩ := w
    -- `w` vanishes on `S` but is nonzero somewhere
    have hwS : ∀ x ∈ S, (w : X → F) x = 0 := by
      intro x hx
      have := congrFun (LinearMap.mem_ker.mp hwker) ⟨x, hx⟩
      simpa [restrictMap] using this
    have hwne : (w : X → F) ≠ 0 := by
      intro h
      apply hw0
      ext
      simpa using congrFun h _
    obtain ⟨x0, hx0⟩ := Function.ne_iff.mp hwne
    have hx0S : x0 ∉ S := fun hmem => hx0 (by simpa using hwS x0 hmem)
    -- so we can enlarge `S`, contradicting maximality
    have hPins : P (insert x0 S) := by
      intro c
      obtain ⟨v, hvW, hv⟩ := hPS c
      refine ⟨v + ((c x0 - v x0) / (w : X → F) x0) • (w : X → F),
        W.add_mem hvW (W.smul_mem _ hwmem), ?_⟩
      intro x hx
      rcases mem_insert.mp hx with rfl | hx
      · have hwx : w x ≠ 0 := by simpa using hx0
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
        field_simp
        ring
      · simp [hv x hx, hwS x hx]
    have : (insert x0 S).card ≤ S.card :=
      hSmax _ (mem_filter.mpr ⟨mem_univ _, hPins⟩)
    rw [Finset.card_insert_of_notMem hx0S] at this
    omega

/-- **Slice rank of the diagonal tensor.** If the diagonal tensor on a finite type `X`
decomposes as a sum of `card I₁ + card I₂ + card I₃` slices, then
`card X ≤ card I₁ + card I₂ + card I₃`. -/
theorem card_le_of_diag_decomp {I₁ I₂ I₃ : Type*} [Fintype I₁] [Fintype I₂] [Fintype I₃]
    (f₁ : I₁ → X → F) (g₁ : I₁ → X → X → F)
    (f₂ : I₂ → X → F) (g₂ : I₂ → X → X → F)
    (f₃ : I₃ → X → F) (g₃ : I₃ → X → X → F)
    (h : ∀ x y z : X, (if x = y ∧ y = z then (1 : F) else 0)
      = (∑ i, f₁ i x * g₁ i y z) + (∑ i, f₂ i y * g₂ i x z) + (∑ i, f₃ i z * g₃ i x y)) :
    Fintype.card X ≤ Fintype.card I₁ + Fintype.card I₂ + Fintype.card I₃ := by
  classical
  -- Step 1: kill the first family of slices by passing to the kernel of `u ↦ (∑ₓ u x f₁ i x)ᵢ`.
  let L : (X → F) →ₗ[F] (I₁ → F) :=
    { toFun := fun u i => ∑ x, u x * f₁ i x
      map_add' := by intro a b; funext i; simp [add_mul, Finset.sum_add_distrib]
      map_smul' := by intro a b; funext i; simp [Finset.mul_sum, mul_assoc] }
  have hcard : Fintype.card X ≤ Fintype.card I₁ + Module.finrank F (LinearMap.ker L) := by
    have h1 := LinearMap.finrank_range_add_finrank_ker L
    have h2 : Module.finrank F (LinearMap.range L) ≤ Fintype.card I₁ := by
      have h := Submodule.finrank_le (LinearMap.range L)
      simpa using h
    have h3 : Module.finrank F (X → F) = Fintype.card X := by simp
    omega
  obtain ⟨S, u, huW, huS, hSge⟩ := exists_large_support (LinearMap.ker L)
  have hu0 : ∀ i, ∑ x, u x * f₁ i x = 0 := by
    intro i
    have h := LinearMap.mem_ker.mp huW
    exact congrFun h i
  -- Step 2: the resulting matrix is diagonal with `S.card` nonzero entries,
  -- but has rank at most `card I₂ + card I₃`.
  set A : X → X → F := fun y z => ∑ x, u x * (if x = y ∧ y = z then (1 : F) else 0) with hA
  have claim1 : ∀ y z, A y z = if y = z then u y else 0 := by
    intro y z
    by_cases hyz : y = z
    · subst hyz; simp [hA]
    · simp [hA, hyz]
  have claim2 : ∀ y z, A y z
      = (∑ i, f₂ i y * (∑ x, u x * g₂ i x z)) + (∑ i, (∑ x, u x * g₃ i x y) * f₃ i z) := by
    intro y z
    have : A y z = ∑ x, u x * ((∑ i, f₁ i x * g₁ i y z) + (∑ i, f₂ i y * g₂ i x z)
        + (∑ i, f₃ i z * g₃ i x y)) := by
      rw [hA]
      exact Finset.sum_congr rfl fun x _ => by rw [← h x y z]
    rw [this]
    have e1 : ∑ x, u x * (∑ i, f₁ i x * g₁ i y z) = 0 := by
      have step : ∀ x : X, u x * (∑ i, f₁ i x * g₁ i y z) = ∑ i, u x * f₁ i x * g₁ i y z := by
        intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [← Finset.sum_mul, hu0 i, zero_mul]
    have e2 : ∑ x, u x * (∑ i, f₂ i y * g₂ i x z) = ∑ i, f₂ i y * (∑ x, u x * g₂ i x z) := by
      have step : ∀ x : X, u x * (∑ i, f₂ i y * g₂ i x z) = ∑ i, f₂ i y * (u x * g₂ i x z) := by
        intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.mul_sum]
    have e3 : ∑ x, u x * (∑ i, f₃ i z * g₃ i x y) = ∑ i, (∑ x, u x * g₃ i x y) * f₃ i z := by
      have step : ∀ x : X, u x * (∑ i, f₃ i z * g₃ i x y) = ∑ i, (u x * g₃ i x y) * f₃ i z := by
        intro x; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [Finset.sum_congr rfl fun x _ => step x, Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => by rw [Finset.sum_mul]
    simp only [mul_add, Finset.sum_add_distrib, e1, e2, e3, zero_add]
  -- the family of rows indexed by `S` is linearly independent
  have hLI : LinearIndependent F (fun y : S => A (y : X)) := by
    rw [Fintype.linearIndependent_iff]
    intro c hc y
    have hy := congrFun hc (y : X)
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hy
    rw [Finset.sum_eq_single y] at hy
    · rw [claim1, if_pos rfl] at hy
      rcases mul_eq_zero.mp hy with h' | h'
      · exact h'
      · exact absurd h' (huS (y : X) y.2)
    · intro b _ hb
      rw [claim1]
      have : (b : X) ≠ (y : X) := fun hbe => hb (Subtype.ext hbe)
      simp [this]
    · intro hy'
      exact absurd (Finset.mem_univ y) hy'
  -- but every row lies in the span of `card I₂ + card I₃` vectors
  let V : I₂ ⊕ I₃ → (X → F) := fun i => match i with
    | Sum.inl i => fun z => ∑ x, u x * g₂ i x z
    | Sum.inr i => fun z => f₃ i z
  have hspan : ∀ y : S, A (y : X) ∈ Submodule.span F (Set.range V) := by
    intro y
    have : A (y : X) = (∑ i : I₂, f₂ i (y : X) • V (Sum.inl i))
        + (∑ i : I₃, (∑ x, u x * g₃ i x (y : X)) • V (Sum.inr i)) := by
      funext z
      simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, V]
      exact claim2 (y : X) z
    rw [this]
    refine Submodule.add_mem _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
      (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_)
    · exact Submodule.subset_span ⟨Sum.inl i, rfl⟩
    · exact Submodule.subset_span ⟨Sum.inr i, rfl⟩
  letI : Fintype (Set.range V) := Set.Finite.fintype (Set.finite_range V)
  have hle : (Cardinal.mk S) ≤ (Fintype.card (Set.range V) : Cardinal) :=
    linearIndependent_le_span' _ hLI (Set.range V) (by
      rintro _ ⟨y, rfl⟩
      exact hspan y)
  have hle' : S.card ≤ Fintype.card I₂ + Fintype.card I₃ := by
    have h1 : Fintype.card S ≤ Fintype.card (Set.range V) := by
      simpa [Cardinal.mk_fintype] using hle
    have h2 : Fintype.card (Set.range V) ≤ Fintype.card (I₂ ⊕ I₃) := Fintype.card_range_le V
    simp only [Fintype.card_coe, Fintype.card_sum] at h1 h2 ⊢
    omega
  omega

end CapSetAux

import RequestProject.CapBound

/-!
# Counting low-degree exponent vectors

A Chernoff-type estimate: the number of vectors in `{0,1,2}ⁿ` whose coordinate sum is at
most `2n/3` is exponentially smaller than `3ⁿ`.
-/

open scoped BigOperators
open Finset

namespace CapSetAux

lemma sum_half_pow_deg (n : ℕ) :
    ∑ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) = (7 / 4) ^ n := by
  have hpow : ∀ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) = ∏ i, ((1 : ℝ) / 2) ^ ((a i : ℕ)) := by
    intro a
    rw [deg, Finset.prod_pow_eq_pow_sum]
  rw [Finset.sum_congr rfl fun a _ => hpow a,
    ← Fintype.prod_sum (fun (_ : Fin n) (k : Fin 3) => ((1 : ℝ) / 2) ^ (k : ℕ))]
  have : ∀ _i : Fin n, ∑ k : Fin 3, ((1 : ℝ) / 2) ^ (k : ℕ) = 7 / 4 := by
    intro _i
    simp [Fin.sum_univ_three]
    norm_num
  rw [Finset.prod_congr rfl fun i _ => this i]
  simp [div_pow]

/-- The basic Chernoff bound on the number of low-degree exponent vectors. -/
lemma lowExp_card_mul_le (n : ℕ) :
    ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n) ≤ (7 / 4) ^ n := by
  have h1 : ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n)
      = ∑ _a ∈ lowExp n, ((1 : ℝ) / 2) ^ (D0 n) := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h2 : ∑ _a ∈ lowExp n, ((1 : ℝ) / 2) ^ (D0 n)
      ≤ ∑ a ∈ lowExp n, ((1 : ℝ) / 2) ^ (deg n a) := by
    refine Finset.sum_le_sum fun a ha => ?_
    have hdeg : deg n a ≤ D0 n := by
      simpa [lowExp] using ha
    exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hdeg
  have h3 : ∑ a ∈ lowExp n, ((1 : ℝ) / 2) ^ (deg n a) ≤ ∑ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun a _ _ => by positivity)
  rw [h1]
  calc ∑ _a ∈ lowExp n, ((1 : ℝ) / 2) ^ (D0 n) ≤ ∑ a ∈ lowExp n, ((1 : ℝ) / 2) ^ (deg n a) := h2
    _ ≤ ∑ a : Exp n, ((1 : ℝ) / 2) ^ (deg n a) := h3
    _ = (7 / 4) ^ n := sum_half_pow_deg n

/-- The cube of the number of low-degree exponent vectors is at most `(343/16)ⁿ`. -/
lemma lowExp_card_cube_le (n : ℕ) : ((lowExp n).card : ℝ) ^ 3 ≤ (343 / 16) ^ n := by
  have hmul := lowExp_card_mul_le n
  have hcard : ((lowExp n).card : ℝ) ≤ (7 / 4) ^ n * 2 ^ (D0 n) := by
    have h2 : (0 : ℝ) < 2 ^ (D0 n) := by positivity
    have : ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n) * 2 ^ (D0 n)
        ≤ (7 / 4) ^ n * 2 ^ (D0 n) := by
      exact mul_le_mul_of_nonneg_right hmul (le_of_lt h2)
    calc ((lowExp n).card : ℝ)
        = ((lowExp n).card : ℝ) * ((1 : ℝ) / 2) ^ (D0 n) * 2 ^ (D0 n) := by
          rw [mul_assoc, ← mul_pow]
          norm_num
      _ ≤ (7 / 4) ^ n * 2 ^ (D0 n) := this
  have hnn : (0 : ℝ) ≤ ((lowExp n).card : ℝ) := by positivity
  have hcube : ((lowExp n).card : ℝ) ^ 3 ≤ ((7 / 4) ^ n * 2 ^ (D0 n)) ^ 3 :=
    pow_le_pow_left₀ hnn hcard 3
  have hD : 3 * D0 n ≤ 2 * n := by
    unfold D0
    omega
  have hexp : ((7 / 4 : ℝ) ^ n * 2 ^ (D0 n)) ^ 3 ≤ (343 / 16) ^ n := by
    have h1 : ((7 / 4 : ℝ) ^ n * 2 ^ (D0 n)) ^ 3 = (343 / 64 : ℝ) ^ n * 2 ^ (3 * D0 n) := by
      rw [mul_pow, ← pow_mul, ← pow_mul, mul_comm n 3, mul_comm (D0 n) 3, pow_mul]
      norm_num
    have h2 : (2 : ℝ) ^ (3 * D0 n) ≤ 2 ^ (2 * n) :=
      pow_le_pow_right₀ (by norm_num) hD
    have h3 : (0 : ℝ) < (343 / 64 : ℝ) ^ n := by positivity
    calc ((7 / 4 : ℝ) ^ n * 2 ^ (D0 n)) ^ 3 = (343 / 64 : ℝ) ^ n * 2 ^ (3 * D0 n) := h1
      _ ≤ (343 / 64 : ℝ) ^ n * 2 ^ (2 * n) := by
          exact mul_le_mul_of_nonneg_left h2 (le_of_lt h3)
      _ = (343 / 16 : ℝ) ^ n := by
          have h4 : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
            rw [pow_mul]; norm_num
          rw [h4, ← mul_pow]
          norm_num
  linarith

end CapSetAux

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

