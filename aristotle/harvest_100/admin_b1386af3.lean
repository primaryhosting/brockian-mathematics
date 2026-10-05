/-
# Singular Series Convergence Rate
Category: Brockian Corpus
Target: Brockian.SingularSeriesConvergenceRate
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open Filter Topology

namespace Brockian

/-- The local factor deficiency `1/(p-1)^2` occurring in the twin-prime singular series. -/
noncomputable def singularTerm (p : ℕ) : ℝ := 1 / ((p : ℝ) - 1) ^ 2

/-- The truncated singular series (the twin-prime constant without its factor `2`):
the product of `1 - 1/(p-1)^2` over the odd primes `p ≤ N`. -/
noncomputable def singularPartial (N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ico 3 (N + 1)).filter Nat.Prime, (1 - singularTerm p)

/-- The tail product of local factors, over the primes `p` with `M < p ≤ N`. -/
noncomputable def tailProd (M N : ℕ) : ℝ :=
  ∏ p ∈ (Finset.Ico (M + 1) (N + 1)).filter Nat.Prime, (1 - singularTerm p)

lemma singularTerm_nonneg (p : ℕ) : 0 ≤ singularTerm p := by
  unfold singularTerm; positivity

lemma singularTerm_le_one {p : ℕ} (hp : 3 ≤ p) : singularTerm p ≤ 1 := by
  have h : (2 : ℝ) ≤ (p : ℝ) - 1 := by
    have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  unfold singularTerm
  rw [div_le_one (by nlinarith)]
  nlinarith

/-- Weierstrass-type product inequality: `1 - ∑ f ≤ ∏ (1 - f)` for `f` valued in `[0,1]`. -/
lemma one_sub_sum_le_prod_one_sub {s : Finset ℕ} {f : ℕ → ℝ}
    (h0 : ∀ i ∈ s, 0 ≤ f i) (h1 : ∀ i ∈ s, f i ≤ 1) :
    1 - ∑ i ∈ s, f i ≤ ∏ i ∈ s, (1 - f i) := by
  classical
  induction s using Finset.cons_induction with
  | empty => simp
  | cons a s ha ih =>
      have h0' : ∀ i ∈ s, 0 ≤ f i := fun i hi => h0 i (Finset.mem_cons_of_mem hi)
      have h1' : ∀ i ∈ s, f i ≤ 1 := fun i hi => h1 i (Finset.mem_cons_of_mem hi)
      have hP := ih h0' h1'
      have hsum : 0 ≤ ∑ i ∈ s, f i := Finset.sum_nonneg h0'
      have hfa0 : 0 ≤ f a := h0 a (Finset.mem_cons_self _ _)
      have hfa1 : f a ≤ 1 := h1 a (Finset.mem_cons_self _ _)
      rw [Finset.prod_cons, Finset.sum_cons]
      have hmul : (1 - f a) * (1 - ∑ i ∈ s, f i) ≤ (1 - f a) * ∏ i ∈ s, (1 - f i) :=
        mul_le_mul_of_nonneg_left hP (by linarith)
      nlinarith

/-- Each partial product lies in `[0, 1]`. -/
lemma singularPartial_mem_Icc (N : ℕ) : 0 ≤ singularPartial N ∧ singularPartial N ≤ 1 := by
  constructor
  · refine Finset.prod_nonneg ?_
    intro p hp
    simp only [Finset.mem_filter, Finset.mem_Ico] at hp
    have := singularTerm_le_one hp.1.1
    linarith
  · refine Finset.prod_le_one ?_ ?_ <;> intro p hp
    · simp only [Finset.mem_filter, Finset.mem_Ico] at hp
      have := singularTerm_le_one hp.1.1
      linarith
    · have := singularTerm_nonneg p
      linarith

lemma singularPartial_nonneg (N : ℕ) : 0 ≤ singularPartial N := (singularPartial_mem_Icc N).1

lemma singularPartial_le_one (N : ℕ) : singularPartial N ≤ 1 := (singularPartial_mem_Icc N).2

/-- Telescoping bound for the tail sum of `1/(n-1)^2`. -/
lemma sum_singularTerm_le {a b : ℕ} (ha : 3 ≤ a) (hab : a ≤ b) :
    ∑ n ∈ Finset.Ico a b, singularTerm n ≤ 1 / ((a : ℝ) - 2) - 1 / ((b : ℝ) - 2) := by
  induction b, hab using Nat.le_induction with
  | base => simp
  | succ b hb ih =>
      have ha3 : (3 : ℝ) ≤ (a : ℝ) := by exact_mod_cast ha
      have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
      have hx : (0 : ℝ) < (b : ℝ) - 2 := by linarith
      have hy : (0 : ℝ) < (b : ℝ) - 1 := by linarith
      rw [Finset.sum_Ico_succ_top hb]
      have hstep : singularTerm b ≤ 1 / ((b : ℝ) - 2) - 1 / ((b : ℝ) - 1) := by
        have hrw : 1 / ((b : ℝ) - 2) - 1 / ((b : ℝ) - 1)
            = 1 / (((b : ℝ) - 2) * ((b : ℝ) - 1)) := by
          field_simp
          ring
        rw [hrw]
        unfold singularTerm
        exact one_div_le_one_div_of_le (by positivity) (by nlinarith)
      have hcast : (((b + 1 : ℕ)) : ℝ) - 2 = (b : ℝ) - 1 := by push_cast; ring
      rw [hcast]
      linarith

/-- The tail product lies in `[0,1]` and is bounded below by `1 - 1/(M-1)`. -/
lemma tailProd_bounds {M N : ℕ} (h2 : 2 ≤ M) :
    0 ≤ tailProd M N ∧ tailProd M N ≤ 1 ∧ 1 - 1 / ((M : ℝ) - 1) ≤ tailProd M N := by
  classical
  set T := (Finset.Ico (M + 1) (N + 1)).filter Nat.Prime with hT
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
  have hterms0 : ∀ p ∈ T, 0 ≤ singularTerm p := fun p _ => singularTerm_nonneg p
  have hterms1 : ∀ p ∈ T, singularTerm p ≤ 1 := by
    intro p hp
    simp only [hT, Finset.mem_filter, Finset.mem_Ico] at hp
    exact singularTerm_le_one (by omega)
  refine ⟨Finset.prod_nonneg fun p hp => by have := hterms1 p hp; linarith,
    Finset.prod_le_one (fun p hp => by have := hterms1 p hp; linarith)
      (fun p hp => by have := hterms0 p hp; linarith), ?_⟩
  have hsumT : ∑ p ∈ T, singularTerm p ≤ 1 / ((M : ℝ) - 1) := by
    rcases le_or_gt M N with hMN | hMN
    · have h1 : ∑ p ∈ T, singularTerm p ≤ ∑ n ∈ Finset.Ico (M + 1) (N + 1), singularTerm n :=
        Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
          (fun i _ _ => singularTerm_nonneg i)
      have h2' := sum_singularTerm_le (a := M + 1) (b := N + 1) (by omega) (by omega)
      have hcast : ((M + 1 : ℕ) : ℝ) - 2 = (M : ℝ) - 1 := by push_cast; ring
      have hNR : (M : ℝ) ≤ (N : ℝ) := by exact_mod_cast hMN
      have hpos : 0 < 1 / (((N + 1 : ℕ) : ℝ) - 2) := by
        have : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) - 2 := by push_cast; linarith
        positivity
      rw [hcast] at h2'
      linarith
    · have hempty : T = ∅ := by
        rw [hT, Finset.Ico_eq_empty (by omega), Finset.filter_empty]
      have hbnd0 : 0 ≤ 1 / ((M : ℝ) - 1) := by
        have : (0 : ℝ) < (M : ℝ) - 1 := by linarith
        positivity
      rw [hempty]
      simpa using hbnd0
  have := one_sub_sum_le_prod_one_sub hterms0 hterms1
  unfold tailProd
  rw [← hT]
  linarith

/-- Splitting the truncated product at level `M`. -/
lemma singularPartial_split {M N : ℕ} (h2 : 2 ≤ M) (hMN : M ≤ N) :
    singularPartial N = singularPartial M * tailProd M N := by
  classical
  unfold singularPartial tailProd
  rw [← Finset.prod_union]
  · rw [← Finset.filter_union, Finset.Ico_union_Ico_eq_Ico (by omega) (by omega)]
  · exact Finset.disjoint_filter_filter (Finset.Ico_disjoint_Ico_consecutive _ _ _)

/-- The truncated products are nonincreasing in the truncation level. -/
lemma singularPartial_antitone : Antitone singularPartial := by
  intro M N hMN
  rcases le_or_gt 2 M with h2 | h2
  · obtain ⟨hP0, hP1, -⟩ := tailProd_bounds (M := M) (N := N) h2
    rw [singularPartial_split h2 hMN]
    nlinarith [singularPartial_nonneg M]
  · have hIco : Finset.Ico 3 (M + 1) = (∅ : Finset ℕ) := by
      rw [Finset.Ico_eq_empty]; omega
    have hM : singularPartial M = 1 := by
      unfold singularPartial
      rw [hIco]
      simp
    rw [hM]
    exact singularPartial_le_one N

/-- Effective Cauchy estimate: truncations at levels `M ≤ N` differ by at most `1/(M-1)`. -/
lemma singularPartial_cauchy {M N : ℕ} (h2 : 2 ≤ M) (hMN : M ≤ N) :
    |singularPartial N - singularPartial M| ≤ 1 / ((M : ℝ) - 1) := by
  obtain ⟨hP0, hP1, hPge⟩ := tailProd_bounds (M := M) (N := N) h2
  have hM2 : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast h2
  have hSM0 := singularPartial_nonneg M
  have hSM1 := singularPartial_le_one M
  have hbnd0 : 0 ≤ 1 / ((M : ℝ) - 1) := by
    have : (0 : ℝ) < (M : ℝ) - 1 := by linarith
    positivity
  rw [singularPartial_split h2 hMN, abs_le]
  constructor
  · nlinarith
  · nlinarith

/-- The truncation at level `3` equals `1 - 1/4 = 3/4`. -/
lemma singularPartial_three : singularPartial 3 = 3 / 4 := by
  have hIco : (Finset.Ico 3 (3 + 1)).filter Nat.Prime = {3} := by decide
  unfold singularPartial
  rw [hIco]
  norm_num [singularTerm]

/-- The truncation at level `4` also equals `3/4`, since `4` is not prime. -/
lemma singularPartial_four : singularPartial 4 = 3 / 4 := by
  have hIco : (Finset.Ico 3 (4 + 1)).filter Nat.Prime = {3} := by decide
  unfold singularPartial
  rw [hIco]
  norm_num [singularTerm]

/-- Every truncation, hence the limit, is at least `1/2`; in particular the singular
series does not degenerate to `0`. -/
lemma singularPartial_ge_half (N : ℕ) : 1 / 2 ≤ singularPartial N := by
  rcases le_or_gt 4 N with h | h
  · obtain ⟨-, -, hPge⟩ := tailProd_bounds (M := 4) (N := N) (by norm_num)
    rw [singularPartial_split (M := 4) (by norm_num) h, singularPartial_four]
    norm_num at hPge ⊢
    linarith
  · have := singularPartial_antitone (show N ≤ 3 by omega)
    rw [singularPartial_three] at this
    linarith

/-- **Singular series convergence rate.**  The truncated twin-prime singular series
`∏_{3 ≤ p ≤ N, p prime} (1 - 1/(p-1)^2)` converges to a limit `L ≥ 1/2`, and the
truncation at level `N ≥ 2` approximates `L` with the effective error bound `1/(N-1)`. -/
theorem SingularSeriesConvergenceRate :
    ∃ L : ℝ, Tendsto singularPartial atTop (𝓝 L) ∧ 1 / 2 ≤ L ∧
      ∀ N : ℕ, 2 ≤ N → |singularPartial N - L| ≤ 1 / ((N : ℝ) - 1) := by
  have hbdd : BddBelow (Set.range singularPartial) :=
    ⟨0, by rintro x ⟨n, rfl⟩; exact singularPartial_nonneg n⟩
  refine ⟨⨅ n, singularPartial n, tendsto_atTop_ciInf singularPartial_antitone hbdd, ?_, ?_⟩
  · exact le_ciInf fun n => singularPartial_ge_half n
  · intro N hN
    have hNR : (2 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hbnd0 : 0 ≤ 1 / ((N : ℝ) - 1) := by
      have : (0 : ℝ) < (N : ℝ) - 1 := by linarith
      positivity
    have hle : (⨅ n, singularPartial n) ≤ singularPartial N := ciInf_le hbdd N
    have hge : singularPartial N - 1 / ((N : ℝ) - 1) ≤ ⨅ n, singularPartial n := by
      refine le_ciInf fun M => ?_
      rcases le_total N M with h | h
      · have hc := abs_le.mp (singularPartial_cauchy hN h)
        linarith [hc.1]
      · have := singularPartial_antitone h
        linarith
    rw [abs_le]
    constructor <;> linarith

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

