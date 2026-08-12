/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Statement: Yao's minimax principle relates randomized and distributional complexity.
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

namespace CS

variable {A I : Type*} [Fintype A] [Nonempty A] [Fintype I] [Nonempty I]

/-- The expected cost of the randomized algorithm given by the mixed strategy `p`
(a distribution over the deterministic algorithms `A`) on the worst-case input. -/
noncomputable def randomizedCost (C : A → I → ℝ) (p : A → ℝ) : ℝ :=
  ⨆ i : I, ∑ a, p a * C a i

/-- The expected cost of the best deterministic algorithm against the input
distribution `q`. -/
noncomputable def distributionalCost (C : A → I → ℝ) (q : I → ℝ) : ℝ :=
  ⨅ a : A, ∑ i, q i * C a i

/-- The randomized complexity: the minimal worst-case expected cost over all
randomized algorithms. -/
noncomputable def randomizedComplexity (C : A → I → ℝ) : ℝ :=
  ⨅ p : stdSimplex ℝ A, randomizedCost C (p : A → ℝ)

/-- The distributional complexity: the maximal, over input distributions, of the
expected cost of the best deterministic algorithm for that distribution. -/
noncomputable def distributionalComplexity (C : A → I → ℝ) : ℝ :=
  ⨆ q : stdSimplex ℝ I, distributionalCost C (q : I → ℝ)

/-! ### Elementary bounds -/

omit [Nonempty A] [Nonempty I] in
lemma expect_le_randomizedCost (C : A → I → ℝ) (p : A → ℝ) (i : I) :
    ∑ a, p a * C a i ≤ randomizedCost C p :=
  le_ciSup (Finite.bddAbove_range (fun i : I => ∑ a, p a * C a i)) i

omit [Nonempty A] [Nonempty I] in
lemma distributionalCost_le_expect (C : A → I → ℝ) (q : I → ℝ) (a : A) :
    distributionalCost C q ≤ ∑ i, q i * C a i :=
  ciInf_le (Finite.bddBelow_range (fun a : A => ∑ i, q i * C a i)) a

/-- A uniform bound on the entries of the cost matrix. -/
noncomputable def costBound (C : A → I → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun a : A => Finset.univ.sup' Finset.univ_nonempty (fun i : I => |C a i|))

lemma le_costBound (C : A → I → ℝ) (a : A) (i : I) : |C a i| ≤ costBound C := by
  refine le_trans ?_ (Finset.le_sup' (f := fun a : A =>
    Finset.univ.sup' Finset.univ_nonempty (fun i : I => |C a i|)) (Finset.mem_univ a))
  exact Finset.le_sup' (f := fun i : I => |C a i|) (Finset.mem_univ i)

lemma abs_expect_le (C : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) (i : I) :
    |∑ a, p a * C a i| ≤ costBound C := by
  obtain ⟨hp0, hp1⟩ := hp
  calc |∑ a, p a * C a i| ≤ ∑ a, |p a * C a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ a, p a * costBound C := by
        refine Finset.sum_le_sum fun a _ => ?_
        rw [abs_mul, abs_of_nonneg (hp0 a)]
        exact mul_le_mul_of_nonneg_left (le_costBound C a i) (hp0 a)
    _ = costBound C := by rw [← Finset.sum_mul, hp1, one_mul]

lemma abs_expect_le' (C : A → I → ℝ) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) (a : A) :
    |∑ i, q i * C a i| ≤ costBound C := by
  obtain ⟨hq0, hq1⟩ := hq
  calc |∑ i, q i * C a i| ≤ ∑ i, |q i * C a i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, q i * costBound C := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (hq0 i)]
        exact mul_le_mul_of_nonneg_left (le_costBound C a i) (hq0 i)
    _ = costBound C := by rw [← Finset.sum_mul, hq1, one_mul]

lemma randomizedCost_le (C : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) :
    randomizedCost C p ≤ costBound C :=
  ciSup_le fun i => (abs_le.1 (abs_expect_le C hp i)).2

lemma le_randomizedCost (C : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) :
    -costBound C ≤ randomizedCost C p := by
  obtain ⟨i⟩ := ‹Nonempty I›
  exact le_trans (abs_le.1 (abs_expect_le C hp i)).1 (expect_le_randomizedCost C p i)

lemma distributionalCost_le (C : A → I → ℝ) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    distributionalCost C q ≤ costBound C := by
  obtain ⟨a⟩ := ‹Nonempty A›
  exact le_trans (distributionalCost_le_expect C q a) (abs_le.1 (abs_expect_le' C hq a)).2

lemma bddBelow_randomizedCost (C : A → I → ℝ) :
    BddBelow (Set.range fun p : stdSimplex ℝ A => randomizedCost C (p : A → ℝ)) := by
  refine ⟨-costBound C, ?_⟩
  rintro x ⟨p, rfl⟩
  exact le_randomizedCost C p.2

lemma bddAbove_distributionalCost (C : A → I → ℝ) :
    BddAbove (Set.range fun q : stdSimplex ℝ I => distributionalCost C (q : I → ℝ)) := by
  refine ⟨costBound C, ?_⟩
  rintro x ⟨q, rfl⟩
  exact distributionalCost_le C q.2

lemma randomizedComplexity_le (C : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) :
    randomizedComplexity C ≤ randomizedCost C p :=
  ciInf_le (bddBelow_randomizedCost C) (⟨p, hp⟩ : stdSimplex ℝ A)

lemma le_distributionalComplexity (C : A → I → ℝ) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    distributionalCost C q ≤ distributionalComplexity C :=
  le_ciSup (bddAbove_distributionalCost C) (⟨q, hq⟩ : stdSimplex ℝ I)

/-! ### Weak duality -/

omit [Nonempty A] [Nonempty I] in
lemma weak_duality (C : A → I → ℝ) {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A)
    {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    distributionalCost C q ≤ randomizedCost C p := by
  obtain ⟨hp0, hp1⟩ := hp
  obtain ⟨hq0, hq1⟩ := hq
  have h1 : distributionalCost C q ≤ ∑ a, p a * (∑ i, q i * C a i) := by
    have h : ∑ a, p a * distributionalCost C q ≤ ∑ a, p a * (∑ i, q i * C a i) :=
      Finset.sum_le_sum fun a _ =>
        mul_le_mul_of_nonneg_left (distributionalCost_le_expect C q a) (hp0 a)
    rwa [← Finset.sum_mul, hp1, one_mul] at h
  refine h1.trans ?_
  have hswap : ∑ a, p a * (∑ i, q i * C a i) = ∑ i, q i * (∑ a, p a * C a i) := by
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  rw [hswap]
  have h : ∑ i, q i * (∑ a, p a * C a i) ≤ ∑ i, q i * randomizedCost C p :=
    Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (expect_le_randomizedCost C p i) (hq0 i)
  rwa [← Finset.sum_mul, hq1, one_mul] at h

lemma distributionalComplexity_le (C : A → I → ℝ) :
    distributionalComplexity C ≤ randomizedComplexity C :=
  ciSup_le fun q => le_ciInf fun p => weak_duality C p.2 q.2

/-! ### The linear map given by the cost matrix -/

/-- The linear map sending a mixed strategy `p` over algorithms to the vector of
expected costs on each input. -/
noncomputable def costMap (C : A → I → ℝ) : (A → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun p := fun i => ∑ a, p a * C a i
  map_add' x y := by
    funext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' c x := by
    funext i; simp [Finset.mul_sum, mul_assoc]

omit [Nonempty A] [Fintype I] [Nonempty I] in
@[simp] lemma costMap_apply (C : A → I → ℝ) (p : A → ℝ) (i : I) :
    costMap C p i = ∑ a, p a * C a i := rfl

/-! ### Strong duality via a separating hyperplane -/

lemma exists_dual_distribution (C : A → I → ℝ) :
    ∃ q ∈ stdSimplex ℝ I, ∀ a : A, randomizedComplexity C ≤ ∑ i, q i * C a i := by
  set v : ℝ := randomizedComplexity C with hv
  set s : Set (I → ℝ) := Set.pi Set.univ (fun _ : I => Set.Iio v) with hs
  set t : Set (I → ℝ) := (costMap C) '' (stdSimplex ℝ A) with ht
  have hsmem : ∀ y : I → ℝ, y ∈ s ↔ ∀ i, y i < v := by
    intro y; simp [hs]
  have hs_conv : Convex ℝ s := convex_pi fun _ _ => convex_Iio v
  have hs_open : IsOpen s := isOpen_set_pi Set.finite_univ fun _ _ => isOpen_Iio
  have ht_conv : Convex ℝ t := (convex_stdSimplex ℝ A).linear_image (costMap C)
  have hdisj : Disjoint s t := by
    rw [Set.disjoint_left]
    rintro y hy ⟨p, hp, rfl⟩
    have hlt : ∀ i, (costMap C p) i < v := (hsmem _).1 hy
    obtain ⟨i₀, hi₀⟩ : ∃ i₀ : I, ∀ i, (costMap C p) i ≤ (costMap C p) i₀ :=
      Finite.exists_max _
    have h1 : randomizedCost C p ≤ (costMap C p) i₀ := ciSup_le fun i => hi₀ i
    have h2 : v ≤ randomizedCost C p := randomizedComplexity_le C hp
    exact absurd (lt_of_le_of_lt (h2.trans h1) (hlt i₀)) (lt_irrefl v)
  obtain ⟨f, u, hfs, hft⟩ := geometric_hahn_banach_open hs_conv hs_open ht_conv hdisj
  -- the coefficient vector of the separating functional
  set qr : I → ℝ := fun i => f (Pi.single i 1) with hqrdef
  have hqr : ∀ i : I, qr i = f (Pi.single i 1) := fun _ => rfl
  have hfy : ∀ y : I → ℝ, f y = ∑ i, y i * qr i := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsing : (Pi.single i (y i) : I → ℝ) = y i • (Pi.single i 1 : I → ℝ) := by
      funext j
      by_cases h : j = i
      · subst h; simp
      · simp [h]
    rw [hsing, map_smul, smul_eq_mul, hqr i]
  have hconst : ∀ c : ℝ, c < v → (fun _ : I => c) ∈ s := fun c hc => (hsmem _).2 fun _ => hc
  -- the coefficients are nonnegative
  have hnonneg : ∀ i, 0 ≤ qr i := by
    intro i
    by_contra hneg
    push_neg at hneg
    set y0 : I → ℝ := fun _ : I => v - 1 with hy0
    have hy0s : y0 ∈ s := hconst _ (by linarith)
    have hpos : 0 < -qr i := by linarith
    have hfy0 : f y0 < u := hfs _ hy0s
    set d : ℝ := (u - f y0) / (-qr i) + 1 with hd
    have hd0 : 0 ≤ d := by
      have : 0 ≤ (u - f y0) / (-qr i) := div_nonneg (by linarith) (le_of_lt hpos)
      linarith
    set y1 : I → ℝ := y0 - d • (Pi.single i 1 : I → ℝ) with hy1
    have hy1s : y1 ∈ s := by
      refine (hsmem _).2 fun j => ?_
      have hval : y1 j = (v - 1) - d * (Pi.single i (1 : ℝ) : I → ℝ) j := by
        simp [hy1, hy0]
      rw [hval]
      have hge : 0 ≤ d * (Pi.single i (1 : ℝ) : I → ℝ) j := by
        refine mul_nonneg hd0 ?_
        by_cases h : j = i
        · subst h; simp
        · simp [h]
      linarith
    have hlt : f y1 < u := hfs _ hy1s
    have hfy1 : f y1 = f y0 - d * qr i := by
      rw [hy1, map_sub, map_smul, smul_eq_mul, hqr i]
    have hdval : d * (-qr i) = (u - f y0) + (-qr i) := by
      rw [hd, add_mul, div_mul_cancel₀ _ (ne_of_gt hpos), one_mul]
    have hrw : f y0 - d * qr i = f y0 + d * (-qr i) := by ring
    rw [hfy1, hrw, hdval] at hlt
    linarith
  set S : ℝ := ∑ i, qr i with hS
  have hSnonneg : 0 ≤ S := Finset.sum_nonneg fun i _ => hnonneg i
  have hSpos : 0 < S := by
    rcases lt_or_eq_of_le hSnonneg with h | h
    · exact h
    · exfalso
      have hall : ∀ i, qr i = 0 := fun i =>
        (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).1 h.symm i (Finset.mem_univ i)
      have hf0 : ∀ y : I → ℝ, f y = 0 := by
        intro y; rw [hfy y]; simp [hall]
      have h1 : (0 : ℝ) < u := by
        have hx := hfs _ (hconst (v - 1) (by linarith))
        rwa [hf0] at hx
      obtain ⟨p0, hp0⟩ : (stdSimplex ℝ A).Nonempty := Set.Nonempty.of_subtype
      have h2 : u ≤ 0 := by
        have hx := hft (costMap C p0) ⟨p0, hp0, rfl⟩
        rwa [hf0] at hx
      linarith
  have hvS : v * S ≤ u := by
    by_contra hcon
    push_neg at hcon
    have hc : u / S < v := by
      rw [div_lt_iff₀ hSpos]
      linarith [mul_comm v S]
    have hlt := hfs _ (hconst (u / S) hc)
    simp only [hfy] at hlt
    have heq : ∑ _i : I, (u / S) * qr _i = u := by
      rw [← Finset.mul_sum, ← hS, div_mul_cancel₀ _ (ne_of_gt hSpos)]
    rw [heq] at hlt
    exact lt_irrefl u hlt
  refine ⟨fun i => qr i / S, ⟨fun i => div_nonneg (hnonneg i) (le_of_lt hSpos), ?_⟩, ?_⟩
  · rw [← Finset.sum_div, ← hS, div_self (ne_of_gt hSpos)]
  · intro a
    have hmem : (Pi.single a (1 : ℝ) : A → ℝ) ∈ stdSimplex ℝ A := by
      constructor
      · intro a'
        by_cases h : a' = a
        · subst h; simp
        · simp [h]
      · simp
    have hrow : ∀ i : I, (costMap C (Pi.single a (1 : ℝ) : A → ℝ)) i = C a i := by
      intro i
      simp [costMap_apply, Pi.single_apply, Finset.sum_ite_eq']
    have hu : u ≤ ∑ i, C a i * qr i := by
      have hx := hft (costMap C (Pi.single a (1 : ℝ) : A → ℝ)) ⟨_, hmem, rfl⟩
      rw [hfy] at hx
      calc u ≤ ∑ i, (costMap C (Pi.single a (1 : ℝ) : A → ℝ)) i * qr i := hx
        _ = ∑ i, C a i * qr i := Finset.sum_congr rfl fun i _ => by rw [hrow i]
    have hfin : v * S ≤ ∑ i, C a i * qr i := le_trans hvS hu
    show v ≤ ∑ i, (qr i / S) * C a i
    have hsum : ∑ i, (qr i / S) * C a i = (∑ i, C a i * qr i) / S := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [hsum, le_div_iff₀ hSpos]
    exact hfin

/-! ### Yao's minimax principle -/

/-- **Yao's minimax principle.** For a finite nonempty set `A` of deterministic algorithms,
a finite nonempty set `I` of inputs, and a cost matrix `C : A → I → ℝ`, the randomized
complexity (the least worst-case expected cost of a randomized algorithm, i.e. of a
distribution over deterministic algorithms) equals the distributional complexity (the
greatest, over input distributions `q`, of the expected cost of the best deterministic
algorithm against `q`). -/
theorem yao_principle (C : A → I → ℝ) :
    randomizedComplexity C = distributionalComplexity C := by
  refine le_antisymm ?_ (distributionalComplexity_le C)
  obtain ⟨q, hq, hqle⟩ := exists_dual_distribution C
  exact (le_ciInf fun a => hqle a).trans (le_distributionalComplexity C hq)

end CS

