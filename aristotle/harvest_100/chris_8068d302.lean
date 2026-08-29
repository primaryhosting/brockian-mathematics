/-
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to come before any module docstring, so the required header appears
-- at the top of the file as a plain comment and again here as the module docstring.)

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

namespace CS

variable {A I : Type*} [Fintype A] [Fintype I] [Nonempty A] [Nonempty I]

/-- The worst-case expected cost of the randomized algorithm given by the distribution `p`
over deterministic algorithms:  `max over inputs i of  E_{a ~ p} [c a i]`. -/
noncomputable def randCost (c : A → I → ℝ) (p : A → ℝ) : ℝ := ⨆ i, ∑ a, p a * c a i

/-- The distributional complexity of the input distribution `q`:
`min over deterministic algorithms a of  E_{i ~ q} [c a i]`. -/
noncomputable def distCost (c : A → I → ℝ) (q : I → ℝ) : ℝ := ⨅ a, ∑ i, q i * c a i

/-! ### Basic facts about `randCost` and `distCost` -/

lemma bddAbove_range_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) : BddAbove (Set.range f) :=
  (Set.finite_range f).bddAbove

lemma bddBelow_range_of_finite {ι : Type*} [Finite ι] (f : ι → ℝ) : BddBelow (Set.range f) :=
  (Set.finite_range f).bddBelow

omit [Nonempty A] [Nonempty I] in
lemma le_randCost (c : A → I → ℝ) (p : A → ℝ) (i : I) :
    ∑ a, p a * c a i ≤ randCost c p := by
  unfold randCost
  exact le_ciSup (f := fun i => ∑ a, p a * c a i) (bddAbove_range_of_finite _) i

omit [Fintype I] [Nonempty A] in
lemma randCost_le {c : A → I → ℝ} {p : A → ℝ} {x : ℝ} (h : ∀ i, ∑ a, p a * c a i ≤ x) :
    randCost c p ≤ x := by
  unfold randCost
  exact ciSup_le h

omit [Nonempty A] [Nonempty I] in
lemma distCost_le (c : A → I → ℝ) (q : I → ℝ) (a : A) :
    distCost c q ≤ ∑ i, q i * c a i := by
  unfold distCost
  exact ciInf_le (f := fun a => ∑ i, q i * c a i) (bddBelow_range_of_finite _) a

omit [Fintype A] [Nonempty I] in
lemma le_distCost {c : A → I → ℝ} {q : I → ℝ} {x : ℝ} (h : ∀ a, x ≤ ∑ i, q i * c a i) :
    x ≤ distCost c q := by
  unfold distCost
  exact le_ciInf h

omit [Nonempty I] in
/-- The minimum over the (finite, nonempty) set of deterministic algorithms is attained. -/
lemma exists_distCost_eq (c : A → I → ℝ) (q : I → ℝ) :
    ∃ a, ∑ i, q i * c a i = distCost c q := by
  obtain ⟨a₀, ha₀⟩ := Finite.exists_min (fun a => ∑ i, q i * c a i)
  exact ⟨a₀, le_antisymm (le_distCost ha₀) (distCost_le c q a₀)⟩

/-- A point mass is a probability distribution. -/
lemma single_mem_stdSimplex {ι : Type*} [Fintype ι] [DecidableEq ι] (i₀ : ι) :
    (Pi.single i₀ 1 : ι → ℝ) ∈ stdSimplex ℝ ι := by
  refine ⟨fun x => ?_, by simp⟩
  by_cases h : x = i₀ <;> simp [Pi.single_apply, h]

lemma stdSimplex_nonempty {ι : Type*} [Fintype ι] [Nonempty ι] :
    (stdSimplex ℝ ι).Nonempty := by
  classical
  exact ⟨Pi.single (Classical.arbitrary ι) 1, single_mem_stdSimplex _⟩

/-- Global bounds on a finite cost matrix. -/
lemma exists_bounds (c : A → I → ℝ) : ∃ m M : ℝ, ∀ a i, m ≤ c a i ∧ c a i ≤ M := by
  obtain ⟨z, hz⟩ := Finite.exists_min (fun z : A × I => c z.1 z.2)
  obtain ⟨w, hw⟩ := Finite.exists_max (fun z : A × I => c z.1 z.2)
  exact ⟨c z.1 z.2, c w.1 w.2, fun a i => ⟨hz (a, i), hw (a, i)⟩⟩

/-! ### Weak duality (the "easy" direction of Yao's principle) -/

omit [Nonempty A] [Nonempty I] in
/-- For any randomized algorithm `p` and any input distribution `q`, the distributional
complexity of `q` is at most the worst-case expected cost of `p`.  This is the direction of
Yao's principle used for proving randomized lower bounds. -/
theorem distCost_le_randCost {c : A → I → ℝ} {p : A → ℝ} {q : I → ℝ}
    (hp : p ∈ stdSimplex ℝ A) (hq : q ∈ stdSimplex ℝ I) :
    distCost c q ≤ randCost c p := by
  have key : ∑ a, p a * (∑ i, q i * c a i) = ∑ i, q i * (∑ a, p a * c a i) := by
    have e1 : ∀ a : A, p a * (∑ i, q i * c a i) = ∑ i, p a * q i * c a i := by
      intro a; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
    have e2 : ∀ i : I, q i * (∑ a, p a * c a i) = ∑ a, p a * q i * c a i := by
      intro i; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun a _ => by ring
    rw [Finset.sum_congr rfl fun a _ => e1 a, Finset.sum_congr rfl fun i _ => e2 i]
    exact Finset.sum_comm
  have h1 : distCost c q = ∑ a, p a * distCost c q := by
    rw [← Finset.sum_mul, hp.2, one_mul]
  have h2 : ∑ a, p a * distCost c q ≤ ∑ a, p a * (∑ i, q i * c a i) :=
    Finset.sum_le_sum fun a _ => by
      exact mul_le_mul_of_nonneg_left (distCost_le c q a) (hp.1 a)
  have h3 : ∑ i, q i * (∑ a, p a * c a i) ≤ ∑ i, q i * randCost c p :=
    Finset.sum_le_sum fun i _ => by
      exact mul_le_mul_of_nonneg_left (le_randCost c p i) (hq.1 i)
  have h4 : ∑ i, q i * randCost c p = randCost c p := by
    rw [← Finset.sum_mul, hq.2, one_mul]
  calc distCost c q = ∑ a, p a * distCost c q := h1
    _ ≤ ∑ a, p a * (∑ i, q i * c a i) := h2
    _ = ∑ i, q i * (∑ a, p a * c a i) := key
    _ ≤ ∑ i, q i * randCost c p := h3
    _ = randCost c p := h4

/-! ### The separation argument (the "hard" direction) -/

/-- The linear map sending a distribution over algorithms to its vector of expected costs. -/
noncomputable def expMap (c : A → I → ℝ) : (A → ℝ) →ₗ[ℝ] (I → ℝ) where
  toFun p := fun i => ∑ a, p a * c a i
  map_add' p p' := by
    funext i; simp [add_mul, Finset.sum_add_distrib]
  map_smul' r p := by
    funext i; simp [Finset.mul_sum, mul_assoc]

omit [Fintype I] [Nonempty A] [Nonempty I] in
lemma continuous_expMap (c : A → I → ℝ) : Continuous (expMap c) :=
  continuous_pi fun _ => continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const

omit [Fintype A] [Nonempty A] [Nonempty I] in
/-- Any continuous linear functional on `I → ℝ` is given by its values on the coordinate
vectors. -/
lemma clm_apply_eq_sum [DecidableEq I] (f : (I → ℝ) →L[ℝ] ℝ) (y : I → ℝ) :
    f y = ∑ i, y i * f (Pi.single i 1) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : Pi.single i (y i) = (y i) • (Pi.single i (1 : ℝ) : I → ℝ) := by
    funext j; by_cases h : j = i <;> simp [Pi.single_apply, h]
  rw [h, map_smul]
  simp

omit [Nonempty I] in
/-- **Hard direction of Yao's principle.**  If every input distribution admits a deterministic
algorithm of expected cost at most `v`, then there is a single randomized algorithm whose
expected cost is at most `v` on *every* input. -/
theorem exists_randomized_of_forall_dist (c : A → I → ℝ) (v : ℝ)
    (hv : ∀ q ∈ stdSimplex ℝ I, ∃ a, ∑ i, q i * c a i ≤ v) :
    ∃ p ∈ stdSimplex ℝ A, ∀ i, ∑ a, p a * c a i ≤ v := by
  classical
  by_contra hcon
  push_neg at hcon
  -- the set of achievable expected-cost vectors
  set K : Set (I → ℝ) := (expMap c) '' (stdSimplex ℝ A) with hK
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ A).linear_image (expMap c)
  have hKcomp : IsCompact K := (isCompact_stdSimplex A).image (continuous_expMap c)
  -- the "good" region
  set T : Set (I → ℝ) := {y | ∀ i, y i ≤ v} with hT
  have hTconv : Convex ℝ T := by
    intro y hy y' hy' s t hs ht hst i
    have h1 : y i ≤ v := hy i
    have h2 : y' i ≤ v := hy' i
    have hsm : (s • y + t • y') i = s * y i + t * y' i := rfl
    rw [hsm]
    have k1 : s * y i ≤ s * v := mul_le_mul_of_nonneg_left h1 hs
    have k2 : t * y' i ≤ t * v := mul_le_mul_of_nonneg_left h2 ht
    have : s * v + t * v = v := by rw [← add_mul, hst, one_mul]
    linarith
  have hTclosed : IsClosed T := by
    have : T = ⋂ i : I, {y : I → ℝ | y i ≤ v} := by
      ext y; simp [hT, Set.mem_iInter]
    rw [this]
    exact isClosed_iInter fun i => isClosed_le (continuous_apply i) continuous_const
  have hdisj : Disjoint K T := by
    rw [Set.disjoint_left]
    rintro y ⟨p, hp, rfl⟩ hyT
    obtain ⟨i, hi⟩ := hcon p hp
    exact absurd (hyT i) (not_le.mpr hi)
  obtain ⟨f, u, w, hfK, huw, hfT⟩ :=
    geometric_hahn_banach_compact_closed hKconv hKcomp hTconv hTclosed hdisj
  -- the coefficients of `-f`
  set q : I → ℝ := fun i => -f (Pi.single i 1) with hq
  have hfy : ∀ y : I → ℝ, f y = -∑ i, y i * q i := by
    intro y
    rw [clm_apply_eq_sum f y, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp [hq]
  -- the constant vector `v`
  have hcv : (fun _ : I => v) ∈ T := fun _ => le_refl v
  have hfcv : w < f (fun _ : I => v) := hfT _ hcv
  -- the coefficients are nonnegative
  have hqnonneg : ∀ i, 0 ≤ q i := by
    intro i
    by_contra hneg
    push_neg at hneg
    set lam : ℝ := (f (fun _ : I => v) - w + 1) / (-q i) with hlam
    have hqpos : 0 < -q i := by linarith
    have hlamnonneg : 0 ≤ lam := by
      apply div_nonneg _ (le_of_lt hqpos); linarith
    set y : I → ℝ := (fun _ : I => v) - lam • (Pi.single i 1 : I → ℝ) with hy
    have hyT : y ∈ T := by
      intro j
      by_cases h : j = i
      · subst h
        have : y j = v - lam := by simp [hy]
        rw [this]; linarith
      · have : y j = v := by simp [hy, h]
        rw [this]
    have h1 : f y = f (fun _ : I => v) - lam * f (Pi.single i 1) := by
      rw [hy, map_sub, map_smul, smul_eq_mul]
    have h2 : f (Pi.single i (1 : ℝ)) = -q i := by simp [hq]
    have h3 : lam * (-q i) = f (fun _ : I => v) - w + 1 := by
      rw [hlam, div_mul_cancel₀ _ (ne_of_gt hqpos)]
    have := hfT y hyT
    rw [h1, h2] at this
    nlinarith
  -- for every distribution over algorithms, the separating functional gives a strict inequality
  have hmain : ∀ p ∈ stdSimplex ℝ A, v * (∑ i, q i) < ∑ i, (∑ a, p a * c a i) * q i := by
    intro p hp
    have h1 : f ((expMap c) p) < u := hfK _ ⟨p, hp, rfl⟩
    have h2 : (expMap c) p = fun i => ∑ a, p a * c a i := rfl
    rw [h2, hfy] at h1
    have h3 : w < -∑ i, v * q i := by
      have := hfcv
      rw [hfy] at this
      exact this
    have h4 : ∑ i, v * q i = v * ∑ i, q i := by rw [Finset.mul_sum]
    rw [h4] at h3
    linarith
  -- total mass is positive
  have hQpos : 0 < ∑ i, q i := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun i _ => hqnonneg i) with h | h
    · exact h
    · exfalso
      have hall : ∀ i ∈ Finset.univ, q i = 0 :=
        (Finset.sum_eq_zero_iff_of_nonneg fun i _ => hqnonneg i).mp h.symm
      obtain ⟨p, hp⟩ := (stdSimplex_nonempty : (stdSimplex ℝ A).Nonempty)
      have := hmain p hp
      rw [Finset.sum_congr rfl (fun i hi => by rw [hall i hi]; ring : ∀ i ∈ Finset.univ,
        (∑ a, p a * c a i) * q i = 0)] at this
      rw [← h] at this
      simp at this
  -- normalize to an input distribution
  set Q : ℝ := ∑ i, q i with hQ
  set qhat : I → ℝ := fun i => q i / Q with hqhat
  have hqhatmem : qhat ∈ stdSimplex ℝ I := by
    refine ⟨fun i => div_nonneg (hqnonneg i) (le_of_lt hQpos), ?_⟩
    rw [hqhat, ← Finset.sum_div, ← hQ, div_self (ne_of_gt hQpos)]
  obtain ⟨a, ha⟩ := hv qhat hqhatmem
  -- but the point mass at `a` contradicts the strict inequality
  have hpa : (Pi.single a 1 : A → ℝ) ∈ stdSimplex ℝ A := single_mem_stdSimplex a
  have h5 := hmain _ hpa
  have h6 : ∀ i, ∑ a', (Pi.single a (1 : ℝ) : A → ℝ) a' * c a' i = c a i := by
    intro i; simp [Pi.single_apply, Finset.sum_ite_eq']
  rw [Finset.sum_congr rfl (fun i _ => by rw [h6 i] : ∀ i ∈ Finset.univ,
    (∑ a', (Pi.single a (1 : ℝ) : A → ℝ) a' * c a' i) * q i = c a i * q i)] at h5
  have h7 : ∑ i, qhat i * c a i = (∑ i, c a i * q i) / Q := by
    rw [Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hqhat]; ring
  rw [h7] at ha
  rw [div_le_iff₀ hQpos] at ha
  linarith

/-! ### Yao's minimax principle -/

/-- **Yao's principle.**  For a finite cost matrix `c` indexed by deterministic algorithms `A`
and inputs `I`, the optimal worst-case expected cost of a randomized algorithm equals the
optimal distributional complexity:

`min_{p ∈ Δ(A)} max_{i ∈ I} E_{a ~ p}[c a i]  =  max_{q ∈ Δ(I)} min_{a ∈ A} E_{i ~ q}[c a i]`. -/
theorem yao_principle (c : A → I → ℝ) :
    sInf (randCost c '' stdSimplex ℝ A) = sSup (distCost c '' stdSimplex ℝ I) := by
  classical
  obtain ⟨m, M, hmM⟩ := exists_bounds c
  have hAne : (stdSimplex ℝ A).Nonempty := stdSimplex_nonempty
  have hIne : (stdSimplex ℝ I).Nonempty := stdSimplex_nonempty
  have hRne : (randCost c '' stdSimplex ℝ A).Nonempty := hAne.image _
  have hDne : (distCost c '' stdSimplex ℝ I).Nonempty := hIne.image _
  -- bounds
  have hRbdd : BddBelow (randCost c '' stdSimplex ℝ A) := by
    refine ⟨m, ?_⟩
    rintro x ⟨p, hp, rfl⟩
    obtain ⟨i₀⟩ := ‹Nonempty I›
    have h1 : ∑ a, p a * m ≤ ∑ a, p a * c a i₀ :=
      Finset.sum_le_sum fun a _ => mul_le_mul_of_nonneg_left (hmM a i₀).1 (hp.1 a)
    have h2 : ∑ a, p a * m = m := by rw [← Finset.sum_mul, hp.2, one_mul]
    calc m = ∑ a, p a * m := h2.symm
      _ ≤ ∑ a, p a * c a i₀ := h1
      _ ≤ randCost c p := le_randCost c p i₀
  have hDbdd : BddAbove (distCost c '' stdSimplex ℝ I) := by
    refine ⟨M, ?_⟩
    rintro x ⟨q, hq, rfl⟩
    obtain ⟨a₀⟩ := ‹Nonempty A›
    have h1 : ∑ i, q i * c a₀ i ≤ ∑ i, q i * M :=
      Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hmM a₀ i).2 (hq.1 i)
    have h2 : ∑ i, q i * M = M := by rw [← Finset.sum_mul, hq.2, one_mul]
    calc distCost c q ≤ ∑ i, q i * c a₀ i := distCost_le c q a₀
      _ ≤ ∑ i, q i * M := h1
      _ = M := h2
  refine le_antisymm ?_ ?_
  · -- hard direction: `sInf ≤ sSup`
    set V : ℝ := sSup (distCost c '' stdSimplex ℝ I) with hV
    have hv : ∀ q ∈ stdSimplex ℝ I, ∃ a, ∑ i, q i * c a i ≤ V := by
      intro q hq
      obtain ⟨a, ha⟩ := exists_distCost_eq c q
      refine ⟨a, ?_⟩
      rw [ha]
      exact le_csSup hDbdd ⟨q, hq, rfl⟩
    obtain ⟨p, hp, hple⟩ := exists_randomized_of_forall_dist c V hv
    calc sInf (randCost c '' stdSimplex ℝ A) ≤ randCost c p := csInf_le hRbdd ⟨p, hp, rfl⟩
      _ ≤ V := randCost_le hple
  · -- easy direction: `sSup ≤ sInf`
    refine csSup_le hDne ?_
    rintro x ⟨q, hq, rfl⟩
    refine le_csInf hRne ?_
    rintro y ⟨p, hp, rfl⟩
    exact distCost_le_randCost hp hq

end CS

