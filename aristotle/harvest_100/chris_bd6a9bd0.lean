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
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace CS

/-- A probability distribution on a finite type. -/
def IsDist {α : Type*} [Fintype α] (p : α → ℝ) : Prop :=
  (∀ a, 0 ≤ p a) ∧ ∑ a, p a = 1

variable {A I : Type*} [Fintype A] [Fintype I] [DecidableEq A] [DecidableEq I]

/-- The Dirac distribution concentrated at `a`. -/
lemma isDist_single (a : A) : IsDist (Pi.single a (1 : ℝ)) := by
  constructor
  · intro b
    by_cases h : b = a <;> simp [Pi.single_apply, h]
  · simp

/-- The (worst-case) expected cost of the randomized algorithm given by the distribution `p`
over deterministic algorithms:  `max over inputs i of E_{a ~ p} [c a i]`. -/
noncomputable def randCost (c : A → I → ℝ) (p : A → ℝ) : ℝ := ⨆ i, ∑ a, p a * c a i

/-- The distributional complexity of the input distribution `q`:
`min over deterministic algorithms a of E_{i ~ q} [c a i]`. -/
noncomputable def distCost (c : A → I → ℝ) (q : I → ℝ) : ℝ := ⨅ a, ∑ i, q i * c a i

section Aux

variable {α : Type*} [Fintype α]

lemma ciInf_le_weighted [Nonempty α] {p : α → ℝ} (hp : IsDist p) (X : α → ℝ) :
    (⨅ a, X a) ≤ ∑ a, p a * X a := by
  have hb : BddBelow (Set.range X) := Finite.bddBelow_range X
  calc (⨅ a, X a) = ∑ a, p a * (⨅ a', X a') := by
        rw [← Finset.sum_mul, hp.2, one_mul]
    _ ≤ ∑ a, p a * X a := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (ciInf_le hb a) (hp.1 a)

lemma weighted_le_ciSup [Nonempty α] {p : α → ℝ} (hp : IsDist p) (X : α → ℝ) :
    ∑ a, p a * X a ≤ ⨆ a, X a := by
  have hb : BddAbove (Set.range X) := Finite.bddAbove_range X
  calc ∑ a, p a * X a ≤ ∑ a, p a * (⨆ a', X a') := by
        refine Finset.sum_le_sum fun a _ => ?_
        exact mul_le_mul_of_nonneg_left (le_ciSup hb a) (hp.1 a)
    _ = ⨆ a, X a := by rw [← Finset.sum_mul, hp.2, one_mul]

end Aux

omit [DecidableEq A] [DecidableEq I] in
/-- **Easy direction of Yao's principle**: the distributional complexity of any input
distribution is a lower bound on the cost of any randomized algorithm. -/
theorem distCost_le_randCost [Nonempty A] [Nonempty I] (c : A → I → ℝ)
    {p : A → ℝ} (hp : IsDist p) {q : I → ℝ} (hq : IsDist q) :
    distCost c q ≤ randCost c p := by
  calc distCost c q ≤ ∑ a, p a * (∑ i, q i * c a i) := ciInf_le_weighted hp _
    _ = ∑ i, q i * (∑ a, p a * c a i) := by
        simp_rw [Finset.mul_sum]
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
    _ ≤ randCost c p := weighted_le_ciSup hq _

/-- The set of achievable randomized costs. -/
def randCosts (c : A → I → ℝ) : Set ℝ := randCost c '' {p | IsDist p}

/-- The set of achievable distributional complexities. -/
def distCosts (c : A → I → ℝ) : Set ℝ := distCost c '' {q | IsDist q}

omit [Fintype I] [DecidableEq I] in
lemma randCosts_nonempty (c : A → I → ℝ) [Nonempty A] : (randCosts c).Nonempty :=
  ⟨_, ⟨Pi.single (Classical.arbitrary A) 1, isDist_single _, rfl⟩⟩

omit [Fintype A] [DecidableEq A] in
lemma distCosts_nonempty (c : A → I → ℝ) [Nonempty I] : (distCosts c).Nonempty :=
  ⟨_, ⟨Pi.single (Classical.arbitrary I) 1, isDist_single _, rfl⟩⟩

omit [DecidableEq A] in
lemma randCosts_bddBelow (c : A → I → ℝ) [Nonempty A] [Nonempty I] :
    BddBelow (randCosts c) := by
  refine ⟨distCost c (Pi.single (Classical.arbitrary I) 1), ?_⟩
  rintro _ ⟨p, hp, rfl⟩
  exact distCost_le_randCost c hp (isDist_single _)

omit [DecidableEq I] in
lemma distCosts_bddAbove (c : A → I → ℝ) [Nonempty A] [Nonempty I] :
    BddAbove (distCosts c) := by
  refine ⟨randCost c (Pi.single (Classical.arbitrary A) 1), ?_⟩
  rintro _ ⟨q, hq, rfl⟩
  exact distCost_le_randCost c (isDist_single _) hq

/-- The "upper" set of cost vectors dominated by some randomized algorithm. -/
def domSet (c : A → I → ℝ) : Set (I → ℝ) :=
  {y | ∃ p : A → ℝ, IsDist p ∧ ∀ i, ∑ a, p a * c a i ≤ y i}

omit [Fintype I] [DecidableEq A] [DecidableEq I] in
lemma convex_domSet (c : A → I → ℝ) : Convex ℝ (domSet c) := by
  rintro y ⟨p, hp, hpy⟩ z ⟨r, hr, hrz⟩ s t hs ht hst
  refine ⟨fun a => s * p a + t * r a,
    ⟨fun a => add_nonneg (mul_nonneg hs (hp.1 a)) (mul_nonneg ht (hr.1 a)), ?_⟩, ?_⟩
  · rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, hp.2, hr.2]
    simpa using hst
  · intro i
    have : ∑ a, (s * p a + t * r a) * c a i
        = s * (∑ a, p a * c a i) + t * (∑ a, r a * c a i) := by
      rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun a _ => by ring
    rw [this]
    have h1 : s * (∑ a, p a * c a i) ≤ s * y i := mul_le_mul_of_nonneg_left (hpy i) hs
    have h2 : t * (∑ a, r a * c a i) ≤ t * z i := mul_le_mul_of_nonneg_left (hrz i) ht
    simpa [Pi.add_apply, smul_eq_mul] using add_le_add h1 h2

omit [Fintype I] [DecidableEq I] in
lemma domSet_single (c : A → I → ℝ) (a : A) : (fun i => c a i) ∈ domSet c := by
  refine ⟨Pi.single a 1, isDist_single a, fun i => ?_⟩
  have h : ∑ a', (Pi.single a (1 : ℝ) : A → ℝ) a' * c a' i = c a i := by
    rw [Finset.sum_eq_single a]
    · simp
    · intro b _ hb; simp [hb]
    · intro hmem; exact absurd (Finset.mem_univ a) hmem
  exact le_of_eq h

/-- The open lower box `{y | ∀ i, y i < t}`. -/
def lowBox (I : Type*) (t : ℝ) : Set (I → ℝ) := {y | ∀ i, y i < t}

omit [DecidableEq I] in
lemma isOpen_lowBox (t : ℝ) : IsOpen (lowBox I t) := by
  have : lowBox I t = ⋂ i : I, (fun y : I → ℝ => y i) ⁻¹' (Set.Iio t) := by
    ext y; simp [lowBox]
  rw [this]
  exact isOpen_iInter_of_finite fun i => (continuous_apply i).isOpen_preimage _ isOpen_Iio

omit [Fintype I] [DecidableEq I] in
lemma convex_lowBox (t : ℝ) : Convex ℝ (lowBox I t) := by
  intro y hy z hz s r hs hr hsr i
  rcases eq_or_lt_of_le hs with h | h
  · have hr1 : r = 1 := by linarith
    simpa [← h, hr1] using hz i
  · have : s * y i + r * z i < s * t + r * t := by
      have h1 : s * y i < s * t := by nlinarith [hy i]
      have h2 : r * z i ≤ r * t := by nlinarith [hz i]
      linarith
    simpa [Pi.add_apply, smul_eq_mul, ← add_mul, hsr] using this

/-- Linear functionals on `I → ℝ` are given by coefficient vectors. -/
lemma clm_apply_eq_sum (f : (I → ℝ) →L[ℝ] ℝ) (y : I → ℝ) :
    f y = ∑ i, y i * f (Pi.single i (1 : ℝ)) := by
  conv_lhs => rw [← Finset.univ_sum_single y]
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h : (Pi.single i (y i) : I → ℝ) = y i • (Pi.single i (1 : ℝ) : I → ℝ) := by
    funext j; by_cases hj : j = i <;> simp [Pi.single_apply, hj]
  rw [h, map_smul]
  simp

/-- **Hard direction of Yao's principle** (the minimax theorem for finite games):
the optimal randomized cost is attained as a limit of distributional complexities. -/
theorem sInf_randCosts_le_sSup_distCosts [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    sInf (randCosts c) ≤ sSup (distCosts c) := by
  set t : ℝ := sInf (randCosts c) with ht
  -- separation
  have hdisj : Disjoint (lowBox I t) (domSet c) := by
    rw [Set.disjoint_left]
    rintro y hy ⟨p, hp, hpy⟩
    obtain ⟨i0, hi0⟩ := Finite.exists_max y
    have hle : randCost c p ≤ y i0 := ciSup_le fun i => le_trans (hpy i) (hi0 i)
    have hge : t ≤ randCost c p := csInf_le (randCosts_bddBelow c) ⟨p, hp, rfl⟩
    have := hy i0
    linarith
  obtain ⟨f, u, hU, hK⟩ :=
    geometric_hahn_banach_open (convex_lowBox t) (isOpen_lowBox t) (convex_domSet c) hdisj
  set q : I → ℝ := fun i => f (Pi.single i (1 : ℝ)) with hqdef
  have hf : ∀ y : I → ℝ, f y = ∑ i, y i * q i := clm_apply_eq_sum f
  -- the coefficients are nonnegative
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i0
    by_contra hneg
    push_neg at hneg
    set y0 : I → ℝ := fun _ => t - 1 with hy0
    set M : ℝ := |u - f y0| / (-q i0) with hM
    have hMpos : 0 ≤ M := by
      apply div_nonneg (abs_nonneg _)
      linarith
    set y1 : I → ℝ := y0 - M • (Pi.single i0 (1 : ℝ) : I → ℝ) with hy1
    have hy1U : y1 ∈ lowBox I t := by
      intro j
      have : (M • (Pi.single i0 (1 : ℝ) : I → ℝ)) j = if j = i0 then M else 0 := by
        by_cases hj : j = i0 <;> simp [hj]
      simp only [hy1, Pi.sub_apply, hy0, this]
      by_cases hj : j = i0
      · rw [if_pos hj]; linarith
      · rw [if_neg hj]; linarith
    have hfy1 : f y1 = f y0 - M * q i0 := by
      rw [hy1, map_sub, map_smul]
      simp [hqdef, smul_eq_mul]
    have hge : u ≤ f y1 := by
      rw [hfy1]
      have hne : q i0 ≠ 0 := ne_of_lt hneg
      have : M * (-q i0) = |u - f y0| := by
        rw [hM]; field_simp
      nlinarith [le_abs_self (u - f y0)]
    exact absurd (hU y1 hy1U) (not_lt.mpr hge)
  -- the coefficients are not all zero
  have hS : 0 < ∑ i, q i := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg fun i _ => hq0 i) with h | h
    · exact h
    · exfalso
      have hz : ∀ i, q i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hq0 i)).mp h.symm i
          (Finset.mem_univ i)
        exact this
      have hf0 : ∀ y : I → ℝ, f y = 0 := by
        intro y; rw [hf]; simp [hz]
      have h1 : (0 : ℝ) < u := by
        have := hU (fun _ => t - 1) (fun i => by simp)
        rwa [hf0] at this
      have h2 : u ≤ 0 := by
        have := hK _ (domSet_single c (Classical.arbitrary A))
        rwa [hf0] at this
      linarith
  -- `t * ∑ q ≤ u`
  have htu : t * (∑ i, q i) ≤ u := by
    refine le_of_forall_pos_le_add fun ε hε => ?_
    have hmem : (fun _ : I => t - ε / (∑ i, q i)) ∈ lowBox I t := by
      intro i
      have : 0 < ε / (∑ i, q i) := div_pos hε hS
      simp only []
      linarith
    have := hU _ hmem
    rw [hf] at this
    have hsum : ∑ i, (t - ε / (∑ i, q i)) * q i = (t - ε / (∑ i, q i)) * (∑ i, q i) := by
      rw [Finset.mul_sum]
    rw [hsum] at this
    have hne : (∑ i, q i) ≠ 0 := ne_of_gt hS
    have hexp : (t - ε / (∑ i, q i)) * (∑ i, q i) = t * (∑ i, q i) - ε := by
      field_simp
    rw [hexp] at this
    linarith
  -- each pure algorithm has cost at least `t` against the normalized `q`
  have hpure : ∀ a : A, u ≤ ∑ i, c a i * q i := by
    intro a
    have := hK _ (domSet_single c a)
    rwa [hf] at this
  set q' : I → ℝ := fun i => q i / (∑ j, q j) with hq'
  have hq'dist : IsDist q' := by
    constructor
    · intro i; exact div_nonneg (hq0 i) (le_of_lt hS)
    · rw [hq']
      rw [← Finset.sum_div]
      exact div_self (ne_of_gt hS)
  have hle : t ≤ distCost c q' := by
    refine le_ciInf fun a => ?_
    have h1 : ∑ i, q' i * c a i = (∑ i, c a i * q i) / (∑ j, q j) := by
      rw [Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by rw [hq']; ring
    rw [h1, le_div_iff₀ hS]
    calc t * (∑ j, q j) ≤ u := htu
      _ ≤ ∑ i, c a i * q i := hpure a
  exact le_trans hle (le_csSup (distCosts_bddAbove c) ⟨q', hq'dist, rfl⟩)

/-- **Yao's minimax principle.**  For a finite set `A` of deterministic algorithms, a finite
set `I` of inputs, and a cost function `c : A → I → ℝ`, the optimal worst-case cost of a
randomized algorithm (a distribution over `A`) equals the optimal distributional complexity
(the best over input distributions of the cost of the best deterministic algorithm):

`inf_{p} sup_{i} E_{a~p} c a i  =  sup_{q} inf_{a} E_{i~q} c a i`. -/
theorem yao_principle [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    sInf (randCosts c) = sSup (distCosts c) := by
  refine le_antisymm (sInf_randCosts_le_sSup_distCosts c) ?_
  refine csSup_le (distCosts_nonempty c) ?_
  rintro _ ⟨q, hq, rfl⟩
  refine le_csInf (randCosts_nonempty c) ?_
  rintro _ ⟨p, hp, rfl⟩
  exact distCost_le_randCost c hp hq

/-- Yao's minimax principle, phrased with indexed infimum/supremum over the subtypes of
probability distributions. -/
theorem yao_principle_iInf_iSup [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    (⨅ p : {p : A → ℝ // IsDist p}, randCost c (p : A → ℝ))
      = ⨆ q : {q : I → ℝ // IsDist q}, distCost c (q : I → ℝ) := by
  have h1 : (⨅ p : {p : A → ℝ // IsDist p}, randCost c (p : A → ℝ)) = sInf (randCosts c) := by
    rw [randCosts, Set.image_eq_range]
    rfl
  have h2 : (⨆ q : {q : I → ℝ // IsDist q}, distCost c (q : I → ℝ)) = sSup (distCosts c) := by
    rw [distCosts, Set.image_eq_range]
    rfl
  rw [h1, h2, yao_principle]

end CS

