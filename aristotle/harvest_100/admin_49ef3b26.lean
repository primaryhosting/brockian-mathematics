import Mathlib

/-!
# Yao Principle
Category: Frontier Cs
Target: CS.yao_principle
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

set_option grind.warning false

namespace CS

section Yao

variable {A I : Type*} [Fintype A] [Fintype I]

/-- The expected cost of the randomized algorithm given by the distribution `p` over
deterministic algorithms, run on the input `i`. -/
def expectedCost (c : A → I → ℝ) (p : A → ℝ) (i : I) : ℝ := ∑ a, p a * c a i

/-- The expected cost of the deterministic algorithm `a` on a random input drawn from the
input distribution `q`. -/
def expectedCostOn (c : A → I → ℝ) (q : I → ℝ) (a : A) : ℝ := ∑ i, q i * c a i

/-- The randomized (worst-case) cost of the randomized algorithm `p`: the maximum over inputs
of the expected cost. -/
noncomputable def randomizedCost [Nonempty I] (c : A → I → ℝ) (p : A → ℝ) : ℝ :=
  Finset.univ.sup' Finset.univ_nonempty (expectedCost c p)

/-- The distributional cost of the input distribution `q`: the cost of the best deterministic
algorithm against `q`. -/
noncomputable def distributionalCost [Nonempty A] (c : A → I → ℝ) (q : I → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty (expectedCostOn c q)

/-- A convex combination is at least the minimum. -/
lemma inf'_le_weighted [Nonempty A] {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) (g : A → ℝ) :
    Finset.univ.inf' Finset.univ_nonempty g ≤ ∑ a, p a * g a := by
  obtain ⟨hp0, hp1⟩ := hp
  calc Finset.univ.inf' Finset.univ_nonempty g
      = ∑ a, p a * Finset.univ.inf' Finset.univ_nonempty g := by
        rw [← Finset.sum_mul, hp1, one_mul]
    _ ≤ ∑ a, p a * g a :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (Finset.inf'_le g (Finset.mem_univ a)) (hp0 a)

/-- A convex combination is at most the maximum. -/
lemma weighted_le_sup' [Nonempty A] {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) (g : A → ℝ) :
    ∑ a, p a * g a ≤ Finset.univ.sup' Finset.univ_nonempty g := by
  obtain ⟨hp0, hp1⟩ := hp
  calc ∑ a, p a * g a
      ≤ ∑ a, p a * Finset.univ.sup' Finset.univ_nonempty g :=
        Finset.sum_le_sum fun a _ =>
          mul_le_mul_of_nonneg_left (Finset.le_sup' g (Finset.mem_univ a)) (hp0 a)
    _ = Finset.univ.sup' Finset.univ_nonempty g := by rw [← Finset.sum_mul, hp1, one_mul]

/-- **Weak duality** (the easy half of Yao's principle): the distributional cost of any input
distribution is a lower bound for the randomized cost of any randomized algorithm. -/
theorem distributionalCost_le_randomizedCost [Nonempty A] [Nonempty I] (c : A → I → ℝ)
    {p : A → ℝ} (hp : p ∈ stdSimplex ℝ A) {q : I → ℝ} (hq : q ∈ stdSimplex ℝ I) :
    distributionalCost c q ≤ randomizedCost c p := by
  have h1 : distributionalCost c q ≤ ∑ a, p a * expectedCostOn c q a :=
    inf'_le_weighted hp _
  have h2 : ∑ i, q i * expectedCost c p i ≤ randomizedCost c p :=
    weighted_le_sup' hq _
  have h3 : ∑ a, p a * expectedCostOn c q a = ∑ i, q i * expectedCost c p i := by
    simp only [expectedCost, expectedCostOn, Finset.mul_sum]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => by ring
  linarith

lemma continuous_randomizedCost [Nonempty I] (c : A → I → ℝ) :
    Continuous (randomizedCost c) := by
  apply Continuous.finset_sup'_apply
  intro i _
  exact continuous_finset_sum _ fun a _ => (continuous_apply a).mul continuous_const

/-- The randomized cost attains its minimum over the simplex of randomized algorithms. -/
lemma exists_min_randomizedCost [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    ∃ p ∈ stdSimplex ℝ A, ∀ p' ∈ stdSimplex ℝ A, randomizedCost c p ≤ randomizedCost c p' := by
  obtain ⟨p, hp, hmin⟩ :=
    (isCompact_stdSimplex A).exists_isMinOn
      ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary A)⟩
      (continuous_randomizedCost c).continuousOn
  exact ⟨p, hp, fun p' hp' => isMinOn_iff.mp hmin p' hp'⟩

/-- **Strong duality** (the hard half of Yao's principle): for an optimal randomized algorithm
`p₀` there is an input distribution `q` whose distributional cost is at least the randomized
cost of `p₀`. This is proved by separating the (convex) set of achievable cost vectors from
the open convex set of vectors all of whose coordinates are below the optimal value. -/
theorem exists_hard_distribution [Nonempty A] [Nonempty I] (c : A → I → ℝ)
    {p₀ : A → ℝ} (hp₀ : p₀ ∈ stdSimplex ℝ A)
    (hmin : ∀ p ∈ stdSimplex ℝ A, randomizedCost c p₀ ≤ randomizedCost c p) :
    ∃ q ∈ stdSimplex ℝ I, randomizedCost c p₀ ≤ distributionalCost c q := by
  set v : ℝ := randomizedCost c p₀ with hv
  obtain ⟨L, hLapp⟩ : ∃ L : (A → ℝ) →ₗ[ℝ] (I → ℝ), ∀ p i, L p i = ∑ a, p a * c a i :=
    ⟨{ toFun := fun p i => ∑ a, p a * c a i
       map_add' := by
         intro x y
         funext i
         simp [add_mul, Finset.sum_add_distrib]
       map_smul' := by
         intro r x
         funext i
         simp [Finset.mul_sum, mul_assoc] }, fun _ _ => rfl⟩
  set K : Set (I → ℝ) := L '' stdSimplex ℝ A with hK
  have hKconv : Convex ℝ K := (convex_stdSimplex ℝ A).linear_image L
  set T : Set (I → ℝ) := {z | ∀ i, z i < v} with hT
  have hTopen : IsOpen T := by
    have hTeq : T = ⋂ i, {z : I → ℝ | z i < v} := by ext z; simp [hT]
    rw [hTeq]
    exact isOpen_iInter_of_finite fun i =>
      isOpen_lt (continuous_apply i) continuous_const
  have hTconv : Convex ℝ T := by
    intro x hx y hy a b ha hb hab
    intro i
    have hx' : x i < v := hx i
    have hy' : y i < v := hy i
    have : a • x i + b • y i < v := by
      simp only [smul_eq_mul]
      nlinarith
    simpa using this
  have hdisj : Disjoint T K := by
    rw [Set.disjoint_left]
    intro z hz hzK
    obtain ⟨p, hp, hpz⟩ := hzK
    obtain ⟨i, -, hi⟩ :=
      Finset.exists_mem_eq_sup' (Finset.univ_nonempty (α := I)) (expectedCost c p)
    have h1 : v ≤ expectedCost c p i := by
      have := hmin p hp
      rw [randomizedCost, hi] at this
      exact this
    have h2 : z i < v := hz i
    rw [← hpz, hLapp] at h2
    exact absurd h1 (not_le.mpr h2)
  obtain ⟨f, u, hfT, hfK⟩ := geometric_hahn_banach_open hTconv hTopen hKconv hdisj
  set q : I → ℝ := fun i => f (Pi.single i 1) with hqdef
  have hfy : ∀ y : I → ℝ, f y = ∑ i, y i * q i := by
    intro y
    conv_lhs => rw [← Finset.univ_sum_single y]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hsing : (Pi.single i (y i) : I → ℝ) = y i • Pi.single i (1 : ℝ) := by
      funext j
      by_cases h : j = i <;> simp [Pi.single_apply, h]
    rw [hsing, map_smul, smul_eq_mul, hqdef]
  set S : ℝ := ∑ i, q i with hSdef
  -- the separating functional has nonnegative coefficients
  have hq0 : ∀ i, 0 ≤ q i := by
    intro i
    by_contra hneg
    push_neg at hneg
    set z₀ : I → ℝ := fun _ => v - 1 with hz₀
    set t : ℝ := (|f z₀| + |u| + 1) / (-q i) with htdef
    have hqi : 0 < -q i := by linarith
    have ht : 0 ≤ t := div_nonneg (by positivity) hqi.le
    have htmul : t * (-q i) = |f z₀| + |u| + 1 := div_mul_cancel₀ _ hqi.ne'
    have hzT : (z₀ - t • Pi.single i (1 : ℝ)) ∈ T := by
      intro j
      by_cases h : j = i
      · subst h
        simp only [hz₀, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one]
        linarith
      · simp only [hz₀, Pi.sub_apply, Pi.smul_apply, Pi.single_eq_of_ne h, smul_eq_mul,
          mul_zero, sub_zero]
        linarith
    have hlt := hfT _ hzT
    rw [map_sub, map_smul, smul_eq_mul, ← hqdef] at hlt
    have habs : |f z₀| + |u| + 1 = t * (-q i) := htmul.symm
    have h1 : f z₀ - t * q i = f z₀ + (|f z₀| + |u| + 1) := by
      rw [habs]; ring
    rw [h1] at hlt
    have h2 : -|f z₀| ≤ f z₀ := neg_abs_le _
    have h3 : u ≤ |u| := le_abs_self u
    linarith
  have hz₀T : (fun _ => v - 1 : I → ℝ) ∈ T := fun i => by
    simp only []
    linarith
  have hK₀ : L p₀ ∈ K := ⟨p₀, hp₀, rfl⟩
  have hS : 0 < S := by
    rcases lt_or_eq_of_le (Finset.sum_nonneg (fun i _ => hq0 i) : (0 : ℝ) ≤ S) with h | h
    · exact h
    · exfalso
      have hall : ∀ i, q i = 0 := by
        intro i
        have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => hq0 j)).mp h.symm i
          (Finset.mem_univ i)
        exact this
      have hf0 : ∀ y : I → ℝ, f y = 0 := by
        intro y
        rw [hfy y]
        exact Finset.sum_eq_zero fun i _ => by rw [hall i, mul_zero]
      have h1 := hfT _ hz₀T
      have h2 := hfK _ hK₀
      rw [hf0] at h1
      rw [hf0] at h2
      linarith
  -- the separating value dominates `v * S`
  have huv : v * S ≤ u := by
    by_contra hcon
    push_neg at hcon
    set ε : ℝ := (v * S - u) / (2 * S) with hεdef
    have hε : 0 < ε := div_pos (by linarith) (by linarith)
    have hmem : (fun _ => v - ε : I → ℝ) ∈ T := fun i => by
      simp only []
      linarith
    have hlt := hfT _ hmem
    rw [hfy] at hlt
    have hsum : ∑ i, (v - ε) * q i = (v - ε) * S := by
      rw [← Finset.mul_sum]
    rw [hsum] at hlt
    have hεS : ε * S = (v * S - u) / 2 := by
      rw [hεdef]
      field_simp
      ring
    nlinarith [hlt, hεS]
  refine ⟨fun i => q i / S, ⟨fun i => div_nonneg (hq0 i) hS.le, ?_⟩, ?_⟩
  · rw [← Finset.sum_div, ← hSdef]
    exact div_self hS.ne'
  · rw [distributionalCost]
    refine Finset.le_inf' _ _ fun a _ => ?_
    have hmemK : (fun i => c a i) ∈ K := by
      refine ⟨Pi.single a 1, single_mem_stdSimplex ℝ a, ?_⟩
      funext i
      rw [hLapp]
      simp [Pi.single_apply]
    have hub := hfK _ hmemK
    rw [hfy] at hub
    have hvS : v * S ≤ ∑ i, c a i * q i := le_trans huv hub
    have hgoal : expectedCostOn c (fun i => q i / S) a = (∑ i, c a i * q i) / S := by
      rw [expectedCostOn, Finset.sum_div]
      exact Finset.sum_congr rfl fun i _ => by field_simp; ring
    rw [hgoal, le_div_iff₀ hS]
    exact hvS

/-- **Yao's minimax principle.** For a finite nonempty set `A` of deterministic algorithms, a
finite nonempty set `I` of inputs, and a cost function `c`, there is an optimal randomized
algorithm `p` (a distribution over `A`) and a hardest input distribution `q` such that:
`p` minimizes the worst-case expected cost over all randomized algorithms, `q` maximizes the
cost of the best deterministic algorithm over all input distributions, and these two optimal
values coincide.  In other words, randomized complexity equals distributional complexity. -/
theorem yao_principle [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    ∃ p ∈ stdSimplex ℝ A, ∃ q ∈ stdSimplex ℝ I,
      IsLeast (randomizedCost c '' stdSimplex ℝ A) (randomizedCost c p) ∧
      IsGreatest (distributionalCost c '' stdSimplex ℝ I) (distributionalCost c q) ∧
      randomizedCost c p = distributionalCost c q := by
  obtain ⟨p, hp, hmin⟩ := exists_min_randomizedCost c
  obtain ⟨q, hq, hge⟩ := exists_hard_distribution c hp hmin
  have hle : distributionalCost c q ≤ randomizedCost c p :=
    distributionalCost_le_randomizedCost c hp hq
  have heq : randomizedCost c p = distributionalCost c q := le_antisymm hge hle
  refine ⟨p, hp, q, hq, ⟨⟨p, hp, rfl⟩, ?_⟩, ⟨⟨q, hq, rfl⟩, ?_⟩, heq⟩
  · rintro _ ⟨p', hp', rfl⟩
    exact hmin p' hp'
  · rintro _ ⟨q', hq', rfl⟩
    rw [← heq]
    exact distributionalCost_le_randomizedCost c hp hq'

/-- Yao's minimax principle in `sInf`/`sSup` form: the infimum over randomized algorithms of the
worst-case expected cost equals the supremum over input distributions of the cost of the best
deterministic algorithm. -/
theorem yao_principle_sInf_eq_sSup [Nonempty A] [Nonempty I] (c : A → I → ℝ) :
    sInf (randomizedCost c '' stdSimplex ℝ A) = sSup (distributionalCost c '' stdSimplex ℝ I) := by
  obtain ⟨p, -, q, -, hleast, hgreatest, heq⟩ := yao_principle c
  rw [hleast.csInf_eq, hgreatest.csSup_eq, heq]

end Yao

end CS

