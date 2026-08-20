/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

open MeasureTheory Set Filter Topology

namespace Frontier

/-!
## Bisecting a single finite measure

The Ham–Sandwich theorem states that `n` finite measures on `ℝⁿ` can be simultaneously
bisected by a single affine hyperplane `{x | ⟪v, x⟫ = c}` (`v` a unit vector), where
"bisected" is understood in the weak sense that each of the two closed half-spaces
carries at least half of the total mass.  (The weak form is the correct one for general
measures: a Dirac mass sitting on the hyperplane cannot be split exactly.)

Mathlib does not contain the Ham–Sandwich theorem, nor the Borsuk–Ulam theorem on which
the general proof rests, so everything below is developed from scratch.  We prove the
base case, `k = 1` measure in `ℝⁿ`, in the form of a median (`Frontier.ham_sandwich`),
together with a genuinely `n`-measure instance for point masses
(`Frontier.ham_sandwich_dirac`).
-/

/-- **Existence of a median.**  For a finite measure `μ` and a measurable real valued
function `f`, there is a threshold `c` such that both `{f ≤ c}` and `{c ≤ f}` carry at
least half of the total mass. -/
theorem exists_median {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (f : α → ℝ) (hf : Measurable f) :
    ∃ c : ℝ, μ univ / 2 ≤ μ {x | f x ≤ c} ∧ μ univ / 2 ≤ μ {x | c ≤ f x} := by
  have hmeas : ∀ t : ℝ, MeasurableSet {x | f x ≤ t} := fun t => hf measurableSet_Iic
  have hsub : ∀ s t : ℝ, s ≤ t → {x | f x ≤ s} ⊆ {x | f x ≤ t} :=
    fun s t hst => Set.setOf_subset_setOf.2 fun x hx => hx.trans hst
  have hmono : Monotone (fun t : ℝ => μ {x | f x ≤ t}) := fun s t hst => measure_mono (hsub s t hst)
  rcases eq_or_ne (μ univ) 0 with h0 | h0
  · exact ⟨0, by simp [h0], by simp [h0]⟩
  set m := μ univ with hm
  have hmtop : m ≠ ⊤ := measure_ne_top μ univ
  have hhalf : m / 2 < m := ENNReal.half_lt_self h0 hmtop
  have hhpos : 0 < m / 2 := ENNReal.half_pos h0
  set S : Set ℝ := {t : ℝ | m / 2 ≤ μ {x | f x ≤ t}} with hS
  -- `S` is nonempty: the measure of `{f ≤ k}` tends to the total mass as `k → ∞`.
  have hunion : (⋃ k : ℕ, {x | f x ≤ (k : ℝ)}) = univ := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨k, hk⟩ := exists_nat_ge (f x)
    exact mem_iUnion.2 ⟨k, hk⟩
  have htend1 : Tendsto (fun k : ℕ => μ {x | f x ≤ (k : ℝ)}) atTop (𝓝 m) := by
    have h := tendsto_measure_iUnion_atTop (μ := μ) (s := fun k : ℕ => {x | f x ≤ (k : ℝ)})
      (fun a b hab => hsub _ _ (by exact_mod_cast hab))
    rw [hunion] at h
    exact h
  obtain ⟨k1, hk1⟩ := (htend1.eventually_const_lt hhalf).exists
  have hSne : S.Nonempty := ⟨(k1 : ℝ), le_of_lt hk1⟩
  -- `S` is bounded below: the measure of `{f ≤ -k}` tends to `0` as `k → ∞`.
  have hinter : (⋂ k : ℕ, {x | f x ≤ -(k : ℝ)}) = ∅ := by
    apply eq_empty_of_forall_notMem
    intro x hx
    obtain ⟨k, hk⟩ := exists_nat_gt (-(f x))
    have h2 : f x ≤ -(k : ℝ) := mem_iInter.1 hx k
    linarith
  have htend2 : Tendsto (fun k : ℕ => μ {x | f x ≤ -(k : ℝ)}) atTop (𝓝 0) := by
    have h := tendsto_measure_iInter_atTop (μ := μ) (s := fun k : ℕ => {x | f x ≤ -(k : ℝ)})
      (fun k => (hmeas _).nullMeasurableSet)
      (fun a b hab => hsub _ _ (by simp only [neg_le_neg_iff]; exact_mod_cast hab))
      ⟨0, measure_ne_top _ _⟩
    rw [hinter, measure_empty] at h
    exact h
  obtain ⟨k2, hk2⟩ := (htend2.eventually_lt_const hhpos).exists
  have hbdd : BddBelow S := by
    refine ⟨-(k2 : ℝ), fun t ht => ?_⟩
    by_contra hlt
    push_neg at hlt
    exact absurd (le_trans ht (hmono hlt.le)) (not_le.2 hk2)
  set c := sInf S with hc
  have hpos : ∀ k : ℕ, (0:ℝ) < 1 / (k + 1 : ℝ) := fun k => by positivity
  have hanti : ∀ a b : ℕ, a ≤ b → (1:ℝ) / (b + 1) ≤ 1 / (a + 1) := by
    intro a b hab
    apply one_div_le_one_div_of_le
    · positivity
    · have : (a:ℝ) ≤ b := by exact_mod_cast hab
      linarith
  refine ⟨c, ?_, ?_⟩
  · -- right-continuity of `t ↦ μ {f ≤ t}` at `c = sInf S`
    have key : ∀ t : ℝ, c < t → m / 2 ≤ μ {x | f x ≤ t} := by
      intro t ht
      obtain ⟨a, ha, hat⟩ := exists_lt_of_csInf_lt hSne ht
      exact le_trans ha (hmono hat.le)
    have hset : (⋂ k : ℕ, {x | f x ≤ c + 1 / (k + 1 : ℝ)}) = {x | f x ≤ c} := by
      ext x
      simp only [mem_iInter, mem_setOf_eq]
      constructor
      · intro h
        refine le_of_forall_pos_le_add ?_
        intro ε hε
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        exact le_trans (h k) (by linarith)
      · intro h k
        have := hpos k
        linarith
    have htend := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun k : ℕ => {x | f x ≤ c + 1 / (k + 1 : ℝ)})
      (fun k => (hmeas _).nullMeasurableSet)
      (fun a b hab => hsub _ _ (by have := hanti a b hab; linarith))
      ⟨0, measure_ne_top _ _⟩
    rw [hset] at htend
    refine ge_of_tendsto htend ?_
    filter_upwards with k
    exact key _ (by have := hpos k; linarith)
  · -- points strictly below `c` are not in `S`, so `{t < f}` has at least half the mass
    have key2 : ∀ t : ℝ, t < c → m / 2 ≤ μ {x | t < f x} := by
      intro t ht
      have htS : t ∉ S := fun h => absurd (csInf_le hbdd h) (not_le.2 ht)
      have hlt : μ {x | f x ≤ t} ≤ m / 2 := le_of_lt (not_le.1 htS)
      have hcompl : {x | t < f x} = {x | f x ≤ t}ᶜ := by ext x; simp [not_le]
      rw [hcompl, measure_compl (hmeas t) (measure_ne_top _ _)]
      calc m / 2 = m - m / 2 := (ENNReal.sub_half hmtop).symm
        _ ≤ m - μ {x | f x ≤ t} := tsub_le_tsub_left hlt m
    have hset : (⋂ k : ℕ, {x | c - 1 / (k + 1 : ℝ) < f x}) = {x | c ≤ f x} := by
      ext x
      simp only [mem_iInter, mem_setOf_eq]
      constructor
      · intro h
        refine le_of_forall_pos_le_add ?_
        intro ε hε
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        have := h k
        linarith
      · intro h k
        have := hpos k
        linarith
    have htend := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun k : ℕ => {x | c - 1 / (k + 1 : ℝ) < f x})
      (fun k => (measurableSet_lt measurable_const hf).nullMeasurableSet)
      (fun a b hab => Set.setOf_subset_setOf.2 (fun x hx => by
        have := hanti a b hab; linarith))
      ⟨0, measure_ne_top _ _⟩
    rw [hset] at htend
    refine ge_of_tendsto htend ?_
    filter_upwards with k
    exact key2 _ (by have := hpos k; linarith)

/-- **Ham–Sandwich theorem, base case: one finite measure in `ℝⁿ`.**

Given a single finite Borel measure on the Euclidean space `ℝⁿ` (`n ≥ 1`), there is an
affine hyperplane `{x | ⟪v, x⟫ = c}` with unit normal `v` that bisects it: each of the two
closed half-spaces `{x | ⟪v, x⟫ ≤ c}` and `{x | c ≤ ⟪v, x⟫}` carries at least half of the
total mass.  The family of measures is indexed by `Fin 1` so that the statement is
literally the `k = 1` instance of the general "`k` measures in `ℝⁿ`" formulation. -/
theorem ham_sandwich {n : ℕ} (hn : 0 < n) (μ : Fin 1 → Measure (EuclideanSpace ℝ (Fin n)))
    [∀ i, IsFiniteMeasure (μ i)] :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), ‖v‖ = 1 ∧ ∀ i : Fin 1,
      (μ i) univ / 2 ≤ (μ i) {x | inner ℝ v x ≤ c} ∧
      (μ i) univ / 2 ≤ (μ i) {x | c ≤ inner ℝ v x} := by
  set v : EuclideanSpace ℝ (Fin n) := EuclideanSpace.single ⟨0, hn⟩ (1:ℝ) with hv
  have hmf : Measurable (fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ v x : ℝ)) :=
    (continuous_const.inner continuous_id).measurable
  obtain ⟨c, h1, h2⟩ := exists_median (μ 0) _ hmf
  refine ⟨v, c, by simp [hv], ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact ⟨h1, h2⟩

/-- Any `n` points of `ℝⁿ` lie on a common affine hyperplane with unit normal vector:
the `n` linear conditions `⟪v, pᵢ⟫ = c` in the `n + 1` unknowns `(v, c)` must have a
nonzero solution, and such a solution necessarily has `v ≠ 0`. -/
theorem exists_unit_hyperplane_through_points {n : ℕ} (hn : 0 < n)
    (p : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), ‖v‖ = 1 ∧ ∀ i, inner ℝ v (p i) = c := by
  classical
  set T : (EuclideanSpace ℝ (Fin n) × ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    { toFun := fun w i => (inner ℝ w.1 (p i) : ℝ) - w.2
      map_add' := by intro a b; funext i; simp [inner_add_left]; ring
      map_smul' := by intro r a; funext i; simp [real_inner_smul_left]; ring } with hT
  have hrank : Module.finrank ℝ (Fin n → ℝ) < Module.finrank ℝ (EuclideanSpace ℝ (Fin n) × ℝ) := by
    simp [Module.finrank_prod, finrank_euclideanSpace]
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (LinearMap.ker_ne_bot_of_finrank_lt (f := T) hrank)
  have hker : ∀ i, (inner ℝ w.1 (p i) : ℝ) = w.2 := by
    intro i
    have h1 : T w = 0 := hw
    have h2 := congrFun h1 i
    simp only [hT, LinearMap.coe_mk, AddHom.coe_mk, Pi.zero_apply, sub_eq_zero] at h2
    exact h2
  have hv0 : w.1 ≠ 0 := by
    intro h
    apply hw0
    have hc : w.2 = 0 := by
      have h3 := hker ⟨0, hn⟩
      rw [h] at h3
      simpa using h3.symm
    exact Prod.ext h hc
  refine ⟨‖w.1‖⁻¹ • w.1, ‖w.1‖⁻¹ * w.2, ?_, ?_⟩
  · rw [norm_smul]
    simp [norm_ne_zero_iff.2 hv0]
  · intro i
    rw [real_inner_smul_left, hker i]

/-- **Ham–Sandwich theorem for `n` point masses in `ℝⁿ`.**

For any `n` Dirac measures on `ℝⁿ` (`n ≥ 1`) there is a single affine hyperplane with unit
normal that simultaneously bisects all of them: each of the two closed half-spaces carries
at least half of the mass of each measure.  Here the hyperplane is chosen to pass through
all `n` points, so that both closed half-spaces carry the full mass. -/
theorem ham_sandwich_dirac {n : ℕ} (hn : 0 < n) (p : Fin n → EuclideanSpace ℝ (Fin n)) :
    ∃ (v : EuclideanSpace ℝ (Fin n)) (c : ℝ), ‖v‖ = 1 ∧ ∀ i : Fin n,
      (Measure.dirac (p i)) univ / 2 ≤ (Measure.dirac (p i)) {x | inner ℝ v x ≤ c} ∧
      (Measure.dirac (p i)) univ / 2 ≤ (Measure.dirac (p i)) {x | c ≤ inner ℝ v x} := by
  obtain ⟨v, c, hv, hp⟩ := exists_unit_hyperplane_through_points hn p
  have hcont : Continuous (fun x : EuclideanSpace ℝ (Fin n) => (inner ℝ v x : ℝ)) :=
    continuous_const.inner continuous_id
  have hm1 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | inner ℝ v x ≤ c} :=
    measurableSet_le hcont.measurable measurable_const
  have hm2 : MeasurableSet {x : EuclideanSpace ℝ (Fin n) | c ≤ inner ℝ v x} :=
    measurableSet_le measurable_const hcont.measurable
  refine ⟨v, c, hv, fun i => ⟨?_, ?_⟩⟩
  · rw [Measure.dirac_apply' _ hm1, Measure.dirac_apply' _ MeasurableSet.univ]
    simp [Set.indicator_of_mem, hp i]
  · rw [Measure.dirac_apply' _ hm2, Measure.dirac_apply' _ MeasurableSet.univ]
    simp [Set.indicator_of_mem, hp i]

end Frontier

