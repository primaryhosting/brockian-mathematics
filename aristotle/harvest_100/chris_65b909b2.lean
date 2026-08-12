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

/-!
# The Ham–Sandwich theorem

The Ham–Sandwich theorem states that any `n` finite measures on `ℝⁿ` can be simultaneously
bisected by a single affine hyperplane.  Here a hyperplane is described by a nonzero normal
vector `v` and a level `c`, and "bisecting" a measure `μ` means that each of the two closed
half-spaces `{x | ⟪v, x⟫ ≤ c}` and `{x | c ≤ ⟪v, x⟫}` carries at least half of the total mass
of `μ`.

The general statement is recorded as `Frontier.HamSandwich n`.  The full theorem for arbitrary
`n` rests on the Borsuk–Ulam theorem, which is not available in Mathlib.  We prove here the base
case `n = 1` (`Frontier.ham_sandwich`), together with a genuinely more general statement
(`Frontier.bisect_one_measure`): a *single* finite measure on `ℝⁿ` can be bisected by a
hyperplane with any prescribed normal direction.  Both rest on the existence of a median of a
real random variable (`Frontier.exists_median`).
-/

namespace Frontier

open MeasureTheory Filter Set Topology

/-- A hyperplane with normal vector `v` and level `c` bisects the measure `μ` if each of the two
closed half-spaces it bounds carries at least half of the total mass of `μ`. -/
def Bisects {n : ℕ} (v : EuclideanSpace ℝ (Fin n)) (c : ℝ)
    (μ : Measure (EuclideanSpace ℝ (Fin n))) : Prop :=
  μ Set.univ ≤ 2 * μ {x | inner ℝ v x ≤ c} ∧ μ Set.univ ≤ 2 * μ {x | c ≤ inner ℝ v x}

/-- The Ham–Sandwich statement in dimension `n`: any `n` finite measures on `ℝⁿ` are
simultaneously bisected by some hyperplane. -/
def HamSandwich (n : ℕ) : Prop :=
  ∀ μ : Fin n → Measure (EuclideanSpace ℝ (Fin n)), (∀ i, IsFiniteMeasure (μ i)) →
    ∃ v : EuclideanSpace ℝ (Fin n), v ≠ 0 ∧ ∃ c : ℝ, ∀ i, Bisects v c (μ i)

/-- Existence of a median: for a finite measure `μ` and a measurable real-valued function `f`
there is a level `c` such that both `{f ≤ c}` and `{c ≤ f}` carry at least half of the mass. -/
theorem exists_median {α : Type*} [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    {f : α → ℝ} (hf : Measurable f) :
    ∃ c : ℝ, μ Set.univ ≤ 2 * μ {x | f x ≤ c} ∧ μ Set.univ ≤ 2 * μ {x | c ≤ f x} := by
  have hmeas : ∀ t : ℝ, MeasurableSet {x | f x ≤ t} := fun t => hf measurableSet_Iic
  have hmeas2 : ∀ t : ℝ, MeasurableSet {x | t < f x} := fun t => hf measurableSet_Ioi
  have hmono' : ∀ {s t : ℝ}, s ≤ t → μ {x | f x ≤ s} ≤ μ {x | f x ≤ t} :=
    fun hst => measure_mono fun x hx => le_trans hx hst
  have hrecip : ∀ a b : ℕ, a ≤ b → (1:ℝ)/((b:ℝ)+1) ≤ 1/((a:ℝ)+1) := by
    intro a b hab
    have hab' : (a:ℝ) ≤ (b:ℝ) := by exact_mod_cast hab
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  rcases eq_or_ne (μ Set.univ) 0 with h0 | h0
  · exact ⟨0, by simp [h0], by simp [h0]⟩
  have hhalf : μ Set.univ / 2 < μ Set.univ := ENNReal.half_lt_self h0 (measure_ne_top μ _)
  have htwo : 2 * (μ Set.univ / 2) = μ Set.univ := by
    rw [ENNReal.mul_div_cancel'] <;> simp
  set S : Set ℝ := {t : ℝ | μ Set.univ ≤ 2 * μ {x | f x ≤ t}} with hSdef
  -- `S` is nonempty, since `μ {f ≤ k} → μ univ` as `k → ∞`.
  have hup : Tendsto (fun k : ℕ => μ {x | f x ≤ (k:ℝ)}) atTop (𝓝 (μ Set.univ)) := by
    have hmono : Monotone (fun k : ℕ => {x | f x ≤ (k:ℝ)}) := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      exact hx.trans (by exact_mod_cast Nat.cast_le.2 hab)
    have h := tendsto_measure_iUnion_atTop (μ := μ) hmono
    have he : (⋃ k : ℕ, {x | f x ≤ (k:ℝ)}) = Set.univ := by
      ext x; simpa using exists_nat_ge (f x)
    rw [he] at h
    exact h
  have hSne : S.Nonempty := by
    obtain ⟨k, hk⟩ := (hup.eventually_const_lt hhalf).exists
    refine ⟨(k:ℝ), ?_⟩
    calc μ Set.univ = 2 * (μ Set.univ / 2) := htwo.symm
      _ ≤ 2 * μ {x | f x ≤ (k:ℝ)} := by gcongr
  -- `S` is bounded below, since `μ {f ≤ -k} → 0` as `k → ∞`.
  have hdown : Tendsto (fun k : ℕ => μ {x | f x ≤ -(k:ℝ)}) atTop (𝓝 0) := by
    have hanti : Antitone (fun k : ℕ => {x | f x ≤ -(k:ℝ)}) := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      refine hx.trans ?_
      simp only [neg_le_neg_iff]
      exact_mod_cast Nat.cast_le.2 hab
    have h := tendsto_measure_iInter_atTop (μ := μ)
      (fun k => (hmeas _).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    have he : (⋂ k : ℕ, {x | f x ≤ -(k:ℝ)}) = (∅ : Set α) := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_forall]
      obtain ⟨k, hk⟩ := exists_nat_ge (-f x)
      exact ⟨k + 1, by push_cast; nlinarith [Nat.cast_nonneg (α := ℝ) k]⟩
    rw [he] at h
    simpa using h
  have hbdd : BddBelow S := by
    obtain ⟨k, hk⟩ := (hdown.eventually_lt_const (ENNReal.half_pos h0)).exists
    refine ⟨-(k:ℝ), fun t ht => ?_⟩
    by_contra hlt
    push_neg at hlt
    have h1 : 2 * μ {x | f x ≤ t} ≤ 2 * μ {x | f x ≤ -(k:ℝ)} := by gcongr
    have h2 : 2 * μ {x | f x ≤ -(k:ℝ)} < μ Set.univ := ENNReal.mul_lt_of_lt_div' hk
    exact absurd (ht.trans_lt (h1.trans_lt h2)) (lt_irrefl _)
  -- The median is the infimum of `S`.
  set c := sInf S with hc
  refine ⟨c, ?_, ?_⟩
  · have key : ∀ k : ℕ, μ Set.univ ≤ 2 * μ {x | f x ≤ c + 1/((k:ℝ)+1)} := by
      intro k
      obtain ⟨a, haS, ha⟩ := Real.lt_sInf_add_pos hSne (ε := 1/((k:ℝ)+1)) (by positivity)
      rw [hSdef] at haS
      exact haS.trans (by gcongr)
    have hanti : Antitone (fun k : ℕ => {x | f x ≤ c + 1/((k:ℝ)+1)}) := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have := hrecip a b hab
      linarith
    have he : (⋂ k : ℕ, {x | f x ≤ c + 1/((k:ℝ)+1)}) = {x | f x ≤ c} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        exact (h k).trans (by linarith)
      · intro h k
        have : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
        linarith
    have hA := tendsto_measure_iInter_atTop (μ := μ)
      (fun k : ℕ => (hmeas (c + 1/((k:ℝ)+1))).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    rw [he] at hA
    exact ge_of_tendsto (ENNReal.Tendsto.const_mul (a := 2) hA (Or.inr (by norm_num)))
      (Eventually.of_forall key)
  · have key : ∀ k : ℕ, μ Set.univ ≤ 2 * μ {x | c - 1/((k:ℝ)+1) < f x} := by
      intro k
      set t := c - 1/((k:ℝ)+1) with ht
      have hpos : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
      have htc : t < c := by rw [ht]; linarith
      have htS : t ∉ S := fun h => absurd (csInf_le hbdd h) (not_le.2 htc)
      rw [hSdef] at htS
      simp only [Set.mem_setOf_eq, not_le] at htS
      have hcompl : {x | f x ≤ t}ᶜ = {x | t < f x} := by ext x; simp [not_le]
      have hsum : μ {x | f x ≤ t} + μ {x | t < f x} = μ Set.univ := by
        rw [← hcompl]
        exact measure_add_measure_compl (hmeas t)
      have hab : μ {x | f x ≤ t} < μ {x | t < f x} := by
        have h2 : μ {x | f x ≤ t} + μ {x | f x ≤ t} < μ {x | f x ≤ t} + μ {x | t < f x} := by
          rw [hsum, ← two_mul]; exact htS
        exact (ENNReal.add_lt_add_iff_left (measure_ne_top μ _)).1 h2
      calc μ Set.univ = μ {x | f x ≤ t} + μ {x | t < f x} := hsum.symm
        _ ≤ μ {x | t < f x} + μ {x | t < f x} := by gcongr
        _ = 2 * μ {x | t < f x} := by rw [two_mul]
    have hanti : Antitone (fun k : ℕ => {x | c - 1/((k:ℝ)+1) < f x}) := by
      intro a b hab x hx
      simp only [Set.mem_setOf_eq] at hx ⊢
      have := hrecip a b hab
      linarith
    have he : (⋂ k : ℕ, {x | c - 1/((k:ℝ)+1) < f x}) = {x | c ≤ f x} := by
      ext x
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      constructor
      · intro h
        refine le_of_forall_pos_le_add fun ε hε => ?_
        obtain ⟨k, hk⟩ := exists_nat_one_div_lt hε
        have := h k
        linarith
      · intro h k
        have : (0:ℝ) < 1/((k:ℝ)+1) := by positivity
        linarith
    have hA := tendsto_measure_iInter_atTop (μ := μ)
      (fun k : ℕ => (hmeas2 (c - 1/((k:ℝ)+1))).nullMeasurableSet) hanti ⟨0, measure_ne_top μ _⟩
    rw [he] at hA
    exact ge_of_tendsto (ENNReal.Tendsto.const_mul (a := 2) hA (Or.inr (by norm_num)))
      (Eventually.of_forall key)

/-- A single finite measure on `ℝⁿ` can be bisected by a hyperplane with any prescribed nonzero
normal vector. -/
theorem bisect_one_measure {n : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin n))) [IsFiniteMeasure μ]
    (v : EuclideanSpace ℝ (Fin n)) : ∃ c : ℝ, Bisects v c μ := by
  have hf : Measurable fun x : EuclideanSpace ℝ (Fin n) => inner ℝ v x := by fun_prop
  obtain ⟨c, h1, h2⟩ := exists_median μ hf
  exact ⟨c, h1, h2⟩

/-- The Ham–Sandwich theorem in dimension one: a finite measure on `ℝ¹` is bisected by some
hyperplane (i.e. by some point). -/
theorem ham_sandwich : HamSandwich 1 := by
  intro μ hμ
  refine ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), ?_, ?_⟩
  · intro h
    have := congrFun (congrArg (fun y : EuclideanSpace ℝ (Fin 1) => (y : Fin 1 → ℝ)) h) 0
    simp [EuclideanSpace.single_apply] at this
  · haveI := hμ 0
    obtain ⟨c, hc⟩ := bisect_one_measure (μ 0) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
    exact ⟨c, fun i => by simpa [Subsingleton.elim i 0] using hc⟩

end Frontier

