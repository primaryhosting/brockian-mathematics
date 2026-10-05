import Mathlib

/-!
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
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

open MeasureTheory Set Filter ENNReal

namespace Frontier

/-- **Existence of a median.**  For a finite Borel measure `μ` on `ℝ` there is a point `c`
(a median) such that each of the two open rays cut out by `c` carries at most half of the
total mass.  This is the one-dimensional ham-sandwich bisection: the "hyperplane" in `ℝ¹`
is the single point `c`.

Note that the two-sided inequality (rather than an exact equality `μ (Iio c) = μ univ / 2`)
is the correct formulation: a measure with atoms, e.g. a Dirac mass, cannot be split exactly. -/
theorem exists_median (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ c : ℝ, μ (Iio c) ≤ μ univ / 2 ∧ μ (Ioi c) ≤ μ univ / 2 := by
  have hmtop : μ univ ≠ ⊤ := measure_ne_top μ univ
  by_cases hm0 : μ univ = 0
  · refine ⟨0, ?_, ?_⟩ <;>
      exact (measure_mono (subset_univ _)).trans (by simp [hm0])
  -- `S` is the set of points whose lower closed ray already carries at least half the mass.
  set S : Set ℝ := {t : ℝ | μ univ / 2 ≤ μ (Iic t)} with hS
  -- `S` is nonempty, by continuity of the measure from below along `Iic n ↑ univ`.
  have hSne : S.Nonempty := by
    by_contra h
    rw [not_nonempty_iff_eq_empty] at h
    have key : ∀ n : ℕ, μ (Iic (n : ℝ)) ≤ μ univ / 2 := by
      intro n
      have hn : (n : ℝ) ∉ S := by rw [h]; simp
      simp only [hS, mem_setOf_eq, not_le] at hn
      exact hn.le
    have hU : (⋃ n : ℕ, Iic (n : ℝ)) = univ := by
      ext x; simp only [mem_iUnion, mem_Iic, mem_univ, iff_true]; exact exists_nat_ge x
    have hmono : Monotone (fun n : ℕ => Iic (n : ℝ)) := fun a b hab =>
      Iic_subset_Iic.mpr (by exact_mod_cast hab)
    have heq := hmono.measure_iUnion (μ := μ)
    rw [hU] at heq
    exact absurd (heq.trans_le (iSup_le key)) (not_le.mpr (ENNReal.half_lt_self hm0 hmtop))
  -- `S` is bounded below, by continuity of the measure from above along `Iic (-n) ↓ ∅`.
  have hSbdd : BddBelow S := by
    have hI : (⋂ n : ℕ, Iic (-(n : ℝ))) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, by linarith⟩
    have hanti : Antitone (fun n : ℕ => Iic (-(n : ℝ))) := fun a b hab =>
      Iic_subset_Iic.mpr (by simp only [neg_le_neg_iff, Nat.cast_le]; exact_mod_cast hab)
    have heq := hanti.measure_iInter (μ := μ)
      (fun _ => measurableSet_Iic.nullMeasurableSet) ⟨0, measure_ne_top μ _⟩
    rw [hI, measure_empty] at heq
    obtain ⟨n, hn⟩ : ∃ n : ℕ, μ (Iic (-(n : ℝ))) < μ univ / 2 :=
      iInf_lt_iff.mp (heq ▸ ENNReal.half_pos hm0)
    refine ⟨-(n : ℝ), fun t ht => ?_⟩
    by_contra hlt
    push_neg at hlt
    have hmm : μ (Iic t) ≤ μ (Iic (-(n : ℝ))) := measure_mono (Iic_subset_Iic.mpr hlt.le)
    exact absurd (le_trans ht hmm) (not_le.mpr hn)
  set c := sInf S with hc
  refine ⟨c, ?_, ?_⟩
  · -- Everything strictly below `c` misses `S`, hence carries at most half the mass.
    have hU : (⋃ n : ℕ, Iic (c - 1 / ((n : ℝ) + 1))) = Iio c := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro h
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (sub_pos.mpr h)
        exact ⟨n, by linarith⟩
    have hmono : Monotone (fun n : ℕ => Iic (c - 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      refine Iic_subset_Iic.mpr ?_
      have : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast Nat.succ_le_succ hab]
      linarith
    have heq := hmono.measure_iUnion (μ := μ)
    rw [hU] at heq
    rw [heq]
    refine iSup_le fun n => ?_
    have hnot : (c - 1 / ((n : ℝ) + 1)) ∉ S := by
      intro hmem
      have hle := csInf_le hSbdd hmem
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      rw [← hc] at hle
      linarith
    simp only [hS, mem_setOf_eq, not_le] at hnot
    exact hnot.le
  · -- The closed lower ray at `c` carries at least half the mass, so its complement at most half.
    have hI : (⋂ n : ℕ, Iic (c + 1 / ((n : ℝ) + 1))) = Iic c := by
      ext x
      simp only [mem_iInter, mem_Iic]
      constructor
      · intro h
        refine le_of_forall_pos_le_add ?_
        intro ε hε
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt hε
        exact (h n).trans (by linarith)
      · intro h n
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have hanti : Antitone (fun n : ℕ => Iic (c + 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      refine Iic_subset_Iic.mpr ?_
      have : (1 : ℝ) / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) := by
        apply one_div_le_one_div_of_le <;> [positivity; exact_mod_cast Nat.succ_le_succ hab]
      linarith
    have heq := hanti.measure_iInter (μ := μ)
      (fun _ => measurableSet_Iic.nullMeasurableSet) ⟨0, measure_ne_top μ _⟩
    rw [hI] at heq
    have hge : μ univ / 2 ≤ μ (Iic c) := by
      rw [heq]
      refine le_iInf fun n => ?_
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨s, hsS, hs⟩ := Real.lt_sInf_add_pos hSne hpos
      have hhalf : μ univ / 2 ≤ μ (Iic s) := hsS
      exact hhalf.trans (measure_mono (Iic_subset_Iic.mpr (by rw [← hc] at hs; linarith)))
    have hcompl : μ (Ioi c) = μ univ - μ (Iic c) := by
      rw [← compl_Iic, measure_compl measurableSet_Iic (measure_ne_top μ _)]
    rw [hcompl]
    calc μ univ - μ (Iic c) ≤ μ univ - μ univ / 2 := tsub_le_tsub_left hge _
      _ = μ univ / 2 := ENNReal.sub_half hmtop

/-- **A single finite measure on a real inner product space is bisected by a hyperplane
orthogonal to any prescribed direction.**  Given `v`, there is a level `c` such that both open
half-spaces `{x | ⟪v, x⟫ < c}` and `{x | c < ⟪v, x⟫}` carry at most half of the total mass.
This is proved by pushing `μ` forward along the continuous linear functional `x ↦ ⟪v, x⟫`
and taking a median of the resulting finite measure on `ℝ`. -/
theorem exists_bisecting_hyperplane {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (μ : Measure E) [IsFiniteMeasure μ] (v : E) :
    ∃ c : ℝ, μ {x : E | inner ℝ v x < c} ≤ μ univ / 2 ∧
             μ {x : E | c < inner ℝ v x} ≤ μ univ / 2 := by
  set f : E → ℝ := fun x => inner ℝ v x with hf
  have hmeas : Measurable f := (innerSL ℝ v).continuous.measurable
  set ν : Measure ℝ := μ.map f with hν
  have hνuniv : ν univ = μ univ := by
    rw [hν, Measure.map_apply hmeas MeasurableSet.univ]; simp
  haveI : IsFiniteMeasure ν := ⟨by rw [hνuniv]; exact measure_lt_top μ univ⟩
  obtain ⟨c, h1, h2⟩ := exists_median ν
  rw [hν, Measure.map_apply hmeas measurableSet_Iio, hνuniv] at h1
  rw [hν, Measure.map_apply hmeas measurableSet_Ioi, hνuniv] at h2
  exact ⟨c, h1, h2⟩

/-- **Ham–Sandwich theorem, base case `n = 1`.**

Any family of `n = 1` finite Borel measures on `ℝ¹ = EuclideanSpace ℝ (Fin 1)` can be
simultaneously bisected by a single affine hyperplane `{x | ⟪v, x⟫ = c}` with `v ≠ 0`:
each of the two open half-spaces it determines carries at most half of the total mass of
every measure in the family.

Remarks on the formulation.
* The bisection is stated as "each open half-space has at most half the mass", which is the
  standard (and, for measures with atoms, the only correct) formulation; exact equality is
  false already for a Dirac measure.
* Only the base case `n = 1` is proved here.  The general statement for `n` measures in `ℝⁿ`
  rests on the Borsuk–Ulam theorem, which is not available in Mathlib.  For arbitrary
  dimension, `Frontier.exists_bisecting_hyperplane` above gives the corresponding statement
  for a single measure. -/
theorem ham_sandwich (μ : Fin 1 → Measure (EuclideanSpace ℝ (Fin 1)))
    [∀ i, IsFiniteMeasure (μ i)] :
    ∃ (v : EuclideanSpace ℝ (Fin 1)) (c : ℝ), v ≠ 0 ∧ ∀ i : Fin 1,
      μ i {x : EuclideanSpace ℝ (Fin 1) | inner ℝ v x < c} ≤ μ i univ / 2 ∧
      μ i {x : EuclideanSpace ℝ (Fin 1) | c < inner ℝ v x} ≤ μ i univ / 2 := by
  obtain ⟨c, h1, h2⟩ :=
    exists_bisecting_hyperplane (μ 0) (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))
  refine ⟨EuclideanSpace.single (0 : Fin 1) (1 : ℝ), c, ?_, ?_⟩
  · intro h
    have h0 := congrArg (fun y : EuclideanSpace ℝ (Fin 1) => y 0) h
    simp at h0
  · intro i
    have hi : i = 0 := Subsingleton.elim _ _
    subst hi
    exact ⟨h1, h2⟩

end Frontier

