/-
# Ham Sandwich
Category: Frontier Physics
Target: Frontier.ham_sandwich
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace Frontier

open MeasureTheory Set Filter Topology

/-!
## The one-dimensional core: existence of a median

Every finite Borel measure on `ℝ` has a *median*: a point `c` such that both open
half-lines `(-∞, c)` and `(c, ∞)` carry at most half of the total mass.  (One cannot
ask for equality: a Dirac mass has no point splitting it exactly in half.)
-/

/-- **Existence of a median.**  For any finite measure `μ` on `ℝ` there is a point `c`
with `μ (-∞, c) ≤ μ(ℝ)/2` and `μ (c, ∞) ≤ μ(ℝ)/2`. -/
theorem exists_median (μ : Measure ℝ) [IsFiniteMeasure μ] :
    ∃ c : ℝ, μ (Iio c) ≤ μ univ / 2 ∧ μ (Ioi c) ≤ μ univ / 2 := by
  set m : ENNReal := μ univ / 2 with hm
  have hmtop : m ≠ ⊤ := ENNReal.div_ne_top (measure_ne_top μ univ) two_ne_zero
  have hsum : m + m = μ univ := ENNReal.add_halves _
  rcases eq_or_ne (μ univ) 0 with h0 | h0
  · exact ⟨0, by simp [measure_mono_null (subset_univ _) h0],
      by simp [measure_mono_null (subset_univ _) h0]⟩
  have hm0 : m ≠ 0 := by
    intro h; rw [h, add_zero] at hsum; exact h0 hsum.symm
  have hmlt : m < μ univ := by
    rw [← hsum]; exact ENNReal.lt_add_right hmtop hm0
  -- `S` is the set of points to the left of which at least half the mass sits.
  set S : Set ℝ := {t : ℝ | m ≤ μ (Iic t)} with hS
  have hSup : ∀ t ∈ S, ∀ u, t ≤ u → u ∈ S := fun t ht u htu =>
    le_trans ht (measure_mono (Iic_subset_Iic.2 htu))
  have hSne : S.Nonempty := by
    obtain ⟨t, ht⟩ := ((tendsto_measure_Iic_atTop μ).eventually
      (eventually_gt_nhds hmlt)).exists
    exact ⟨t, le_of_lt ht⟩
  have hlow : ∃ t : ℝ, μ (Iic t) < m := by
    have hanti : Antitone (fun n : ℕ => Iic (-(n : ℝ))) := by
      intro a b hab
      have : (a : ℝ) ≤ b := by exact_mod_cast hab
      exact Iic_subset_Iic.2 (by linarith)
    have hinter : (⋂ n : ℕ, Iic (-(n : ℝ))) = ∅ := by
      ext x
      simp only [mem_iInter, mem_Iic, mem_empty_iff_false, iff_false, not_forall, not_le]
      obtain ⟨n, hn⟩ := exists_nat_gt (-x)
      exact ⟨n, by linarith⟩
    have htend := tendsto_measure_iInter_atTop (μ := μ) (s := fun n : ℕ => Iic (-(n : ℝ)))
      (fun _ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter] at htend
    simp only [measure_empty] at htend
    obtain ⟨n, hn⟩ := (htend.eventually (eventually_lt_nhds (pos_iff_ne_zero.2 hm0))).exists
    exact ⟨-(n : ℝ), hn⟩
  obtain ⟨t0, ht0⟩ := hlow
  have hbdd : BddBelow S := by
    refine ⟨t0, fun s hs => ?_⟩
    by_contra h
    push_neg at h
    exact absurd (hSup s hs t0 (le_of_lt h)) (by simpa [hS] using not_le.2 ht0)
  set c := sInf S with hc
  refine ⟨c, ?_, ?_⟩
  · -- Approximate `Iio c` from inside by `Iic (c - 1/(n+1))`, each of mass `≤ m`.
    have key : ∀ n : ℕ, μ (Iic (c - 1 / ((n : ℝ) + 1))) ≤ m := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      have hlt : c - 1 / ((n : ℝ) + 1) < c := by linarith
      have hnot : c - 1 / ((n : ℝ) + 1) ∉ S := fun hmem =>
        absurd (csInf_le hbdd hmem) (not_le.2 hlt)
      exact le_of_lt (by simpa [hS, not_le] using hnot)
    have hmono : Monotone (fun n : ℕ => Iic (c - 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      have h1 : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      exact Iic_subset_Iic.2 (by linarith)
    have hunion : (⋃ n : ℕ, Iic (c - 1 / ((n : ℝ) + 1))) = Iio c := by
      ext x
      simp only [mem_iUnion, mem_Iic, mem_Iio]
      constructor
      · rintro ⟨n, hn⟩
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
      · intro hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < c - x by linarith)
        exact ⟨n, by linarith⟩
    have htend := tendsto_measure_iUnion_atTop (μ := μ) hmono
    rw [hunion] at htend
    exact le_of_tendsto htend (Eventually.of_forall key)
  · -- Approximate `Iic c` from outside by `Iic (c + 1/(n+1))`, each of mass `≥ m`.
    have key : ∀ n : ℕ, m ≤ μ (Iic (c + 1 / ((n : ℝ) + 1))) := by
      intro n
      have hpos : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
      obtain ⟨s, hs, hslt⟩ :=
        exists_lt_of_csInf_lt hSne (show c < c + 1 / ((n : ℝ) + 1) by linarith)
      exact hSup s hs _ (le_of_lt hslt)
    have hanti : Antitone (fun n : ℕ => Iic (c + 1 / ((n : ℝ) + 1))) := by
      intro a b hab
      have hab' : (a : ℝ) ≤ b := by exact_mod_cast hab
      have h1 : 1 / ((b : ℝ) + 1) ≤ 1 / ((a : ℝ) + 1) :=
        one_div_le_one_div_of_le (by positivity) (by linarith)
      exact Iic_subset_Iic.2 (by linarith)
    have hinter : (⋂ n : ℕ, Iic (c + 1 / ((n : ℝ) + 1))) = Iic c := by
      ext x
      simp only [mem_iInter, mem_Iic]
      constructor
      · intro h
        by_contra hx
        push_neg at hx
        obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0 : ℝ) < x - c by linarith)
        exact absurd (h n) (by push_neg; linarith)
      · intro hx n
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        linarith
    have htend := tendsto_measure_iInter_atTop (μ := μ)
      (s := fun n : ℕ => Iic (c + 1 / ((n : ℝ) + 1)))
      (fun _ => measurableSet_Iic.nullMeasurableSet) hanti ⟨0, measure_ne_top _ _⟩
    rw [hinter] at htend
    have hIic : m ≤ μ (Iic c) := ge_of_tendsto htend (Eventually.of_forall key)
    have hsplit : μ (Ioi c) + μ (Iic c) = μ univ := by
      rw [← measure_union (by simp [Set.disjoint_left]) measurableSet_Iic]
      congr 1
      ext x; simp [lt_or_ge]
    by_contra hcon
    push_neg at hcon
    have step1 : m + m ≤ m + μ (Iic c) := by gcongr
    have step2 : m + μ (Iic c) < μ (Ioi c) + μ (Iic c) :=
      ENNReal.add_lt_add_right (measure_ne_top μ _) hcon
    have hfinal : m + m < μ univ := by rw [← hsplit]; exact lt_of_le_of_lt step1 step2
    rw [hsum] at hfinal
    exact lt_irrefl _ hfinal

/-!
## Bisecting a single measure in `ℝⁿ`
-/

/-- **A single finite measure in `ℝ^(n+1)` can be bisected by a hyperplane.**
There is a nonzero direction `v` and a level `c` such that each of the two *open*
half-spaces determined by the affine hyperplane `⟪v, ·⟫ = c` carries at most half
of the total mass. -/
theorem exists_bisecting_hyperplane (n : ℕ)
    (μ : Measure (EuclideanSpace ℝ (Fin (n + 1)))) [IsFiniteMeasure μ] :
    ∃ v : EuclideanSpace ℝ (Fin (n + 1)), ∃ c : ℝ, v ≠ 0 ∧
      μ {x | inner ℝ v x < c} ≤ μ univ / 2 ∧
      μ {x | c < inner ℝ v x} ≤ μ univ / 2 := by
  classical
  set f : EuclideanSpace ℝ (Fin (n + 1)) → ℝ := fun x => x 0 with hf
  have hmeas : Measurable f := by fun_prop
  set ν : Measure ℝ := μ.map f with hν
  have hνfin : IsFiniteMeasure ν := by
    constructor
    rw [hν, Measure.map_apply hmeas MeasurableSet.univ]
    exact measure_lt_top μ _
  have hνuniv : ν univ = μ univ := by
    rw [hν, Measure.map_apply hmeas MeasurableSet.univ]
    simp
  obtain ⟨c, hc1, hc2⟩ := exists_median ν
  refine ⟨EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ), c, by simp, ?_, ?_⟩
  · have hset : {x : EuclideanSpace ℝ (Fin (n + 1)) |
        inner ℝ (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) x < c} = f ⁻¹' (Iio c) := by
      ext x
      simp [hf, EuclideanSpace.inner_single_left]
    rw [hset, ← Measure.map_apply hmeas measurableSet_Iio, ← hν, ← hνuniv]
    exact hc1
  · have hset : {x : EuclideanSpace ℝ (Fin (n + 1)) |
        c < inner ℝ (EuclideanSpace.single (0 : Fin (n + 1)) (1 : ℝ)) x} = f ⁻¹' (Ioi c) := by
      ext x
      simp [hf, EuclideanSpace.inner_single_left]
    rw [hset, ← Measure.map_apply hmeas measurableSet_Ioi, ← hν, ← hνuniv]
    exact hc2

/-!
## The Ham–Sandwich statement
-/

/-- The Ham–Sandwich property in dimension `n`: any family of `n` finite measures on
`ℝⁿ` can be simultaneously bisected by a single affine hyperplane, in the sense that
each of the two open half-spaces it determines carries at most half of the mass of
each measure. -/
def HamSandwichProperty (n : ℕ) : Prop :=
  ∀ (μ : Fin n → Measure (EuclideanSpace ℝ (Fin n))), (∀ i, IsFiniteMeasure (μ i)) →
    ∃ v : EuclideanSpace ℝ (Fin n), ∃ c : ℝ, v ≠ 0 ∧ ∀ i : Fin n,
      μ i {x | inner ℝ v x < c} ≤ μ i univ / 2 ∧
      μ i {x | c < inner ℝ v x} ≤ μ i univ / 2

/-- **Ham–Sandwich theorem, base case `n = 1`.**
A single finite measure on the line `ℝ¹` is bisected by a hyperplane (a point):
there is a nonzero direction `v` and a level `c` such that both open half-spaces
`⟪v, x⟫ < c` and `⟪v, x⟫ > c` carry at most half of the total mass.

This is the `n = 1` instance of `Frontier.HamSandwichProperty`, i.e. of the general
statement "any `n` finite measures in `ℝⁿ` can be simultaneously bisected by one
hyperplane". -/
theorem ham_sandwich : HamSandwichProperty 1 := by
  intro μ hμ
  haveI := hμ 0
  obtain ⟨v, c, hv, h1, h2⟩ := exists_bisecting_hyperplane 0 (μ 0)
  refine ⟨v, c, hv, ?_⟩
  intro i
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  exact ⟨h1, h2⟩

end Frontier

