/-
# Uhlenbeck Bubbling
Category: Frontier Abel
Target: Frontier.uhlenbeck_bubbling
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped NNReal ENNReal

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

/-!
## Uhlenbeck bubbling: quantization of the blow-up set

For a sequence of Yang–Mills connections `A n` on a bundle over a Riemannian manifold `X`
with uniformly bounded Yang–Mills energy `E`, Uhlenbeck's compactness theorem says that,
after gauge transformations and passing to a subsequence, the connections converge smoothly
away from a finite "bubbling" set of points, and at each bubbling point at least a fixed
quantum `ε₀ > 0` of energy is lost.

The genuinely analytic inputs of that theorem are (i) Uhlenbeck's gauge fixing / removable
singularity theorem and (ii) the ε-regularity estimate, which produces the energy quantum
`ε₀`.  What is formalized here is the *bubbling / energy-quantization* mechanism itself,
stated for the sequence of energy densities: the energy densities of the connections are
encoded as a sequence of Borel measures `μ n` on `X` (`μ n = |F_{A n}|² dvol`), the uniform
energy bound is `μ n univ ≤ E`, and the bubbling set is the set of points at which, at every
scale, at least the energy quantum `ε₀` persists in the limit.

The theorem proved below is the resulting reduction: **the bubbling set is finite, and the
number of bubbles times the energy quantum is bounded by the total energy**, i.e. there are
at most `E / ε₀` bubbles.  This is exactly the counting statement used in the Uhlenbeck
compactness theorem to conclude that only finitely many bubbles occur.
-/

namespace Frontier

open MeasureTheory Metric Filter Set

/-- The **bubbling (energy concentration) set** of a sequence of energy measures `μ` at
quantum `ε₀`: the set of points `x` such that at *every* scale `r > 0` the balls `ball x r`
carry, in the limit inferior along the sequence, at least the energy quantum `ε₀`. -/
def bubbleSet {X : Type*} [MetricSpace X] [MeasurableSpace X]
    (μ : ℕ → Measure X) (ε₀ : ℝ≥0∞) : Set X :=
  {x : X | ∀ r : ℝ, 0 < r → ε₀ ≤ liminf (fun n => μ n (ball x r)) atTop}

/-- Around the points of a finite set of a metric space one can put balls of a common
positive radius that are pairwise disjoint. -/
theorem exists_pos_radius_pairwiseDisjoint_ball {X : Type*} [MetricSpace X] (S : Finset X) :
    ∃ r : ℝ, 0 < r ∧ (↑S : Set X).PairwiseDisjoint (fun x => ball x r) := by
  classical
  set P : Finset (X × X) := (S ×ˢ S).filter (fun p => p.1 ≠ p.2) with hPdef
  rcases P.eq_empty_or_nonempty with hP | hP
  · refine ⟨1, one_pos, ?_⟩
    intro x hx y hy hxy
    have hx' : x ∈ S := hx
    have hy' : y ∈ S := hy
    have hmem : (x, y) ∈ P := by simp [hPdef, hx', hy', hxy]
    rw [hP] at hmem
    exact absurd hmem (Finset.notMem_empty _)
  · refine ⟨P.inf' hP (fun p => dist p.1 p.2) / 2, ?_, ?_⟩
    · have : 0 < P.inf' hP (fun p => dist p.1 p.2) := by
        rw [Finset.lt_inf'_iff]
        intro p hp
        have hne : p.1 ≠ p.2 := by
          rw [hPdef, Finset.mem_filter] at hp
          exact hp.2
        exact dist_pos.2 hne
      linarith
    · intro x hx y hy hxy
      have hx' : x ∈ S := hx
      have hy' : y ∈ S := hy
      have hmem : (x, y) ∈ P := by simp [hPdef, hx', hy', hxy]
      have hle : P.inf' hP (fun p => dist p.1 p.2) ≤ dist x y := Finset.inf'_le _ hmem
      exact ball_disjoint_ball (by linarith)

/-- **Energy counting for bubbles.** Any finite set of bubbling points has cardinality at
most `E / ε₀`, in the multiplicative form `card * ε₀ ≤ E`. -/
theorem card_mul_energyQuantum_le {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) (ε₀ E : ℝ≥0∞)
    (hε₀ : ε₀ ≠ 0) (hε₀top : ε₀ ≠ ⊤) (hbdd : ∀ n, μ n univ ≤ E)
    (S : Finset X) (hS : ↑S ⊆ bubbleSet μ ε₀) :
    (S.card : ℝ≥0∞) * ε₀ ≤ E := by
  obtain ⟨r, hr, hdisj⟩ := exists_pos_radius_pairwiseDisjoint_ball S
  refine ENNReal.le_of_forall_lt_one_mul_le ?_
  intro a ha
  have hlt : a * ε₀ < ε₀ := by
    calc a * ε₀ = ε₀ * a := mul_comm _ _
      _ < ε₀ * 1 := ENNReal.mul_lt_mul_right hε₀ hε₀top ha
      _ = ε₀ := mul_one _
  have hev : ∀ᶠ n in atTop, ∀ x ∈ S, a * ε₀ < μ n (ball x r) := by
    refine (eventually_all_finset S).2 ?_
    intro x hx
    exact eventually_lt_of_lt_liminf (lt_of_lt_of_le hlt (hS hx r hr))
  obtain ⟨n, hn⟩ := hev.exists
  calc a * ((S.card : ℝ≥0∞) * ε₀) = ∑ _x ∈ S, a * ε₀ := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ ∑ x ∈ S, μ n (ball x r) := Finset.sum_le_sum fun x hx => (hn x hx).le
    _ = μ n (⋃ x ∈ S, ball x r) :=
        (measure_biUnion_finset hdisj fun _ _ => measurableSet_ball).symm
    _ ≤ μ n univ := measure_mono (subset_univ _)
    _ ≤ E := hbdd n

/-- **Uhlenbeck bubbling: finiteness and quantization of the blow-up set.**

Let `μ n` be the energy densities of a sequence of connections on a metric measure space `X`,
with total energy uniformly bounded by a finite `E`, and let `ε₀` be the (finite, positive)
energy quantum supplied by ε-regularity.  Then the bubbling set — the set of points where at
every scale at least `ε₀` of energy survives in the limit — is finite, and the number of
bubbles satisfies `#bubbles * ε₀ ≤ E`, i.e. there are at most `E / ε₀` bubbles. -/
theorem uhlenbeck_bubbling {X : Type*} [MetricSpace X] [MeasurableSpace X]
    [OpensMeasurableSpace X] (μ : ℕ → Measure X) (ε₀ E : ℝ≥0∞)
    (hε₀ : 0 < ε₀) (hε₀top : ε₀ ≠ ⊤) (hE : E ≠ ⊤) (hbdd : ∀ n, μ n univ ≤ E) :
    (bubbleSet μ ε₀).Finite ∧ ((bubbleSet μ ε₀).ncard : ℝ≥0∞) * ε₀ ≤ E := by
  have hε₀' : ε₀ ≠ 0 := hε₀.ne'
  have hkey : ∀ S : Finset X, ↑S ⊆ bubbleSet μ ε₀ → (S.card : ℝ≥0∞) * ε₀ ≤ E :=
    fun S hS => card_mul_energyQuantum_le μ ε₀ E hε₀' hε₀top hbdd S hS
  -- a uniform natural number bound on the cardinality of finite subsets of the bubbling set
  obtain ⟨N, hN⟩ : ∃ N : ℕ, E / ε₀ < (N : ℝ≥0∞) :=
    ENNReal.exists_nat_gt (by
      simp [ENNReal.div_eq_top, hE, hε₀'])
  have hcard : ∀ S : Finset X, ↑S ⊆ bubbleSet μ ε₀ → S.card ≤ N := by
    intro S hS
    have h1 : (S.card : ℝ≥0∞) ≤ E / ε₀ := ENNReal.le_div_iff_mul_le
      (Or.inl hε₀') (Or.inl hε₀top) |>.2 (hkey S hS)
    have h2 : (S.card : ℝ≥0∞) < (N : ℝ≥0∞) := lt_of_le_of_lt h1 hN
    exact le_of_lt (by exact_mod_cast h2)
  have hfin : (bubbleSet μ ε₀).Finite := by
    have hmk : Cardinal.mk (bubbleSet μ ε₀) ≤ (N : Cardinal) :=
      Cardinal.mk_le_iff_forall_finset_subset_card_le.2 hcard
    exact Cardinal.lt_aleph0_iff_set_finite.1
      (lt_of_le_of_lt hmk (Cardinal.natCast_lt_aleph0))
  refine ⟨hfin, ?_⟩
  have hsub : (↑hfin.toFinset : Set X) ⊆ bubbleSet μ ε₀ := by
    simp [Set.Finite.coe_toFinset]
  have hbound := hkey hfin.toFinset hsub
  rwa [Set.ncard_eq_toFinset_card _ hfin]

/-!
### Non-vacuity: a genuine one-bubble example

A sequence of connections concentrating all of a quantum `ε₀` of energy at a single point is
modelled by the constant sequence of measures `ε₀ • δ₀`.  Its bubbling set is exactly `{0}`,
so `uhlenbeck_bubbling` is not vacuous, and the bound `#bubbles * ε₀ ≤ E` is sharp for
`E = ε₀`.
-/

theorem bubbleSet_smul_dirac (ε₀ : ℝ≥0∞) (hε₀ : ε₀ ≠ 0) :
    bubbleSet (fun _ : ℕ => ε₀ • (Measure.dirac (0 : ℝ))) ε₀ = {(0 : ℝ)} := by
  ext x
  simp only [bubbleSet, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro hx
    by_contra hne
    have hr : 0 < |x| / 2 := by
      have : 0 < |x| := abs_pos.2 hne
      linarith
    have h0 : (0 : ℝ) ∉ ball x (|x| / 2) := by
      simp only [mem_ball, dist_zero_left, Real.norm_eq_abs]
      intro hlt
      linarith [abs_pos.2 hne]
    have hmeas : (ε₀ • (Measure.dirac (0 : ℝ))) (ball x (|x| / 2)) = 0 := by
      simp [Measure.dirac_apply' _ measurableSet_ball, h0]
    have := hx (|x| / 2) hr
    rw [show (fun _ : ℕ => (ε₀ • (Measure.dirac (0 : ℝ))) (ball x (|x| / 2)))
        = fun _ : ℕ => (0 : ℝ≥0∞) from funext fun _ => hmeas] at this
    simp at this
    exact hε₀ this
  · rintro rfl
    intro r hr
    have hmem : (0 : ℝ) ∈ ball (0 : ℝ) r := mem_ball_self hr
    have hmeas : (ε₀ • (Measure.dirac (0 : ℝ))) (ball (0 : ℝ) r) = ε₀ := by
      simp [Measure.dirac_apply' _ measurableSet_ball, hmem]
    rw [show (fun _ : ℕ => (ε₀ • (Measure.dirac (0 : ℝ))) (ball (0 : ℝ) r))
        = fun _ : ℕ => ε₀ from funext fun _ => hmeas]
    simp

end Frontier

