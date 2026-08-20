import Mathlib

/-!
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types false
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Quadratic-like maps (Douady–Hubbard)

A *quadratic-like map* is a triple `(f, U, V)` where `U ⋐ V` are bounded, connected open
subsets of `ℂ` and `f : U → V` is a proper holomorphic map of degree `2`.  Degree two is
encoded here concretely: `f` has a unique critical point `c ∈ U`, the fibre over the critical
value `f c` is the singleton `{c}`, and every other fibre over `V` consists of exactly two
points.
-/

/-- A quadratic-like map in the sense of Douady–Hubbard, presented as a globally defined
function `f : ℂ → ℂ` together with the data of the domains `U ⋐ V`.  Only the behaviour of
`f` on `U` is constrained. -/
structure QuadraticLike where
  /-- The small domain. -/
  U : Set ℂ
  /-- The large domain. -/
  V : Set ℂ
  /-- The map. -/
  f : ℂ → ℂ
  /-- The critical point. -/
  critical : ℂ
  isOpen_U : IsOpen U
  isOpen_V : IsOpen V
  isConnected_U : IsConnected U
  isConnected_V : IsConnected V
  isBounded_V : Bornology.IsBounded V
  /-- `U` is compactly contained in `V`. -/
  closure_U_subset : closure U ⊆ V
  differentiableOn : DifferentiableOn ℂ f U
  mapsTo : Set.MapsTo f U V
  /-- `f : U → V` is proper. -/
  properOn : ∀ ⦃K : Set ℂ⦄, K ⊆ V → IsCompact K → IsCompact (U ∩ f ⁻¹' K)
  critical_mem : critical ∈ U
  /-- The fibre over the critical value is a single (doubled) point. -/
  fiber_critical : U ∩ f ⁻¹' {f critical} = {critical}
  /-- Every non-critical fibre over `V` has exactly two points: `f` has degree two. -/
  fiber_card : ∀ w ∈ V, w ≠ f critical → (U ∩ f ⁻¹' {w}).ncard = 2
  deriv_critical : deriv f critical = 0
  unique_critical : ∀ z ∈ U, deriv f z = 0 → z = critical

namespace QuadraticLike

variable (Q : QuadraticLike)

/-- The filled Julia set of a quadratic-like map: the points whose whole forward orbit
stays in `U`. -/

noncomputable def sq (R : ℝ) (hR : 1 < R) : QuadraticLike where
  U := Metric.ball 0 R
  V := Metric.ball 0 (R ^ 2)
  f := fun z => z ^ 2
  critical := 0
  isOpen_U := Metric.isOpen_ball
  isOpen_V := Metric.isOpen_ball
  isConnected_U := Metric.isConnected_ball (by linarith)
  isConnected_V := Metric.isConnected_ball (by nlinarith)
  isBounded_V := Metric.isBounded_ball
  closure_U_subset := by
    refine Metric.closure_ball_subset_closedBall.trans ?_
    intro z hz
    simp only [Metric.mem_closedBall, Metric.mem_ball, dist_zero_right] at hz ⊢
    nlinarith [norm_nonneg z]
  differentiableOn := (by fun_prop : Differentiable ℂ fun z : ℂ => z ^ 2).differentiableOn
  mapsTo := by
    intro z hz
    simp only [Metric.mem_ball, dist_zero_right, norm_pow] at hz ⊢
    nlinarith [norm_nonneg z]
  properOn := by
    intro K hKV hK
    have hset : Metric.ball (0 : ℂ) R ∩ (fun z : ℂ => z ^ 2) ⁻¹' K
        = Metric.closedBall (0 : ℂ) R ∩ (fun z : ℂ => z ^ 2) ⁻¹' K := by
      ext z
      simp only [Set.mem_inter_iff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
        Set.mem_preimage]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1.le, h2⟩
      · rintro ⟨h1, h2⟩
        refine ⟨?_, h2⟩
        have hmem := hKV h2
        simp only [Metric.mem_ball, dist_zero_right, norm_pow] at hmem
        nlinarith [norm_nonneg z]
    rw [hset]
    exact (isCompact_closedBall _ _).inter_right (hK.isClosed.preimage (by fun_prop))
  critical_mem := Metric.mem_ball_self (by linarith)
  fiber_critical := by
    ext z
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball,
      dist_zero_right]
    constructor
    · rintro ⟨-, hz⟩
      simpa using hz
    · rintro rfl
      exact ⟨by simpa using (by linarith : (0 : ℝ) < R), rfl⟩
  fiber_card := by
    intro w hw hw0
    have hw0' : w ≠ 0 := by simpa using hw0
    obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq w 2
    have hsne : s ≠ 0 := by
      rintro rfl
      exact hw0' (by simpa using hs.symm)
    have hwR : ‖w‖ < R ^ 2 := by simpa [dist_zero_right] using hw
    have hnorm : ‖s‖ < R := by
      have hns : ‖s‖ ^ 2 = ‖w‖ := by rw [← hs, norm_pow]
      nlinarith [norm_nonneg s, (by linarith : (0 : ℝ) < R)]
    have hset : Metric.ball (0 : ℂ) R ∩ (fun z : ℂ => z ^ 2) ⁻¹' {w} = {s, -s} := by
      ext z
      simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Metric.mem_ball,
        dist_zero_right, Set.mem_insert_iff]
      constructor
      · rintro ⟨-, hz⟩
        have hfac : (z - s) * (z + s) = 0 := by linear_combination hz - hs
        rcases mul_eq_zero.1 hfac with h | h
        · exact Or.inl (by linear_combination h)
        · exact Or.inr (by linear_combination h)
      · rintro (rfl | rfl)
        · exact ⟨hnorm, hs⟩
        · refine ⟨by simpa using hnorm, ?_⟩
          simpa using hs
    rw [hset]
    exact Set.ncard_pair (fun h => hsne (by linear_combination h / 2))
  deriv_critical := by simp
  unique_critical := by
    intro z _ hz
    simpa using hz

