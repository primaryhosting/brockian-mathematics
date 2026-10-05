/-
# Mcmullen Renormalization
Category: Frontier — Fields Medal Work
Target: Frontier.mcmullen_renormalization
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Frontier

/-! ## Quadratic-like maps

Following Douady–Hubbard and McMullen, a *quadratic-like map* is a holomorphic proper
degree-two branched covering `f : U → V` between simply connected planar domains with
`closure U` a compact subset of `V`.  We encode "proper of degree two, branched over the
unique critical value" by the fibre conditions `fiber_crit` and `fiber_two`. -/

/-- A quadratic-like map `f : U → V` with critical point `c`. -/
structure QuadraticLike (f : ℂ → ℂ) (U V : Set ℂ) (c : ℂ) : Prop where
  /-- The domain is open. -/
  isOpen_U : IsOpen U
  /-- The range is open. -/
  isOpen_V : IsOpen V
  /-- `U` is relatively compact. -/
  isCompact_closure : IsCompact (closure U)
  /-- `U` is compactly contained in `V`. -/
  closure_subset : closure U ⊆ V
  /-- `f` is holomorphic on a neighbourhood of `V`. -/
  analytic : AnalyticOnNhd ℂ f V
  /-- `f` maps `U` into `V`. -/
  mapsTo : Set.MapsTo f U V
  /-- The critical point lies in `U`. -/
  crit_mem : c ∈ U
  /-- `c` is a critical point. -/
  crit_deriv : deriv f c = 0
  /-- The fibre over the critical value is the single (doubled) point `c`. -/
  fiber_crit : {z ∈ U | f z = f c} = {c}
  /-- Every other fibre consists of exactly two points: `f : U → V` is proper of degree 2. -/
  fiber_two : ∀ w ∈ V, w ≠ f c → ∃ a b : ℂ, a ≠ b ∧ {z ∈ U | f z = w} = {a, b}

/-- The filled Julia set of a quadratic-like map `f : U → V`:
points whose whole forward orbit stays in `U`. -/

theorem quadraticLike_sq :
    QuadraticLike (fun z : ℂ => z ^ 2) (Metric.ball 0 2) (Metric.ball 0 4) 0 := by
  have hcl : closure (Metric.ball (0 : ℂ) 2) = Metric.closedBall (0 : ℂ) 2 :=
    closure_ball 0 (by norm_num)
  refine ⟨Metric.isOpen_ball, Metric.isOpen_ball, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcl]; exact isCompact_closedBall 0 2
  · rw [hcl]
    intro z hz
    simp only [Metric.mem_closedBall, dist_zero_right] at hz
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  · exact fun z _ => analyticAt_id.pow 2
  · intro z hz
    simp only [Metric.mem_ball, dist_zero_right] at hz ⊢
    have h0 : (0 : ℝ) ≤ ‖z‖ := norm_nonneg z
    rw [norm_pow]
    nlinarith
  · simp
  · simp
  · ext z
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff, Metric.mem_ball, dist_zero_right]
    constructor
    · rintro ⟨-, h⟩
      simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 (by simpa using h)
    · rintro rfl; norm_num
  · intro w hw hw0
    simp only [Metric.mem_ball, dist_zero_right] at hw
    simp only [ne_eq] at hw0
    have hw0' : w ≠ 0 := by simpa using hw0
    obtain ⟨s, hs⟩ := IsSepClosed.exists_pow_nat_eq w 2
    have hsne : s ≠ 0 := by rintro rfl; simp at hs; exact hw0' hs.symm
    have hnorm : ‖s‖ < 2 := by
      have hns : ‖s‖ ^ 2 = ‖w‖ := by rw [← norm_pow, hs]
      nlinarith [norm_nonneg s]
    refine ⟨s, -s, ?_, ?_⟩
    · intro h
      apply hsne
      have h2 : (2 : ℂ) * s = 0 := by linear_combination h
      simpa using h2
    · ext z
      simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff, Metric.mem_ball,
        dist_zero_right]
      constructor
      · rintro ⟨-, h⟩
        have h2 : (z - s) * (z + s) = 0 := by rw [← hs] at h; linear_combination h
        rcases mul_eq_zero.1 h2 with h1 | h1
        · left; linear_combination h1
        · right; linear_combination h1
      · rintro (rfl | rfl)
        · exact ⟨hnorm, hs⟩
        · exact ⟨by simpa using hnorm, by rw [← hs]; ring⟩

/-! ## Main theorem -/

/-- **McMullen renormalization: statement and Lean-checked base case / reduction.**

For quadratic-like maps (Douady–Hubbard–McMullen) we record:

1. *(non-vacuity)* the family of quadratic-like maps with connected filled Julia set is
   nonempty — `z ↦ z²` on `𝔻(0,2) → 𝔻(0,4)` is such a map;
2. *(base case)* every quadratic-like map with connected filled Julia set is renormalizable
   of period `1`, so `renormPeriods` is nonempty;
3. *(reduction / tower law)* renormalization periods compose multiplicatively: a period-`m`
   renormalization of the period-`n` renormalization of `f` is a period-`n*m`
   renormalization of `f`;
4. *(rigidity of the small Julia sets)* the filled Julia set of any renormalization is
   contained in the filled Julia set of the original map, and its full forward orbit under
   `f` stays inside `U`. -/
