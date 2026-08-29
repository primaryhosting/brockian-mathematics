import Mathlib

/-!
# Stone Generator
Category: Quantum Physics
Target: QPhys.stone_generator
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open MeasureTheory Set Filter Topology Complex
open scoped LinearPMap

namespace QPhys

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- A strongly continuous one-parameter unitary group on a complex Hilbert space `H`:
a family `U : ℝ → (H →L[ℂ] H)` with `U 0 = 1`, `U (s + t) = U s ∘ U t`, each `U t` norm
preserving (hence unitary, since the group law provides the inverse `U (-t)`), and such that
`t ↦ U t x` is continuous for every `x` (strong continuity). -/
structure IsUnitaryGroup (U : ℝ → H →L[ℂ] H) : Prop where
  map_zero : U 0 = 1
  map_add : ∀ s t, U (s + t) = (U s).comp (U t)
  norm_map : ∀ t x, ‖U t x‖ = ‖x‖
  continuous_apply : ∀ x, Continuous fun t => U t x

omit [CompleteSpace H] in
/-- Sanity check that the hypotheses are satisfiable: the constant family `U t = 1` is a
strongly continuous one-parameter unitary group. -/

theorem gen_isFormalAdjoint {U : ℝ → H →L[ℂ] H} (hU : IsUnitaryGroup U) :
    (gen U).IsFormalAdjoint (gen U) := by
  intro x y
  have hx := hasDerivAt_gen U x
  have hy := hasDerivAt_gen U y
  have hd : HasDerivAt (fun t : ℝ => inner ℂ (U t (x : H)) (U t (y : H)))
      (inner ℂ (U 0 (x : H)) (I • gen U y) + inner ℂ (I • gen U x) (U 0 (y : H))) 0 :=
    hx.inner ℂ hy
  have hconst : (fun t : ℝ => inner ℂ (U t (x : H)) (U t (y : H)))
      = fun _ : ℝ => (inner ℂ (x : H) (y : H) : ℂ) := by
    funext t
    exact hU.inner_map t _ _
  rw [hconst] at hd
  have h0 : inner ℂ (U 0 (x : H)) (I • gen U y) + inner ℂ (I • gen U x) (U 0 (y : H)) = 0 :=
    hd.unique (hasDerivAt_const _ _)
  rw [hU.map_zero] at h0
  simp only [ContinuousLinearMap.one_apply, inner_smul_left, inner_smul_right,
    Complex.conj_I] at h0
  have hI : (I : ℂ) ≠ 0 := Complex.I_ne_zero
  field_simp at h0
  rcases mul_eq_zero.1 h0 with h | h
  · exact absurd h hI
  · linear_combination -h

/-! ### Surjectivity of `A ± i` -/

/-- Key analytic step (a resolvent construction): for every `y` there is `x` with
`d/dt (U t x)|_{t=0} = x - y`. -/
