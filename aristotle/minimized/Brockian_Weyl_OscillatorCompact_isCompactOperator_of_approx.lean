/-
  CompactCriterion.lean — an abstract compactness criterion: an operator whose
  unit-ball image is uniformly approximable by finite-dimensional subspaces is
  a compact operator.
-/
import Mathlib

open Metric Filter

namespace Brockian.Weyl.OscillatorCompact

/-- An operator whose closed-unit-ball image is uniformly approximable by
finite-dimensional subspaces is a compact operator. -/

theorem isCompactOperator_of_approx {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (R : H →L[ℂ] H)
    (happrox : ∀ ε : ℝ, 0 < ε → ∃ V : Submodule ℂ H, FiniteDimensional ℂ V ∧
      ∀ y : H, ‖y‖ ≤ 1 → ∃ v ∈ V, ‖R y - v‖ ≤ ε) :
    IsCompactOperator R := by
  set S : Set H := (R : H → H) '' Metric.closedBall 0 1 with hS
  have htb : TotallyBounded S := by
    rw [Metric.totallyBounded_iff]
    intro ε hε
    obtain ⟨V, hVfin, hV⟩ := happrox (ε / 3) (by linarith)
    have hWcompact : IsCompact ((V.subtype) '' (Metric.closedBall (0 : V) (‖R‖ + ε))) :=
      (isCompact_closedBall _ _).image continuous_subtype_val
    obtain ⟨t, htfin, htcover⟩ :=
      Metric.totallyBounded_iff.mp hWcompact.totallyBounded (ε / 3) (by linarith)
    refine ⟨t, htfin, ?_⟩
    rintro x ⟨y, hy, rfl⟩
    have hy1 : ‖y‖ ≤ 1 := by simpa using hy
    obtain ⟨v, hvV, hv⟩ := hV y hy1
    have hRy : ‖R y‖ ≤ ‖R‖ := by
      have h := R.le_opNorm y
      have h2 := R.opNorm_nonneg
      nlinarith
    have hvnorm : ‖v‖ ≤ ‖R‖ + ε := by
      have h3 : ‖v‖ ≤ ‖R y‖ + ‖R y - v‖ := by
        calc ‖v‖ = ‖R y - (R y - v)‖ := by congr 1; abel
          _ ≤ ‖R y‖ + ‖R y - v‖ := norm_sub_le _ _
      linarith
    have hvW : v ∈ (V.subtype) '' (Metric.closedBall (0 : V) (‖R‖ + ε)) := by
      refine ⟨⟨v, hvV⟩, ?_, rfl⟩
      simpa using hvnorm
    obtain ⟨w, hwt, hw⟩ := Set.mem_iUnion₂.mp (htcover hvW)
    refine Set.mem_iUnion₂.mpr ⟨w, hwt, ?_⟩
    have hd1 : dist (R y) v ≤ ε / 3 := by rw [dist_eq_norm]; exact hv
    have hd2 : dist v w < ε / 3 := by simpa [Metric.mem_ball] using hw
    have h4 : dist (R y) w ≤ dist (R y) v + dist v w := dist_triangle _ _ _
    simp only [Metric.mem_ball]
    linarith
  have hcpt : IsCompact (closure S) := htb.closure.isCompact_of_isClosed isClosed_closure
  exact (isCompactOperator_iff_exists_mem_nhds_isCompact_closure_image (R : H → H)).mpr
    ⟨Metric.closedBall 0 1, Metric.closedBall_mem_nhds _ one_pos, hcpt⟩

end Brockian.Weyl.OscillatorCompact

/-
  Base.lean — reconstruction of the corpus modules that the target theorem
  depends on:

  * `Brockian/WeylOperator.lean`            (verbatim)
  * `Brockian/WeylSchrodingerMinimal.lean`  (the L² / Schwartz-core scaffolding
                                             used by the harmonic oscillator)
  * `Brockian/WeylHarmonicOscillator.lean`  (verbatim, minus the
                                             `CompactResolventShape` statements,
                                             which the target does not use)
-/
import Mathlib

/-! ## Brockian/WeylOperator.lean -/

namespace Brockian.Weyl.Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Symmetric operator.** A partially-defined operator `T : H →ₗ.[ℂ] H` is
*symmetric* when it is its own formal adjoint: `⟪T x, y⟫ = ⟪x, T y⟫` for all
`x, y` in the domain. -/
