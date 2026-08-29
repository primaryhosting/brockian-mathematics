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

theorem mem_deficiencySpace_of_mem_orthogonal {T : H →ₗ.[ℂ] H}
    (hd : Dense (T.domain : Set H)) {z : ℂ} {g : H}
    (hg : g ∈ (shiftedRange T z)ᗮ) :
    ∃ hmem : g ∈ T.adjoint.domain,
      (⟨g, hmem⟩ : T.adjoint.domain) ∈ deficiencySpace T ((starRingEnd ℂ) z) := by
  have hzero : ∀ v : T.domain, ⟪T v - z • (v : H), g⟫_ℂ = 0 := fun v =>
    hg _ ((mem_shiftedRange_iff T z _).mpr ⟨v, rfl⟩)
  have hkey : ∀ v : T.domain, ⟪(starRingEnd ℂ) z • g, (v : H)⟫_ℂ = ⟪g, T v⟫_ℂ := by
    intro v
    have h := hzero v
    rw [inner_sub_left, inner_smul_left, sub_eq_zero] at h
    have h2 : ⟪g, T v⟫_ℂ = z * ⟪g, (v : H)⟫_ℂ := by
      have hc := congrArg (starRingEnd ℂ) h
      rwa [inner_conj_symm, map_mul, Complex.conj_conj, inner_conj_symm] at hc
    rw [inner_smul_left, Complex.conj_conj, h2]
  have hmem : g ∈ T.adjoint.domain :=
    LinearPMap.mem_adjoint_domain_of_exists _ ⟨(starRingEnd ℂ) z • g, hkey⟩
  refine ⟨hmem, ?_⟩
  rw [mem_deficiencySpace_iff]
  exact LinearPMap.adjoint_apply_eq hd ⟨g, hmem⟩ hkey

/-! ### Injectivity and surjectivity of the shifted closure -/

omit [CompleteSpace H] in
/-- The basic lower bound for a symmetric operator at a spectral parameter at
distance one from the real axis. -/
