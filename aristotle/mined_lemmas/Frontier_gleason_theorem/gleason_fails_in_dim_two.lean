import RequestProject.Main
/-!
# Gleason's theorem fails in dimension two

This file complements `RequestProject/Main.lean`.  It constructs an explicit quantum measure on
the projection lattice of `ℂ²` which does not come from any density operator, showing that the
dimension hypothesis `3 ≤ N` in Gleason's theorem cannot be dropped.

The measure is the two-valued "lexicographic sign" measure: in dimension two the only nontrivial
orthogonality relation between projections is `Q = 1 - P` for a rank-one projection `P`, so any
function on rank-one projections satisfying `f P + f (1 - P) = 1` is finitely additive.
-/

open scoped Classical
open scoped ComplexOrder

namespace Frontier

open Matrix

/-! ## Structure of projections in dimension two -/

/-- The Cayley–Hamilton identity for `2 × 2` matrices. -/

theorem gleason_fails_in_dim_two :
    ¬ ∃ ρ : Matrix (Fin 2) (Fin 2) ℂ, IsDensityMatrix ρ ∧
        ∀ P : Matrix (Fin 2) (Fin 2) ℂ, IsProj P → badMeasure P = (ρ * P).trace.re := by
  rintro ⟨ρ, ⟨hpsd, htr⟩, hrep⟩
  have hherm : ρ 1 0 = star (ρ 0 1) := by
    have h := hpsd.1.apply 0 1
    rw [← h, star_star]
  have him00 : (ρ 0 0).im = 0 := Complex.conj_eq_iff_im.mp (hpsd.1.apply 0 0)
  have him11 : (ρ 1 1).im = 0 := Complex.conj_eq_iff_im.mp (hpsd.1.apply 1 1)
  -- the `z` projection forces `ρ 0 0 = 1`
  have hz := hrep projZ isProj_projZ
  rw [badMeasure_projZ] at hz
  have hz' : (ρ 0 0).re = 1 := by
    have : (ρ * projZ).trace = ρ 0 0 := by
      simp [projZ, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    rw [this] at hz
    exact hz.symm
  -- unit trace forces `ρ 1 1 = 0`
  have htr' : (ρ 0 0).re + (ρ 1 1).re = 1 := by
    have := congrArg Complex.re htr
    rw [Matrix.trace_fin_two] at this
    simpa using this
  have h11 : (ρ 1 1).re = 0 := by linarith
  -- the `x` projection forces `Re (ρ 0 1) = 1/2`
  have hx := hrep projX isProj_projX
  rw [badMeasure_projX] at hx
  have hxtrace : (ρ * projX).trace = (ρ 0 0 + ρ 0 1 + ρ 1 0 + ρ 1 1) / 2 := by
    simp [projX, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two]
    ring
  rw [hxtrace] at hx
  have hre01 : (ρ 0 1).re = 1 / 2 := by
    have hrew : ((ρ 0 0 + ρ 0 1 + ρ 1 0 + ρ 1 1) / 2).re
        = ((ρ 0 0).re + (ρ 0 1).re + (ρ 1 0).re + (ρ 1 1).re) / 2 := by
      simp
    rw [hrew] at hx
    have h10 : (ρ 1 0).re = (ρ 0 1).re := by rw [hherm]; simp
    rw [h10, hz', h11] at hx
    linarith
  -- but then positive semidefiniteness fails on the vector `(-1/2, 1)`
  have hpos := hpsd.re_dotProduct_nonneg ![(-1 : ℂ), 2]
  have hval : (star ![(-1 : ℂ), 2] ⬝ᵥ ρ *ᵥ ![(-1 : ℂ), 2])
      = ρ 0 0 - 2 * ρ 0 1 - 2 * ρ 1 0 + 4 * ρ 1 1 := by
    have h2 : (starRingEnd ℂ) 2 = 2 := Complex.conj_eq_iff_re.mpr rfl
    simp [dotProduct, mulVec, Fin.sum_univ_two, h2]
    ring
  rw [hval] at hpos
  have h10re : (ρ 1 0).re = (ρ 0 1).re := by rw [hherm]; simp
  have hρ00 : ρ 0 0 = 1 := Complex.ext (by rw [hz']; rfl) (by rw [him00]; rfl)
  have hρ11 : ρ 1 1 = 0 := Complex.ext (by rw [h11]; rfl) (by rw [him11]; rfl)
  rw [hρ00, hρ11] at hpos
  simp [RCLike.re_to_complex, Complex.sub_re, Complex.mul_re, h10re, hre01] at hpos
  linarith

end Frontier

/-
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` to precede any module docstring, so the header above is repeated
-- below as the module docstring of this file.)
import Mathlib
/-!
# Gleason Theorem
Category: Frontier Physics
Target: Frontier.gleason_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

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

open Matrix

variable {N : ℕ}

/-- An orthogonal projection on the Hilbert space `ℂ^N`, represented as a matrix. -/
