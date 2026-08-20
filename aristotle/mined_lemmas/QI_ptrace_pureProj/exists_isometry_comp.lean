import Mathlib

set_option maxHeartbeats 1000000

/-!
# Purification of mixed states

A mixed state on a finite dimensional system `n` is a positive semidefinite matrix `rho` of
trace one.  A *purification* of `rho` is a unit vector `psi` on the composite system
`n × m` (system ⊗ ancilla) whose reduced density matrix (partial trace over the ancilla `m`)
is `rho`.

The main theorem `QI.purification_exists` states that

* every mixed state admits a purification (with ancilla a copy of the system), and
* any two purifications of the same mixed state are related by an isometry acting on the
  ancilla alone (in particular, for ancillas of the same dimension, by a unitary).
-/

namespace QI

open Matrix
open scoped ComplexOrder MatrixOrder

section Defs

variable {n m : Type*}

/-- The matrix `A` whose `(i,k)` entry is `psi (i,k)`; this is the standard identification of a
vector of the composite system `n × m` with a linear map. -/

theorem exists_isometry_comp {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
    [NormedAddCommGroup F] [InnerProductSpace ℂ F] [FiniteDimensional ℂ F]
    (fa fb : E →ₗ[ℂ] F) (hinner : ∀ x y, inner ℂ (fa x) (fa y) = inner ℂ (fb x) (fb y)) :
    ∃ L : F →ₗᵢ[ℂ] F, ∀ x, L (fa x) = fb x := by
  have hkerle : LinearMap.ker fa ≤ LinearMap.ker fb := by
    intro x hx
    simp only [LinearMap.mem_ker] at *
    have h2 := hinner x x
    rw [hx] at h2
    simp only [inner_zero_left] at h2
    exact inner_self_eq_zero.mp h2.symm
  set g : (E ⧸ LinearMap.ker fa) →ₗ[ℂ] F := (LinearMap.ker fa).liftQ fb hkerle with hg
  set g0 : (LinearMap.range fa) →ₗ[ℂ] F :=
    g ∘ₗ (fa.quotKerEquivRange.symm : (LinearMap.range fa) →ₗ[ℂ] _) with hg0
  have hg0_apply : ∀ (x : E) (hx : fa x ∈ LinearMap.range fa), g0 ⟨fa x, hx⟩ = fb x := by
    intro x hx
    rw [hg0]
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [LinearMap.quotKerEquivRange_symm_apply_image, hg]
    simp [Submodule.liftQ_apply]
  have hg0iso : ∀ v w : LinearMap.range fa,
      inner ℂ (g0 v) (g0 w) = inner ℂ (v : F) (w : F) := by
    rintro ⟨v, x, rfl⟩ ⟨w, y, rfl⟩
    rw [hg0_apply x, hg0_apply y]
    exact (hinner x y).symm
  refine ⟨(LinearMap.isometryOfInner g0 hg0iso).extend, fun x => ?_⟩
  have h1 :=
    (LinearMap.isometryOfInner g0 hg0iso).extend_apply (⟨fa x, ⟨x, rfl⟩⟩ : LinearMap.range fa)
  simpa [hg0_apply x] using h1

/-- If `A Aᴴ = B Bᴴ` then `B = A U` for some unitary `U`. -/
