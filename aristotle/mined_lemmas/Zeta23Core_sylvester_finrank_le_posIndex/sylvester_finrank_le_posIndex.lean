import Mathlib

/-!
# Sylvester Finrank Le Pos Index
Category: Brockian Corpus
Target: Zeta23Core.sylvester_finrank_le_posIndex
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

set_option grind.warning false

namespace Zeta23Core

open Matrix

variable {𝕜 : Type*} [RCLike 𝕜] {n : Type*} [Fintype n] [DecidableEq n]

/-- The positive index of inertia of a Hermitian matrix: the number of indices `i` such that
the `i`-th eigenvalue is positive (i.e. the number of positive eigenvalues, counted with
multiplicity). -/

theorem sylvester_finrank_le_posIndex {A : Matrix n n 𝕜} (hA : A.IsHermitian)
    (W : Submodule 𝕜 (n → 𝕜))
    (hpos : ∀ x ∈ W, x ≠ 0 → 0 < RCLike.re (star x ⬝ᵥ (A *ᵥ x))) :
    Module.finrank 𝕜 W ≤ posIndex hA := by
  set f : W →ₗ[𝕜] ({i : n // 0 < hA.eigenvalues i} → 𝕜) := (posCoords hA).comp W.subtype with hf
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    by_contra hne
    have hw0 : (w : n → 𝕜) ≠ 0 := fun h => hne (Subtype.ext h)
    have hpos' := hpos (w : n → 𝕜) w.2 hw0
    rw [quadForm_eq_sum hA] at hpos'
    have hle : ∑ i, hA.eigenvalues i *
        ‖(star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ (w : n → 𝕜)) i‖ ^ 2 ≤ 0 := by
      refine Finset.sum_nonpos fun i _ => ?_
      rcases lt_or_ge 0 (hA.eigenvalues i) with hgt | hle'
      · have : (star (hA.eigenvectorUnitary : Matrix n n 𝕜) *ᵥ (w : n → 𝕜)) i = 0 := by
          have := congrFun hw ⟨i, hgt⟩
          simpa [hf] using this
        simp [this]
      · exact mul_nonpos_of_nonpos_of_nonneg hle' (by positivity)
    exact absurd hpos' (not_lt.mpr hle)
  calc Module.finrank 𝕜 W
      ≤ Module.finrank 𝕜 ({i : n // 0 < hA.eigenvalues i} → 𝕜) :=
        f.finrank_le_finrank_of_injective hinj
    _ = posIndex hA := by simp [posIndex]

end Zeta23Core

