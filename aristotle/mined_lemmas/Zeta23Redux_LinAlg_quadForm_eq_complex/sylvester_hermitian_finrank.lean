import Mathlib
/-!
# Sylvester Hermitian Finrank
Category: Zeta-23 §3 Linear Algebra (re-derivation)
Target: Zeta23Redux.LinAlg.sylvester_hermitian_finrank
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Classical

namespace Zeta23Redux.LinAlg

open Matrix

variable {d : ℕ} {A : Matrix (Fin d) (Fin d) ℂ}

/-- The positive index of inertia of a Hermitian matrix: the number of strictly positive
eigenvalues (counted with multiplicity, i.e. over the index set of the matrix). -/

theorem sylvester_hermitian_finrank (hA : A.IsHermitian) (W : Submodule ℂ (Fin d → ℂ))
    (hW : ∀ x ∈ W, x ≠ 0 → 0 < (star x ⬝ᵥ A *ᵥ x).re) :
    Module.finrank ℂ W ≤ posIndex hA := by
  set T : W →ₗ[ℂ] ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) :=
    (posCoordMap hA).comp W.subtype with hT
  have hinj : Function.Injective T := by
    rw [← LinearMap.ker_eq_bot]
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hx0 : ∀ i, 0 < hA.eigenvalues i → eigCoord hA (x : Fin d → ℂ) i = 0 := by
      intro i hi
      have := congrFun (LinearMap.mem_ker.mp hx) ⟨i, hi⟩
      simpa [hT, posCoordMap] using this
    by_contra hne
    have hxne : (x : Fin d → ℂ) ≠ 0 := by
      simpa [Submodule.coe_eq_zero] using hne
    exact absurd (quadForm_nonpos_of_eigCoord_eq_zero hA _ hx0)
      (not_le.mpr (hW _ x.2 hxne))
  have hle : Module.finrank ℂ W
      ≤ Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) :=
    LinearMap.finrank_le_finrank_of_injective hinj
  calc Module.finrank ℂ W
      ≤ Module.finrank ℂ ({i : Fin d // 0 < hA.eigenvalues i} → ℂ) := hle
    _ = Fintype.card {i : Fin d // 0 < hA.eigenvalues i} := by
        simp
    _ = posIndex hA := by
        rw [Fintype.card_subtype]
        rfl

end Zeta23Redux.LinAlg

import Mathlib

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
set_option pp.piBinderTypes true

set_option grind.warning false

