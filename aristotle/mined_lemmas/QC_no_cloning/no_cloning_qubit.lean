/-
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# No Cloning
Category: Quantum Computing
Target: QC.no_cloning
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace QC

open scoped TensorProduct

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **Key lemma.** If a unitary `U` on `H ⊗ H` clones every unit vector against the
"blank" unit vector `e₀`, then for any two unit vectors `u`, `v` the overlap
`⟪u, v⟫` satisfies `⟪u, v⟫ = ⟪u, v⟫ ^ 2`, since unitaries preserve inner products. -/

theorem no_cloning_qubit :
    ¬ ∃ U : ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] (EuclideanSpace ℂ (Fin 2)))
        ≃ₗᵢ[ℂ] ((EuclideanSpace ℂ (Fin 2)) ⊗[ℂ] (EuclideanSpace ℂ (Fin 2))),
      ∀ u : EuclideanSpace ℂ (Fin 2), ‖u‖ = 1 →
        U (u ⊗ₜ[ℂ] (EuclideanSpace.single 0 (1 : ℂ)))
          = u ⊗ₜ[ℂ] u := by
  refine no_cloning (EuclideanSpace.single 0 (1 : ℂ)) (EuclideanSpace.single 1 (1 : ℂ)) ?_ ?_ ?_
  · simp
  · simp
  · simp [EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

end QC

