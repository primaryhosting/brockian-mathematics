/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped TensorProduct
open Representation

namespace Phys

variable {k G U V W : Type*} [Field k] [Group G]
  [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]

/-- The space of intertwining (`G`-equivariant) linear maps between two representations,
as a subspace of all linear maps. -/

theorem wigner_eckart_of_irreducible [IsAlgClosed k] {τ : Representation k G U}
    {ρ : Representation k G V} {σ : Representation k G W} [FiniteDimensional k W]
    [IsIrreducible (τ.tprod ρ)] [IsIrreducible σ]
    (CG T : (U ⊗[k] V) →ₗ[k] W)
    (hCG : CG ∈ intertwiners (τ.tprod ρ) σ) (hT : T ∈ intertwiners (τ.tprod ρ) σ)
    (hCG0 : CG ≠ 0) :
    ∃ red : k, T = red • CG ∧ ∀ (φ : W →ₗ[k] k) (u : U) (v : V),
      φ (T (u ⊗ₜ[k] v)) = red * φ (CG (u ⊗ₜ[k] v)) :=
  wigner_eckart rank_intertwiners_le_one CG T hCG hT hCG0

/-! ### A concrete instance, showing the hypotheses are not vacuous -/

section Concrete

variable (Γ : Type*) [Group Γ]

/-- The trivial one-dimensional complex representation of a group `Γ`. -/
