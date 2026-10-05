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

theorem rank_intertwiners_trivial_le_one :
    Module.rank ℂ (intertwiners ((trivialRep Γ).tprod (trivialRep Γ)) (trivialRep Γ)) ≤ 1 := by
  have h0 :
      Module.rank ℂ (intertwiners ((trivialRep Γ).tprod (trivialRep Γ)) (trivialRep Γ))
        ≤ Module.rank ℂ ((ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ) :=
    Submodule.rank_le _
  refine le_trans h0 ?_
  have h : Module.finrank ℂ ((ℂ ⊗[ℂ] ℂ) →ₗ[ℂ] ℂ) = 1 := by
    rw [Module.finrank_linearMap]; simp
  rw [← Module.finrank_eq_rank, h]
  norm_num

/-- The canonical multiplication map `ℂ ⊗ ℂ → ℂ` is an intertwiner of trivial representations;
it plays the role of the Clebsch–Gordan map in this example. -/
