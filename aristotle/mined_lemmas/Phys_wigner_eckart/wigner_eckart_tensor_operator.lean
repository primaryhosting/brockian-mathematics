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

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped TensorProduct

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

namespace Phys

section

variable {G : Type*} [Group G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A complex representation is *irreducible* if the space is nontrivial and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/

theorem wigner_eckart_tensor_operator
    [FiniteDimensional ℂ Vj] [FiniteDimensional ℂ Vk]
    {ρ : Representation ℂ G Vj} {τ : Representation ℂ G Vk} {σ : Representation ℂ G W}
    (hρτ : IsIrrep (Representation.tprod ρ τ)) (hσ : IsIrrep σ)
    {T S : Vj ⊗[ℂ] Vk →ₗ[ℂ] W}
    (hT : Intertwines (Representation.tprod ρ τ) σ T)
    (hS : Intertwines (Representation.tprod ρ τ) σ S) (hS0 : S ≠ 0)
    {M Q M' : Type*} (bj : Module.Basis M ℂ Vj) (bk : Module.Basis Q ℂ Vk) (bW : Module.Basis M' ℂ W) :
    ∃ c : ℂ, ∀ (m : M) (q : Q) (m' : M'),
      bW.repr (T (bj m ⊗ₜ[ℂ] bk q)) m' = c * bW.repr (S (bj m ⊗ₜ[ℂ] bk q)) m' := by
  obtain ⟨c, hc⟩ := wigner_eckart hρτ hσ hT hS hS0
  exact ⟨c, fun m q m' =>
    hc ((Finsupp.lapply m').comp (bW.repr : W →ₗ[ℂ] (M' →₀ ℂ))) (bj m ⊗ₜ[ℂ] bk q)⟩

/-- Sanity check (non-vacuity): the hypotheses of `Phys.wigner_eckart` are satisfiable —
the one-dimensional trivial representation of any group is irreducible and the identity is a
nonzero intertwiner of it with itself. -/
