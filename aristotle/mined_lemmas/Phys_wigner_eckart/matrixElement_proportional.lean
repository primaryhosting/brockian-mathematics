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

open scoped TensorProduct

variable {G : Type*} [Group G]
variable {V W : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/-- A (complex) representation is *irreducible* if the space is nontrivial and the only
subspaces invariant under the group action are `⊥` and `⊤`. -/

theorem matrixElement_proportional [FiniteDimensional ℂ V] {ρ : Representation ℂ G V}
    {σ : Representation ℂ G W} (hρ : IsIrrep ρ) (hσ : IsIrrep σ)
    {ι κ : Type*} (bV : Module.Basis ι ℂ V) (bW : Module.Basis κ ℂ W)
    {T T' : V →ₗ[ℂ] W} (hT : Intertwines ρ σ T) (hT' : Intertwines ρ σ T') (hT'0 : T' ≠ 0) :
    ∃ c : ℂ, ∀ (m' : κ) (m : ι),
      bW.repr (T (bV m)) m' = c * bW.repr (T' (bV m)) m' := by
  obtain ⟨c, rfl⟩ := exists_smul_of_intertwines hρ hσ hT' hT'0 hT
  exact ⟨c, fun m' m => by simp [smul_eq_mul]⟩

/-- Non-vacuity check: the trivial one-dimensional representation is irreducible, so the
hypotheses of `Phys.wigner_eckart` are satisfiable. -/
