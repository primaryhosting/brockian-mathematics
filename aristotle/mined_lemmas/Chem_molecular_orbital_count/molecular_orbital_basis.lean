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

namespace Chem

/-- The molecular orbitals produced by the LCAO (Linear Combination of Atomic Orbitals)
method: given `n` atomic orbitals `phi j` in a complex vector space of states and a
coefficient matrix `C`, the `i`-th molecular orbital is `∑ j, C i j • phi j`. -/

theorem molecular_orbital_basis {n : ℕ} {V : Type*} [AddCommGroup V] [Module ℂ V]
    (phi : Fin n → V) (hphi : LinearIndependent ℂ phi)
    (C : Matrix (Fin n) (Fin n) ℂ) (hC : IsUnit C.det) :
    Nonempty (Module.Basis (Fin n) ℂ (Submodule.span ℂ (Set.range phi))) := by
  obtain ⟨hind, hspan, -⟩ := molecular_orbital_count phi hphi C hC
  exact ⟨hspan ▸ Module.Basis.span hind⟩

end Chem

