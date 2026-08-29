import Mathlib

/-!
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
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

namespace Chem

/-- The space of molecular orbitals produced by the LCAO (Linear Combination of Atomic
Orbitals) method from a family of atomic orbitals `chi : Fin n → H`: it is the set of all
linear combinations `∑ i, c i • chi i` of the atomic orbitals, i.e. their complex span
inside the one-electron Hilbert space `H`. -/

theorem card_molecular_orbital_basis {H : Type*} [AddCommGroup H] [Module ℂ H]
    {n : ℕ} (chi : Fin n → H) (hchi : LinearIndependent ℂ chi)
    {ι : Type*} [Fintype ι] (mo : Module.Basis ι ℂ (lcaoSpace chi)) :
    Fintype.card ι = n := by
  rw [← Module.finrank_eq_card_basis mo]
  exact molecular_orbital_count chi hchi

end Chem

