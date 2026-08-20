/-
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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

/-- **LCAO dimension preservation.**

In the Linear Combination of Atomic Orbitals (LCAO) method, the molecular orbitals are the
elements of the span of the `n` atomic orbitals `chi 0, …, chi (n-1)` inside the one-electron
state space `H` over the field of scalars `ℂ`.  If the atomic orbitals are linearly independent,
then this space of molecular orbitals has dimension exactly `n`: combining `n` atomic orbitals
yields exactly `n` molecular orbitals.

This is `finrank_span_eq_card` from Mathlib, specialized to a family indexed by `Fin n`. -/

theorem molecular_orbital_count
    {H : Type*} [AddCommGroup H] [Module ℂ H] {n : ℕ}
    (chi : Fin n → H) (hchi : LinearIndependent ℂ chi) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range chi)) = n := by
  rw [finrank_span_eq_card hchi, Fintype.card_fin]

/-- The same statement packaged as a basis: the `n` linearly independent atomic orbitals form a
basis of the space of molecular orbitals they span, indexed by `Fin n`. -/
