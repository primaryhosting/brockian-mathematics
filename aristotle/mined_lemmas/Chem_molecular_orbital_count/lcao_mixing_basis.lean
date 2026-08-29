/-
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- **LCAO dimension preservation.**

Model: the one-electron orbital space `V` over the (scalar) field `K` is spanned by a set of
`n` atomic orbitals `ao : Module.Basis (Fin n) K V` (linearly independent atomic orbitals).
A family of molecular orbitals `mo : ι → V` obtained by linear combination of atomic
orbitals is required to be linearly independent (`hli`) and to span the same orbital space
(`hsp`) — i.e. the LCAO mixing is invertible.

Conclusion: the index type of the molecular orbitals is in bijection with `Fin n`, i.e. the
LCAO procedure applied to `n` atomic orbitals yields *exactly* `n` molecular orbitals. -/

theorem lcao_mixing_basis
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (ao : Module.Basis (Fin n) K V)
    (c : Matrix (Fin n) (Fin n) K) (hc : IsUnit c.det)
    (mo : Fin n → V) (hmo : ∀ i, mo i = ∑ j, c i j • ao j) :
    ∃ B : Module.Basis (Fin n) K V, ⇑B = mo := by
  have h : LinearIndependent K mo ∧ Submodule.span K (Set.range mo) = ⊤ := by
    rw [Module.Basis.is_basis_iff_det ao, Module.Basis.det_apply]
    have hT : ao.toMatrix mo = c.transpose := by
      ext i j
      simp [Module.Basis.toMatrix_apply, hmo, Finsupp.single_apply, Matrix.transpose_apply]
    rw [hT, Matrix.det_transpose]
    exact hc
  exact ⟨Module.Basis.mk h.1 h.2.ge, funext fun i => Module.Basis.mk_apply _ _ i⟩

end Chem

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

