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

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/-- The space of molecular orbitals obtained by the LCAO (linear combination of atomic
orbitals) procedure from a family `ao` of atomic orbitals: it is the span of the atomic
orbitals inside the ambient one-electron state space `V`. -/
def moSpace {n : ℕ} (ao : Fin n → V) : Submodule K V :=
  Submodule.span K (Set.range ao)

/-- The LCAO map: a tuple of coefficients `c : Fin n → K` is sent to the linear combination
`∑ i, c i • ao i` of the atomic orbitals. -/
noncomputable def lcao {n : ℕ} (ao : Fin n → V) : (Fin n → K) →ₗ[K] V :=
  Fintype.linearCombination K ao

@[simp] theorem lcao_apply {n : ℕ} (ao : Fin n → V) (c : Fin n → K) :
    lcao (K := K) ao c = ∑ i, c i • ao i := rfl

/-- The range of the LCAO map is exactly the molecular-orbital space. -/
theorem range_lcao {n : ℕ} (ao : Fin n → V) :
    LinearMap.range (lcao (K := K) ao) = moSpace (K := K) ao := by
  simp [moSpace, lcao]

/-- If the atomic orbitals are linearly independent, the LCAO map is injective:
distinct coefficient tuples give distinct molecular orbitals. -/
theorem lcao_injective {n : ℕ} {ao : Fin n → V} (h : LinearIndependent K ao) :
    Function.Injective (lcao (K := K) ao) := by
  simpa [lcao] using h.fintypeLinearCombination_injective

/-- **Molecular orbital count.** The LCAO procedure applied to `n` linearly independent
atomic orbitals produces a space of molecular orbitals of dimension exactly `n`:
`n` atomic orbitals yield `n` molecular orbitals (dimension preservation). -/
theorem molecular_orbital_count {n : ℕ} {ao : Fin n → V} (h : LinearIndependent K ao) :
    Module.finrank K (moSpace (K := K) ao) = n := by
  simpa [moSpace] using (finrank_span_eq_card (R := K) h)

/-- A basis of the molecular-orbital space indexed by the atomic orbitals: each atomic
orbital contributes exactly one molecular orbital. -/
noncomputable def moBasis {n : ℕ} {ao : Fin n → V} (h : LinearIndependent K ao) :
    Module.Basis (Fin n) K (moSpace (K := K) ao) :=
  Module.Basis.span h

/-- The coefficient space `Fin n → K` of LCAO coefficients is linearly isomorphic to the
molecular-orbital space, when the atomic orbitals are linearly independent. -/
noncomputable def lcaoEquiv {n : ℕ} {ao : Fin n → V} (h : LinearIndependent K ao) :
    (Fin n → K) ≃ₗ[K] moSpace (K := K) ao :=
  (LinearEquiv.ofInjective _ (lcao_injective h)).trans
    (LinearEquiv.ofEq _ _ (range_lcao ao))

#print axioms Chem.molecular_orbital_count

end Chem

