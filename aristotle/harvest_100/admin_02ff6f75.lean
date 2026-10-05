import Mathlib

/-!
# Pauli Exclusion Antisym
Category: Quantum Physics
Target: QPhys.pauli_exclusion_antisym
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

namespace QPhys

variable {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup W] [Module K W]

/-- The (unnormalized) antisymmetric two-fermion state built from the two
single-particle states `u` and `f`: the Slater determinant
`u ⊗ f - f ⊗ u` inside the two-particle space `V ⊗ V`. -/
noncomputable def slater (u f : V) : V ⊗[K] V := u ⊗ₜ[K] f - f ⊗ₜ[K] u

/-- The two-fermion state is antisymmetric under exchange of the two particles. -/
theorem slater_swap (u f : V) : slater (K := K) f u = - slater (K := K) u f := by
  simp [slater]

/-- **Pauli exclusion principle.** A two-fermion antisymmetric state whose two
single-particle states coincide is the zero state. -/
theorem pauli_exclusion_antisym (u : V) : slater (K := K) u u = 0 :=
  sub_self _

/-- More generally, the antisymmetric two-fermion state vanishes whenever the two
single-particle states are proportional. -/
theorem slater_smul_left (c : K) (f : V) : slater (K := K) (c • f) f = 0 := by
  simp [slater, TensorProduct.smul_tmul']

/-- Abstract form of the Pauli exclusion principle: any antisymmetric bilinear
two-particle wavefunction vanishes when both particles occupy the same
single-particle state (in characteristic `≠ 2`). -/
theorem pauli_exclusion_antisym_bilinear (h2 : (2 : K) ≠ 0)
    (T : V →ₗ[K] V →ₗ[K] W) (hT : ∀ x y : V, T x y = - T y x) (u : V) :
    T u u = 0 := by
  have h : T u u + T u u = 0 := by
    nth_rewrite 1 [hT u u]
    exact neg_add_cancel _
  have h' : (2 : K) • (T u u) = 0 := by
    rw [two_smul]; exact h
  rcases smul_eq_zero.mp h' with h'' | h''
  · exact absurd h'' h2
  · exact h''

end QPhys

