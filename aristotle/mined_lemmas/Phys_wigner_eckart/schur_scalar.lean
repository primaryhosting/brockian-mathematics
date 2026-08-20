/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Statement: Matrix elements of tensor operators factor into a Clebsch–Gordan × reduced element (Wigner–Eckart).
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

namespace Phys

open TensorProduct

variable {G : Type*} [Monoid G]

/-- `f` intertwines the representations `ρ` and `σ`. -/

theorem schur_scalar {V : Type*} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (ρ : Representation ℂ G V) (hirr : IsIrred ρ) (f : V →ₗ[ℂ] V)
    (hf : Intertwines ρ ρ f) : ∃ r : ℂ, ∀ v : V, f v = r • v := by
  obtain ⟨hnt, hsub⟩ := hirr
  haveI : Nontrivial V := hnt
  obtain ⟨r, hr⟩ := Module.End.exists_eigenvalue (K := ℂ) (V := V) f
  refine ⟨r, ?_⟩
  set S : Submodule ℂ V := Module.End.eigenspace f r with hS
  have hSinv : ∀ (g : G), ∀ v ∈ S, ρ g v ∈ S := by
    intro g v hv
    rw [hS, Module.End.mem_eigenspace_iff] at hv ⊢
    rw [hf g v, hv, map_smul]
  have hSne : S ≠ ⊥ := hr
  rcases hsub S hSinv with h | h
  · exact absurd h hSne
  · intro v
    have : v ∈ S := by rw [h]; trivial
    rw [hS, Module.End.mem_eigenspace_iff] at this
    exact this

section Abstract

variable {Vi Vf K : Type*}
  [AddCommGroup Vi] [Module ℂ Vi]
  [AddCommGroup Vf] [Module ℂ Vf] [FiniteDimensional ℂ Vf]
  [AddCommGroup K] [Module ℂ K]

/-- If the "coupled" space `Vi` splits equivariantly as `Vf ⊕ K` with `K` containing no
copy of `Vf`, then every intertwiner `Vi → Vf` is a scalar multiple of the projection onto
the `Vf`-summand. -/
