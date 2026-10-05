import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
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

/-! ## Setup

A quantum system is modelled by a complex vector space `V` (the space of states),
a `ℂ`-linear Hamiltonian `A : V →ₗ[ℂ] V`, and a *time-reversal* operator `T`, which is
**antilinear** (conjugate-linear), i.e. a semilinear map for the ring homomorphism
`starRingEnd ℂ` (complex conjugation).

Half-integer spin is encoded by the relation `T ∘ T = -1`, and time-reversal invariance
of the dynamics by the commutation relation `T ∘ A = A ∘ T`.

Kramers' theorem: every (real) energy level of such a system is at least doubly degenerate.
-/

section

variable {V : Type*} [AddCommGroup V] [Module ℂ V]

/-- An antilinear (conjugate-linear) endomorphism of a complex vector space. -/
abbrev Antilinear (V : Type*) [AddCommGroup V] [Module ℂ V] := V →ₛₗ[starRingEnd ℂ] V

/-- For a complex number `c`, the quantity `conj c * c + 1` is never zero: its real part
is `‖c‖ ^ 2 + 1 > 0`. -/

lemma mem_eigenspace_apply (T : Antilinear V) (A : V →ₗ[ℂ] V)
    (hcomm : ∀ v : V, T (A v) = A (T v)) (μ : ℝ) (v : V)
    (hv : v ∈ Module.End.eigenspace A (μ : ℂ)) :
    T v ∈ Module.End.eigenspace A (μ : ℂ) := by
  rw [Module.End.mem_eigenspace_iff] at hv ⊢
  have : T (A v) = ((μ : ℂ)) • T v := by
    rw [hv, T.map_smulₛₗ]
    simp
  rw [hcomm] at this
  exact this

/-- A nonzero eigenvector `v` and its time reverse `T v` are linearly independent
(the *Kramers pair*). -/
