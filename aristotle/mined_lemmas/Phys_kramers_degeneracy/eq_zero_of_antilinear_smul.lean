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

lemma eq_zero_of_antilinear_smul (T : Antilinear V) (hT : ∀ v : V, T (T v) = -v)
    (v : V) (c : ℂ) (hv : T v = c • v) : v = 0 := by
  have h1 : T (T v) = ((starRingEnd ℂ) c * c) • v := by
    rw [hv, T.map_smulₛₗ, hv, smul_smul]
  have h2 : ((starRingEnd ℂ) c * c) • v = -v := by rw [← h1, hT]
  have h3 : ((starRingEnd ℂ) c * c + 1) • v = 0 := by
    rw [add_smul, one_smul, h2, neg_add_cancel]
  rcases smul_eq_zero.mp h3 with h | h
  · exact absurd h (conj_mul_self_add_one_ne_zero c)
  · exact h

/-- The time-reversed state `T v` of an eigenvector `v` with **real** eigenvalue `μ` is again
an eigenvector with the same eigenvalue. -/
