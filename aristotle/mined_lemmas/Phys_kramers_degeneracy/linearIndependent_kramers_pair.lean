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

lemma linearIndependent_kramers_pair (T : Antilinear V) (hT : ∀ v : V, T (T v) = -v)
    (v : V) (hv : v ≠ 0) : LinearIndependent ℂ ![v, T v] := by
  rw [LinearIndependent.pair_iff]
  intro s t hst
  by_cases ht : t = 0
  · subst ht
    simp only [zero_smul, add_zero] at hst
    rcases smul_eq_zero.mp hst with h | h
    · exact ⟨h, rfl⟩
    · exact absurd h hv
  · exfalso
    have h1 : t • T v = (-s) • v := by
      rw [neg_smul, eq_neg_iff_add_eq_zero, add_comm]; exact hst
    have h2 : T v = (-s / t) • v := by
      have := congrArg (fun x => t⁻¹ • x) h1
      simpa [smul_smul, inv_mul_cancel₀ ht, div_eq_inv_mul] using this
    exact hv (eq_zero_of_antilinear_smul T hT v (-s / t) h2)

end

/-- **Kramers degeneracy.**

Let `V` be a complex vector space of states, `A : V →ₗ[ℂ] V` a Hamiltonian, and
`T : V →ₛₗ[starRingEnd ℂ] V` an antilinear time-reversal operator satisfying

* `T ∘ T = -1` (half-integer spin), and
* `T ∘ A = A ∘ T` (time-reversal invariance).

Then every real energy level `μ` which actually occurs (i.e. whose eigenspace is nonzero)
has degeneracy at least `2`: the eigenspace has rank at least `2`, spanned in part by a
*Kramers pair* `v`, `T v`. -/
