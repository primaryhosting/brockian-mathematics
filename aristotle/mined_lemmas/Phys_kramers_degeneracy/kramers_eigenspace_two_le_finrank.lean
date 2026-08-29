import Mathlib

/-!
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace ComplexConjugate

namespace Phys

/-- **Kramers degeneracy.**

Setting: a complex inner product space `V` (the state space), a time-reversal operator
`Θ : V → V` which is *antiunitary* (conjugate-linear, `Θ (c • x) = conj c • Θ x`, and
`⟪Θ x, Θ y⟫ = ⟪y, x⟫`) and satisfies `Θ² = -1`, the hallmark of **half-integer spin**.
The Hamiltonian `H` is time-reversal invariant: `Θ ∘ H = H ∘ Θ`.

Conclusion: for any eigenvector `v ≠ 0` of `H` with (real) energy `E`, the Kramers partner
`Θ v` is an eigenvector with the *same* energy `E`, it is orthogonal to `v`, and the pair
`v, Θ v` is linearly independent — i.e. the level `E` is (at least) doubly degenerate.

The additivity of `Θ` is not needed: conjugate-homogeneity together with the antiunitarity
relation on inner products already forces the conclusion. -/

theorem kramers_eigenspace_two_le_finrank
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V]
    (Θ : V → V)
    (hsmul : ∀ (c : ℂ) (x : V), Θ (c • x) = (starRingEnd ℂ) c • Θ x)
    (hinner : ∀ x y : V, ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hsq : ∀ x : V, Θ (Θ x) = -x)
    (H : V →ₗ[ℂ] V) (hcomm : ∀ x : V, Θ (H x) = H (Θ x))
    (E : ℝ) (v : V) (hv : v ≠ 0) (heig : H v = (E : ℂ) • v) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace H (E : ℂ)) := by
  obtain ⟨hH, -, hind⟩ := kramers_degeneracy Θ hsmul hinner hsq H hcomm E v hv heig
  set W := Module.End.eigenspace H (E : ℂ)
  have hvW : v ∈ W := Module.End.mem_eigenspace_iff.2 heig
  have hwW : Θ v ∈ W := Module.End.mem_eigenspace_iff.2 hH
  have h : LinearIndependent ℂ ![(⟨v, hvW⟩ : W), ⟨Θ v, hwW⟩] := by
    apply LinearIndependent.of_comp W.subtype
    convert hind using 1
    ext i
    fin_cases i <;> rfl
  simpa using h.fintype_card_le_finrank

end Phys

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

