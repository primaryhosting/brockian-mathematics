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
theorem kramers_degeneracy
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    (Θ : V → V)
    (hsmul : ∀ (c : ℂ) (x : V), Θ (c • x) = (starRingEnd ℂ) c • Θ x)
    (hinner : ∀ x y : V, ⟪Θ x, Θ y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hsq : ∀ x : V, Θ (Θ x) = -x)
    (H : V →ₗ[ℂ] V) (hcomm : ∀ x : V, Θ (H x) = H (Θ x))
    (E : ℝ) (v : V) (hv : v ≠ 0) (heig : H v = (E : ℂ) • v) :
    H (Θ v) = (E : ℂ) • Θ v ∧ ⟪v, Θ v⟫_ℂ = 0 ∧ LinearIndependent ℂ ![v, Θ v] := by
  -- The Kramers partner is nonzero, since `Θ (Θ v) = -v ≠ 0`.
  have hΘv : Θ v ≠ 0 := by
    intro h
    have h2 := hsq v
    rw [h] at h2
    have h0 : Θ (0 : V) = 0 := by simpa using hsmul 0 v
    rw [h0] at h2
    exact hv (by simpa using h2.symm)
  -- `Θ v` is an eigenvector for the same (real) energy.
  have hH : H (Θ v) = (E : ℂ) • Θ v := by
    have h3 := hcomm v
    rw [heig, hsmul] at h3
    simpa using h3.symm
  -- Antiunitarity plus `Θ² = -1` force `⟪Θ v, v⟫ = -⟪Θ v, v⟫`.
  have horth : ⟪v, Θ v⟫_ℂ = 0 := by
    have h1 := hinner v (Θ v)
    rw [hsq v, inner_neg_right] at h1
    have h4 : ⟪Θ v, v⟫_ℂ = 0 := by linear_combination (-1 / 2 : ℂ) * h1
    have h5 := congrArg (starRingEnd ℂ) h4
    rw [inner_conj_symm] at h5
    simpa using h5
  refine ⟨hH, horth, ?_⟩
  rw [LinearIndependent.pair_iff]
  intro s t hst
  have h2 : ⟪v, s • v + t • Θ v⟫_ℂ = 0 := by rw [hst, inner_zero_right]
  rw [inner_add_right, inner_smul_right, inner_smul_right, horth] at h2
  have hvv : ⟪v, v⟫_ℂ ≠ 0 := by simpa [inner_self_eq_zero] using hv
  have hs : s = 0 := by
    have h6 : s * ⟪v, v⟫_ℂ = 0 := by linear_combination h2
    rcases mul_eq_zero.1 h6 with h | h
    · exact h
    · exact absurd h hvv
  subst hs
  simp only [zero_smul, zero_add] at hst
  rcases smul_eq_zero.1 hst with h | h
  · exact ⟨rfl, h⟩
  · exact absurd h hΘv

/-- Dimensional form of Kramers degeneracy: in finite dimensions, every energy level of a
time-reversal-invariant half-integer-spin Hamiltonian has eigenspace of dimension at least `2`. -/
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

