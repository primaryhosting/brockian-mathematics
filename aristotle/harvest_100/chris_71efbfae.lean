import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## The quantum virial theorem

For a bound stationary state `ψ` (a normalizable eigenvector of the Hamiltonian `H = T + V`)
one has

  `2⟨T⟩ = ⟨r·∇V⟩`.

The mathematical content of the statement is the following.  Let `D` be the generator of
dilations (`D = (r·p + p·r)/2` in the usual physical normalisation).  The canonical commutation
relations give

  `[T, D] = 2i T`,      `[V, D] = -i (r·∇V)`,

so that `[H, D] = i (2T - r·∇V)`.  On the other hand, the expectation value of any commutator
`[H, D]` in an eigenstate of a symmetric `H` vanishes (this is where stationarity and
boundedness of the state enter: the eigenvalue is real, and the two terms of the commutator
have the same expectation value).  Combining the two facts yields the virial theorem.

We formalise this in an arbitrary complex inner product space, with the operator `W` playing the
role of `r·∇V` and the two commutation relations as hypotheses; these are exactly the
kinematical input of the physical statement.
-/

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The expectation value `⟨ψ, A ψ⟩` of an operator `A` in the state `ψ`. -/
noncomputable def expect (A : E →ₗ[ℂ] E) (ψ : E) : ℂ := inner ℂ ψ (A ψ)

/-- An eigenvalue of a symmetric operator, on a nonzero eigenvector, is real. -/
theorem eigenvalue_isReal {Hop : E →ₗ[ℂ] E} {ψ : E} {En : ℂ}
    (hsymm : ∀ x y : E, inner ℂ (Hop x) y = inner ℂ x (Hop y))
    (hψ : ψ ≠ 0) (heig : Hop ψ = En • ψ) : (starRingEnd ℂ) En = En := by
  have h := hsymm ψ ψ
  rw [heig, inner_smul_left, inner_smul_right] at h
  have hnz : (inner ℂ ψ ψ : ℂ) ≠ 0 := by simpa [inner_self_eq_zero] using hψ
  field_simp at h
  exact h

/-- **Stationarity**: in an eigenstate of a symmetric operator `Hop`, the expectation value of
any commutator `[Hop, D]` vanishes. -/
theorem expect_commutator_eq_zero {Hop D : E →ₗ[ℂ] E} {ψ : E} {En : ℂ}
    (hsymm : ∀ x y : E, inner ℂ (Hop x) y = inner ℂ x (Hop y))
    (hψ : ψ ≠ 0) (heig : Hop ψ = En • ψ) :
    inner ℂ ψ (Hop (D ψ) - D (Hop ψ)) = 0 := by
  have hEn := eigenvalue_isReal hsymm hψ heig
  have h1 : inner ℂ ψ (Hop (D ψ)) = (starRingEnd ℂ) En * inner ℂ ψ (D ψ) := by
    rw [← hsymm ψ (D ψ), heig, inner_smul_left]
  have h2 : inner ℂ ψ (D (Hop ψ)) = En * inner ℂ ψ (D ψ) := by
    rw [heig, map_smul, inner_smul_right]
  rw [inner_sub_right, h1, h2, hEn, sub_self]

/-- The commutator of `Hop = T + V` with the dilation generator `D`, computed from the two
canonical relations `[T, D] = 2i T` and `[V, D] = -i W`. -/
theorem commutator_hamiltonian_dilation {T V D W : E →ₗ[ℂ] E} {ψ : E}
    (hTD : ∀ x : E, T (D x) - D (T x) = (2 * Complex.I) • T x)
    (hVD : ∀ x : E, V (D x) - D (V x) = (-Complex.I) • W x) :
    (T + V) (D ψ) - D ((T + V) ψ) = Complex.I • ((2 : ℂ) • T ψ - W ψ) := by
  have hsplit : (T + V) (D ψ) - D ((T + V) ψ)
      = (T (D ψ) - D (T ψ)) + (V (D ψ) - D (V ψ)) := by
    simp only [LinearMap.add_apply, map_add]; abel
  rw [hsplit, hTD ψ, hVD ψ]
  module

/-- **Quantum virial theorem.**  Let `Hop = T + V` be a symmetric Hamiltonian (kinetic energy `T`
plus potential `V`) on a complex inner product space, let `D` be the generator of dilations
obeying the canonical relations `[T, D] = 2i T` and `[V, D] = -i W` (where `W = r·∇V`), and let
`ψ ≠ 0` be a bound stationary state, i.e. an eigenvector of `Hop`.  Then

  `2⟨T⟩ = ⟨W⟩`,   that is   `2⟨T⟩ = ⟨r·∇V⟩`. -/
theorem virial_theorem {Hop T V D W : E →ₗ[ℂ] E} {ψ : E} {En : ℂ}
    (hsymm : ∀ x y : E, inner ℂ (Hop x) y = inner ℂ x (Hop y))
    (hψ : ψ ≠ 0) (heig : Hop ψ = En • ψ) (hH : Hop = T + V)
    (hTD : ∀ x : E, T (D x) - D (T x) = (2 * Complex.I) • T x)
    (hVD : ∀ x : E, V (D x) - D (V x) = (-Complex.I) • W x) :
    2 * expect T ψ = expect W ψ := by
  have hcomm : Hop (D ψ) - D (Hop ψ) = Complex.I • ((2 : ℂ) • T ψ - W ψ) := by
    rw [hH]; exact commutator_hamiltonian_dilation hTD hVD
  have hzero := expect_commutator_eq_zero (D := D) hsymm hψ heig
  rw [hcomm, inner_smul_right, inner_sub_right, inner_smul_right] at hzero
  have hdiff : (2 : ℂ) * expect T ψ - expect W ψ = 0 := by
    simpa [expect, sub_eq_zero] using (mul_eq_zero.1 hzero).resolve_left Complex.I_ne_zero
  linear_combination hdiff

/-- **Virial theorem for a homogeneous potential.**  If in addition the potential satisfies
`r·∇V = n V` (Euler's relation for a potential homogeneous of degree `n`, e.g. `n = -1` for the
Coulomb potential and `n = 2` for the harmonic oscillator), then `2⟨T⟩ = n⟨V⟩`. -/
theorem virial_theorem_homogeneous {Hop T V D W : E →ₗ[ℂ] E} {ψ : E} {En : ℂ} {n : ℂ}
    (hsymm : ∀ x y : E, inner ℂ (Hop x) y = inner ℂ x (Hop y))
    (hψ : ψ ≠ 0) (heig : Hop ψ = En • ψ) (hH : Hop = T + V)
    (hTD : ∀ x : E, T (D x) - D (T x) = (2 * Complex.I) • T x)
    (hVD : ∀ x : E, V (D x) - D (V x) = (-Complex.I) • W x)
    (hhom : W = n • V) :
    2 * expect T ψ = n * expect V ψ := by
  have h := virial_theorem hsymm hψ heig hH hTD hVD
  rw [h, hhom]
  simp [expect]

end Phys

#print axioms Phys.virial_theorem
#print axioms Phys.virial_theorem_homogeneous

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

