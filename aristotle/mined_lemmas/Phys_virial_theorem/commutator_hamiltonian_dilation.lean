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
