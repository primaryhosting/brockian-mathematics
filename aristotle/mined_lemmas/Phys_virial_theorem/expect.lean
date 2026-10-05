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
