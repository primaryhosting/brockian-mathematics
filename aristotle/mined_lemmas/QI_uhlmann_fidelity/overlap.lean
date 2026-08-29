import Mathlib

/-!
# Uhlmann Fidelity
Category: Frontier Qi
Target: QI.uhlmann_fidelity
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We work with finite-dimensional quantum systems, a state on `ℂⁿ` being described by a positive
semidefinite matrix `ρ : Matrix n n ℂ`.  Its fidelity with a second state `σ` is

`F(ρ, σ) = Tr √(√ρ σ √ρ)`,

which is `QI.fidelity`.

A *purification* of `ρ` in the doubled system `ℂⁿ ⊗ ℂⁿ` is a vector `u : n × n → ℂ` whose reduced
density matrix (partial trace over the second factor) is `ρ`; this is `QI.reducedDensity`.
`QI.uhlmann_fidelity` is Uhlmann's theorem: `F(ρ, σ)` is the *greatest* value of the overlap
`|⟪u, v⟫|` as `u` ranges over the purifications of `ρ` and `v` over those of `σ`.

The proof goes through the polar decomposition of a matrix (`QI.exists_unitary_polar`, proved
here from scratch by extending a linear isometry defined on a subspace) and the variational
characterisation of the trace norm (`QI.isGreatest_traceNorm`).
-/

open scoped InnerProductSpace MatrixOrder ComplexOrder BigOperators
open Matrix

namespace QI

/-! ### An auxiliary extension lemma for linear isometries -/

/-- If `f g : E →ₗ[ℂ] E` satisfy `‖g x‖ = ‖f x‖` for all `x`, then there is a linear isometry `V`
of `E` with `V ∘ f = g`.  This is the key step in the polar decomposition. -/

noncomputable def overlap (u v : n × n → ℂ) : ℂ := ∑ p, (starRingEnd ℂ) (u p) * v p

/-- The reduced density matrix on the first factor of a bipartite pure state of `ℂⁿ ⊗ ℂⁿ`,
i.e. the partial trace of `|v⟩⟨v|` over the second factor. -/
