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

import Mathlib

/-!
# Variational Bound
Category: Quantum Physics
Target: QPhys.variational_bound
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

/-- **Variational principle (ground-state bound).**

Let `H` be a Hamiltonian on a complex inner product space `E` which is diagonalized by an
orthonormal basis `b` with real eigenvalues `ev` (`H (b i) = ev i • b i`), and let `E₀` be a
lower bound for the spectrum (`E₀ ≤ ev i` for every `i`).  Then for every nonzero state `ψ`
the Rayleigh quotient satisfies
`⟨ψ|H|ψ⟩ / ⟨ψ|ψ⟩ ≥ E₀`,
where `⟨ψ|H|ψ⟩` is the (real part of the) inner product `⟪ψ, H ψ⟫` and `⟨ψ|ψ⟩ = ‖ψ‖ ^ 2`. -/

theorem variational_bound_min_eigenvalue {n : Type*} [Fintype n] [Nonempty n] {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] (b : OrthonormalBasis n ℂ E) (H : E →ₗ[ℂ] E)
    (ev : n → ℝ) (hev : ∀ i, H (b i) = (ev i : ℂ) • b i) (ψ : E) (hψ : ψ ≠ 0) :
    Finset.univ.inf' Finset.univ_nonempty ev ≤ (inner ℂ ψ (H ψ)).re / ‖ψ‖ ^ 2 :=
  variational_bound b H ev hev _ (fun i => Finset.inf'_le ev (Finset.mem_univ i)) ψ hψ

end QPhys

