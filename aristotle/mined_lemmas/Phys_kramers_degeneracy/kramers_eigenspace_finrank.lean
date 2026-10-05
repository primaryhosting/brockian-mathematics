/-
# Kramers Degeneracy
Category: Frontier Phys
Target: Phys.kramers_degeneracy
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; it is repeated verbatim as the module docstring after the imports.)

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
open scoped InnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Phys

/-!
## Setup

We model a quantum system by a complex inner product space `E`.

* The time-reversal operator is an **antiunitary** map `T`, i.e. a conjugate-linear map
  (`T : E →ₗ⋆[ℂ] E`) preserving the inner product up to the conjugation coming from
  `⟪T x, T y⟫ = ⟪y, x⟫`.
* **Half-integer spin** is encoded by the relation `T ∘ T = -1` (for integer spin one has
  `T ∘ T = +1` instead, and then no degeneracy follows).
* **Time-reversal invariance** of the Hamiltonian `A` is the commutation relation `A ∘ T = T ∘ A`.
* Energy levels are real, so an eigenvalue is written `(μ : ℝ)` viewed in `ℂ`.

The conclusion is Kramers' theorem: for every eigenvector `v ≠ 0` of `A` with eigenvalue `μ`,
the vector `T v` is a *further* eigenvector with the same eigenvalue, is nonzero, is orthogonal
to `v`, and `{v, T v}` is linearly independent — so the level `μ` is (at least) doubly degenerate.
-/

/-- **Kramers degeneracy.**  In a time-reversal invariant system with half-integer spin
(`T` antiunitary with `T ∘ T = -1`, commuting with the Hamiltonian `A`), every eigenvector
`v ≠ 0` of `A` with (real) eigenvalue `μ` gives rise to a second, orthogonal eigenvector
`T v` for the same eigenvalue; in particular `v` and `T v` are linearly independent, so the
energy level `μ` is at least doubly degenerate. -/

theorem kramers_eigenspace_finrank
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]
    (T : E →ₗ⋆[ℂ] E) (A : E →ₗ[ℂ] E) (μ : ℝ) (v : E)
    (hTinner : ∀ x y, ⟪T x, T y⟫_ℂ = ⟪y, x⟫_ℂ)
    (hT2 : ∀ x, T (T x) = -x)
    (hcomm : ∀ x, A (T x) = T (A x))
    (hv : v ≠ 0) (hAv : A v = (μ : ℂ) • v) :
    2 ≤ Module.finrank ℂ (Module.End.eigenspace A (μ : ℂ)) := by
  have h := kramers_eigenspace_rank T A μ v hTinner hT2 hcomm hv hAv
  rw [← Module.finrank_eq_rank] at h
  exact_mod_cast h

end Phys

