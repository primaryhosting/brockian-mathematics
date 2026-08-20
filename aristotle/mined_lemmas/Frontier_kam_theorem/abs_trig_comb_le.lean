import Mathlib

/-!
# Kam Theorem
Category: Frontier Physics
Target: Frontier.kam_theorem
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

set_option grind.warning false

namespace Frontier

variable {n : ℕ}

/-- Pairing of an integer covector `k` with a real vector `x`: `⟪k, x⟫ = ∑ i, k i * x i`. -/

lemma abs_trig_comb_le (A B x : ℝ) :
    |A * Real.cos x + B * Real.sin x| ≤ |A| + |B| := by
  have h1 : |A * Real.cos x| ≤ |A| := by
    rw [abs_mul]
    nlinarith [Real.abs_cos_le_one x, abs_nonneg A, abs_nonneg (Real.cos x)]
  have h2 : |B * Real.sin x| ≤ |B| := by
    rw [abs_mul]
    nlinarith [Real.abs_sin_le_one x, abs_nonneg B, abs_nonneg (Real.sin x)]
  have := abs_add_le (A * Real.cos x) (B * Real.sin x)
  linarith

/-! ### The main theorem -/

/--
**KAM theorem (persistence of invariant tori), exact version for an isochronous
integrable Hamiltonian with trigonometric-polynomial perturbation.**

Let `ω ∈ ℝⁿ` be a Diophantine frequency vector: `|⟪k, ω⟫| ≥ γ / ‖k‖^τ` for all nonzero integer
vectors `k`. Consider the nearly integrable Hamiltonian
`H_ε(θ, I) = ⟪ω, I⟫ + ε P(θ)` on `𝕋ⁿ × ℝⁿ`, where `P` is a mean-zero trigonometric polynomial
(finite mode set `K` not containing `0`). For `ε = 0` the torus `{I = 0}` is invariant and
carries the quasi-periodic flow `θ(t) = θ₀ + tω`.

Then for **every** `ε` the invariant torus persists: there is a family of embeddings
`θ ↦ (θ, G ε θ)` of `𝕋ⁿ` (i.e. `G ε` is `ℤⁿ`-periodic) which is `O(ε)`-close to the
unperturbed torus `{I = 0}`, uniformly in `ε` and `θ`, and which is invariant under the flow of
`H_ε` with the *same* quasi-periodic dynamics `θ(t) = θ₀ + tω` on it.

The Diophantine hypothesis enters through the small divisors `⟪k, ω⟫` used to solve the
homological equation `∂_ω u = P`.
-/
