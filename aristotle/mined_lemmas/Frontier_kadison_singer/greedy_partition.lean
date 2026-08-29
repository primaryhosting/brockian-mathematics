import Mathlib
/-!
# Kadison Singer
Category: Frontier — Fields Medal Work
Target: Frontier.kadison_singer
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

/-!
## The statement

The Kadison–Singer problem (1959) asks whether every pure state on the atomic MASA
`ℓ^∞(ℕ) ⊆ B(ℓ²(ℕ))` extends uniquely to a state on `B(ℓ²(ℕ))`.  It was resolved
affirmatively by Marcus, Spielman and Srivastava, who proved **Weaver's conjecture `KS_r`**
by the method of *interlacing families of polynomials*:

> if `v₁, …, v_m ∈ ℂ^d` satisfy `∑ᵢ vᵢ vᵢ* = I` and `‖vᵢ‖² ≤ α` for all `i`, then there is a
> partition `{1,…,m} = S₁ ⊔ … ⊔ S_r` with `‖∑_{i ∈ S_j} vᵢ vᵢ*‖ ≤ (1/√r + √α)²` for all `j`.

We phrase the two operator-theoretic conditions through the associated quadratic forms, which
is equivalent (all the operators involved are positive semidefinite) and avoids committing to
a particular encoding of the operator norm:

* `∑ᵢ vᵢ vᵢ* = I`             ⟺  `∀ x, ∑ᵢ |⟪vᵢ, x⟫|² = ‖x‖²`;
* `‖∑_{i ∈ S} vᵢ vᵢ*‖ ≤ c`    ⟺  `∀ x, ∑_{i ∈ S} |⟪vᵢ, x⟫|² ≤ c ‖x‖²`.
-/

/-- **Weaver's `KS_r` statement** in dimension `d` with bound `α`: every isotropic family of
vectors in `ℂ^d` whose members have squared norm at most `α` can be partitioned into `r`
subfamilies, each of operator norm at most `(1/√r + √α)²`.

The proposition `∀ r α d, 0 < r → 0 ≤ α → WeaverKS r α d` is Weaver's conjecture, which is
equivalent to a positive solution of the Kadison–Singer problem and is the theorem of
Marcus–Spielman–Srivastava. -/

theorem greedy_partition {ι : Type} [Fintype ι] (r : ℕ) (hr : 0 < r) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) (α : ℝ) (hα0 : 0 ≤ α) (hα : ∀ i, a i ≤ α) :
    ∃ f : ι → Fin r, ∀ j : Fin r,
      ∑ i ∈ Finset.univ.filter (fun i => f i = j), a i ≤ (∑ i, a i) / r + α :=
  greedy_partition_finset r hr a ha α hα0 hα Finset.univ

/-- The elementary numerical inequality behind the `KS_r` bound: `1/r + α ≤ (1/√r + √α)²`. -/
