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

theorem one_div_add_le_sq_sqrt_add_sqrt (r : ℕ) (α : ℝ) (hα : 0 ≤ α) (hrR : (0 : ℝ) < r) :
    1 / (r : ℝ) + α ≤ (1 / Real.sqrt r + Real.sqrt α) ^ 2 := by
  have hsr : 0 < Real.sqrt (r : ℝ) := Real.sqrt_pos.mpr hrR
  have hsr2 : Real.sqrt (r : ℝ) ^ 2 = (r : ℝ) := Real.sq_sqrt hrR.le
  have hα2 : Real.sqrt α ^ 2 = α := Real.sq_sqrt hα
  have expand : (1 / Real.sqrt r + Real.sqrt α) ^ 2
      = (1 / Real.sqrt r) ^ 2 + 2 * (1 / Real.sqrt r) * Real.sqrt α + Real.sqrt α ^ 2 := by ring
  rw [expand, div_pow, one_pow, hsr2, hα2]
  have h0 : 0 ≤ 2 * (1 / Real.sqrt r) * Real.sqrt α := by positivity
  linarith

/-!
## The base case `r = 1`
-/

/-- The base case `r = 1` of Weaver's `KS_r`, in every dimension: the trivial partition works,
because `(1/√1 + √α)² ≥ 1`. -/
