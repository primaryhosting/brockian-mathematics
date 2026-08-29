/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
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

/-!
## Mermin–Wagner: absence of continuous symmetry breaking in dimensions `d ≤ 2`

The mechanism behind the Mermin–Wagner theorem is an *energy–entropy* (spin-wave) estimate.
In a lattice system with a continuous internal symmetry, a configuration may be deformed by a
slowly varying, *finitely supported* rotation field `u : ℤ^d → ℝ`; to second order (which is
the relevant order, the first order term vanishing by the symmetry `θ ↦ -θ`) the free-energy
cost of the deformation at temperature `T` and coupling `J` is

  `(J / (2T)) * ∑_{⟨x,y⟩} (u x - u y)^2`,

i.e. `J / (2T)` times the *Dirichlet energy* of `u`.  Spontaneous breaking of the continuous
symmetry requires this cost to stay bounded away from zero when a fixed finite region is
rotated by a fixed angle `α` and the rotation is relaxed back to `0` at infinity; this
infimum is (up to the factor `J / (2T)`) the *capacity* of the region.

The theorem `Phys.mermin_wagner` below is exactly the statement that in dimension `d ≤ 2`
this cost vanishes: for every temperature `T > 0`, every coupling `J > 0`, every finite
region `A`, every rotation angle `α` and every `ε > 0`, there is a finitely supported
rotation field which rotates all of `A` by the full angle `α` at a free-energy cost less
than `ε`.  Equivalently: finite subsets of `ℤ^d` have zero capacity for `d ≤ 2` (`ℤ^d` is
recurrent/parabolic), so no continuous symmetry can be broken at any positive temperature.

The dimension enters through the divergence of the harmonic series: the shells
`{x : ‖x‖_∞ = s}` of `ℤ^d` with `d ≤ 2` contain `O(s)` points, so the harmonic profile
`u x = φ(‖x‖_∞)` used below has Dirichlet energy `O(1 / ∑_{s ≤ N} 1/s) → 0`.  In dimension
`d ≥ 3` shells contain `≍ s^{d-1}` points, the estimate fails, and indeed symmetry breaking
does occur.
-/

namespace Phys

variable {d : ℕ}

/-- The `i`-th unit vector of the lattice `ℤ^d`. -/

lemma abs_harm_sub_le {k m : ℕ} (hk : 1 ≤ k) (h1 : m ≤ k + 1) (h2 : k ≤ m + 1) :
    |harm m - harm k| ≤ 1 / (k : ℝ) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hcase : m = j ∨ m = j + 1 ∨ m = j + 2 := by omega
  have hj : (0 : ℝ) < (j : ℝ) + 1 := by positivity
  rcases hcase with rfl | rfl | rfl
  · rw [harm_succ]
    have h : harm m - (harm m + 1 / ((m : ℝ) + 1)) = -(1 / ((m : ℝ) + 1)) := by ring
    rw [h, abs_neg, abs_of_nonneg (by positivity)]
    push_cast
    exact le_refl _
  · simp
    positivity
  · rw [show j + 2 = (j + 1) + 1 from rfl, harm_succ (j + 1)]
    have h : harm (j + 1) + 1 / (((j : ℕ) + 1 : ℕ) + 1 : ℝ) - harm (j + 1)
        = 1 / ((j : ℝ) + 2) := by push_cast; ring
    rw [h, abs_of_nonneg (by positivity)]
    push_cast
    apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
    linarith

/-! ### The key counting estimate -/

/-- In dimension `d ≤ 2`, `∑_{0 < ‖x‖_∞ ≤ M} ‖x‖_∞^{-2}` grows only like the harmonic sum. -/
