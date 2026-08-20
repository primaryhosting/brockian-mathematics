/-
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (The header above is repeated below as a module docstring; Lean requires `import` commands to
-- precede any module docstring.)

import Mathlib

/-!
# Mermin Wagner
Category: Frontier Phys
Target: Phys.mermin_wagner
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## What is formalized

We formalize the Mermin–Wagner theorem for the classical XY model, the standard model with a
continuous internal symmetry group (rotations of the spin circle `Spin = ℝ / 2πℤ`).

*The model.*  Sites are the lattice points of the box `Λ_L = {x ∈ ℤ^d : ‖x‖_∞ ≤ L}`; a
configuration assigns a spin angle to each site; the a priori measure is the uniform (Haar)
measure on `Λ_L → Spin`.  The energy is
`H(θ) = - ∑_{x,y} J x y * cos (θ x - θ y) + W θ`,
where `J` is an arbitrary nearest-neighbour coupling of strength at most `1` and `W` is an
arbitrary continuous boundary term depending only on the spins of the outermost shell of the box
(this encodes an arbitrary boundary condition, possibly strongly favouring one direction).
The thermal average of an observable is `gibbsAvg β H f`.

*The theorem* (`Phys.mermin_wagner`).  For `d ≤ 2`, any `β = 1/T < ∞` and any `ε > 0`, there is
`L₀` such that for all `L ≥ L₀` the magnetization at the centre of the box in any direction `c`
satisfies `|⟨cos (θ x₀ - c)⟩| ≤ ε`, uniformly in the coupling and in the boundary condition:
there is no spontaneous breaking of the rotation symmetry.  `Phys.mermin_wagner_magnetization`
restates this for the magnetization vector.

*The proof* is the spin-wave (twisting) argument.  Twisting a configuration by a slowly varying
radial profile `a` which equals `π` at the centre and `0` on the boundary shell costs, in the
symmetrized sense, at most the Dirichlet energy `K` of the profile, and one deduces from
`H(θ+a) + H(θ-a) ≤ 2 H(θ) + K` together with the arithmetic–geometric mean inequality that
`|magnetization| ≤ β K / 2`.  In dimension `d ≤ 2` the profile built from partial sums of the
harmonic series has Dirichlet energy `O(1 / harm L) → 0`, because the number of sites at distance
`r` grows at most like `r`, whereas the harmonic series diverges.
-/

open scoped BigOperators
open scoped Real
open MeasureTheory

set_option maxHeartbeats 1000000

namespace Phys

instance : Fact (0 < 2 * Real.pi) := ⟨by positivity⟩

/-- The single–spin space: the circle `ℝ / 2πℤ`.  The continuous internal symmetry group of the
model is this circle acting on itself by rotations. -/
abbrev Spin := AddCircle (2 * Real.pi)

/-! ## Part 1: an abstract twisting (spin–wave) inequality -/

section Abstract

variable {V : Type*} [Fintype V]

/-- Every continuous function on the (compact) configuration space is integrable. -/

lemma twist_ineq (β : ℝ) (hβ : 0 ≤ β) (H : (V → Spin) → ℝ) (hH : Continuous H)
    (a : V → Spin) (K : ℝ) (hK : ∀ θ, H (θ + a) + H (θ - a) ≤ 2 * H θ + K)
    (f : (V → Spin) → ℝ) (hf : Continuous f) (hf0 : ∀ θ, 0 ≤ f θ) :
    2 * Real.exp (-(β * K) / 2) * ∫ θ, f θ * Real.exp (-β * H θ) ≤
      (∫ θ, f (θ + a) * Real.exp (-β * H θ)) + (∫ θ, f (θ - a) * Real.exp (-β * H θ)) := by
  have e1 : (∫ θ, f (θ + a) * Real.exp (-β * H θ)) = ∫ θ, f θ * Real.exp (-β * H (θ - a)) := by
    have := integral_add_right_eq_self (μ := (volume : Measure (V → Spin)))
      (fun θ : V → Spin => f θ * Real.exp (-β * H (θ - a))) a
    simpa using this
  have e2 : (∫ θ, f (θ - a) * Real.exp (-β * H θ)) = ∫ θ, f θ * Real.exp (-β * H (θ + a)) := by
    have := integral_add_right_eq_self (μ := (volume : Measure (V → Spin)))
      (fun θ : V → Spin => f θ * Real.exp (-β * H (θ + a))) (-a)
    simpa [sub_eq_add_neg] using this
  rw [e1, e2]
  have hc1 : Continuous fun θ : V → Spin => f θ * Real.exp (-β * H (θ - a)) := by fun_prop
  have hc2 : Continuous fun θ : V → Spin => f θ * Real.exp (-β * H (θ + a)) := by fun_prop
  have hc0 : Continuous fun θ : V → Spin =>
      2 * Real.exp (-(β * K) / 2) * (f θ * Real.exp (-β * H θ)) := by fun_prop
  rw [← integral_add (cont_integrable _ hc1) (cont_integrable _ hc2), ← integral_const_mul]
  refine integral_mono (cont_integrable _ hc0) (cont_integrable _ (hc1.add hc2)) ?_
  intro θ
  have h1 : 2 * Real.exp (-(β * K) / 2) * Real.exp (-β * H θ) ≤
      Real.exp (-β * H (θ - a)) + Real.exp (-β * H (θ + a)) := by
    refine le_trans ?_ (exp_amgm (-β * H (θ - a)) (-β * H (θ + a)))
    rw [mul_assoc, ← Real.exp_add]
    have hle : -(β * K) / 2 + -β * H θ ≤ (-β * H (θ - a) + -β * H (θ + a)) / 2 := by
      nlinarith [hK θ]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 hle) (by norm_num)
  have h2 := mul_le_mul_of_nonneg_left h1 (hf0 θ)
  simp only []
  nlinarith [h2]

