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

theorem mermin_wagner_magnetization {d : ℕ} (hd : d ≤ 2) (β : ℝ) (hβ : 0 ≤ β) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      ∀ (J : Site d L → Site d L → ℝ) (W : (Site d L → Spin) → ℝ) (x₀ : Site d L),
        (∀ x y, |J x y| ≤ 1) →
        (∀ x y : Site d L, ¬ Adj (x : Fin d → ℤ) (y : Fin d → ℤ) → J x y = 0) →
        Continuous W →
        (∀ θ θ' : Site d L → Spin,
          (∀ x : Site d L, latticeNorm (x : Fin d → ℤ) = L → θ x = θ' x) → W θ = W θ') →
        (x₀ : Fin d → ℤ) = 0 →
        Real.sqrt ((gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.cos (θ x₀)) ^ 2
            + (gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.sin (θ x₀)) ^ 2) ≤ ε := by
  obtain ⟨L₀, hL₀⟩ := mermin_wagner hd β hβ (ε := ε / 2) (by linarith)
  refine ⟨L₀, fun L hL J W x₀ hJ1 hJ0 hWc hW hx₀ => ?_⟩
  have hcos := hL₀ L hL J W 0 x₀ hJ1 hJ0 hWc hW hx₀
  have hsin := hL₀ L hL J W (((Real.pi / 2 : ℝ) : Spin)) x₀ hJ1 hJ0 hWc hW hx₀
  simp only [sub_zero] at hcos
  have hrw : (fun θ : Site d L → Spin =>
      Real.Angle.cos ((θ x₀ - ((Real.pi / 2 : ℝ) : Spin) : Spin)))
      = fun θ : Site d L → Spin => Real.Angle.sin (θ x₀) := by
    funext θ
    exact Real.Angle.cos_sub_pi_div_two (θ x₀)
  rw [hrw] at hsin
  set a := gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.cos (θ x₀)
  set b := gibbsAvg β (xyHamiltonian J W) fun θ => Real.Angle.sin (θ x₀)
  have hle : Real.sqrt (a ^ 2 + b ^ 2) ≤ |a| + |b| := by
    rw [show |a| + |b| = Real.sqrt ((|a| + |b|) ^ 2) by rw [Real.sqrt_sq (by positivity)]]
    apply Real.sqrt_le_sqrt
    nlinarith [abs_nonneg a, abs_nonneg b, sq_abs a, sq_abs b]
  linarith

end Phys

