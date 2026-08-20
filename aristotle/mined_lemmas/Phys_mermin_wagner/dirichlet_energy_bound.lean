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

lemma dirichlet_energy_bound {d : ℕ} (hd : d ≤ 2) {L : ℕ} (hL : 1 ≤ L) :
    (∑ x : Site d L, ∑ y : Site d L,
        if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0)
      ≤ 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 := by
  classical
  have hA := harm_pos hL
  have hinner : ∀ x : Site d L,
      (∑ y : Site d L, if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0)
        ≤ 9 * (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 := by
    intro x
    rw [← Finset.sum_filter]
    have hbd : ∀ y ∈ ({y : Site d L | Adj (x : Fin d → ℤ) (y : Fin d → ℤ)} : Finset (Site d L)),
        (profile L (latticeNorm (x : Fin d → ℤ))
            - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2
          ≤ (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 := by
      intro y hy
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hy
      have h1 : latticeNorm (y : Fin d → ℤ) ≤ latticeNorm (x : Fin d → ℤ) + 1 :=
        latticeNorm_adj hy
      have h2 : latticeNorm (x : Fin d → ℤ) ≤ latticeNorm (y : Fin d → ℤ) + 1 :=
        latticeNorm_adj (adj_symm hy)
      have hp := profile_diff_le hL h1 h2
      have habs := abs_nonneg (profile L (latticeNorm (x : Fin d → ℤ))
        - profile L (latticeNorm (y : Fin d → ℤ)))
      calc (profile L (latticeNorm (x : Fin d → ℤ)) - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2
          = |profile L (latticeNorm (x : Fin d → ℤ))
              - profile L (latticeNorm (y : Fin d → ℤ))| ^ 2 := (sq_abs _).symm
        _ ≤ (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 :=
            pow_le_pow_left₀ habs hp 2
    refine le_trans (Finset.sum_le_card_nsmul _ _ _ hbd) ?_
    rw [nsmul_eq_mul]
    have hcard := card_neighbours_le hd x
    have hcast : ((({y : Site d L | Adj (x : Fin d → ℤ) (y : Fin d → ℤ)} :
        Finset (Site d L)).card : ℝ)) ≤ 9 := by exact_mod_cast hcard
    have hnn : (0 : ℝ) ≤ (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 :=
      sq_nonneg _
    nlinarith
  calc (∑ x : Site d L, ∑ y : Site d L,
        if Adj (x : Fin d → ℤ) (y : Fin d → ℤ)
          then (profile L (latticeNorm (x : Fin d → ℤ))
                  - profile L (latticeNorm (y : Fin d → ℤ))) ^ 2 else 0)
      ≤ ∑ x : Site d L,
          9 * (Real.pi / (max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) * harm L)) ^ 2 :=
        Finset.sum_le_sum fun x _ => hinner x
    _ = (9 * Real.pi ^ 2 / harm L ^ 2)
          * ∑ x : Site d L, (1 / max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        have hmax : (0 : ℝ) < max 1 ((latticeNorm (x : Fin d → ℤ) : ℕ) : ℝ) :=
          lt_of_lt_of_le zero_lt_one (le_max_left _ _)
        field_simp
    _ ≤ (9 * Real.pi ^ 2 / harm L ^ 2) * (1 + 8 * harm L) :=
        mul_le_mul_of_nonneg_left (sum_inv_sq_norm_le hd L) (by positivity)
    _ = 9 * Real.pi ^ 2 * (1 + 8 * harm L) / harm L ^ 2 := by ring

/-- The elementary trigonometric identity behind the spin-wave estimate. -/
