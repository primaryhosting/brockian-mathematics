import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

We formalise the finite-volume Lieb-Schultz-Mattis theorem for a periodic spin-`1/2`
(hence half-integer spin) chain of `L` sites.

The Hilbert space is the space of functions on spin configurations `Cfg L = ZMod L → Bool`
(each site carries two states, `S^z_j = ±1/2`).  A Hamiltonian is given by its matrix
elements `H : Cfg L → Cfg L → ℂ`.  The physical hypotheses are:

* `hherm`  : `H` is Hermitian;
* `htrans` : `H` is invariant under the lattice translation `shiftCfg`;
* `hloc`   : off-diagonal matrix elements only connect configurations that differ by an
  exchange of the two spins on a nearest-neighbour bond (locality together with conservation
  of the total magnetisation);
* `hbdd`   : matrix elements are bounded by `M`.

`ψ0` is a normalised ground state (`hmin`) lying in the zero-magnetisation sector (`hsector`,
i.e. exactly half of the spins are up; this is where the half-integer value of the spin enters,
producing the momentum shift by `π` of the twisted state).

The conclusion is the LSM alternative: either the ground state is degenerate, or there is a
state orthogonal to `ψ0` whose energy lies within `2π²M/L` of the ground state energy, i.e.
the gap closes at least as fast as `O(1/L)` as the chain grows: the chain is gapless or
degenerate.

The proof is the classical Lieb-Schultz-Mattis twist argument: the twist operator
`U = exp (2πi/L ∑ j j n_j)` produces a variational state of energy `E0 + O(1/L)` (using the
average of `U` and `U*` so that the first order term cancels), and, in the half-filled sector,
`U` shifts the momentum by `π`, so `Uψ0` is orthogonal to `ψ0` whenever `ψ0` is a translation
eigenvector, which it is when the ground state is unique.
-/

open scoped BigOperators
open scoped Real
open scoped Classical

set_option maxHeartbeats 1000000

namespace Phys

/-! ## The spin-1/2 periodic chain -/

/-- Spin configurations of a periodic spin-`1/2` chain with `L` sites: each site carries a
two-dimensional spin space (`S = 1/2`, i.e. half-integer spin), encoded by a `Bool`. -/
abbrev Cfg (L : ℕ) := ZMod L → Bool

variable {L : ℕ} [NeZero L]

/-- The lattice translation acting on configurations. -/

lemma twist_energy_bound (hL : 2 ≤ L) (H : Cfg L → Cfg L → ℂ) (M : ℝ)
    (hherm : ∀ σ σ', H σ' σ = (starRingEnd ℂ) (H σ σ'))
    (hloc : ∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ)
    (hbdd : ∀ σ σ', ‖H σ σ'‖ ≤ M)
    (ψ : Cfg L → ℂ) (hnorm : sqNorm ψ = 1) :
    energy H (fun σ => twist σ * ψ σ) + energy H (fun σ => (starRingEnd ℂ) (twist σ) * ψ σ)
      ≤ 2 * energy H ψ + 4 * Real.pi ^ 2 * M / L := by
  have hM : 0 ≤ M := le_trans (norm_nonneg _) (hbdd (fun _ => false) (fun _ => false))
  have hL0 : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  -- rewrite the difference of energies as a single sum
  have hcomb : ∀ (f g h : Cfg L → Cfg L → ℂ),
      (∑ σ : Cfg L, ∑ σ', f σ σ') + (∑ σ : Cfg L, ∑ σ', g σ σ') - 2 * (∑ σ : Cfg L, ∑ σ', h σ σ')
        = ∑ σ : Cfg L, ∑ σ', (f σ σ' + g σ σ' - 2 * h σ σ') := by
    intro f g h
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  have hdiff : energy H (fun σ => twist σ * ψ σ)
        + energy H (fun σ => (starRingEnd ℂ) (twist σ) * ψ σ) - 2 * energy H ψ
      = (∑ σ : Cfg L, ∑ σ' : Cfg L,
          ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
            * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)).re := by
    rw [energy_mul, energy_mul, energy]
    rw [show ∀ (X Y Z : ℂ), X.re + Y.re - 2 * Z.re = (X + Y - 2*Z).re from by
      intro X Y Z; simp [Complex.add_re, Complex.sub_re]]
    congr 1
    rw [hcomb]
    refine Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun σ' _ => ?_
    simp only [twist, Complex.conj_conj]
    linear_combination ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
      * twist_pair (twistPhase σ) (twistPhase σ')
  -- estimate the sum
  have hkey : ∀ σ σ' : Cfg L,
      ‖((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
          * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)‖
        ≤ (4*Real.pi^2/(L:ℝ)^2)
            * (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0) := by
    intro σ σ'
    by_cases hH : H σ σ' = 0
    · simp [hH]
    by_cases heq : σ' = σ
    · subst heq; simp
    · rw [if_pos ⟨hH, heq⟩]
      obtain ⟨j, hj⟩ := (hloc σ σ' hH).resolve_left heq
      have hcos : 2 - 2 * Real.cos (twistPhase σ' - twistPhase σ) ≤ 4*Real.pi^2/(L:ℝ)^2 := by
        have h := one_sub_cos_twist_swap_le hL j σ
        rw [← hj] at h
        have h2 : 4*Real.pi^2/(L:ℝ)^2 = 2*(2*Real.pi^2/(L:ℝ)^2) := by ring
        rw [h2]; linarith
      have hnormc : ‖(starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ'‖ ≤ M * (‖ψ σ‖ * ‖ψ σ'‖) := by
        rw [norm_mul, norm_mul, RCLike.norm_conj]
        calc ‖ψ σ‖ * ‖H σ σ'‖ * ‖ψ σ'‖ ≤ ‖ψ σ‖ * M * ‖ψ σ'‖ := by
              gcongr
              exact hbdd σ σ'
          _ = M * (‖ψ σ‖ * ‖ψ σ'‖) := by ring
      have hfac : ‖2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2‖
          = 2 - 2 * Real.cos (twistPhase σ' - twistPhase σ) := by
        have h1 : (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)
            = (((2 * Real.cos (twistPhase σ' - twistPhase σ) - 2 : ℝ)) : ℂ) := by push_cast; ring
        rw [h1, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonpos (by linarith [Real.cos_le_one (twistPhase σ' - twistPhase σ)])]
        ring
      rw [norm_mul, hfac, mul_comm (4*Real.pi^2/(L:ℝ)^2)]
      exact mul_le_mul hnormc hcos
        (by linarith [Real.cos_le_one (twistPhase σ' - twistPhase σ)]) (by positivity)
  have hbound : (∑ σ : Cfg L, ∑ σ' : Cfg L,
          ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
            * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)).re
      ≤ 4 * Real.pi ^ 2 * M / L := by
    calc (∑ σ : Cfg L, ∑ σ' : Cfg L,
            ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
              * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)).re
        ≤ ‖∑ σ : Cfg L, ∑ σ' : Cfg L,
            ((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
              * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)‖ :=
          Complex.re_le_norm _
      _ ≤ ∑ σ : Cfg L, ∑ σ' : Cfg L,
            ‖((starRingEnd ℂ) (ψ σ) * H σ σ' * ψ σ')
              * (2 * ((Real.cos (twistPhase σ' - twistPhase σ) : ℝ) : ℂ) - 2)‖ :=
          le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun σ _ => norm_sum_le _ _)
      _ ≤ ∑ σ : Cfg L, ∑ σ' : Cfg L, (4*Real.pi^2/(L:ℝ)^2)
              * (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0) :=
          Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun σ' _ => hkey σ σ'
      _ = (4*Real.pi^2/(L:ℝ)^2) * ∑ σ : Cfg L, ∑ σ' : Cfg L,
              (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun σ _ => (Finset.mul_sum _ _ _).symm
      _ ≤ (4*Real.pi^2/(L:ℝ)^2) * (M * L) :=
          mul_le_mul_of_nonneg_left (nbr_sum_bound H M hM hherm hloc ψ hnorm) (by positivity)
      _ = 4 * Real.pi ^ 2 * M / L := by field_simp
  linarith [hdiff ▸ hbound]

/-! ## Main theorem -/

/-- **Lieb-Schultz-Mattis theorem** (finite-volume form) for a periodic spin-`1/2` chain,
i.e. a translation invariant chain with half-integer spin per site.

`H` is a Hermitian, translation invariant Hamiltonian whose off-diagonal matrix elements only
connect configurations differing by an exchange on a nearest-neighbour bond (locality together
with conservation of the total magnetisation), with matrix elements bounded by `M`.  `ψ0` is a
normalised ground state lying in the zero-magnetisation sector.  Then either the ground state is
degenerate, or there is a state orthogonal to `ψ0` whose energy exceeds the ground state energy
by at most `2π²M/L` (and at least the ground state energy): the spectral gap above the ground
state closes at least as fast as `O(1/L)`.  So a half-integer-spin translation invariant chain
is gapless or degenerate. -/
