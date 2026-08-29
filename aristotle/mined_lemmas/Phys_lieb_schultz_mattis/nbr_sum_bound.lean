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

lemma nbr_sum_bound (H : Cfg L → Cfg L → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hherm : ∀ σ σ', H σ' σ = (starRingEnd ℂ) (H σ σ'))
    (hloc : ∀ σ σ', H σ σ' ≠ 0 → σ' = σ ∨ ∃ j, σ' = swapCfg j σ)
    (ψ : Cfg L → ℂ) (hnorm : sqNorm ψ = 1) :
    ∑ σ : Cfg L, ∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0)
      ≤ M * L := by
  have hrow := row_card H hloc
  have hcol := col_card H hherm hloc
  have step1 : ∀ σ σ' : Cfg L,
      (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0)
        ≤ (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0)
          + (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ'‖^2/2) else 0) := by
    intro σ σ'
    by_cases h : H σ σ' ≠ 0 ∧ σ' ≠ σ
    · simp only [if_pos h, ← mul_add]
      have : ‖ψ σ‖ * ‖ψ σ'‖ ≤ ‖ψ σ‖^2/2 + ‖ψ σ'‖^2/2 := by nlinarith [sq_nonneg (‖ψ σ‖ - ‖ψ σ'‖)]
      exact mul_le_mul_of_nonneg_left this hM
    · simp [if_neg h]
  have rowsum : ∀ σ : Cfg L,
      (∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0))
        ≤ (L : ℝ) * (M * (‖ψ σ‖^2/2)) := by
    intro σ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h1 : ((Finset.univ.filter (fun σ' => H σ σ' ≠ 0 ∧ σ' ≠ σ)).card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hrow σ
    have h2 : (0:ℝ) ≤ M * (‖ψ σ‖^2/2) := by positivity
    exact mul_le_mul_of_nonneg_right h1 h2
  have colsum : ∀ τ : Cfg L,
      (∑ σ : Cfg L, (if H σ τ ≠ 0 ∧ τ ≠ σ then M * (‖ψ τ‖^2/2) else 0))
        ≤ (L : ℝ) * (M * (‖ψ τ‖^2/2)) := by
    intro τ
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have h1 : ((Finset.univ.filter (fun σ => H σ τ ≠ 0 ∧ τ ≠ σ)).card : ℝ) ≤ (L : ℝ) := by
      exact_mod_cast hcol τ
    have h2 : (0:ℝ) ≤ M * (‖ψ τ‖^2/2) := by positivity
    exact mul_le_mul_of_nonneg_right h1 h2
  calc ∑ σ : Cfg L, ∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖ * ‖ψ σ'‖) else 0)
      ≤ ∑ σ : Cfg L, ∑ σ' : Cfg L,
          ((if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0)
            + (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ'‖^2/2) else 0)) :=
        Finset.sum_le_sum fun σ _ => Finset.sum_le_sum fun σ' _ => step1 σ σ'
    _ = (∑ σ : Cfg L, ∑ σ' : Cfg L, (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ‖^2/2) else 0))
          + (∑ σ : Cfg L, ∑ σ' : Cfg L,
              (if H σ σ' ≠ 0 ∧ σ' ≠ σ then M * (‖ψ σ'‖^2/2) else 0)) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun σ _ => Finset.sum_add_distrib
    _ ≤ (∑ σ : Cfg L, (L:ℝ) * (M * (‖ψ σ‖^2/2))) + (∑ τ : Cfg L, (L:ℝ) * (M * (‖ψ τ‖^2/2))) := by
        refine add_le_add (Finset.sum_le_sum fun σ _ => rowsum σ) ?_
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun τ _ => colsum τ
    _ = M * L := by
        simp only [← Finset.mul_sum]
        have h : ∑ i : Cfg L, ‖ψ i‖^2/2 = 1/2 := by
          rw [← Finset.sum_div, show (∑ σ : Cfg L, ‖ψ σ‖^2) = sqNorm ψ from rfl, hnorm]
        rw [h]; ring

