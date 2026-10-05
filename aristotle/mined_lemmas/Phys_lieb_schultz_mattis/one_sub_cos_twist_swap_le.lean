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

lemma one_sub_cos_twist_swap_le (hL : 2 ≤ L) (j : ZMod L) (σ : Cfg L) :
    1 - Real.cos (twistPhase (swapCfg j σ) - twistPhase σ) ≤ 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by
  have hL0 : (0:ℝ) < L := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne L)
  have hbase : 1 - Real.cos (2*Real.pi/L) ≤ 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by
    have hx : (2*Real.pi/(L:ℝ)) ≠ 0 := by positivity
    have h1 := Real.one_sub_sq_div_two_lt_cos hx
    have h2 : (2*Real.pi/(L:ℝ))^2/2 = 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by field_simp
    linarith
  have hpos : (0:ℝ) ≤ 2 * Real.pi ^ 2 / (L : ℝ) ^ 2 := by positivity
  set A : ℝ := ((j+1).val : ℝ) - (j.val : ℝ) with hA
  have hcases :
      (((if σ (j+1) then (j.val : ℝ) else 0) + (if σ j then (((j+1).val : ℕ) : ℝ) else 0))
          - ((if σ j then (j.val : ℝ) else 0)
              + (if σ (j+1) then (((j+1).val : ℕ) : ℝ) else 0))) = 0
      ∨ (((if σ (j+1) then (j.val : ℝ) else 0) + (if σ j then (((j+1).val : ℕ) : ℝ) else 0))
          - ((if σ j then (j.val : ℝ) else 0)
              + (if σ (j+1) then (((j+1).val : ℕ) : ℝ) else 0))) = A
      ∨ (((if σ (j+1) then (j.val : ℝ) else 0) + (if σ j then (((j+1).val : ℕ) : ℝ) else 0))
          - ((if σ j then (j.val : ℝ) else 0)
              + (if σ (j+1) then (((j+1).val : ℕ) : ℝ) else 0))) = -A := by
    by_cases h1 : σ j <;> by_cases h2 : σ (j+1)
    · exact Or.inl (by simp [h1, h2])
    · exact Or.inr (Or.inl (by simp [h1, h2, hA]))
    · exact Or.inr (Or.inr (by simp [h1, h2, hA]))
    · exact Or.inl (by simp [h1, h2])
  rw [twistPhase_swap hL]
  rcases hcases with h | h | h <;> rw [h]
  · simpa using hpos
  · rw [cos_phase_eq]; exact hbase
  · rw [mul_neg, Real.cos_neg, cos_phase_eq]; exact hbase

/-! ## Invariance properties -/

