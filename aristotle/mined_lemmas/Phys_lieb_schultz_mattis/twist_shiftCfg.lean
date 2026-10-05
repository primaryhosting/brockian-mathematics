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

lemma twist_shiftCfg {σ : Cfg L} (h : 2 * occ σ = L) : twist (shiftCfg σ) = - twist σ := by
  have hL : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne L)
  have hoccR : (2 : ℝ) * (occ σ : ℝ) = (L : ℝ) := by exact_mod_cast congrArg (fun n : ℕ => (n : ℝ)) h
  have hocc : (2 * Real.pi / L) * (occ σ : ℝ) = Real.pi := by
    field_simp
    linarith [hoccR]
  rw [twist, twist, twistPhase_shiftCfg, hocc]
  by_cases h0 : σ 0
  · simp only [h0, if_true]
    push_cast
    rw [show ((twistPhase σ : ℂ) - Real.pi + 2 * Real.pi * 1) * Complex.I
        = (twistPhase σ : ℂ) * Complex.I + (Real.pi : ℂ) * Complex.I by ring,
      Complex.exp_add, Complex.exp_pi_mul_I]
    ring
  · simp only [h0]
    push_cast
    rw [show ((twistPhase σ : ℂ) - Real.pi + 2 * Real.pi * 0) * Complex.I
        = (twistPhase σ : ℂ) * Complex.I + (-((Real.pi : ℂ) * Complex.I)) by ring,
      Complex.exp_add, Complex.exp_neg, Complex.exp_pi_mul_I]
    norm_num

