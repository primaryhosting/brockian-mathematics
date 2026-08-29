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

lemma ip_eq_zero_of_anti (v ψ0 : Cfg L → ℂ)
    (hv : ∀ σ, 2 * occ σ = L → v (shiftCfg σ) = - v σ)
    (hsector : ∀ σ, ψ0 σ ≠ 0 → 2 * occ σ = L)
    (lam : ℂ) (hlam : ∀ σ, ψ0 (shiftCfg σ) = lam * ψ0 σ) (hlam1 : ‖lam‖ = 1) :
    ip ψ0 (fun σ => v σ * ψ0 σ) = 0 := by
  have hll : (starRingEnd ℂ) lam * lam = 1 := by
    rw [mul_comm, Complex.mul_conj', hlam1]; norm_num
  have key : ∀ σ : Cfg L,
      (starRingEnd ℂ) (ψ0 (shiftCfg σ)) * (v (shiftCfg σ) * ψ0 (shiftCfg σ))
        = -((starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ)) := by
    intro σ
    by_cases h : ψ0 σ = 0
    · rw [hlam σ, h]; simp
    · rw [hlam σ, hv σ (hsector σ h), map_mul]
      linear_combination (-((starRingEnd ℂ) (ψ0 σ) * v σ * ψ0 σ)) * hll
  have hsum : ip ψ0 (fun σ => v σ * ψ0 σ) = - ip ψ0 (fun σ => v σ * ψ0 σ) := by
    unfold ip
    calc ∑ σ : Cfg L, (starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ)
        = ∑ σ : Cfg L, (starRingEnd ℂ) (ψ0 (shiftCfg σ)) * (v (shiftCfg σ) * ψ0 (shiftCfg σ)) :=
          (Fintype.sum_bijective shiftCfg shiftCfg_bijective _ _ (fun _ => rfl)).symm
      _ = ∑ σ : Cfg L, -((starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ)) :=
          Finset.sum_congr rfl fun σ _ => key σ
      _ = - ∑ σ : Cfg L, (starRingEnd ℂ) (ψ0 σ) * (v σ * ψ0 σ) := by rw [Finset.sum_neg_distrib]
  linear_combination hsum / 2

/-! ## The variational energy estimate -/

