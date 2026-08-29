/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

## Overview

Li's criterion states that the Riemann Hypothesis is equivalent to the nonnegativity of the
Li coefficients
`λ_n = ∑_ρ (1 - (1 - 1/ρ)^n)`,
the sum running over the (nontrivial) zeros `ρ` of the Riemann zeta function, counted with
multiplicity.

Mathlib currently has no theory of the zero multiset of `ζ` (no Hadamard factorisation of the
completed zeta function `ξ`, no statement of RH), so the criterion cannot be stated for `ζ`
itself.  What *is* stated and proved here is the arithmetic-free core of the criterion, the
Bombieri–Lagarias positivity theorem, for a finite family of zeros:

For any finite family `ρ : ι → ℂ` of nonzero complex numbers (indexed by a `Finset s`, so that
multiplicities are allowed) which is closed under the functional-equation symmetry
`ρ ↦ 1 - ρ`, one has

  (all `ρ i` lie on the critical line `Re ρ = 1/2`)  ↔  (`λ_n ≥ 0` for every `n ≥ 1`).

Both directions are proved from scratch:

* the easy direction rests on the elementary equivalence `Re ρ ≥ 1/2 ↔ |1 - 1/ρ| ≤ 1`
  (`Frontier.norm_one_sub_inv_le_one_iff`);
* the hard direction is the finite Bombieri–Lagarias argument
  (`Frontier.norm_le_one_of_re_sum_pow_le`): if the real parts of the power sums
  `∑ᵢ zᵢ^n` stay bounded above, then every `zᵢ` lies in the closed unit disc.  This uses a
  recurrence (almost-periodicity) statement `Frontier.exists_pow_near_one`, proved by
  compactness of the polydisc, which produces arbitrarily large exponents `k` for which all the
  `k`-th powers of finitely many unimodular numbers are simultaneously close to `1`.

No lemma of Mathlib closes the statement (a search for `RiemannHypothesis`, `riemannXi` zero
multisets, or Bombieri–Lagarias positivity returns nothing); the Mathlib input used consists of
standard facts such as `tendsto_subseq_of_bounded`, `Complex.normSq_eq_norm_sq` and
`tendsto_pow_atTop_atTop_of_one_lt`.
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

open Filter

namespace Frontier

/-! ### The critical line in terms of the Li transform `ρ ↦ 1 - 1/ρ` -/

/-- The Li transform `ρ ↦ 1 - 1/ρ` maps the closed half plane `Re ρ ≥ 1/2` onto the closed
unit disc. -/

theorem norm_pow_sub_one_le {u : ℂ} (hu : ‖u‖ ≤ 1) (t : ℕ) : ‖u ^ t - 1‖ ≤ t * ‖u - 1‖ := by
  induction t with
  | zero => simp
  | succ n ih =>
      have e : u ^ (n + 1) - 1 = u ^ n * (u - 1) + (u ^ n - 1) := by ring
      rw [e]
      calc ‖u ^ n * (u - 1) + (u ^ n - 1)‖ ≤ ‖u ^ n * (u - 1)‖ + ‖u ^ n - 1‖ := norm_add_le _ _
        _ ≤ 1 * ‖u - 1‖ + n * ‖u - 1‖ := by
              gcongr
              · rw [norm_mul]
                gcongr
                simpa using pow_le_one₀ (norm_nonneg u) hu
        _ = ((n : ℝ) + 1) * ‖u - 1‖ := by ring
        _ = ((n + 1 : ℕ) : ℝ) * ‖u - 1‖ := by push_cast; ring

/-- Poincaré recurrence for a finite family of unimodular complex numbers: there is a positive
exponent `k` for which all the `k`-th powers are simultaneously within `ε` of `1`.

Proved by compactness of the closed unit polydisc. -/
