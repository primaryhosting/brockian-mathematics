/-
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` to precede any module docstring, so the header above is a plain
-- block comment; it is repeated verbatim as the module docstring below.)

import Mathlib

/-!
# RH Li Criterion
Category: Frontier — Moonshot
Target: Frontier.RH_Li_criterion
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

namespace Frontier

/-!
## Li's criterion

Let `Z` be the multiset of (nontrivial) zeros of a completed zeta-type function.  Li's
coefficients are

`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`,

and Li's criterion states that all zeros lie on the critical line `Re ρ = 1/2` if and only if
`λ_n ≥ 0` for every `n ≥ 1`.

The content of the criterion is the Möbius change of variable `z = 1 - 1/ρ`, which maps the
critical line to the unit circle and the functional-equation symmetry `ρ ↦ 1 - ρ` to the
inversion `z ↦ 1/z`.  We prove the criterion for an arbitrary finite multiset of zeros which
avoids `0` and is stable under `ρ ↦ 1 - ρ`; this is the arithmetic-free core of Li's theorem
(the analytic input specific to `ζ`, namely the Hadamard product for the completed zeta
function, is what turns this statement into the statement about `ζ` itself).

The nontrivial direction uses a simultaneous recurrence statement on the unit circle
(`Frontier.exists_large_pow_near_one`): for finitely many unimodular numbers there are
arbitrarily large exponents `n` making all `n`-th powers simultaneously close to `1`.  This is
what forces a zero off the critical line to produce a negative Li coefficient.
-/

/-- The `n`-th Li coefficient attached to a finite multiset `Z` of zeros:
`λ_n = ∑_{ρ ∈ Z} (1 - (1 - 1/ρ)^n)`. -/

lemma liCoeff_nonneg_of_RH (Z : Multiset ℂ) (h0 : ∀ ρ ∈ Z, ρ ≠ 0)
    (hRH : RiemannHypothesisFor Z) (n : ℕ) : 0 ≤ (liCoeff Z n).re := by
  rw [liCoeff, re_multiset_sum, Multiset.map_map]
  refine Multiset.sum_nonneg ?_
  intro x hx
  obtain ⟨ρ, hρ, rfl⟩ := Multiset.mem_map.mp hx
  have hz : ‖1 - 1 / ρ‖ = 1 := (norm_mobius_eq_one_iff ρ (h0 ρ hρ)).mpr (hRH ρ hρ)
  have hpow : ‖(1 - 1 / ρ) ^ n‖ = 1 := by rw [norm_pow, hz, one_pow]
  have := Complex.re_le_norm ((1 - 1 / ρ) ^ n)
  rw [hpow] at this
  simp only [Function.comp_apply, Complex.sub_re, Complex.one_re]
  linarith

/-- Hard direction, on the `z`-side: if a finite multiset `W` of nonzero complex numbers
contains an element of modulus `> 1`, then for some `n ≥ 1` the sum `∑_{z ∈ W} (1 - z^n)` has
negative real part. -/
