import Mathlib

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean 4 requires `import` lines to precede every command, including module docstrings,
-- so the header above is a plain block comment; the module docstring below repeats it.)

import Mathlib

/-!
# Counting Diverges Of Discrete And Weyl Law Match
Category: Brockian (Open Discharge)
Target: Brockian.Weyl.WeylLawTarget.counting_diverges_of_discrete_and_WeylLawMatch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Filter Topology

namespace Brockian.Weyl.WeylLawTarget

/-- The eigenvalue counting function of a spectrum `lam : ℕ → ℝ`:
`counting lam t` is the number of indices `n` with `lam n ≤ t`.
(For a non-discrete spectrum the set is infinite and `Set.ncard` returns `0`.) -/

theorem eigenvalues_tendsto_atTop_of_discrete (lam : ℕ → ℝ) (hdisc : Discrete lam) :
    Tendsto lam atTop atTop := by
  rw [tendsto_atTop]
  intro b
  have hcof := (hdisc b).compl_mem_cofinite
  rw [Nat.cofinite_eq_atTop] at hcof
  filter_upwards [hcof] with n hn
  exact le_of_not_ge (by simpa [Set.mem_compl_iff] using hn)

/-- **Counting diverges.** If a discrete spectrum satisfies a Weyl law
`counting lam t ~ C * t ^ a` with `C > 0` and `a > 0`, then the eigenvalue counting
function diverges to `+∞`.

The proof writes `counting lam t = (counting lam t / (C * t ^ a)) * (C * t ^ a)` for `t > 0`;
the first factor tends to `1 > 0` and the second to `+∞` (by Mathlib's `tendsto_rpow_atTop`
and `Filter.Tendsto.const_mul_atTop`), so `Filter.Tendsto.pos_mul_atTop` concludes.

Note: the discreteness hypothesis is part of the statement as requested, but it turns out not
to be needed for the argument: the Weyl asymptotics alone already force divergence. -/
