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

noncomputable def counting (lam : ℕ → ℝ) (t : ℝ) : ℕ :=
  {n : ℕ | lam n ≤ t}.ncard

/-- `Discrete lam` says that the spectrum `lam` is discrete in the sense that only finitely
many eigenvalues lie below any given threshold. -/

def Discrete (lam : ℕ → ℝ) : Prop :=
  ∀ t : ℝ, {n : ℕ | lam n ≤ t}.Finite

/-- `WeylLawMatch lam C a` says that the counting function of `lam` matches a Weyl law
with leading constant `C > 0` and exponent `a > 0`, i.e. `counting lam t ~ C * t ^ a`
as `t → ∞`. -/

def WeylLawMatch (lam : ℕ → ℝ) (C a : ℝ) : Prop :=
  0 < C ∧ 0 < a ∧
    Tendsto (fun t : ℝ => (counting lam t : ℝ) / (C * t ^ a)) atTop (𝓝 1)

/-- A discrete spectrum has eigenvalues diverging to `+∞`: since `{n | lam n ≤ b}` is finite
for every `b`, its complement is cofinite, and on `ℕ` the cofinite filter is `atTop`. -/
