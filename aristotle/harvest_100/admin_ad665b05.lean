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
theorem counting_diverges_of_discrete_and_WeylLawMatch
    (lam : ℕ → ℝ) (C a : ℝ) (_hdisc : Discrete lam) (hWeyl : WeylLawMatch lam C a) :
    Tendsto (fun t : ℝ => (counting lam t : ℝ)) atTop atTop := by
  obtain ⟨hC, ha, hW⟩ := hWeyl
  have hden : Tendsto (fun t : ℝ => C * t ^ a) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hC (tendsto_rpow_atTop ha)
  refine (hW.pos_mul_atTop one_pos hden).congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with t ht
  have h0 : C * t ^ a ≠ 0 := by positivity
  field_simp

end Brockian.Weyl.WeylLawTarget

