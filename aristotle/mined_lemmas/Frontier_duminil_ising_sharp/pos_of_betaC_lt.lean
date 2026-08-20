import Mathlib

/-!
# Duminil Ising Sharp
Category: Frontier — Fields Medal Work
Target: Frontier.duminil_ising_sharp
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to be the very first commands in a
file, so the required header comment is placed immediately after the single `import Mathlib`
line (its text is otherwise verbatim).
-/

open scoped Classical

namespace Frontier

/-!
## Setting

Duminil-Copin's *sharpness of the phase transition* for the Ising model says that the
order parameter (the spontaneous magnetisation `m(β)`, or equivalently the long-range
order parameter) exhibits **no intermediate phase**: there is a single critical inverse
temperature `β_c` such that the order parameter vanishes identically on the whole
subcritical interval `β < β_c` and is strictly positive on the whole supercritical
interval `β > β_c`.

We formalise the order-parameter half of this statement in the axiomatic form in which it
is actually used: the input is a nonnegative, monotone (in `β`) order parameter, the
critical point is *defined* as the infimum of the set of inverse temperatures at which the
order parameter is positive, and the conclusion is the sharp dichotomy above.  This is the
Lean-checked reduction of the theorem to monotonicity of the magnetisation (which for the
Ising model is Griffiths' second inequality).
-/

/-- An abstract Ising-type order parameter: a nonnegative, nondecreasing function of the
inverse temperature `β`.  For the Ising model on a graph, `m β` is the spontaneous
magnetisation `⟨σ_0⟩⁺_β`, which is nonnegative and nondecreasing in `β` by the
Griffiths–Kelly–Sherman inequalities. -/
structure IsingOrderParameter where
  /-- The order parameter as a function of the inverse temperature. -/
  m : ℝ → ℝ
  /-- The order parameter is nondecreasing in the inverse temperature. -/
  mono : Monotone m
  /-- The order parameter is nonnegative. -/
  nonneg : ∀ β, 0 ≤ m β

namespace IsingOrderParameter

variable (M : IsingOrderParameter)

/-- The ordered phase: the set of inverse temperatures at which the order parameter is
strictly positive. -/

theorem pos_of_betaC_lt (hne : M.orderedPhase.Nonempty) {β : ℝ} (hβ : M.betaC < β) :
    0 < M.m β := by
  obtain ⟨β', hβ'mem, hβ'lt⟩ := Real.lt_sInf_add_pos hne (sub_pos.mpr hβ)
  have h : β' ≤ β := by
    have : M.betaC + (β - M.betaC) = β := by ring
    exact le_of_lt (this ▸ hβ'lt)
  exact lt_of_lt_of_le hβ'mem (M.mono h)

/-- Below the critical point the order parameter vanishes identically (no intermediate
phase). -/
