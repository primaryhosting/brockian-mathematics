/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Module

/-- The space of intensive state variables of a heterogeneous system with `C` chemical
components distributed over `P = p + 1` phases: the temperature and the pressure
(the two entries of the `ℝ × ℝ` factor), together with, for every phase, the
composition vector listing the mole fraction of each component in that phase. -/
abbrev IntensiveSpace (C p : ℕ) : Type := (ℝ × ℝ) × (Fin (p + 1) → Fin C → ℝ)

/-- The space in which the equilibrium constraints of a system with `C` components and
`P = p + 1` phases take their values: one scalar per phase (the closure relation saying
that the mole fractions of that phase sum to `1`) together with, for each of the `p`
consecutive pairs of phases, one scalar per component (equality of the chemical potential
of that component in the two phases). -/
abbrev ConstraintSpace (C p : ℕ) : Type := (Fin (p + 1) → ℝ) × (Fin p → Fin C → ℝ)

/-- The number of intensive variables is `2 + P * C`. -/

lemma exists_surjective_of_finrank_le {V W : Type} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (h : finrank ℝ W ≤ finrank ℝ V) : ∃ L : V →ₗ[ℝ] W, Function.Surjective L := by
  classical
  set bV := Module.finBasis ℝ V
  set bW := Module.finBasis ℝ W
  refine ⟨bV.constr ℝ (fun i => if hi : (i : ℕ) < finrank ℝ W then bW ⟨i, hi⟩ else 0), ?_⟩
  rw [← LinearMap.range_eq_top, eq_top_iff, ← bW.span_eq, Submodule.span_le]
  rintro _ ⟨j, rfl⟩
  refine ⟨bV ⟨j, lt_of_lt_of_le j.2 h⟩, ?_⟩
  rw [Basis.constr_basis]
  simp

/-- The hypothesis of `gibbs_phase_rule` is not vacuous: whenever the phase rule predicts a
nonnegative number of degrees of freedom, i.e. whenever `P = p + 1 ≤ C + 2`, there really is
a system of independent constraints, and for it the number of degrees of freedom equals
`C - P + 2`. -/
