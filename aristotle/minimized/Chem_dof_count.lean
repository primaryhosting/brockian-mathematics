/-
# Gibbs Phase Rule
Category: Chemistry
Target: Chem.gibbs_phase_rule
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

namespace Chem

/-- Number of intensive state variables of a `P`-phase, `C`-component system:
temperature and pressure, together with `C - 1` independent mole fractions in each
of the `P` phases. -/

def phaseVarCount (C P : ℕ) : ℕ := P * (C - 1) + 2

/-- Number of equilibrium constraints: for each of the `C` components, equality of its
chemical potential across the `P` phases gives `P - 1` independent equations. -/

def phaseConstraintCount (C P : ℕ) : ℕ := C * (P - 1)

/-- Arithmetic core of the phase rule: if the `C * (P - 1)` constraints are independent,
the solution dimension `k` satisfies `k = C - P + 2` (over `ℤ`, so that no truncation of
natural subtraction occurs). -/

theorem dof_count (C P : ℕ) (hC : 1 ≤ C) (hP : 1 ≤ P) (k : ℕ)
    (h : phaseConstraintCount C P + k = phaseVarCount C P) :
    (k : ℤ) = (C : ℤ) - (P : ℤ) + 2 := by
  obtain ⟨c, rfl⟩ : ∃ c, C = c + 1 := ⟨C - 1, by omega⟩
  obtain ⟨q, rfl⟩ : ∃ q, P = q + 1 := ⟨P - 1, by omega⟩
  simp only [phaseConstraintCount, phaseVarCount, Nat.add_sub_cancel] at h
  have h' : ((c + 1) * q + k : ℤ) = ((q + 1) * c + 2 : ℤ) := by exact_mod_cast h
  push_cast
  linear_combination h'

/-- **Gibbs phase rule** as an affine-dimension count.

The intensive state of a system with `C` components and `P` phases is described by
`phaseVarCount C P = P * (C - 1) + 2` real variables, subject to
`phaseConstraintCount C P = C * (P - 1)` equilibrium conditions, encoded here by an
arbitrary linear map `L` with an arbitrary right-hand side `b`.  Assuming the
constraints are independent (`L` surjective), the equilibrium set `{x | L x = b}` is a
nonempty affine subspace: it is a translate of `ker L`, and its dimension (the number of
degrees of freedom) is

  `F = C - P + 2`.

The dimension computation is `LinearMap.finrank_range_add_finrank_ker` (rank–nullity). -/
