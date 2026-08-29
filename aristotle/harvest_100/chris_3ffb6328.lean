/-
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: the requested header is reproduced verbatim above, but as a plain block
comment `/- ... -/` rather than a module docstring `/-! ... -/`, because Lean 4
requires every `import` command to precede any other command in the file, and a
module docstring counts as a command.  The same text is repeated below as the
module docstring, immediately after the imports.)
-/

import Mathlib

/-!
# Molecular Orbital Count
Category: Chemistry
Target: Chem.molecular_orbital_count
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Chem

open Matrix

/-- **LCAO dimension preservation: `n` atomic orbitals yield exactly `n` molecular orbitals.**

Model: the atomic orbitals form a basis `ao : Module.Basis (Fin n) K V` of the space `V` of
one-electron wavefunctions (so there are `n` atomic orbitals), and an LCAO ansatz is given
by a coefficient matrix `C`, the `i`-th molecular orbital being the linear combination
`∑ j, C i j • ao j`.  Assuming the coefficient matrix is invertible (`IsUnit C.det`, i.e.
the linear combinations are genuinely independent), the resulting family of molecular
orbitals is again a basis of `V` indexed by `Fin n`: there are exactly `n` molecular
orbitals, and the dimension `n` of the orbital space is preserved. -/
theorem molecular_orbital_count {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    {n : ℕ} (ao : Module.Basis (Fin n) K V) (C : Matrix (Fin n) (Fin n) K) (hC : IsUnit C.det) :
    ∃ mo : Module.Basis (Fin n) K V,
      (∀ i, mo i = ∑ j, C i j • ao j) ∧
      Module.finrank K V = n := by
  have hCT : IsUnit (Cᵀ).det := by simpa [Matrix.det_transpose] using hC
  refine ⟨ao.map (Matrix.toLinearEquiv ao Cᵀ hCT), ?_, ?_⟩
  · intro i
    simp [Module.Basis.map_apply, Matrix.toLinearEquiv_apply, Matrix.toLin_self]
  · simpa using Module.finrank_eq_card_basis ao

end Chem

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

