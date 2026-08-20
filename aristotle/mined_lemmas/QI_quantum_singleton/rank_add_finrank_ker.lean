/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

lemma rank_add_finrank_ker [Fintype X] [Fintype Y] (M : Matrix X Y ℂ) :
    M.rank + Module.finrank ℂ (LinearMap.ker M.mulVecLin) = Fintype.card Y := by
  have h := LinearMap.finrank_range_add_finrank_ker (K := ℂ) M.mulVecLin
  rw [Module.finrank_fintype_fun_eq_card] at h
  exact h

/-- A nonzero matrix has positive rank. -/
