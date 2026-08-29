import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/


open scoped BigOperators
open scoped Classical

set_option maxHeartbeats 1000000

namespace QI

open Module

/-- The symplectic (phase-space) representation of the Pauli group on `n` qudits over the
finite field `F`: a Pauli operator is recorded by its `X`-part and `Z`-part on each qudit. -/
abbrev PSpace (F : Type*) (n : ℕ) := Fin n → F × F

variable {F : Type*} [Field F] {n : ℕ}

/-- The symplectic form on the phase space, as a bilinear map.  Two Pauli operators commute
iff their symplectic form vanishes. -/

lemma finrank_add_le_of_disjoint (S : Submodule F (PSpace F n)) {B C : Finset (Fin n)}
    (h : Disjoint B C) :
    finrank F ((S ⊓ coordSub B : Submodule F (PSpace F n))) +
      finrank F ((S ⊓ coordSub C : Submodule F (PSpace F n))) ≤
      finrank F ((S ⊓ coordSub (B ∪ C) : Submodule F (PSpace F n))) := by
  have hbot : ((S ⊓ coordSub B) ⊓ (S ⊓ coordSub C) : Submodule F (PSpace F n)) = ⊥ := by
    rw [eq_bot_iff, ← coordSub_inf_eq_bot h]
    exact inf_le_inf inf_le_right inf_le_right
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq
    (S ⊓ coordSub B : Submodule F (PSpace F n)) (S ⊓ coordSub C)
  rw [hbot] at h2
  simp only [finrank_bot, add_zero] at h2
  have h3 : ((S ⊓ coordSub B) ⊔ (S ⊓ coordSub C) : Submodule F (PSpace F n)) ≤
      S ⊓ coordSub (B ∪ C) :=
    sup_le (inf_le_inf_left _ (coordSub_mono Finset.subset_union_left))
      (inf_le_inf_left _ (coordSub_mono Finset.subset_union_right))
  calc finrank F ((S ⊓ coordSub B : Submodule F (PSpace F n))) +
        finrank F ((S ⊓ coordSub C : Submodule F (PSpace F n)))
      = finrank F ((S ⊓ coordSub B) ⊔ (S ⊓ coordSub C) : Submodule F (PSpace F n)) := h2.symm
    _ ≤ finrank F ((S ⊓ coordSub (B ∪ C) : Submodule F (PSpace F n))) :=
        Submodule.finrank_mono h3

/-- A set of fewer than `d` qudits is correctable: every centralizer element supported there
already lies in the stabilizer. -/
