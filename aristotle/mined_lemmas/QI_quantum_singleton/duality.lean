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

lemma duality (S : Submodule F (PSpace F n)) (A : Finset (Fin n)) :
    2 * A.card ≤ finrank F (S.map (proj A)) +
      finrank F ((orth S ⊓ coordSub A : Submodule F (PSpace F n))) := by
  set T := S.map (proj A) with hT
  set Θ : (coordSub A : Submodule F (PSpace F n)) →ₗ[F] Module.Dual F T :=
    T.dualRestrict ∘ₗ (sympB ∘ₗ (coordSub A).subtype) with hΘ
  have hker : LinearMap.ker Θ = Submodule.comap (coordSub A).subtype (orth S) := by
    ext w
    simp only [hΘ, LinearMap.mem_ker, LinearMap.ext_iff, LinearMap.comp_apply,
      Submodule.dualRestrict_apply, Submodule.subtype_apply, LinearMap.zero_apply,
      Submodule.mem_comap, mem_orth]
    constructor
    · intro h s hs
      have h2 := h ⟨proj A s, Submodule.mem_map_of_mem hs⟩
      rw [← symp_proj w.2 s]
      exact h2
    · intro h t
      obtain ⟨s, hs, hst⟩ := t.2
      have : symp (w : PSpace F n) (t : PSpace F n) = 0 := by
        rw [← hst, symp_proj w.2 s]
        exact h s hs
      exact this
  have hrn := LinearMap.finrank_range_add_finrank_ker Θ
  have h1 : finrank F (LinearMap.range Θ) ≤ finrank F T := by
    calc finrank F (LinearMap.range Θ) ≤ finrank F (Module.Dual F T) := Submodule.finrank_le _
      _ = finrank F T := Subspace.dual_finrank_eq
  rw [hker, finrank_comap_subtype, finrank_coordSub, inf_comm] at hrn
  omega

