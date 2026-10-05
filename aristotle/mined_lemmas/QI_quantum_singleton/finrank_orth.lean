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

lemma finrank_orth (S : Submodule F (PSpace F n)) :
    finrank F (orth S) + finrank F S = 2 * n := by
  have hfr : finrank F (Module.Dual F (PSpace F n)) = finrank F (PSpace F n) :=
    Subspace.dual_finrank_eq
  have hbij : Function.Bijective (sympB : PSpace F n →ₗ[F] Module.Dual F (PSpace F n)) :=
    ⟨sympB_injective, (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      hfr.symm).mp sympB_injective⟩
  set e : PSpace F n ≃ₗ[F] Module.Dual F (PSpace F n) := LinearEquiv.ofBijective sympB hbij with he
  have horth : orth S = Submodule.comap (e : PSpace F n →ₗ[F] Module.Dual F (PSpace F n))
      (Submodule.dualAnnihilator S) := rfl
  have hda := Subspace.finrank_add_finrank_dualAnnihilator_eq S
  rw [horth, Submodule.comap_equiv_eq_map_symm, LinearEquiv.finrank_map_eq]
  rw [finrank_PSpace] at hda
  omega

/-- **Quantum Singleton bound.**  For an `[[n, k, d]]` stabilizer code — that is, an isotropic
subspace `S` of the symplectic phase space `(F × F)^n` of `n` qudits, with `n - k` generators,
whose centralizer `orth S` contains a nontrivial logical operator and all of whose nontrivial
logical operators have weight at least `d` — one has `n - k ≥ 2 (d - 1)`.

The isotropy hypothesis `hiso` (i.e. the stabilizer group is abelian) is part of the definition
of a stabilizer code; it is used only to rule out the degenerate situation where the code
encodes no qudits at all. -/
