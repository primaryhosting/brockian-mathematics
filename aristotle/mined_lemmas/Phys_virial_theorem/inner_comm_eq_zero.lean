import Mathlib

/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped InnerProductSpace

namespace Phys

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The commutator `[A, B] = AB - BA` of two linear operators on `E`. -/

lemma inner_comm_eq_zero (H G : Module.End ℂ E)
    (hHsymm : ∀ u v : E, ⟪H u, v⟫_ℂ = ⟪u, H v⟫_ℂ)
    (psi : E) (En : ℝ) (heig : H psi = (En : ℂ) • psi) :
    ⟪psi, comm H G psi⟫_ℂ = 0 := by
  have h1 : comm H G psi = H (G psi) - G (H psi) := rfl
  rw [h1, inner_sub_right, ← hHsymm, heig, inner_smul_left, map_smul, inner_smul_right]
  simp [Complex.conj_ofReal]

/-- **Quantum virial theorem.**

Let `x j`, `p j` (with `j` ranging over a finite set of spatial directions) be position and
momentum operators on a complex inner product space `E`, satisfying the canonical
commutation relations `[xⱼ, p_k] = i ħ δⱼk`, the momenta commuting among themselves.
Let `V` be a potential commuting with the positions, and let `W j` be its directional
derivative operators, characterised by `[V, pⱼ] = i ħ Wⱼ` (so `Wⱼ = ∂ⱼ V`).

Let `T = (1/2m) Σⱼ pⱼ²` be the kinetic energy and `H = T + V` the Hamiltonian, assumed
symmetric.  If `psi` is a normalised bound stationary state, i.e. an eigenvector of `H`
with real energy `En`, then

`2 ⟨T⟩ = ⟨r · ∇V⟩`,  i.e.  `2 ⟪psi, T psi⟫ = ⟪psi, (Σⱼ xⱼ Wⱼ) psi⟫`.

(The normalisation hypothesis `‖psi‖ = 1` is part of the physical statement and is kept,
although the proof does not need it: the identity between the two unnormalised quadratic
forms holds for every stationary state.) -/
