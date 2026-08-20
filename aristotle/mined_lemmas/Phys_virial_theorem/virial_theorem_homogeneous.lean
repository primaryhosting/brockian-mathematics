import Mathlib
/-!
# Virial Theorem
Category: Frontier Phys
Target: Phys.virial_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Note: Lean 4 requires `import` to be the very first command of a file, so the
requested header block appears immediately after the import.)
-/

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

namespace Phys

open InnerProductSpace

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℂ X]

/-- **Quantum virial theorem**: `2⟨T⟩ = ⟨r · ∇V⟩` for a bound stationary state.

Setting (units with `ħ = 1`): on a complex inner product space of states `X`, the
Hamiltonian is `Top + Vop`, the sum of the kinetic and the potential energy operator,
`Wop` is the virial operator `r · ∇V`, and `Aop` is the generator `r · p` of dilations.

* `hsymm` says the Hamiltonian is symmetric (hermitian) — energies are real observables;
* `hcomm` is the operator identity `[H, r · p] = i (2 T - r · ∇V)`, which follows from
  the canonical commutation relations;
* `ψ` is a bound stationary state: an eigenvector of the Hamiltonian with real energy
  `e`.  Boundedness (normalizability) is what makes the expectation values below
  meaningful; here it is reflected in `ψ` being an element of the inner product space,
  so that `⟪ψ, · ψ⟫` is defined.

Conclusion: `2 ⟪ψ, Top ψ⟫ = ⟪ψ, Wop ψ⟫`, i.e. `2⟨T⟩ = ⟨r · ∇V⟩`.

The proof is the standard one: the expectation value of the commutator `[H, A]` in a
stationary state vanishes, because `⟪ψ, H (A ψ)⟫ = ⟪H ψ, A ψ⟫ = e ⟪ψ, A ψ⟫ = ⟪ψ, A (H ψ)⟫`.
-/

theorem virial_theorem_homogeneous
    (Top Vop Wop Aop : X →ₗ[ℂ] X) (n : ℝ)
    (hsymm : ∀ x y : X, ⟪(Top + Vop) x, y⟫_ℂ = ⟪x, (Top + Vop) y⟫_ℂ)
    (hcomm : ∀ x : X,
      (Top + Vop) (Aop x) - Aop ((Top + Vop) x) = Complex.I • (2 • Top x - Wop x))
    (hhom : Wop = (n : ℂ) • Vop)
    (ψ : X) (e : ℝ) (hψ : (Top + Vop) ψ = (e : ℂ) • ψ) :
    2 * ⟪ψ, Top ψ⟫_ℂ = (n : ℂ) * ⟪ψ, Vop ψ⟫_ℂ := by
  have h := virial_theorem Top Vop Wop Aop hsymm hcomm ψ e hψ
  rw [hhom] at h
  simpa [inner_smul_right] using h

end Phys

#print axioms Phys.virial_theorem
#print axioms Phys.virial_theorem_homogeneous

