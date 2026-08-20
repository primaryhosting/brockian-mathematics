import Mathlib

/-!
# Hellmann Feynman
Category: Frontier Phys
Target: Phys.hellmann_feynman
Statement: dE_n/dλ = ⟨ψ_n|∂H/∂λ|ψ_n⟩ (Hellmann–Feynman).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
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

set_option grind.warning false

namespace Phys

/-- **Hellmann–Feynman theorem.**

Let `V` be a complex inner product space and let `Hm : ℝ → V →L[ℂ] V` be a family of
operators depending on a parameter `λ`, with `psi λ` a normalized eigenvector of `Hm λ`
with real eigenvalue `en λ`.  If `Hm`, `psi` and `en` are differentiable at `lam`
(with derivatives `dH`, `dpsi`, `den`) and `Hm lam` is symmetric, then

`dE_n/dλ = ⟪ψ_n, (∂H/∂λ) ψ_n⟫`,

i.e. `den = ⟪psi lam, dH (psi lam)⟫`. -/

theorem hellmann_feynman_of_norm_one
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {Hm : ℝ → V →L[ℂ] V} {dH : V →L[ℂ] V} {psi : ℝ → V} {dpsi : V}
    {en : ℝ → ℝ} {den lam : ℝ}
    (hH : HasDerivAt Hm dH lam)
    (hpsi : HasDerivAt psi dpsi lam)
    (hen : HasDerivAt en den lam)
    (hnorm : ‖psi lam‖ = 1)
    (hsymm : ∀ y z : V, inner ℂ (Hm lam y) z = inner ℂ y (Hm lam z))
    (heig : ∀ x, Hm x (psi x) = (en x : ℂ) • psi x) :
    den = (inner ℂ (psi lam) (dH (psi lam)) : ℂ).re := by
  have hnorm' : inner ℂ (psi lam) (psi lam) = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num
  have := hellmann_feynman hH hpsi hen hnorm' hsymm heig
  rw [← this, Complex.ofReal_re]

end Phys

