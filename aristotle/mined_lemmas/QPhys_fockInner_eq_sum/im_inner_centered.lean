import Mathlib
import RequestProject.Main

/-!
# A concrete model for the canonical commutation relation

This file shows that the hypotheses of `QPhys.heisenberg_uncertainty` are *consistent* with a
nonzero `ℏ`: we build the (algebraic) Fock space of finitely supported sequences `ℕ →₀ ℂ`
with the Bargmann inner product `⟪eₘ, eₙ⟫ = n! δₘₙ`, the annihilation and creation operators,
and the resulting position and momentum operators `X`, `P`, which are symmetric and satisfy
`X P - P X = i` (i.e. `ℏ = 1`).
-/

open scoped ComplexConjugate InnerProductSpace
open Finsupp

namespace QPhys

/-! ## The Bargmann inner product on `ℕ →₀ ℂ` -/

/-- The Bargmann inner product: `⟪f, g⟫ = ∑ₙ conj (f n) * g n * n!`. -/

theorem im_inner_centered (X P : E →ₗ[ℂ] E)
    (hX : ∀ u v : E, ⟪X u, v⟫_ℂ = ⟪u, X v⟫_ℂ)
    (hP : ∀ u v : E, ⟪P u, v⟫_ℂ = ⟪u, P v⟫_ℂ)
    (hbar : ℝ) (psi : E) (hnorm : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = ((Complex.I * hbar) : ℂ) • psi) :
    (⟪X psi - ⟪psi, X psi⟫_ℂ • psi, P psi - ⟪psi, P psi⟫_ℂ • psi⟫_ℂ).im = hbar / 2 := by
  have hpp : ⟪psi, psi⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hnorm]; norm_num
  set u : E := X psi - ⟪psi, X psi⟫_ℂ • psi
  set v : E := P psi - ⟪psi, P psi⟫_ℂ • psi
  have h1 : ⟪u, v⟫_ℂ = ⟪psi, X (P psi)⟫_ℂ - ⟪psi, X psi⟫_ℂ * ⟪psi, P psi⟫_ℂ :=
    inner_centered X P hX psi hnorm
  have h2 : ⟪v, u⟫_ℂ = ⟪psi, P (X psi)⟫_ℂ - ⟪psi, P psi⟫_ℂ * ⟪psi, X psi⟫_ℂ :=
    inner_centered P X hP psi hnorm
  have hcomm' : ⟪psi, X (P psi)⟫_ℂ - ⟪psi, P (X psi)⟫_ℂ = (Complex.I * hbar : ℂ) := by
    rw [← inner_sub_right, hcomm, inner_smul_right, hpp, mul_one]
  have hkey : ⟪u, v⟫_ℂ - (starRingEnd ℂ) ⟪u, v⟫_ℂ = (Complex.I * hbar : ℂ) := by
    have hconj : (starRingEnd ℂ) ⟪u, v⟫_ℂ = ⟪v, u⟫_ℂ := inner_conj_symm v u
    rw [hconj, h1, h2, ← hcomm']
    ring
  have := congrArg Complex.im hkey
  simp only [Complex.sub_im, Complex.conj_im, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, Complex.ofReal_im] at this
  linarith

/-- **Heisenberg uncertainty principle** (Robertson form for the canonical commutator).

Let `E` be a complex inner product space of states, and let `X` and `P` be symmetric
(formally self-adjoint) linear operators — position and momentum — satisfying the canonical
commutation relation `X P psi - P X psi = i ℏ psi` at a normalized state `psi`.

Then the product of the uncertainties `Δx = ‖(X - ⟪X⟫) psi‖` and `Δp = ‖(P - ⟪P⟫) psi‖`
is at least `ℏ / 2`.

The analytic ingredient is Cauchy–Schwarz, `norm_inner_le_norm`. -/
