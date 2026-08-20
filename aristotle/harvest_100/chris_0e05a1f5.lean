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

/-
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Heisenberg Uncertainty
Category: Quantum Physics
Target: QPhys.heisenberg_uncertainty
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace QPhys

open ComplexConjugate

local notation "⟪" x ", " y "⟫" => inner ℂ x y

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- For a symmetric operator `A`, the expectation value `⟪ψ, A ψ⟫` is real. -/
lemma conj_expectation_eq (A : H →ₗ[ℂ] H)
    (hA : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫) (psi : H) :
    conj ⟪psi, A psi⟫ = ⟪psi, A psi⟫ := by
  rw [inner_conj_symm, hA]

/-- The commutator expectation, expressed through the "centred" vectors. -/
lemma inner_sub_inner_eq (A B : H →ₗ[ℂ] H)
    (hA : ∀ u v : H, ⟪A u, v⟫ = ⟪u, A v⟫) (hB : ∀ u v : H, ⟪B u, v⟫ = ⟪u, B v⟫)
    (psi : H) :
    ⟪A psi - ⟪psi, A psi⟫ • psi, B psi - ⟪psi, B psi⟫ • psi⟫
      - ⟪B psi - ⟪psi, B psi⟫ • psi, A psi - ⟪psi, A psi⟫ • psi⟫
      = ⟪psi, A (B psi) - B (A psi)⟫ := by
  have ha : conj ⟪psi, A psi⟫ = ⟪psi, A psi⟫ := conj_expectation_eq A hA psi
  have hb : conj ⟪psi, B psi⟫ = ⟪psi, B psi⟫ := conj_expectation_eq B hB psi
  have hAp : ⟪A psi, psi⟫ = ⟪psi, A psi⟫ := by rw [← inner_conj_symm, ha]
  have hBp : ⟪B psi, psi⟫ = ⟪psi, B psi⟫ := by rw [← inner_conj_symm, hb]
  have h1 : ⟪psi, A (B psi)⟫ = ⟪A psi, B psi⟫ := by rw [hA]
  have h2 : ⟪psi, B (A psi)⟫ = ⟪B psi, A psi⟫ := by rw [hB]
  simp only [inner_sub_left, inner_sub_right, inner_smul_left, inner_smul_right,
    h1, h2, ha, hb, hAp, hBp]
  ring

/--
**Heisenberg uncertainty principle** (Robertson form, specialised to the canonical
commutation relation).

Let `X` and `P` be symmetric (formally self-adjoint) operators on a complex inner
product space, and let `psi` be a normalized state satisfying the canonical
commutation relation `X P psi - P X psi = (i ℏ) psi`.  Then the product of the
standard deviations of `X` and `P` in the state `psi` is at least `ℏ / 2`.

The proof is the classical one: the commutator expectation equals twice the
imaginary part of `⟪Δx ψ, Δp ψ⟫`, which is bounded by its modulus, which in turn
is bounded by `‖Δx ψ‖ ‖Δp ψ‖` by Cauchy–Schwarz (`norm_inner_le_norm`).
-/
theorem heisenberg_uncertainty
    (X P : H →ₗ[ℂ] H)
    (hX : ∀ u v : H, ⟪X u, v⟫ = ⟪u, X v⟫)
    (hP : ∀ u v : H, ⟪P u, v⟫ = ⟪u, P v⟫)
    (hbar : ℝ) (psi : H) (hpsi : ‖psi‖ = 1)
    (hcomm : X (P psi) - P (X psi) = ((hbar : ℂ) * Complex.I) • psi) :
    ‖X psi - ⟪psi, X psi⟫ • psi‖ * ‖P psi - ⟪psi, P psi⟫ • psi‖ ≥ hbar / 2 := by
  set u : H := X psi - ⟪psi, X psi⟫ • psi with hu
  set v : H := P psi - ⟪psi, P psi⟫ • psi with hv
  -- the commutator expectation
  have hnorm : ⟪psi, psi⟫ = (1 : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, hpsi]; norm_num
  have hkey : ⟪u, v⟫ - ⟪v, u⟫ = (hbar : ℂ) * Complex.I := by
    rw [hu, hv, inner_sub_inner_eq X P hX hP psi, hcomm, inner_smul_right, hnorm]
    ring
  -- hence the imaginary part of ⟪u, v⟫ is ℏ/2
  have hconj : ⟪v, u⟫ = conj ⟪u, v⟫ := (inner_conj_symm v u).symm
  have him : (⟪u, v⟫).im = hbar / 2 := by
    have h := congrArg Complex.im hkey
    rw [hconj, Complex.sub_im, Complex.conj_im] at h
    simp only [Complex.mul_im, Complex.I_im, Complex.I_re, Complex.ofReal_re,
      Complex.ofReal_im] at h
    linarith
  have h1 : hbar / 2 ≤ ‖⟪u, v⟫‖ := by
    have := Complex.abs_im_le_norm ⟪u, v⟫
    rw [him] at this
    exact le_trans (le_abs_self _) this
  exact le_trans h1 (norm_inner_le_norm u v)

end QPhys

