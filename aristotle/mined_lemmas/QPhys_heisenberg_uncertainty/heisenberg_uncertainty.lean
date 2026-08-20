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

