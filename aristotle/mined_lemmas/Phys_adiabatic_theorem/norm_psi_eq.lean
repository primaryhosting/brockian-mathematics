/-
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Adiabatic Theorem
Category: Frontier Phys
Target: Phys.adiabatic_theorem
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped InnerProductSpace

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

namespace Phys

/-! ## The pure ring algebra behind Kato's construction -/

/-- The algebraic heart of the adiabatic theorem.  In a ring, let `p` be an idempotent,
`k` an element annihilating `p` on both sides (think of `k = H - E` with `p` the spectral
projection of the eigenvalue `E`), `d` the derivative of `p` (so that `d = d*p + p*d`), and `b`
a two-sided inverse of `k + p`.  Then the explicitly constructed element
`b*(1-p)*d*p - p*d*(1-p)*b` has commutator with `k` equal to `d`. -/

lemma norm_psi_eq {ε : ℝ} (hHam_sa : ∀ s, IsSelfAdjoint (Ham s)) (psi : ℝ → 𝓗)
    (hpsi : ∀ s, HasDerivAt psi (-(Complex.I / ε) • (Ham s (psi s))) s)
    (hpsi0 : ‖psi 0‖ = 1) (s : ℝ) : ‖psi s‖ = 1 := by
  have hd : ∀ t : ℝ, HasDerivAt (fun u => ⟪psi u, psi u⟫_ℂ) 0 t := by
    intro t
    have h := hasDerivAt_expectation Ham (fun _ => (1 : 𝓗 →L[ℂ] 𝓗)) 0 hHam_sa psi t (hpsi t)
      (hasDerivAt_const t (1 : 𝓗 →L[ℂ] 𝓗))
    simpa using h
  have hdiff : Differentiable ℝ (fun u => ⟪psi u, psi u⟫_ℂ) := fun t => (hd t).differentiableAt
  have hconst := is_const_of_deriv_eq_zero hdiff (fun t => (hd t).deriv) s 0
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hpsi0] at hconst
  have h2 : (‖psi s‖ : ℝ) ^ 2 = 1 ^ 2 := by exact_mod_cast hconst
  nlinarith [norm_nonneg (psi s)]

/-- **Adiabatic theorem.**  Let `s ↦ H(s)` be a `C¹` family of self-adjoint Hamiltonians on a
finite-dimensional complex Hilbert space, and let `P(s)` be a `C²` family of rank-one
(i.e. nondegenerate) orthogonal spectral projections for an eigenvalue `E(s)` that is
separated from the rest of the spectrum by a uniform gap `gap > 0`.  Then there is a constant
`C`, depending only on the family, such that every solution of the Schrödinger equation
`i ε ψ'(s) = H(s) ψ(s)` starting in the eigenspace of `H(0)` stays within `C √ε` of the
instantaneous eigenspace of `H(s)` for all `s ∈ [0,1]`: the state is dragged along with the
slowly varying eigenspace.  (Physical time is `t = s/ε`, so `ε → 0` is exactly the
slowly-varying limit.)

The nondegeneracy hypothesis `hP_rank` is included because it is part of the physical
statement; the proof only uses that `P s` is an orthogonal projection onto an eigenspace
separated by a gap.  The solution `psi` is assumed to solve the Schrödinger equation on all
of `ℝ`, which is no restriction: the Hamiltonian family is globally `C¹`, so solutions of
this linear equation extend to all of `ℝ`.  See `Phys.adiabatic_hypotheses_satisfiable` for
a model satisfying all the hypotheses. -/
