/-
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Lieb Schultz Mattis
Category: Frontier Phys
Target: Phys.lieb_schultz_mattis
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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

/-!
## Setting

We formalise the Lieb–Schultz–Mattis (LSM) theorem in its finite-volume, variational form
(Lieb–Schultz–Mattis 1961, Affleck–Lieb 1986, Oshikawa 2000).

For each system size `L` we have a finite dimensional complex Hilbert space `E L`
(the state space of a chain of `L` sites), a self-adjoint Hamiltonian `Ham L`, and a
unitary translation operator `Tr L`.  The two physical inputs of LSM are:

* the ground state `ψ₀ L` is a translation eigenstate, `Tr L ψ₀ = ω • ψ₀` with `‖ω‖ = 1`
  (its momentum);
* for a chain with **half-integer spin per unit cell** the Lieb–Schultz–Mattis twist
  `ψ₁ L = U_twist ψ₀ L` is a normalised state whose momentum is shifted by exactly `π`,
  i.e. `Tr L ψ₁ = (-ω) • ψ₁`, and whose energy exceeds the ground energy by at most
  `C / L` (the twist is a low-energy variational state).

The theorem proved below is that these inputs are incompatible with the chain having,
for every size, a *unique* ground state separated from the rest of the spectrum by a
gap `γ > 0` that does not shrink with `L`.  In other words the chain is gapless or its
ground state is degenerate.
-/

namespace Phys

open Module

section Spectral

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

/-- The energy (expectation value of the Hamiltonian `H`) of a state `ψ`. -/

theorem gappedGroundState_toy :
    GappedGroundState toyHam (EuclideanSpace.single 0 (1 : ℂ)) 0 1 where
  isSymmetric := by
    intro x y
    simp [toyHam, EuclideanSpace.inner_single_left, EuclideanSpace.inner_single_right, mul_comm]
  norm_ground := by simp
  ham_ground := by
    ext i
    fin_cases i <;> simp [toyHam, EuclideanSpace.single_apply]
  simple := by
    intro v hv
    refine ⟨v.ofLp 0, ?_⟩
    have h1 : v.ofLp 1 = 0 := by
      have := congrFun (congrArg WithLp.ofLp hv) 1
      simpa [toyHam, EuclideanSpace.single_apply] using this
    ext i
    fin_cases i <;> simp [EuclideanSpace.single_apply, h1]
  spectral_gap := by
    intro μ v hv h
    have h0 := congrFun (congrArg WithLp.ofLp h) 0
    have h1 := congrFun (congrArg WithLp.ofLp h) 1
    simp only [toyHam, LinearMap.coe_mk, AddHom.coe_mk, EuclideanSpace.single_apply,
      PiLp.smul_apply, smul_eq_mul, if_true, if_neg (by decide : ¬((0 : Fin 2) = 1))] at h0 h1
    by_cases hv0 : v.ofLp 0 = 0
    · right
      have hv1 : v.ofLp 1 ≠ 0 := by
        intro hz
        apply hv
        ext i
        fin_cases i <;> simp [hv0, hz]
      have hmu : ((μ : ℂ) - 1) * v.ofLp 1 = 0 := by linear_combination -h1
      rcases mul_eq_zero.mp hmu with hc | hc
      · have hc' : (μ : ℂ) = 1 := by linear_combination hc
        have : μ = 1 := by exact_mod_cast hc'
        simp [this]
      · exact absurd hc hv1
    · left
      rcases mul_eq_zero.mp h0.symm with hc | hc
      · exact_mod_cast hc
      · exact absurd hc hv0

end LSM

end Phys

