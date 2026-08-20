/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

open scoped TensorProduct

namespace Phys

open Representation

variable {k G M N : Type*} [Field k] [IsAlgClosed k] [Monoid G]
  [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- The range of an intertwining map, as a subrepresentation of the target. -/

theorem exists_unique_reduced_scalar {ρ : Representation k G M} {σ : Representation k G N}
    [FiniteDimensional k N] [σ.IsIrreducible]
    (C T : M →ₗ[k] N)
    (hC : ∀ g x, C (ρ g x) = σ g (C x)) (hT : ∀ g x, T (ρ g x) = σ g (T x))
    (hC0 : C ≠ 0) (hker : ∀ x, C x = 0 → T x = 0) :
    ∃! r : k, ∀ x, T x = r • C x := by
  have hsurj : Function.Surjective C := surjective_of_ne_zero C hC hC0
  -- factor `T` through `C`
  set e := LinearMap.quotKerEquivOfSurjective C hsurj
  have hker' : LinearMap.ker C ≤ LinearMap.ker T := fun x hx =>
    hker x (by simpa using hx)
  set phi : N →ₗ[k] N := ((LinearMap.ker C).liftQ T hker').comp e.symm.toLinearMap with hphi
  have hphiC : ∀ x, phi (C x) = T x := by
    intro x
    have hx : e (Submodule.Quotient.mk x) = C x := rfl
    have : e.symm (C x) = Submodule.Quotient.mk x := by
      rw [← hx, LinearEquiv.symm_apply_apply]
    simp only [hphi, LinearMap.comp_apply, LinearEquiv.coe_coe, this]
    rfl
  -- `phi` is an intertwining map
  have hphieq : ∀ g n, phi (σ g n) = σ g (phi n) := by
    intro g n
    obtain ⟨x, rfl⟩ := hsurj n
    rw [← hC g x, hphiC, hphiC, hT]
  let Phi : IntertwiningMap σ σ := ⟨phi, fun g n => hphieq g n⟩
  obtain ⟨r, hr⟩ := (IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed
    (ρ := σ)).2 Phi
  have hrphi : ∀ n, phi n = r • n := by
    intro n
    have : (algebraMap k (IntertwiningMap σ σ) r) n = Phi n := by rw [hr]
    simpa using this.symm
  refine ⟨r, fun x => by rw [← hphiC, hrphi], ?_⟩
  intro s hs
  obtain ⟨x, hx⟩ : ∃ x, C x ≠ 0 := by
    by_contra h
    exact hC0 (by ext x; simpa using not_not.mp (not_exists.mp h x))
  have := hs x
  rw [← hphiC x, hrphi] at this
  have hsub : (r - s) • C x = 0 := by
    rw [sub_smul, sub_eq_zero]; exact this
  rcases smul_eq_zero.mp hsub with h | h
  · exact (sub_eq_zero.mp h).symm
  · exact absurd h hx

/-- **The Wigner–Eckart theorem.**

Let `U`, `V`, `W` be representations of a symmetry group `G` over an algebraically closed field
(think `G = SU(2)`, `U` the spin-`k` space of a tensor operator, `V` the spin-`j` initial space
and `W` the spin-`j'` final space), with `W` irreducible and finite-dimensional.

Let `CG : U ⊗ V →ₗ W` be the Clebsch–Gordan intertwiner and `T : U ⊗ V →ₗ W` the intertwiner
attached to an irreducible tensor operator, and assume the multiplicity-one condition that
`CG` and `T` cannot separate vectors that `CG` kills.

Then there is a *unique* scalar `r` — the reduced matrix element `⟨j' ‖ T ‖ j⟩`, independent of
the magnetic quantum numbers — such that every matrix element `⟨j' m' | T^k_q | j m⟩` factors as
the Clebsch–Gordan coefficient times `r`. -/
