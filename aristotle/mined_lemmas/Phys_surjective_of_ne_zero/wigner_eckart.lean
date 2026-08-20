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

theorem wigner_eckart {k G U V W : Type*} [Field k] [IsAlgClosed k] [Group G]
    [AddCommGroup U] [Module k U] [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
    (ρU : Representation k G U) (ρV : Representation k G V) (ρW : Representation k G W)
    [FiniteDimensional k W] [ρW.IsIrreducible]
    (CG T : U ⊗[k] V →ₗ[k] W)
    (hCG : ∀ g x, CG ((ρU.tprod ρV) g x) = ρW g (CG x))
    (hT : ∀ g x, T ((ρU.tprod ρV) g x) = ρW g (T x))
    (hCG0 : CG ≠ 0)
    (hmult : ∀ x, CG x = 0 → T x = 0) :
    ∃! r : k, ∀ (bra : W →ₗ[k] k) (u : U) (v : V),
      bra (T (u ⊗ₜ[k] v)) = r * bra (CG (u ⊗ₜ[k] v)) := by
  obtain ⟨r, hr, huniq⟩ := exists_unique_reduced_scalar (ρ := ρU.tprod ρV) (σ := ρW)
    CG T hCG hT hCG0 hmult
  refine ⟨r, fun bra u v => by rw [hr, map_smul, smul_eq_mul], ?_⟩
  intro s hs
  refine huniq s ?_
  intro x
  -- test against all functionals
  have key : ∀ bra : W →ₗ[k] k, bra (T x) = s * bra (CG x) := by
    intro bra
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul u v => exact hs bra u v
    | add a b ha hb => simp only [map_add, ha, hb]; ring
  have : ∀ bra : W →ₗ[k] k, bra (T x - s • CG x) = 0 := by
    intro bra
    simp only [map_sub, map_smul, smul_eq_mul, key bra, sub_self]
  have := (Module.forall_dual_apply_eq_zero_iff k (T x - s • CG x)).mp this
  rw [sub_eq_zero] at this
  exact this

/-! ### Non-vacuity

We check that the hypotheses of `Phys.wigner_eckart` are satisfiable, by instantiating them with
the (one-dimensional, hence irreducible) trivial representation of an arbitrary group on `ℂ`. -/

section NonVacuous

variable {k G V : Type*} [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Subrepresentations of a trivial representation are exactly its submodules. -/
