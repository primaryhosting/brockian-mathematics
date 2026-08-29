/-
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Wigner Eckart
Category: Frontier Phys
Target: Phys.wigner_eckart
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace Phys

/-- **Schur's lemma, quantitative form.**

If `M` and `N` are simple modules over a `ℂ`-algebra `A` (e.g. the group algebra of the
symmetry group, or the universal enveloping algebra of its Lie algebra), `N` is
finite-dimensional over `ℂ`, and `CG : M →ₗ[A] N` is a nonzero intertwiner, then *every*
intertwiner `T : M →ₗ[A] N` is a complex multiple of `CG`. -/

theorem wigner_eckart_rep
    {G : Type*} [Monoid G] {V W : Type*}
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (rhoV : Representation ℂ G V) (rhoW : Representation ℂ G W)
    (hV : ∀ p : Submodule ℂ V, (∀ (g : G), ∀ x ∈ p, rhoV g x ∈ p) → p = ⊥ ∨ p = ⊤)
    (hW : ∀ p : Submodule ℂ W, (∀ (g : G), ∀ x ∈ p, rhoW g x ∈ p) → p = ⊥ ∨ p = ⊤)
    (CG T : V →ₗ[ℂ] W) (hCG : CG ≠ 0)
    (hCGeq : ∀ (g : G) (x : V), CG (rhoV g x) = rhoW g (CG x))
    (hTeq : ∀ (g : G) (x : V), T (rhoV g x) = rhoW g (T x))
    {ιin ιout : Type*} (ket : ιin → V) (bra : ιout → (W →ₗ[ℂ] ℂ)) :
    ∃ red : ℂ, ∀ (i : ιin) (o : ιout),
      bra o (T (ket i)) = red * bra o (CG (ket i)) := by
  -- The kernel of `CG` is an invariant subspace, hence `⊥`.
  have hker : LinearMap.ker CG = ⊥ := by
    rcases hV (LinearMap.ker CG) (fun g x hx => by
      simp only [LinearMap.mem_ker] at hx ⊢; rw [hCGeq, hx, map_zero]) with h | h
    · exact h
    · exact absurd (LinearMap.ext fun x => by
        simpa [LinearMap.mem_ker] using (h ▸ Submodule.mem_top : x ∈ LinearMap.ker CG)) hCG
  -- The range of `CG` is an invariant subspace, hence `⊤`.
  have hrange : LinearMap.range CG = ⊤ := by
    rcases hW (LinearMap.range CG) (fun g y hy => by
      obtain ⟨x, rfl⟩ := hy
      exact ⟨rhoV g x, hCGeq g x⟩) with h | h
    · refine absurd (LinearMap.ext fun x => ?_) hCG
      simpa using (h ▸ (LinearMap.mem_range_self CG x) : CG x ∈ (⊥ : Submodule ℂ W))
    · exact h
  set e : V ≃ₗ[ℂ] W :=
    LinearEquiv.ofBijective CG ⟨LinearMap.ker_eq_bot.mp hker, LinearMap.range_eq_top.mp hrange⟩
  have hesymm : ∀ x : V, e.symm (CG x) = x := fun x => e.symm_apply_apply x
  have heapply : ∀ w : W, CG (e.symm w) = w := fun w => e.apply_symm_apply w
  set f : W →ₗ[ℂ] W := T ∘ₗ (e.symm : W →ₗ[ℂ] V) with hf
  -- `f = T ∘ CG⁻¹` is equivariant.
  have hfeq : ∀ (g : G) (w : W), f (rhoW g w) = rhoW g (f w) := by
    intro g w
    have hw : rhoW g w = CG (rhoV g (e.symm w)) := by rw [hCGeq, heapply]
    rw [hw]
    simp only [hf, LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe, hesymm]
    rw [hTeq]
  -- `W` is nontrivial because `CG ≠ 0`.
  obtain ⟨x₀, hx₀⟩ : ∃ x : V, CG x ≠ 0 := by
    by_contra hcon
    exact hCG (LinearMap.ext fun x => by simpa using not_exists.mp hcon x)
  haveI : Nontrivial W := ⟨⟨CG x₀, 0, hx₀⟩⟩
  -- `f` has an eigenvalue `c`; its eigenspace is invariant, hence everything.
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue f
  obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
  have hfv : f v = c • v := Module.End.mem_eigenspace_iff.mp hv
  set g₀ : W →ₗ[ℂ] W := f - c • LinearMap.id with hg₀
  have hmem : ∀ w : W, w ∈ LinearMap.ker g₀ ↔ f w = c • w := by
    intro w
    simp [hg₀, LinearMap.mem_ker, sub_eq_zero]
  have hker₀ : LinearMap.ker g₀ = ⊤ := by
    rcases hW (LinearMap.ker g₀) (fun g w hw => by
      rw [hmem] at hw ⊢
      rw [hfeq, hw, map_smul]) with h | h
    · exact absurd (by simpa [h] using (hmem v).mpr hfv) hv0
    · exact h
  have hfc : ∀ w : W, f w = c • w := fun w =>
    (hmem w).mp (hker₀ ▸ Submodule.mem_top)
  refine ⟨c, fun i o => ?_⟩
  have hTx : T (ket i) = c • CG (ket i) := by
    simpa [hf, hesymm] using hfc (CG (ket i))
  rw [hTx, map_smul, smul_eq_mul]

/-- Sanity check that the hypotheses of `Phys.wigner_eckart` are satisfiable (so the theorem is
not vacuous): the one-dimensional representation of `A = ℂ` with `CG = T = id`. -/
example : ∃ red : ℂ, ∀ (_i : Unit) (_o : Unit), (1 : ℂ) = red * 1 :=
  wigner_eckart (A := ℂ) LinearMap.id LinearMap.id
    (fun h => by simpa using LinearMap.congr_fun h (1 : ℂ))
    (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => LinearMap.id)

/-- Sanity check that the hypotheses of `Phys.wigner_eckart_rep` are satisfiable: the trivial
representation of the trivial group on the one-dimensional space `ℂ`, with `CG = T = id`. -/
example : ∃ red : ℂ, ∀ (_i : Unit) (_o : Unit), (1 : ℂ) = red * 1 :=
  wigner_eckart_rep (G := Unit) 1 1
    (fun p _ => eq_bot_or_eq_top p) (fun p _ => eq_bot_or_eq_top p)
    LinearMap.id LinearMap.id (fun h => by simpa using LinearMap.congr_fun h (1 : ℂ))
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun _ : Unit => (1 : ℂ)) (fun _ : Unit => LinearMap.id)

end Phys

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

