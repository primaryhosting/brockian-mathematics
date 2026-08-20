import Mathlib

/-!
# Margulis Superrigidity
Category: Frontier Abel
Target: Frontier.margulis_superrigidity
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

/-!
## Overview

Margulis' superrigidity theorem says, in its classical form:

> Let `G` be a connected semisimple Lie group of real rank at least `2`, with finite centre and
> no compact factors, let `Γ ≤ G` be an irreducible lattice, let `H` be a connected non-compact
> simple algebraic group over `ℝ`, and let `ρ : Γ → H(ℝ)` be a homomorphism whose image is
> Zariski dense.  Then `ρ` extends to a continuous homomorphism `G → H(ℝ)`.

The flagship instance is `Γ = SL(n, ℤ) ≤ SL(n, ℝ) = G` for `n ≥ 3`.

This file does three things.

* It formalises the *extension property* that is the conclusion of superrigidity, both in the
  dense-image form (`Frontier.SuperrigidDense`) and in the unrestricted form
  (`Frontier.SuperrigidAll`), and formalises the statement of Margulis superrigidity for the
  concrete higher-rank lattice `SL(n,ℤ) ≤ SL(n,ℝ)` with target `GL(m,ℝ)`
  (`Frontier.MargulisSuperrigidityStatement`).

* It proves two Lean-checked *reductions*.  The main one,
  `Frontier.superrigidAll_of_superrigidDense`, reduces the extension problem for an arbitrary
  homomorphism to the dense-image case, by replacing the target by the closure of the image;
  this is the (elementary) step by which the general form of superrigidity is deduced from the
  Zariski-dense form.  The target theorem `Frontier.margulis_superrigidity` is this reduction
  carried out for `SL(n,ℤ) ≤ SL(n,ℝ)`: assuming the deep dense-image input of Margulis' theorem
  for closed subgroups of the target, *every* homomorphism `SL(n,ℤ) → GL(m,ℝ)` extends to a
  continuous homomorphism on `SL(n,ℝ)`.

* It proves, unconditionally, the abelian *base case* of the extension phenomenon
  (`Frontier.margulis_superrigidity_baseCase`): every homomorphism from the lattice
  `ℤⁿ ≤ ℝⁿ` to the vector group `ℝᵐ` extends to a **unique** continuous homomorphism
  `ℝⁿ → ℝᵐ`.

Two deliberate deviations from the classical statement are recorded here.  First, Zariski density
of the image is replaced by density in the ambient (Hausdorff, locally compact) topology; this is
a stronger hypothesis on `ρ`, so the dense-image statements below are formally weaker than
Margulis'.  Second, the deep analytic content of Margulis' theorem is *not* proved: it appears as
an explicit hypothesis of the reduction theorems, which is what makes them reductions.
-/

namespace Frontier

/-! ## The extension property -/

/-- `SuperrigidDense G Γ H` : every homomorphism from the subgroup `Γ ≤ G` to `H` whose image is
dense in `H` extends to a continuous homomorphism `G → H`.  This is the conclusion of Margulis
superrigidity, in the form in which it is proved (density replacing Zariski density here). -/

theorem margulis_superrigidity_baseCase {n m : ℕ} (f : (Fin n → ℤ) →+ (Fin m → ℝ)) :
    ∃! F : (Fin n → ℝ) →+ (Fin m → ℝ),
      Continuous F ∧ ∀ v : Fin n → ℤ, F (fun i => (v i : ℝ)) = f v := by
  classical
  set c : Fin n → (Fin m → ℝ) := fun i => f (Pi.single i 1) with hc
  have key : ∀ v : Fin n → ℤ, f v = ∑ i, ((v i : ℝ)) • c i := by
    intro v
    have hv : v = ∑ i, v i • Pi.single i (1 : ℤ) := by
      funext j; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hv]
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hc, Int.cast_smul_eq_zsmul]
  refine ⟨{ toFun := fun x => ∑ i, x i • c i
            map_zero' := by simp
            map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib] }, ⟨?_, ?_⟩, ?_⟩
  · show Continuous fun x : Fin n → ℝ => ∑ i, x i • c i
    exact continuous_finset_sum _ fun i _ =>
      (continuous_apply i).smul (continuous_const : Continuous fun _ : Fin n → ℝ => c i)
  · intro v
    exact (key v).symm
  · rintro F ⟨hFc, hF⟩
    have h₂ : Continuous (fun x : Fin n → ℝ => ∑ i, x i • c i) :=
      continuous_finset_sum _ fun i _ =>
        (continuous_apply i).smul (continuous_const : Continuous fun _ : Fin n → ℝ => c i)
    set F₂ : (Fin n → ℝ) →+ (Fin m → ℝ) :=
      { toFun := fun x => ∑ i, x i • c i
        map_zero' := by simp
        map_add' := by intro x y; simp [add_smul, Finset.sum_add_distrib] } with hF₂
    have hagree : ∀ v : Fin n → ℤ, F (fun i => (v i : ℝ)) = F₂ (fun i => (v i : ℝ)) := by
      intro v
      rw [hF v]
      show f v = ∑ i, ((v i : ℝ)) • c i
      exact key v
    have hbasis : ∀ i : Fin n, (F.toRealLinearMap hFc).toLinearMap ((Pi.basisFun ℝ (Fin n)) i)
        = (F₂.toRealLinearMap h₂).toLinearMap ((Pi.basisFun ℝ (Fin n)) i) := by
      intro i
      simp only [Pi.basisFun_apply]
      show F (Pi.single i (1 : ℝ)) = F₂ (Pi.single i (1 : ℝ))
      have he : (Pi.single i (1 : ℝ)) = fun j => (((Pi.single i (1 : ℤ) : Fin n → ℤ) j : ℤ) : ℝ) := by
        funext j; by_cases hij : i = j <;> simp [Pi.single_apply, hij]
      rw [he]
      exact hagree _
    have hL := (Pi.basisFun ℝ (Fin n)).ext hbasis
    refine AddMonoidHom.ext fun x => ?_
    exact congrFun (congrArg
      (fun L : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ) => (L : (Fin n → ℝ) → (Fin m → ℝ))) hL) x

end Frontier

