/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix ComplexConjugate
open scoped BigOperators ComplexOrder

namespace QI

/-! ## Linear-algebra preliminaries -/

section RankLemmas

variable {X Y : Type*}

/-- Rank–nullity for the linear map `v ↦ M *ᵥ v`. -/

lemma rank_le_rank_ptrace_mul [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (ρ : Matrix (X × Y) (X × Y) ℂ) (hρ : ρ.PosSemidef) :
    ρ.rank ≤ (Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y)).rank * Fintype.card Y := by
  classical
  set ρX : Matrix X X ℂ := Matrix.of fun x x' : X => ∑ y, ρ (x, y) (x', y) with hρX
  have hmem : ∀ f : Y → (LinearMap.ker ρX.mulVecLin),
      ρ.mulVecLin (fun p : X × Y => (f p.2).1 p.1) = 0 := by
    intro f
    have hslice : ∀ y : Y, ρ *ᵥ (fun p : X × Y => if p.2 = y then (f y).1 p.1 else 0) = 0 := by
      intro y
      refine mulVec_slice_eq_zero ρ hρ _ ?_ y
      have h2 := (f y).2
      rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at h2
    funext p
    have hsplit : (ρ *ᵥ (fun p : X × Y => (f p.2).1 p.1)) p
        = ∑ y : Y, (ρ *ᵥ (fun p' : X × Y => if p'.2 = y then (f y).1 p'.1 else 0)) p := by
      simp only [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, mul_ite, mul_zero,
        Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact Finset.sum_comm
    rw [Matrix.mulVecLin_apply, hsplit]
    simp [hslice]
  let Ψ : (Y → (LinearMap.ker ρX.mulVecLin)) →ₗ[ℂ] (LinearMap.ker ρ.mulVecLin) :=
  { toFun := fun f => ⟨fun p => (f p.2).1 p.1, by rw [LinearMap.mem_ker]; exact hmem f⟩
    map_add' := by intros f g; ext p; simp
    map_smul' := by intros c f; ext p; simp }
  have hinj : Function.Injective Ψ := by
    intro f g hfg
    funext y
    apply Subtype.ext
    funext x
    exact congrFun (congrArg Subtype.val hfg) (x, y)
  have hle : Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)
      ≤ Module.finrank ℂ (LinearMap.ker ρ.mulVecLin) := by
    have h := LinearMap.finrank_le_finrank_of_injective (f := Ψ) hinj
    rwa [Module.finrank_pi_fintype, Finset.sum_const, Finset.card_univ, smul_eq_mul] at h
  have h1 := rank_add_finrank_ker ρ
  have h2 := rank_add_finrank_ker ρX
  rw [Fintype.card_prod] at h1
  have h3 : ρ.rank + Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)
      ≤ Fintype.card Y * ρX.rank
        + Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin) := by
    calc ρ.rank + Fintype.card Y * Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)
        ≤ ρ.rank + Module.finrank ℂ (LinearMap.ker ρ.mulVecLin) := by omega
      _ = Fintype.card X * Fintype.card Y := h1
      _ = Fintype.card Y * (ρX.rank + Module.finrank ℂ (LinearMap.ker ρX.mulVecLin)) := by
            rw [h2]; ring
      _ = _ := by ring
  have h4 := Nat.add_le_add_iff_right.1 h3
  rwa [mul_comm] at h4

end RankLemmas

/-! ## The core bound

Abstract form of the quantum Singleton bound: a `K`-dimensional code inside `A ⊗ B ⊗ C`
for which both the `A`-part and the `C`-part are erasure-correctable satisfies `K ≤ dim B`. -/

