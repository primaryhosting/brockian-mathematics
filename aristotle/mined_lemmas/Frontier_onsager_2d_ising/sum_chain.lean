import Mathlib
/-!
# Onsager 2 D Ising
Category: Frontier Physics
Target: Frontier.onsager_2d_ising
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

namespace Frontier

noncomputable section

/-! ## The model -/

/-- The real value `±1` of a spin encoded as a `Bool`. -/

theorem sum_chain (K : ℝ) :
    ∀ (k : ℕ) (H : Bool → Bool → ℝ),
      (∑ σ : Fin (k + 1) → Bool,
          (∏ i : Fin k, tw K (σ i.castSucc) (σ i.succ)) * H (σ 0) (σ (Fin.last k)))
        = ∑ a : Bool, ∑ b : Bool, tmat K k a b * H a b := by
  intro k
  induction k with
  | zero =>
      intro H
      rw [← (Equiv.funUnique (Fin 1) Bool).symm.sum_comp (fun x => (∏ i : Fin 0,
        tw K (x i.castSucc) (x i.succ)) * H (x 0) (x (Fin.last 0)))]
      simp [tmat]
  | succ k ih =>
      intro H
      rw [← Equiv.sum_comp (Fin.snocEquiv (fun _ : Fin (k + 2) => Bool)), Fintype.sum_prod_type]
      have key : ∀ (b : Bool) (s : Fin (k + 1) → Bool),
          (∏ i : Fin (k + 1), tw K ((Fin.snoc s b : Fin (k + 2) → Bool) i.castSucc)
              ((Fin.snoc s b : Fin (k + 2) → Bool) i.succ)) *
            H ((Fin.snoc s b : Fin (k + 2) → Bool) 0)
              ((Fin.snoc s b : Fin (k + 2) → Bool) (Fin.last (k + 1)))
          = (∏ i : Fin k, tw K (s i.castSucc) (s i.succ)) *
              (tw K (s (Fin.last k)) b * H (s 0) b) := by
        intro b s
        rw [Fin.prod_univ_castSucc]
        simp only [Fin.succ_castSucc, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last,
          Fin.snoc_apply_zero, mul_assoc]
      simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
      rw [Finset.sum_comm]
      simp only [key]
      have hpull : ∀ s : Fin (k + 1) → Bool,
          (∑ b : Bool, (∏ i : Fin k, tw K (s i.castSucc) (s i.succ)) *
              (tw K (s (Fin.last k)) b * H (s 0) b))
            = (∏ i : Fin k, tw K (s i.castSucc) (s i.succ)) *
                (∑ b : Bool, tw K (s (Fin.last k)) b * H (s 0) b) := by
        intro s; rw [Finset.mul_sum]
      rw [Finset.sum_congr rfl (fun s _ => hpull s)]
      rw [ih (fun a c => ∑ b : Bool, tw K c b * H a b)]
      simp [tmat]
      ring

/-- Exact partition function of the periodic 1D Ising chain (transfer-matrix solution). -/
