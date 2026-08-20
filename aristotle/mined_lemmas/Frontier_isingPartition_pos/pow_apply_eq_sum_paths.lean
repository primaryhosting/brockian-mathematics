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

/-! ## The two-dimensional Ising model on a periodic square lattice -/

/-- The real spin value attached to a Boolean spin variable: `true ↦ +1`, `false ↦ -1`. -/

theorem pow_apply_eq_sum_paths {S : Type} [Fintype S] [DecidableEq S] (T : Matrix S S ℝ) :
    ∀ (m : ℕ) (x y : S), (T ^ (m + 1)) x y =
      ∑ f : Fin m → S,
        (∏ i : Fin m, T ((Fin.cons x f : Fin (m + 1) → S) i.castSucc)
            ((Fin.cons x f : Fin (m + 1) → S) i.succ)) *
          T ((Fin.cons x f : Fin (m + 1) → S) (Fin.last m)) y := by
  intro m
  induction m with
  | zero => intro x y; simp
  | succ m ih =>
      intro x y
      have hpow : (T ^ (m + 2)) x y = ∑ z : S, T x z * (T ^ (m + 1)) z y := by
        rw [pow_succ']
        simp [Matrix.mul_apply]
      rw [hpow]
      simp only [ih]
      rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => S)), Fintype.sum_prod_type]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun f _ => ?_
      show T x z * _ = _
      rw [Fin.prod_univ_succ]
      simp only [Fin.consEquiv, Equiv.coe_fn_mk, Fin.castSucc_zero, Fin.cons_zero,
        Fin.succ_zero_eq_one, ← Fin.succ_castSucc, Fin.cons_succ, ← Fin.succ_last]
      rw [show (1 : Fin (m + 2)) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
      ring

/-- The trace of a matrix power as a sum over closed cycles. -/
