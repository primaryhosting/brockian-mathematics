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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-! ## The 2D Ising model on a periodic `m × n` lattice (a torus) -/

/-- Real value of an Ising spin: `true ↦ +1`, `false ↦ -1`. -/

theorem sum_path_prod_eq_trace {S : Type} [Fintype S] [DecidableEq S]
    (T A : Matrix S S ℝ) (j : ℕ) :
    ∑ r : Fin (j + 1) → S,
        (A (r (Fin.last j)) (r 0) * ∏ i : Fin j, T (r i.castSucc) (r i.succ))
      = Matrix.trace (A * T ^ j) := by
  induction j generalizing A with
  | zero =>
      simp only [Matrix.trace, Matrix.diag, pow_zero, mul_one, Finset.univ_unique,
        Finset.prod_empty, Finset.prod_const_one, mul_one, Fin.last_zero]
      exact Fintype.sum_equiv (Equiv.funUnique (Fin 1) S) _ _ (fun _ => rfl)
  | succ j ih =>
      have key : ∑ r : Fin (j + 2) → S,
          (A (r (Fin.last (j + 1))) (r 0) * ∏ i : Fin (j + 1), T (r i.castSucc) (r i.succ))
          = ∑ p : S × (Fin (j + 1) → S),
              (A p.1 (p.2 0) * ((∏ i : Fin j, T (p.2 i.castSucc) (p.2 i.succ))
                * T (p.2 (Fin.last j)) p.1)) := by
        refine (Fintype.sum_equiv (Fin.snocEquiv (fun _ : Fin (j + 2) => S)) _ _ ?_).symm
        rintro ⟨u, q⟩
        simp only [Fin.snocEquiv, Equiv.coe_fn_mk]
        rw [Fin.prod_univ_castSucc]
        have h0 : (0 : Fin (j + 2)) = (0 : Fin (j + 1)).castSucc := rfl
        rw [h0, Fin.snoc_castSucc, Fin.snoc_last, Fin.snoc_castSucc, Fin.succ_last, Fin.snoc_last]
        congr 2
        refine Finset.prod_congr rfl ?_
        intro i _
        rw [show i.castSucc.castSucc = (Fin.castSucc i).castSucc from rfl, Fin.snoc_castSucc,
          Fin.succ_castSucc, Fin.snoc_castSucc]
      rw [key, Fintype.sum_prod_type_right]
      have hstep : ∀ q : Fin (j + 1) → S,
          ∑ u : S, A u (q 0) * ((∏ i : Fin j, T (q i.castSucc) (q i.succ)) * T (q (Fin.last j)) u)
            = (T * A) (q (Fin.last j)) (q 0) * ∏ i : Fin j, T (q i.castSucc) (q i.succ) := by
        intro q
        rw [Matrix.mul_apply, Finset.sum_mul]
        exact Finset.sum_congr rfl (fun _ _ => by ring)
      simp_rw [hstep]
      rw [ih (T * A)]
      calc Matrix.trace ((T * A) * T ^ j) = Matrix.trace (T * (A * T ^ j)) := by rw [mul_assoc]
        _ = Matrix.trace ((A * T ^ j) * T) := Matrix.trace_mul_comm _ _
        _ = Matrix.trace (A * T ^ (j + 1)) := by rw [mul_assoc, ← pow_succ]

/-- Sum over closed paths: `∑_{r : Fin (j+1) → S} ∏_i T(r i, r (i+1)) = tr (T^(j+1))`,
the indices being read cyclically. -/
