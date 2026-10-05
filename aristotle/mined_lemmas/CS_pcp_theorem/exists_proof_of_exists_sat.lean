import Mathlib
/-!
# Pcp Theorem
Category: Frontier Cs
Target: CS.pcp_theorem
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

namespace CS

/-! ## Polynomial bounds -/

/-- `PolyBd f` says that `f : ℕ → ℕ` is bounded by a polynomial. -/

theorem exists_proof_of_exists_sat
    (h : ∃ y : Fin V.wlen → Bool, V.npCircuit.eval (Fin.append x y) = true) :
    ∃ pi : (Fin V.plen → Bool) → Bool, ∀ r, V.accepts x r pi = true := by
  obtain ⟨y, hy⟩ := h
  rw [eval_npCircuit] at hy
  obtain ⟨h1, h2⟩ := hy
  classical
  refine ⟨fun p => if hp : ∃ ri : (Fin V.rlen → Bool) × Fin V.qnum,
      (fun j => (V.query ri.2 j).eval (Fin.append x ri.1)) = p then y (V.enc hp.choose)
      else false, ?_⟩
  have key : ∀ (r : Fin V.rlen → Bool) (i : Fin V.qnum),
      (if hp : ∃ ri : (Fin V.rlen → Bool) × Fin V.qnum,
          (fun j => (V.query ri.2 j).eval (Fin.append x ri.1))
            = (fun j => (V.query i j).eval (Fin.append x r))
        then y (V.enc hp.choose) else false) = y (V.enc (r, i)) := by
    intro r i
    have hex : ∃ ri : (Fin V.rlen → Bool) × Fin V.qnum,
        (fun j => (V.query ri.2 j).eval (Fin.append x ri.1))
          = (fun j => (V.query i j).eval (Fin.append x r)) := ⟨(r, i), rfl⟩
    rw [dif_pos hex]
    exact h2 hex.choose.1 hex.choose.2 r i (fun j => congrFun hex.choose_spec j)
  intro r
  simp only [accepts]
  refine Eq.trans ?_ (h1 r)
  exact congrArg (fun f => V.dec.eval (Fin.append (Fin.append x r) f)) (funext fun i => key r i)

/-! ### Size of the constructed circuit -/

