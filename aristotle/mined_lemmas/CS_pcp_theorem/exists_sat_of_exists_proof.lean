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

theorem exists_sat_of_exists_proof
    (h : ∃ pi : (Fin V.plen → Bool) → Bool, ∀ r, V.accepts x r pi = true) :
    ∃ y : Fin V.wlen → Bool, V.npCircuit.eval (Fin.append x y) = true := by
  obtain ⟨pi, hpi⟩ := h
  refine ⟨fun k => pi (fun j => (V.query (V.enc.symm k).2 j).eval
    (Fin.append x (V.enc.symm k).1)), ?_⟩
  have key : ∀ (r : Fin V.rlen → Bool) (i : Fin V.qnum),
      (fun k => pi (fun j => (V.query (V.enc.symm k).2 j).eval
        (Fin.append x (V.enc.symm k).1))) (V.enc (r, i))
        = pi (fun j => (V.query i j).eval (Fin.append x r)) := by
    intro r i
    simp
  rw [eval_npCircuit]
  refine ⟨fun r => ?_, fun r i r' i' hq => ?_⟩
  · have h := hpi r
    simp only [accepts] at h
    refine Eq.trans ?_ h
    exact congrArg (fun f => V.dec.eval (Fin.append (Fin.append x r) f)) (funext fun i => key r i)
  · simp only [Equiv.symm_apply_apply]
    exact congrArg pi (funext hq)

/-- Conversely, a satisfying assignment of the NP circuit yields a proof that is accepted
with probability one. -/
