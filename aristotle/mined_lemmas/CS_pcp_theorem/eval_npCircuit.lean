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

theorem eval_npCircuit :
    V.npCircuit.eval (Fin.append x y) = true ↔
      ((∀ r, V.dec.eval (Fin.append (Fin.append x r) (fun i => y (V.enc (r, i)))) = true) ∧
        (∀ r i r' i',
          (∀ j, (V.query i j).eval (Fin.append x r) = (V.query i' j).eval (Fin.append x r')) →
            y (V.enc (r, i)) = y (V.enc (r', i')))) := by
  simp only [npCircuit, Circuit.eval_bigAnd, npList, List.mem_append, List.mem_map,
    Finset.mem_toList, Finset.mem_univ, true_and]
  constructor
  · intro h
    refine ⟨fun r => ?_, fun r i r' i' hq => ?_⟩
    · simpa using h (V.decC r) (Or.inl ⟨r, rfl⟩)
    · exact (eval_consC V x y r i r' i').1
        (h (V.consC r i r' i') (Or.inr ⟨((r, i), (r', i')), rfl⟩)) hq
  · rintro ⟨h1, h2⟩ c (⟨r, rfl⟩ | ⟨p, rfl⟩)
    · simpa using h1 r
    · exact (eval_consC V x y p.1.1 p.1.2 p.2.1 p.2.2).2 (h2 p.1.1 p.1.2 p.2.1 p.2.2)

/-- If some proof is accepted with probability one, the associated NP circuit is
satisfiable. -/
