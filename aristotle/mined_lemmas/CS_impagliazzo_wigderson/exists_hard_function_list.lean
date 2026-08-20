/-
# Impagliazzo Wigderson
Category: Frontier Cs
Target: CS.impagliazzo_wigderson
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

set_option grind.warning false

namespace CS

/-! ## Boolean circuits (straight-line programs) -/

/-- A single gate of a straight-line Boolean program.  Arguments refer to positions in the
current environment (first the input bits, then the values of the previously computed gates).
Out-of-range references evaluate to `false`. -/
inductive Gate
  | const (b : Bool)
  | not (a : ℕ)
  | and (a b : ℕ)
  | or (a b : ℕ)
deriving DecidableEq

/-- A Boolean circuit is a straight-line program, i.e. a list of gates. -/
abbrev Circuit := List Gate

/-- Value of a single gate in a given environment. -/

lemma exists_hard_function_list (n s : ℕ)
    (h : (gateSet (n + s)).card ^ s * (s + 1) < 2 ^ 2 ^ n) :
    ∃ f : List Bool → Bool, ∀ C : Circuit, C.length ≤ s →
      ∃ x : List Bool, x.length = n ∧ C.eval x ≠ f x := by
  obtain ⟨f₀, hf₀⟩ := exists_hard_function n s h
  classical
  refine ⟨fun x => if hx : x.length = n then f₀ (fun i => x.get (Fin.cast hx.symm i)) else false,
    ?_⟩
  intro C hC
  obtain ⟨y, hy⟩ := hf₀ C hC
  refine ⟨List.ofFn y, by simp, ?_⟩
  have hx : (List.ofFn y).length = n := by simp
  simp only [hx, dif_pos]
  have : (fun i => (List.ofFn y).get (Fin.cast hx.symm i)) = y := by
    funext i
    simp
  rw [this]
  exact hy

