import Mathlib

/-!
# Barrington
Category: Frontier Cs
Target: CS.barrington
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Barrington's theorem: the Boolean functions computed by fan-in-two Boolean circuits of
depth `d` are exactly the ones computed by width-5 permutation branching programs of
length `4 ^ d` (up to a constant factor in the exponent / a logarithm in the length).

We formalise the two quantitative directions:

* `CS.exists_bprog`  : a circuit of depth `d` is simulated by a width-5 permutation
  branching program of length at most `4 ^ d`  (the hard direction of Barrington's theorem);
* `CS.exists_circuit`: a width-5 permutation branching program of length `L` is simulated
  by a circuit of depth at most `4 * ⌈log₂ L⌉ + 6` (the easy direction).

Together (`CS.barrington`) these say `NC¹ = width-5 permutation branching programs`:
logarithmic depth corresponds to polynomial length.
-/

namespace CS

open Equiv

/-! ## Boolean circuits -/

/-- Boolean circuits with fan-in two `∧`/`∨` gates and `¬` gates, over the variables
`x 0, x 1, …`. -/
inductive Circuit where
  | const : Bool → Circuit
  | var : ℕ → Circuit
  | not : Circuit → Circuit
  | and : Circuit → Circuit → Circuit
  | or : Circuit → Circuit → Circuit
  deriving Inhabited

/-- The Boolean function computed by a circuit. -/

theorem and_computes {P Q : BProg} {σ τ : Perm (Fin 5)} {f g : (ℕ → Bool) → Bool}
    (h1 : Computes P σ f) (h2 : Computes Q τ g) :
    Computes (P ++ Q ++ P.inv ++ Q.inv) (σ * τ * σ⁻¹ * τ⁻¹) (fun x => f x && g x) := by
  intro x
  simp only [BProg.eval_append, BProg.eval_inv, h1 x, h2 x]
  rcases Bool.eq_false_or_eq_true (f x) with hf | hf <;>
    rcases Bool.eq_false_or_eq_true (g x) with hg | hg <;>
      simp only [hf, hg] <;> simp

