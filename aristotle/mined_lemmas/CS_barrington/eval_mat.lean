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

theorem eval_mat (k : ℕ) : ∀ P : BProg, P.length ≤ 2 ^ k → ∀ (x : ℕ → Bool) (i j : Fin 5),
    (mat k P i j).eval x = decide (P.eval x i = j) := by
  induction k with
  | zero =>
      intro P hP x i j
      match P with
      | [] => simp [mat, matBase, BProg.eval, Circuit.eval]
      | [t] =>
          cases ht : x t.1 <;>
            simp [mat, matBase, matOne, BProg.eval, Circuit.eval, Instr.run, ht]
      | t :: u :: r => simp at hP
  | succ k ih =>
      intro P hP x i j
      have hsplit : P.take (2 ^ k) ++ P.drop (2 ^ k) = P := List.take_append_drop _ _
      have h1 : (P.take (2 ^ k)).length ≤ 2 ^ k := by simp
      have h2 : (P.drop (2 ^ k)).length ≤ 2 ^ k := by
        have : P.length ≤ 2 ^ k + 2 ^ k := by
          have : (2:ℕ) ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
          omega
        simp only [List.length_drop]
        omega
      have hPe : P.eval x = BProg.eval (P.take (2 ^ k)) x * BProg.eval (P.drop (2 ^ k)) x := by
        conv_lhs => rw [← hsplit]
        exact BProg.eval_append _ _ x
      simp only [mat, eval_orAll, Circuit.eval, Bool.and_eq_true, ih _ h1, ih _ h2,
        decide_eq_true_eq, hPe, Equiv.Perm.mul_apply, decide_eq_decide]
      constructor
      · rintro ⟨l, hl1, hl2⟩
        rw [hl1]; exact hl2
      · intro h
        exact ⟨_, rfl, h⟩

/-- Every width-5 permutation branching program of length `L` is simulated by a Boolean
circuit of depth at most `4 * ⌈log₂ L⌉ + 6`. -/
