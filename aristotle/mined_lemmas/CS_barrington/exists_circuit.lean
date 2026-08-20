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

theorem exists_circuit (P : BProg) (γ : Perm (Fin 5)) :
    ∃ c : Circuit, c.depth ≤ 4 * Nat.clog 2 P.length + 6 ∧
      ∀ x, c.eval x = decide (P.eval x = γ) := by
  have hk : P.length ≤ 2 ^ Nat.clog 2 P.length := Nat.le_pow_clog (by norm_num) _
  refine ⟨andAll fun i => mat (Nat.clog 2 P.length) P i (γ i), ?_, ?_⟩
  · have := depth_andAll (fun i => depth_mat (Nat.clog 2 P.length) P i (γ i))
    omega
  · intro x
    rw [eval_andAll]
    simp only [eval_mat _ P hk x, decide_eq_true_eq, decide_eq_decide]
    exact (Equiv.ext_iff).symm

/-! ## Barrington's theorem -/

/-- **Barrington's theorem: `NC¹` equals width-5 permutation branching programs.**

* Any Boolean circuit of depth `d` is computed by a width-5 permutation branching program
  of length at most `4 ^ d` (the program outputs a fixed five-cycle `γ` exactly on the
  accepted inputs, and the identity elsewhere).
* Conversely, any width-5 permutation branching program of length `L` — read as accepting
  the inputs on which its output is a prescribed permutation `γ` — is computed by a Boolean
  circuit of depth at most `4 * ⌈log₂ L⌉ + 6`.

Thus depth `O(log n)` circuits correspond exactly to branching programs of polynomial
length. -/
