/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.Savitch.Model
import RequestProject.Savitch.Reach
import RequestProject.Savitch.Interp
import RequestProject.Savitch.BigStep
import RequestProject.Savitch.Invariant
import RequestProject.Savitch.Encode

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Statement

`NSPACE(f) ⊆ DSPACE(f²)`, and consequently `PSPACE = NPSPACE` (Savitch's theorem).

The model of computation is the standard configuration-graph model, set up in
`RequestProject.Savitch.Model`: configurations are natural numbers (binary strings), a machine
runs in space `f` on input `x` if all configurations reachable on `x` are `< 2 ^ f |x|`, and
one step may depend on the current configuration together with the single input symbol scanned
by the input head, whose position is determined by the configuration.  The initial
configuration may depend on the input length (the usual assumption that the space bound is
constructible).  No computability assumption is imposed on the transition functions.

The deterministic simulator is built explicitly: it performs the depth-first evaluation of
Savitch's divide-and-conquer recursion, its states are recursion stacks of depth at most `s`,
each frame holding boundedly many numbers `< 2 ^ s`, and the whole state is encoded as a
natural number `< 2 ^ (42 * (s + 1) ^ 2)`.  Hence a nondeterministic machine running in space
`f` is simulated deterministically in space `42 * (f + 1) ^ 2`.
-/

namespace CS

open Classical

variable {Γ : Type}

/-! ### Deterministic machines are nondeterministic machines -/

/-- A deterministic machine, viewed as a nondeterministic one. -/

theorem savitchMachine_step_of_good (N : NMachine Γ) (f : ℕ → ℕ) (x : List Γ) {st : St}
    (h : Good st) :
    (savitchMachine N f).next (encSt st) x[(savitchMachine N f).head (encSt st)]? =
      encSt (stepx N x st) := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  simp only [savitchMachine, decSt_encSt h]
  cases ctrl with
  | eval a b k =>
      cases k with
      | zero => rfl
      | succ k =>
          exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))
  | init => exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))
  | ret v => exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))
  | halt v => exact congrArg encSt (step_symb_irrelevant N _ _ _ (by intro a' b'; simp))

/-- The run of the simulator tracks the run of the abstract stack machine. -/
