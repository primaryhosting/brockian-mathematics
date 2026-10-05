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

noncomputable def step (N : NMachine Γ) (σ : Option Γ) (st : St) : St :=
  match st.ctrl with
  | .init =>
      if st.target < 2 ^ st.s then
        if N.accept st.target then { st with ctrl := .eval st.a₀ st.target st.s }
        else { st with target := st.target + 1 }
      else { st with ctrl := .halt false }
  | .eval a b 0 => { st with ctrl := .ret (decide (a = b ∨ b ∈ N.next a σ)) }
  | .eval a b (k + 1) =>
      { st with ctrl := .eval a 0 k, stack := ⟨a, b, k, 0, false⟩ :: st.stack }
  | .ret v =>
      match st.stack with
      | [] =>
          if v then { st with ctrl := .halt true }
          else { st with target := st.target + 1, ctrl := .init }
      | fr :: rest =>
          if v then
            if fr.ph then { st with ctrl := .ret true, stack := rest }
            else { st with ctrl := .eval fr.m fr.b fr.k, stack := { fr with ph := true } :: rest }
          else
            if fr.m + 1 < 2 ^ st.s then
              { st with ctrl := .eval fr.a (fr.m + 1) fr.k,
                        stack := { fr with m := fr.m + 1, ph := false } :: rest }
            else { st with ctrl := .ret false, stack := rest }
  | .halt _ => st

/-- The input symbol scanned in a given state. -/
