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

theorem exists_isPath_of_reflTransGen {a b : ℕ} (h : Relation.ReflTransGen edge a b) :
    ∃ p t, IsPath edge p t a b := by
  induction h with
  | refl => exact ⟨fun _ => a, 0, rfl, rfl, by omega⟩
  | @tail c d _ hcd ih =>
      obtain ⟨p, t, h0, ht, hstep⟩ := ih
      refine ⟨fun i => if i ≤ t then p i else d, t + 1, ?_, ?_, ?_⟩
      · simpa using h0
      · simp
      · intro i hi
        rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hi) with h | h
        · have h1 : i ≤ t := le_of_lt h
          have h2 : i + 1 ≤ t := h
          simp only [h1, h2, if_pos]
          exact hstep i h
        · subst h
          have h1 : ¬ (i + 1 ≤ i) := by omega
          simp only [le_refl, if_pos, if_neg h1]
          rw [ht]
          exact hcd

/-- A walk of length at most `2 ^ k` whose vertices are all `< 2 ^ s` witnesses the
Savitch predicate at level `k`. -/
