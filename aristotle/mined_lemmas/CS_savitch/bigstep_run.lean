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

theorem bigstep_run (N : NMachine Γ) (x : List Γ) (s a₀ : ℕ) :
    ∃ (t : ℕ) (v : Bool) (tg' : ℕ),
      iter N x t ⟨s, a₀, 0, .init, []⟩ = ⟨s, a₀, tg', .halt v, []⟩ ∧
        (v = true ↔ ∃ c, c < 2 ^ s ∧ N.accept c ∧ Reach s (N.stepRel x) s a₀ c) := by
  obtain ⟨t, v, tg', ht, hv⟩ := bigstep_init N x s a₀ (2 ^ s) 0 (by simp)
  refine ⟨t, v, tg', ht, ?_⟩
  rw [hv]
  constructor
  · rintro ⟨c, -, hc2, hc3, hc4⟩; exact ⟨c, hc2, hc3, hc4⟩
  · rintro ⟨c, hc2, hc3, hc4⟩; exact ⟨c, Nat.zero_le _, hc2, hc3, hc4⟩

end CS

