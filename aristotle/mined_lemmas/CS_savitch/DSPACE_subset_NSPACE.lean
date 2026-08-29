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

theorem DSPACE_subset_NSPACE (g : ℕ → ℕ) : DSPACE Γ g ⊆ NSPACE Γ g := by
  rintro L ⟨M, hsp, hdec⟩
  refine ⟨M.toNMachine, ?_, ?_⟩
  · intro x c hc
    rw [DMachine.reachable_toNMachine] at hc
    exact hsp x c hc
  · intro x
    constructor
    · rintro ⟨c, hc, hacc⟩
      rw [DMachine.reachable_toNMachine] at hc
      obtain ⟨t, rfl⟩ := hc
      have hacc' : M.result (M.run x t) = some true := hacc
      by_contra hx
      obtain ⟨t', ht'⟩ := (hdec x).2 hx
      rcases Nat.le_total t t' with hle | hle
      · rw [M.run_stationary x hacc' t' hle, hacc'] at ht'
        simp at ht'
      · rw [M.run_stationary x ht' t hle, ht'] at hacc'
        simp at hacc'
    · intro hx
      obtain ⟨t, ht⟩ := (hdec x).1 hx
      refine ⟨M.run x t, ?_, ht⟩
      rw [DMachine.reachable_toNMachine]
      exact ⟨t, rfl⟩

/-! ### The deterministic simulator -/

/-- Steps other than the base case of the recursion do not look at the input. -/
