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

theorem NSPACE_zero_trivial {L : Set (List Γ)} (hL : L ∈ NSPACE Γ (fun _ => 0)) :
    L = ∅ ∨ L = Set.univ := by
  obtain ⟨N, hsp, hacc⟩ := hL
  have hz : ∀ x : List Γ, N.Accepts x ↔ N.accept 0 := by
    intro x
    constructor
    · rintro ⟨c, hc, ha⟩
      have hc0 : c < 2 ^ (0 : ℕ) := hsp x c hc
      have : c = 0 := by simpa using hc0
      rwa [this] at ha
    · intro h
      have hs : N.start x.length < 2 ^ (0 : ℕ) := hsp x _ (N.start_mem_reachable x)
      have h0 : N.start x.length = 0 := by simpa using hs
      exact ⟨0, h0 ▸ N.start_mem_reachable x, h⟩
  by_cases h : N.accept 0
  · right
    ext x
    simp only [Set.mem_univ, iff_true, ← hacc x, hz x]
    exact h
  · left
    ext x
    simp only [Set.mem_empty_iff_false, iff_false, ← hacc x, hz x]
    exact h

/-- A deterministic machine with a single configuration decides only `∅` or everything. -/
