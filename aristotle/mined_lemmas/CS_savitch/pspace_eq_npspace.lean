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

theorem pspace_eq_npspace : PSPACE Γ = NPSPACE Γ := by
  apply Set.eq_of_subset_of_subset
  · rintro L ⟨c, k, hL⟩
    exact ⟨c, k, DSPACE_subset_NSPACE _ hL⟩
  · rintro L ⟨c, k, hL⟩
    refine ⟨42 * (c + 1) ^ 2, 2 * k, ?_⟩
    refine DSPACE_mono ?_ (savitch (fun n => c * (n + 1) ^ k) hL)
    intro n
    have h1 : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by
      have : 1 ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
      nlinarith
    calc 42 * (c * (n + 1) ^ k + 1) ^ 2
        ≤ 42 * ((c + 1) * (n + 1) ^ k) ^ 2 := by
          exact Nat.mul_le_mul_left 42 (Nat.pow_le_pow_left h1 2)
      _ = 42 * (c + 1) ^ 2 * (n + 1) ^ (2 * k) := by
          rw [mul_pow, ← pow_mul]; ring_nf

/-! ### Non-degeneracy of the model

The following two lemmas record that the space measure is meaningful: with zero space, i.e.
a single configuration, only the two trivial languages can be recognised. -/

/-- A nondeterministic machine with a single configuration recognises only `∅` or everything. -/
