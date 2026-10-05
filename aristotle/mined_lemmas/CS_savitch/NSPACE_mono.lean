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

theorem NSPACE_mono {f f' : ℕ → ℕ} (h : ∀ n, f n ≤ f' n) :
    NSPACE Γ f ⊆ NSPACE Γ f' := by
  rintro L ⟨M, hsp, hacc⟩
  exact ⟨M, fun x c hc => lt_of_lt_of_le (hsp x c hc) (Nat.pow_le_pow_right (by norm_num) (h _)),
    hacc⟩

end CS

import RequestProject.Savitch.Invariant

/-!
# Encoding simulator states as natural numbers

The deterministic machines of our model have natural numbers as configurations, so the states
of the Savitch simulator have to be encoded.  We use a plain positional encoding of the list
of numerical components of a state, in a base large enough to accommodate them, paired with
the space bound `s`.

The two facts we need are that the encoding is injective on states satisfying the invariant
`CS.Good`, and that such states have codes below `2 ^ (42 * (s + 1) ^ 2)`.
-/

namespace CS

open Classical

/-- Positional encoding of a list of numbers `< B` in base `B + 1`. -/
