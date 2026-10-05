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

theorem Reach.iff_reflTransGen {a b : ℕ}
    (hbound : ∀ c, Relation.ReflTransGen edge a c → c < 2 ^ s) :
    Reach s edge s a b ↔ Relation.ReflTransGen edge a b :=
  ⟨Reach.sound, Reach.complete hbound⟩

end CS

import RequestProject.Savitch.Interp

/-!
# Big-step correctness of the Savitch simulator

We show that the depth-first evaluation of the Savitch recursion implemented by `CS.step`
computes the predicate `CS.Reach`, and that the outer loop over target configurations halts
with the verdict "some accepting configuration below `2 ^ s` is reachable".
-/

namespace CS

open Classical

variable {Γ : Type}

/-- The inner loop over midpoints.  Given that the recursive calls at level `k` work
(hypothesis `ih`), the loop starting at midpoint `m` returns whether some midpoint
`m' ∈ [m, 2 ^ s)` splits the path. -/
