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

theorem encList_lt (B : ℕ) : ∀ (d : ℕ) (l : List ℕ), (∀ a ∈ l, a < B) → l.length ≤ d →
    encList B l < (B + 1) ^ d := by
  intro d
  induction d with
  | zero =>
      intro l _ hlen
      have : l = [] := List.length_eq_zero_iff.mp (Nat.le_zero.mp hlen)
      subst this
      simp [encList_nil]
  | succ d ih =>
      intro l hb hlen
      cases l with
      | nil => simp only [encList_nil]; positivity
      | cons a l =>
          have h1 : encList B l < (B + 1) ^ d :=
            ih l (fun c hc => hb c (by simp [hc])) (by simp at hlen; omega)
          have ha : a < B := hb a (by simp)
          rw [encList_cons, pow_succ]
          have hstep : (B + 1) * (encList B l + 1) = (B + 1) * encList B l + (B + 1) := by ring
          calc (a + 1) + (B + 1) * encList B l
              < (B + 1) * (encList B l + 1) := by omega
            _ ≤ (B + 1) * (B + 1) ^ d := Nat.mul_le_mul_left _ (by omega)
            _ = (B + 1) ^ d * (B + 1) := by ring

/-- The numerical components of a frame. -/
