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

theorem bigstep_eval (N : NMachine Γ) (x : List Γ) (s a₀ : ℕ) :
    ∀ (k a b tg : ℕ) (S : List Frame), ∃ (t : ℕ) (v : Bool),
      iter N x t ⟨s, a₀, tg, .eval a b k, S⟩ = ⟨s, a₀, tg, .ret v, S⟩ ∧
        (v = true ↔ Reach s (N.stepRel x) k a b) := by
  intro k
  induction k with
  | zero =>
      intro a b tg S
      refine ⟨1, decide (a = b ∨ N.stepRel x a b), ?_, ?_⟩
      · rw [iter_one]; rfl
      · rw [Reach_zero]; exact decide_eq_true_iff
  | succ k ih =>
      intro a b tg S
      have hpos : (0 : ℕ) < 2 ^ s := Nat.two_pow_pos s
      obtain ⟨t, v, ht, hv⟩ :=
        bigstep_loop N x s a₀ k ih (2 ^ s) a b tg 0 S hpos (by omega)
      have e1 : iter N x 1 ⟨s, a₀, tg, .eval a b (k + 1), S⟩ =
          ⟨s, a₀, tg, .eval a 0 k, ⟨a, b, k, 0, false⟩ :: S⟩ := by
        rw [iter_one, stepx_eval_succ]
      refine ⟨1 + t, v, iter_trans N x e1 ht, ?_⟩
      rw [hv, Reach_succ]
      constructor
      · rintro ⟨m, -, hm2, hm3, hm4⟩; exact ⟨m, hm2, hm3, hm4⟩
      · rintro ⟨m, hm2, hm3, hm4⟩; exact ⟨m, Nat.zero_le _, hm2, hm3, hm4⟩

/-- Big-step correctness of the outer loop over candidate accepting configurations. -/
