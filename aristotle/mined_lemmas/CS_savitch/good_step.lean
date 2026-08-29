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

theorem good_step (N : NMachine Γ) (σ : Option Γ) (st : St) (h : Good st) :
    Good (step N σ st) := by
  obtain ⟨s, a₀, tg, ctrl, stack⟩ := st
  obtain ⟨ha₀, hrest⟩ := h
  simp only at ha₀ hrest
  cases ctrl with
  | init =>
      obtain ⟨hstack, htg⟩ := hrest
      subst hstack
      rw [step_init]
      by_cases h1 : tg < 2 ^ s
      · rw [if_pos h1]
        by_cases h2 : N.accept tg
        · rw [if_pos h2]
          exact ⟨ha₀, ha₀, h1, h1, rfl⟩
        · rw [if_neg h2]
          exact ⟨ha₀, rfl, show tg + 1 ≤ 2 ^ s by omega⟩
      · rw [if_neg h1]
        exact ⟨ha₀, rfl, htg⟩
  | eval a b k =>
      obtain ⟨hA, hB, htg, hstk⟩ := hrest
      cases k with
      | zero =>
          rw [step_eval_zero]
          exact ⟨ha₀, htg, 0, hstk⟩
      | succ k =>
          rw [step_eval_succ]
          refine ⟨ha₀, hA, Nat.two_pow_pos s, htg, ?_⟩
          exact ⟨rfl, hA, hB, Nat.two_pow_pos s, hstk⟩
  | ret v =>
      obtain ⟨htg, k, hstk⟩ := hrest
      cases stack with
      | nil =>
          rw [step_ret_nil]
          by_cases hv : v = true
          · subst hv
            simp only [if_pos]
            exact ⟨ha₀, rfl, le_of_lt htg⟩
          · have : v = false := by simpa using hv
            subst this
            simp only [Bool.false_eq_true, if_false]
            exact ⟨ha₀, rfl, show tg + 1 ≤ 2 ^ s by omega⟩
      | cons fr rest =>
          obtain ⟨hk, hA, hB, hM, hrst⟩ := hstk
          rw [step_ret_cons]
          by_cases hv : v = true
          · subst hv
            simp only [if_pos]
            by_cases hph : fr.ph = true
            · rw [if_pos hph]
              exact ⟨ha₀, htg, k + 1, hrst⟩
            · have : fr.ph = false := by simpa using hph
              rw [if_neg (by simp [this])]
              exact ⟨ha₀, hM, hB, htg, ⟨rfl, hA, hB, hM, by rw [hk]; exact hrst⟩⟩
          · have hvf : v = false := by simpa using hv
            subst hvf
            simp only [Bool.false_eq_true, if_false]
            by_cases hm : fr.m + 1 < 2 ^ s
            · rw [if_pos hm]
              exact ⟨ha₀, hA, hm, htg, ⟨rfl, hA, hB, hm, by rw [hk]; exact hrst⟩⟩
            · rw [if_neg hm]
              exact ⟨ha₀, htg, k + 1, hrst⟩
  | halt v =>
      rw [step_halt]
      exact ⟨ha₀, hrest⟩

