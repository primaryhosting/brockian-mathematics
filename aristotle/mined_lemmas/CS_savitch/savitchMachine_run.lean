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

theorem savitchMachine_run (N : NMachine Γ) (f : ℕ → ℕ) (x : List Γ)
    (h : Good (⟨f x.length, N.start x.length, 0, .init, []⟩ : St)) (t : ℕ) :
    (savitchMachine N f).run x t =
      encSt (iter N x t ⟨f x.length, N.start x.length, 0, .init, []⟩) := by
  induction t with
  | zero => rfl
  | succ t ih =>
      set st₀ : St := ⟨f x.length, N.start x.length, 0, .init, []⟩ with hst₀
      have hgood : Good (iter N x t st₀) := good_iter N x t st₀ h
      have hiter : iter N x (t + 1) st₀ = stepx N x (iter N x t st₀) := iter_succ_of N x rfl
      rw [DMachine.run, ih, hiter]
      by_cases hhalt : ∃ v, (iter N x t st₀).ctrl = .halt v
      · obtain ⟨v, hv⟩ := hhalt
        have hres : (savitchMachine N f).result (encSt (iter N x t st₀)) = some v := by
          rw [savitchMachine_result_of_good N f hgood, hv]
        rw [if_neg (by rw [hres]; simp)]
        exact congrArg encSt (stepx_halt_of N x _ hv).symm
      · have hres : (savitchMachine N f).result (encSt (iter N x t st₀)) = none := by
          rw [savitchMachine_result_of_good N f hgood]
          cases hc : (iter N x t st₀).ctrl with
          | init => rfl
          | eval a b k => rfl
          | ret v => rfl
          | halt v => exact absurd ⟨v, hc⟩ hhalt
        rw [if_pos hres]
        exact savitchMachine_step_of_good N f x hgood

/-! ### Savitch's theorem -/

/-- **Savitch's theorem**: a language accepted by a nondeterministic machine running in space
`f` is decided by a deterministic machine running in space `42 * (f + 1) ^ 2`. -/
