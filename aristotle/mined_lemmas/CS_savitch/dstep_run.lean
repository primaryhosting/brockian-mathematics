import RequestProject.Savitch.Machine

/-!
# Savitch
Category: Frontier Cs
Target: CS.savitch
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Savitch's theorem

We model a space-`s` machine by its configuration graph: it has at most `2 ^ s`
configurations (`s` bits of workspace), a start configuration, an acceptance
predicate, and a transition relation (a relation for nondeterministic machines, a
function for deterministic ones).  A nondeterministic machine accepts when some
accepting configuration is reachable from the start configuration; a deterministic
machine accepts when its (unique) run visits an accepting configuration.

The main theorem `CS.savitch` states `NSPACE f ⊆ DSPACE (9 * (f + 1) ^ 2)`, i.e.
nondeterministic space `f` is contained in deterministic space `O(f ^ 2)`, and
`CS.PSPACE_eq_NPSPACE` deduces `PSPACE = NPSPACE`.
-/

namespace CS

open Savitch

/-- A nondeterministic machine using space `s`: at most `2 ^ s` configurations. -/
structure NMachine (s : ℕ) where
  /-- Number of configurations. -/
  size : ℕ
  /-- The space bound: `s` bits of workspace. -/
  hsize : size ≤ 2 ^ s
  /-- The (nondeterministic) transition relation. -/
  step : Fin size → Fin size → Bool
  /-- The initial configuration. -/
  start : Fin size
  /-- The accepting configurations. -/
  acc : Fin size → Bool

/-- A nondeterministic machine accepts if some accepting configuration is reachable. -/

theorem dstep_run (R : Fin n → Fin n → Bool) (K : ℕ) (a b : Fin n) :
    ∃ N, (dstep R K)^[N] (dstart a b K) = dfinal n K (cy R K a b) := by
  obtain ⟨N, hN⟩ := bigstep_call R K K a b [] (by simp)
  exact ⟨N, Subtype.ext (by rw [dstep_iterate_val]; exact hN)⟩

end CS.Savitch

import Mathlib

/-!
Walks in a finite directed graph on `Fin n`, and bounded reachability.
-/

namespace CS.Savitch

variable {n K : ℕ} {R : Fin n → Fin n → Bool} {a b m : Fin n} {t t₁ t₂ : ℕ}

/-- `Walk R t a b`: there is a walk of exactly `t` steps from `a` to `b`. -/
