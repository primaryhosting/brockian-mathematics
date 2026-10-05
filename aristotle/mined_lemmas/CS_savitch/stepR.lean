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

def stepR (R : Fin n → Fin n → Bool) (K : ℕ) : Raw n → Raw n
  | (Sum.inl (a, b), st) =>
      if K - st.length = 0 then (Sum.inr ((a == b) || R a b), st)
      else (Sum.inl (a, mid0 a), (a, b, mid0 a, false) :: st)
  | (Sum.inr v, []) => (Sum.inr v, [])
  | (Sum.inr v, (a, b, mid, ph) :: st) =>
      if ph then (if v then (Sum.inr true, st) else advance a b mid st)
      else (if v then (Sum.inl (mid, b), (a, b, mid, true) :: st) else advance a b mid st)

/-- `Reaches R K c c'` : the machine goes from `c` to `c'` in some number of steps. -/
