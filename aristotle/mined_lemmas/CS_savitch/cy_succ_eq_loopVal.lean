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

theorem cy_succ_eq_loopVal (R : Fin n → Fin n → Bool) (k : ℕ) (a b : Fin n) :
    cy R (k + 1) a b = loopVal R k a b 0 := by
  rw [Bool.eq_iff_iff, cy_succ_iff, loopVal_iff]
  constructor
  · rintro ⟨m, h1, h2⟩
    exact ⟨m, Nat.zero_le _, h1, h2⟩
  · rintro ⟨m, -, h1, h2⟩
    exact ⟨m, h1, h2⟩

end CS.Savitch

import RequestProject.Savitch.CanYield

/-!
The deterministic stack machine implementing Savitch's algorithm, with its
correctness proof and the bound on its number of configurations.
-/

namespace CS.Savitch

/-- A stack frame `(a, b, mid, ph)`: we are computing whether `b` is reachable from `a`,
currently testing the midpoint `mid`; `ph = false` means the first half is being computed,
`ph = true` the second half. -/
abbrev Frame (n : ℕ) := Fin n × Fin n × Fin n × Bool

/-- Control state: `Sum.inl (a, b)` is a call, `Sum.inr v` is a return with value `v`. -/
abbrev Ctrl (n : ℕ) := (Fin n × Fin n) ⊕ Bool

/-- A raw configuration of the Savitch machine. -/
abbrev Raw (n : ℕ) := Ctrl n × List (Frame n)

variable {n : ℕ} {R : Fin n → Fin n → Bool} {K : ℕ}

/-- The first node index, as an element of `Fin n` (`n > 0` since `a : Fin n`). -/
