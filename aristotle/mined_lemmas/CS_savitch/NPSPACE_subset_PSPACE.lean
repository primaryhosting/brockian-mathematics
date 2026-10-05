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

theorem NPSPACE_subset_PSPACE : NPSPACE ⊆ PSPACE := by
  rintro L ⟨c, k, hL⟩
  have h1 : L ∈ DSPACE (fun n => 9 * (c * (n + 1) ^ k + 1) ^ 2) := savitch _ hL
  refine ⟨9 * (c + 1) ^ 2, 2 * k, DSPACE_mono ?_ h1⟩
  intro n
  have hpow : (1 : ℕ) ≤ (n + 1) ^ k := Nat.one_le_pow _ _ (by omega)
  have h2 : c * (n + 1) ^ k + 1 ≤ (c + 1) * (n + 1) ^ k := by nlinarith
  calc 9 * (c * (n + 1) ^ k + 1) ^ 2 ≤ 9 * ((c + 1) * (n + 1) ^ k) ^ 2 :=
        Nat.mul_le_mul_left 9 (Nat.pow_le_pow_left h2 2)
  _ = 9 * (c + 1) ^ 2 * (n + 1) ^ (2 * k) := by rw [mul_pow, ← pow_mul]; ring

/-- **Savitch's theorem**, corollary: `PSPACE = NPSPACE`. -/
