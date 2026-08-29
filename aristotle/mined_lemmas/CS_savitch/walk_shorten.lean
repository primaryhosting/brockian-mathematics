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

theorem walk_shorten (h : Walk R t a b) (ht : n ≤ t) : ∃ t' < t, Walk R t' a b := by
  obtain ⟨f, hf0, hf1, hfs⟩ := h
  have hcard : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by simp
  obtain ⟨i, j, hij, hfe⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun i : Fin (n + 1) => f (i : ℕ)) hcard
  have hij' : (i : ℕ) ≠ (j : ℕ) := fun h => hij (Fin.ext h)
  have hi : (i : ℕ) ≤ n := by omega
  have hj : (j : ℕ) ≤ n := by omega
  rcases lt_or_gt_of_ne hij' with hlt | hlt
  · exact walk_cut hf0 hf1 hfs hlt (by omega) hfe
  · exact walk_cut hf0 hf1 hfs hlt (by omega) hfe.symm

