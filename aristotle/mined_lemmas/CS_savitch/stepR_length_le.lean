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

theorem stepR_length_le {c : Raw n} (h : c.2.length ≤ K) : (stepR R K c).2.length ≤ K := by
  obtain ⟨ctrl, st⟩ := c
  simp only at h
  match ctrl, st with
  | Sum.inl (a, b), st =>
    show (stepR R K (Sum.inl (a, b), st)).2.length ≤ K
    simp only [stepR]
    split
    · exact h
    · rename_i hK
      simp only [List.length_cons]
      omega
  | Sum.inr v, [] =>
    show (stepR R K (Sum.inr v, ([] : List (Frame n)))).2.length ≤ K
    simp [stepR]
  | Sum.inr v, (a, b, mid, ph) :: st =>
    show (stepR R K (Sum.inr v, (a, b, mid, ph) :: st)).2.length ≤ K
    have h' : st.length + 1 ≤ K := by simpa using h
    simp only [stepR]
    split
    · split
      · simpa using by omega
      · exact advance_length_le h'
    · split
      · simpa using h'
      · exact advance_length_le h'

instance : DecidableEq (Conf n K) := fun _ _ => decidable_of_iff _ Subtype.ext_iff.symm

/-- Encoding of a bounded configuration into a fixed finite type. -/
