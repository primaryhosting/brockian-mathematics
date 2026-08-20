/-
# Savitch
Category: Frontier Cs
Target: CS.savitch
Statement: NSPACE(f) ⊆ DSPACE(f²), so PSPACE = NPSPACE (Savitch).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

(Lean requires `import` commands to precede every declaration, including module
docstrings, so the header above is a plain block comment.)
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk
import RequestProject.Savitch.Sim
import RequestProject.Savitch.Semantics
import RequestProject.Savitch.Space

/-!
The space-bounded machine model, the classes `CS.NSPACE`, `CS.DSPACE`,
`CS.PSPACE` and `CS.NPSPACE`, and the simulator used in the proof are defined in
the files `RequestProject/Savitch/*.lean`.

A machine reads its input through a head whose position is determined by its
memory value, and it works in space `g` if on inputs of length `n` all reachable
memory values lie in a set of at most `2 ^ g n` values depending only on `n`
(the standard correspondence between `s` tape cells and `2 ^ O(s)`
configurations).  The classes `NSPACE g` and `DSPACE g` are closed under
constant factors by definition, as usual for space classes.

Savitch's theorem is proved for space bounds `f` with `n + 1 ≤ 2 ^ f n`
(i.e. `f n ≥ log₂ (n+1)`), the standard hypothesis `f (n) ≥ log n`.
-/

namespace CS

/-- **Savitch's theorem**: a language recognized by a nondeterministic machine in
space `f` (with `f n ≥ log₂ (n + 1)`) is recognized by a deterministic machine in
space `O(f²)`, i.e. `NSPACE f ⊆ DSPACE (f²)`. -/

theorem stackAt_frames {n : ℕ} : ∀ (st : List (Frame N.Mem)) (k : ℕ),
    StackAt N S g n k st → ∀ fr ∈ st, FrameOK N S n fr ∧ fr.k ≤ g n := by
  intro st
  induction st with
  | nil => intro k _ fr hfr; exact absurd hfr (List.not_mem_nil)
  | cons fr0 st ih =>
    intro k h fr hfr
    have hlen := stackAt_length (fr0 :: st) k h
    obtain ⟨hk, hok, hst⟩ := h
    rcases List.mem_cons.mp hfr with rfl | hfr'
    · refine ⟨hok, ?_⟩
      simp only [List.length_cons] at hlen
      omega
    · exact ih (k + 1) hst fr hfr'

/-! ### The invariant is preserved -/

