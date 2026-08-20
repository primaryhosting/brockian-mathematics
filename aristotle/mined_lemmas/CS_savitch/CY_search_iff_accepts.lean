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

theorem CY_search_iff_accepts
    (hS : ∀ (y : List Bool) (m : N.Mem), Reach N y m → m ∈ S y.length)
    (hcard : ∀ n, (S n).card ≤ 2 ^ g n) :
    (∃ b ∈ cands N S x.length, N.acc b ∧ CY N S x x.length (g x.length) N.start b) ↔
      Accepts N x := by
  constructor
  · rintro ⟨b, -, hb, hcy⟩
    obtain ⟨t, ht⟩ := CY_sound (S := S) x.length (g x.length) N.start b hcy
    exact ⟨b, reach_of_walk Reach.start t ht, hb⟩
  · rintro ⟨m, hm, hacc⟩
    have hwalks : ∀ (c : N.Mem) (t : ℕ), Walk (stepR N x) t N.start c → c ∈ S x.length := by
      intro c t hw
      exact hS x c ((reach_iff_walk c).mpr ⟨t, hw⟩)
    obtain ⟨t, htlt, hw⟩ :=
      exists_short_walk (S x.length) N.start m hwalks ((reach_iff_walk m).mp hm)
    have htle : t ≤ 2 ^ g x.length := le_trans (Nat.le_of_lt_succ (by omega)) (hcard x.length)
    refine ⟨m, ?_, hacc, ?_⟩
    · rw [cands, Finset.mem_toList]
      exact hS x m hm
    · exact CY_complete hS (g x.length) t N.start m Reach.start hw htle

end

end CS

/-
# The Savitch simulator

Given a nondeterministic machine `N` whose reachable memory values on inputs of
length `n` are contained in a finite set `S n` of size at most `2 ^ g n`, we
build a deterministic machine which decides acceptance of `N` by the recursive
midpoint search of Savitch's theorem, implemented as an explicit stack machine.
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch.Walk

namespace CS

attribute [local instance] Classical.propDecidable

noncomputable section

variable (N : Machine) (S : ℕ → Finset N.Mem) (g : ℕ → ℕ)

/-- A stack frame of the recursive midpoint search: we are computing
`CanYield a b (k+1)` by trying the midpoints `cur :: rest` in order; `second`
records whether we are checking the first or the second half. -/
structure Frame (α : Type) where
  /-- Source configuration of the subproblem. -/
  a : α
  /-- Target configuration of the subproblem. -/
  b : α
  /-- Level of the two recursive subcalls. -/
  k : ℕ
  /-- The midpoint currently being tried. -/
  cur : α
  /-- The midpoints still to be tried. -/
  rest : List α
  /-- `false`: checking `a ⇝ cur`; `true`: checking `cur ⇝ b`. -/
  second : Bool

/-- Memory values of the simulator. -/
inductive SMem (α : Type) where
  /-- Scanning the input to determine its length. -/
  | scan (i : ℕ)
  /-- Looking for an accepting target among `todo`. -/
  | outer (n : ℕ) (todo : List α)
  /-- Evaluating `CanYield a b k` with the given stack of pending frames. -/
  | call (n : ℕ) (todo : List α) (a b : α) (k : ℕ) (st : List (Frame α))
  /-- Returning the value `v` to the stack. -/
  | ret (n : ℕ) (todo : List α) (v : Bool) (st : List (Frame α))
  /-- The accepting (absorbing) memory value. -/
  | acc

/-- The list of candidate configurations on inputs of length `n`. -/
