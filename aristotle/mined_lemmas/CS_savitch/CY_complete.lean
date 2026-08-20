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

theorem CY_complete (hS : ∀ (y : List Bool) (m : N.Mem), Reach N y m → m ∈ S y.length) :
    ∀ (k t : ℕ) (a b : N.Mem), Reach N x a → Walk (stepR N x) t a b → t ≤ 2 ^ k →
      CY N S x x.length k a b := by
  intro k
  induction k with
  | zero =>
    intro t a b _ hw ht
    interval_cases t
    · exact Or.inl hw
    · obtain ⟨c, hc, hcb⟩ := hw
      cases hc
      exact Or.inr hcb
  | succ k ihk =>
    intro t a b ha hw ht
    have hpow : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
    set i := min t (2 ^ k) with hi
    have hile : i ≤ t := Nat.min_le_left _ _
    obtain ⟨c, hac, hcb⟩ := hw.split i hile
    have hc_reach : Reach N x c := reach_of_walk ha i hac
    have hc_mem : c ∈ cands N S x.length := by
      rw [cands, Finset.mem_toList]
      exact hS x c hc_reach
    have h1 : i ≤ 2 ^ k := Nat.min_le_right _ _
    have h2 : t - i ≤ 2 ^ k := by omega
    exact ⟨c, hc_mem, ihk i a c ha hac h1, ihk (t - i) c b hc_reach hcb h2⟩

/-- The Savitch search succeeds exactly when `N` accepts. -/
