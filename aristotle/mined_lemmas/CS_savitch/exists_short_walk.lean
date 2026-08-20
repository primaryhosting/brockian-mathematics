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

theorem exists_short_walk {r : α → α → Prop} (S : Finset α) (a b : α)
    (hS : ∀ (c : α) (t : ℕ), Walk r t a c → c ∈ S) (h : ∃ t, Walk r t a b) :
    ∃ t, t < S.card ∧ Walk r t a b := by
  classical
  set T := Nat.find h with hTdef
  have hT : Walk r T a b := Nat.find_spec h
  obtain ⟨p, hp0, hpT, hstep⟩ := hT.exists_path
  have hpre : ∀ i ≤ T, Walk r i a (p i) := by
    intro i hi
    have := walk_of_path hstep i hi 0 (Nat.zero_le _)
    simpa [hp0] using this
  have hsuf : ∀ i ≤ T, Walk r (T - i) (p i) b := by
    intro i hi
    have := walk_of_path hstep T le_rfl i hi
    rwa [hpT] at this
  have hmaps : ∀ i ∈ Finset.range (T + 1), p i ∈ S := by
    intro i hi
    simp only [Finset.mem_range] at hi
    exact hS _ i (hpre i (by omega))
  have hinj : Set.InjOn p (Finset.range (T + 1)) := by
    intro i hi j hj hij
    simp only [Finset.coe_range, Set.mem_Iio] at hi hj
    by_contra hne
    rcases Nat.lt_or_ge i j with hlt | hge
    · have h1 : Walk r i a (p i) := hpre i (by omega)
      have h2 : Walk r (T - j) (p j) b := hsuf j (by omega)
      rw [← hij] at h2
      have : Walk r (i + (T - j)) a b := h1.trans h2
      have hlt' : i + (T - j) < T := by omega
      exact absurd this (Nat.find_min h hlt')
    · have hlt : j < i := by omega
      have h1 : Walk r j a (p j) := hpre j (by omega)
      have h2 : Walk r (T - i) (p i) b := hsuf i (by omega)
      rw [hij] at h2
      have : Walk r (j + (T - i)) a b := h1.trans h2
      have hlt' : j + (T - i) < T := by omega
      exact absurd this (Nat.find_min h hlt')
  have hcard : T + 1 ≤ S.card := by
    have := Finset.card_le_card_of_injOn p (by simpa [Set.MapsTo] using hmaps) hinj
    simpa using this
  exact ⟨T, by omega, Nat.find_spec h⟩

end CS

/-
# A sanity check: the classes are not degenerate

We exhibit a language that genuinely depends on its input and show it lies in
`PSPACE` (hence, by `CS.PSPACE_eq_NPSPACE`, in `NPSPACE`).  This checks that the
machine model of `RequestProject/Savitch/Model.lean` can actually read its input
and that the space classes are inhabited by non-trivial languages.
-/
import Mathlib
import RequestProject.Savitch.Model
import RequestProject.Savitch

namespace CS

/-- The language of bit strings containing a `true`. -/
