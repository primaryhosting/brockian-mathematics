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

theorem outer_accept {n : ℕ} :
    ∀ (todo : List N.Mem), (∃ b ∈ todo, N.acc b ∧ CY N S x n (g n) N.start b) →
      SReach N S g x (.outer n todo) .acc := by
  intro todo
  induction todo with
  | nil => rintro ⟨b, hb, -⟩; exact absurd hb (List.not_mem_nil)
  | cons b bs ih =>
    rintro ⟨b', hb', hacc', hcy'⟩
    by_cases hb : N.acc b
    · have s1 : SReach N S g x (.outer n (b :: bs)) (.call n bs N.start b (g n) []) :=
        SReach.one' (dstep_outer_cons_acc hb)
      have s2 := eval (N := N) (S := S) (g := g) (x := x) n (g n) bs N.start b []
      by_cases hcy : CY N S x n (g n) N.start b
      · rw [decide_eq_true hcy] at s2
        exact s1.trans' (s2.trans' (SReach.one' dstep_ret_nil_true))
      · rw [decide_eq_false hcy] at s2
        have s3 : SReach N S g x (.ret n bs false ([] : List (Frame N.Mem))) (.outer n bs) :=
          SReach.one' dstep_ret_nil_false
        refine s1.trans' (s2.trans' (s3.trans' (ih ?_)))
        rcases List.mem_cons.mp hb' with rfl | hb''
        · exact absurd hcy' hcy
        · exact ⟨b', hb'', hacc', hcy'⟩
    · have s1 : SReach N S g x (.outer n (b :: bs)) (.outer n bs) :=
        SReach.one' (dstep_outer_cons_not_acc hb)
      refine s1.trans' (ih ?_)
      rcases List.mem_cons.mp hb' with rfl | hb''
      · exact absurd hacc' hb
      · exact ⟨b', hb'', hacc', hcy'⟩

/-- If no target in `todo` is accepting and reachable, the simulator never
accepts from the outer loop. -/
