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

theorem simAccepts_iff_CY :
    Accepts (simMachine N S g) x ↔
      ∃ b ∈ cands N S x.length, N.acc b ∧ CY N S x x.length (g x.length) N.start b := by
  rw [simAccepts_iff]
  constructor
  · intro h
    by_contra hno
    push_neg at hno
    have hno' : ∀ b ∈ cands N S x.length,
        ¬ (N.acc b ∧ CY N S x x.length (g x.length) N.start b) := by
      intro b hb ⟨h1, h2⟩
      exact hno b hb h1 h2
    obtain ⟨t, ht⟩ := h
    rcases Nat.lt_or_ge t (x.length + 1) with hlt | hge
    · rw [scan_iter t (by omega)] at ht
      simp at ht
    · obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hge
      have hcomm : x.length + 1 + d = d + (x.length + 1) := by omega
      rw [hcomm, Function.iterate_add_apply, scan_done] at ht
      exact outer_reject _ hno' d ht
  · intro h
    obtain ⟨t, ht⟩ := outer_accept (g := g) _ h
    refine ⟨t + (x.length + 1), ?_⟩
    rw [Function.iterate_add_apply, scan_done, ht]

end Correctness

end

end CS

/-
# A machine model for space-bounded computation

We use the standard "bounded-memory machine with a read-only random-access
input" model of space-bounded computation:

* a machine has a memory type `Mem` with a distinguished initial memory `start`;
* the memory determines a position `head m` of the input which the machine
  currently reads;
* the transition `next m o` gives the set of possible successor memories, where
  `o : Option Bool` is the bit read (`none` if the head is past the end of the
  input, so that the machine can detect the length of its input);
* `acc` marks the accepting memory values, and the machine accepts `x` if some
  accepting memory is reachable.

Space is measured in the standard way: a machine works in space `g` if on every
input of length `n` all reachable memory values lie in a fixed set of at most
`2 ^ g n` values (a machine using `s` tape cells over a finite alphabet has
`2 ^ O(s)` configurations, and conversely).
-/
import Mathlib

namespace CS

/-- A (nondeterministic) space-bounded machine with read-only random access
to the input. -/
structure Machine where
  /-- The type of memory values (configurations) of the machine. -/
  Mem : Type
  /-- The initial memory value. -/
  start : Mem
  /-- The input position that the machine reads in a given memory value. -/
  head : Mem → ℕ
  /-- The possible successor memory values, given the bit currently read
  (`none` if the head is beyond the end of the input). -/
  next : Mem → Option Bool → Set Mem
  /-- The accepting memory values. -/
  acc : Mem → Prop

/-- The memory values reachable by `M` on input `x`. -/
inductive Reach (M : Machine) (x : List Bool) : M.Mem → Prop
  | start : Reach M x M.start
  | step {a b : M.Mem} : Reach M x a → b ∈ M.next a x[M.head a]? → Reach M x b

/-- `M` accepts `x` if some accepting memory value is reachable. -/
