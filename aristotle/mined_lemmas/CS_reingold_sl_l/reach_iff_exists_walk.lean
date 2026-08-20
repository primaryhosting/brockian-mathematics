/-!
# Reingold Sl L
Category: Frontier Cs
Target: CS.reingold_sl_l
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
This file is deliberately import-free (it uses only the Lean 4 core library), so that the
required header comment above can literally be the first thing in the file.
-/

namespace CS

/-! ## Counting -/

/-- `HasCard α N` says that the type `α` embeds into `Fin N`; i.e. `α` has at most `N`
elements, so an element of `α` can be stored in `⌈log₂ N⌉` bits. -/

theorem reach_iff_exists_walk {n d : Nat} (G : RotGraph n d) {s t : Fin n} :
    G.Reach s t ↔ ∃ l : List (Fin d), G.walk s l = t := by
  constructor
  · intro h
    induction h with
    | refl => exact ⟨[], rfl⟩
    | tail _ hadj ih =>
        obtain ⟨l, hl⟩ := ih
        obtain ⟨a, ha⟩ := hadj
        exact ⟨l ++ [a], by rw [G.walk_append, hl, ha]⟩
  · rintro ⟨l, rfl⟩
    exact G.reach_walk s l

end RotGraph

/-! ## A space-bounded machine model with oracle access to the graph -/

/-- A deterministic machine with a finite memory (at most `size` configurations, i.e.
`⌈log₂ size⌉` bits of work space) that accesses the input graph only through its rotation
map: at each step it asks for the value of the rotation map at one point, determined by its
current memory contents, and updates its memory using the answer.  This is the standard
read-only/oracle formulation of a space-bounded algorithm; the space used is
`⌈log₂ size⌉` bits. -/
structure Machine (n d : Nat) where
  Mem : Type
  size : Nat
  card : HasCard Mem size
  init : Fin n → Fin n → Mem
  query : Mem → Fin n × Fin d
  update : Mem → Fin n × Fin d → Mem
  out : Mem → Bool
  time : Nat

/-- Iterating a function. -/
