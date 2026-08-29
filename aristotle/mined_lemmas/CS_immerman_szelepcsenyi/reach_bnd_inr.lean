import Mathlib

/-!
# Nondeterministic small-space machines (branching-program model)

This file sets up a model of nondeterministic space-bounded computation on
inputs of a fixed length `n`, in the style of nondeterministic branching
programs: a machine has a finite state set `S`, each state may read (query) one
bit of the input, and the successor states are given by a relation depending on
the state and the queried bit.  The *space* used by such a machine is
`log₂ |S|`, so polynomially many states corresponds to logarithmic space.

Machines are value-producing (`out : S → Option α`), which lets us build them
with monadic combinators (`pure`, `bind`, `guess`, `query`, `fail`).
-/

open scoped Classical

namespace CS

/-- A nondeterministic machine on inputs of length `n`, producing values in `α`.

`label s` says which input bit (if any) is read at state `s`; `next s b` is the
set of possible successors of `s` when the bit read has value `b`; `out s` is
the value output if the computation halts at `s`. -/
structure Mach (n : ℕ) (α : Type) : Type 1 where
  S : Type
  fintypeS : Fintype S
  start : S
  label : S → Option (Fin n)
  next : S → Bool → Set S
  out : S → Option α

attribute [instance] Mach.fintypeS

namespace Mach

variable {n : ℕ} {α β : Type}

/-- The bit visible at state `s` on input `x` (`false` if `s` reads nothing). -/

theorem reach_bnd_inr {a : α} {u v : (f a).S} (h : (f a).reach x u v) :
    (bnd M f).reach x (Sum.inr ⟨a, u⟩) (Sum.inr ⟨a, v⟩) := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hstep ih => exact ih.tail (step_bnd_inr M f x hstep)

/-- Description of the states reachable in `bnd M f`. -/
