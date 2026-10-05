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

def size (M : Mach n α) : ℕ := Fintype.card M.S

/-! ### Basic combinators -/

/-- The machine that immediately outputs `a`. -/

def bnd (M : Mach n α) [Fintype α] (f : α → Mach n β) : Mach n β where
  S := M.S ⊕ (Σ a : α, (f a).S)
  fintypeS := by
    haveI : Fintype M.S := M.fintypeS
    haveI : ∀ a : α, Fintype (f a).S := fun a => (f a).fintypeS
    infer_instance
  start := Sum.inl M.start
  label := Sum.elim M.label (fun p => (f p.1).label p.2)
  next := fun u b => match u with
    | Sum.inl s => (Sum.inl '' (M.next s b)) ∪ {t | ∃ a, M.out s = some a ∧ t = Sum.inr ⟨a, (f a).start⟩}
    | Sum.inr p => (fun t => Sum.inr ⟨p.1, t⟩) '' ((f p.1).next p.2 b)
  out := Sum.elim (fun _ => none) (fun p => (f p.1).out p.2)

/-! ### Semantics of the combinators -/

theorem size_bnd (M : Mach n α) [Fintype α] (f : α → Mach n β) :
    (bnd M f).size = M.size + ∑ a : α, (f a).size := by
  classical
  haveI : Fintype M.S := M.fintypeS
  haveI : ∀ a : α, Fintype (f a).S := fun a => (f a).fintypeS
  have h : Fintype.card ((bnd M f).S) = Fintype.card (M.S ⊕ Σ a : α, (f a).S) := by
    congr 1 <;> exact Subsingleton.elim _ _
  have hp : ∀ (a : α) (i : Fintype (f a).S), @Fintype.card (f a).S i = (f a).size := by
    intro a i; simp only [size]; congr 1
  have hM : ∀ (i : Fintype M.S), @Fintype.card M.S i = M.size := by
    intro i; simp only [size]; congr 1
  simp only [size, hp, hM] at h ⊢
  rw [h, Fintype.card_sum, Fintype.card_sigma, hM, hp]
  simp only [hp, hM]

end Mach

end CS

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false
