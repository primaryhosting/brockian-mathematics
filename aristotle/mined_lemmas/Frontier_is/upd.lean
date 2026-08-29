import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

def upd (v : Nat → Nat) (i m : Nat) : Nat → Nat := fun j => if j = i then m else v j

/-- Tarskian satisfaction in the standard model `Nat`: `φ.Sat v` says that the assignment
`v : Nat → Nat` satisfies the formula `φ` in the structure `(Nat, 0, 1, +, *, =)`. -/
