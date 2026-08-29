import Mathlib
import RequestProject.Frontier

/-!
# A concrete Gödel numbering, and non-vacuity of Tarski's undefinability theorem

`Frontier.Tarski_undefinability` is stated for an arbitrary *injective* Gödel numbering
`code : AForm → Nat`.  Here we exhibit such a numbering, so that the hypothesis of the

def AForm.Sat : AForm → (Nat → Nat) → Prop
  | .eq t u, v => t.eval v = u.eval v
  | .not p, v => ¬ p.Sat v
  | .and p q, v => p.Sat v ∧ q.Sat v
  | .ex i p, v => ∃ m : Nat, p.Sat (upd v i m)

/-! ## Arithmetical definability -/

/-- A set `S ⊆ Nat` is *arithmetically definable* if some arithmetical formula `φ` is
satisfied exactly by those assignments whose value at the variable `x₀` lies in `S`.
Quantifying over all assignments simultaneously forces `φ` to have no free variable other
than `x₀`. -/
