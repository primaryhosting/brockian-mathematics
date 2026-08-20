/-
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators

namespace CS

/-! ## Boolean circuits

We use a term representation of Boolean circuits, but we measure their size in the
*DAG* sense: the size of a circuit is the number of distinct subcircuits occurring in
it (equivalently, the number of gates when identical subcircuits are shared). -/

/-- Boolean circuits on `n` input variables. -/
inductive Circ (n : ℕ) where
  | var : Fin n → Circ n
  | const : Bool → Circ n
  | not : Circ n → Circ n
  | and : Circ n → Circ n → Circ n
  | or : Circ n → Circ n → Circ n
  deriving DecidableEq

namespace Circ

/-- The Boolean function computed by a circuit. -/

lemma eval_juntaCirc {n : ℕ} (h : (Fin n → Bool) → Bool) :
    ∀ (L : List (Fin n)) (ρ x : Fin n → Bool),
      eval (juntaCirc h L ρ) x = h (fun k => if k ∈ L then x k else ρ k) := by
  intro L
  induction L with
  | nil => intro ρ x; simp [juntaCirc, eval]
  | cons i L ih =>
      intro ρ x
      simp only [juntaCirc, eval, ih]
      cases hx : x i with
      | true =>
          simp only [Bool.true_and, Bool.not_true, Bool.false_and, Bool.or_false]
          congr 1
          funext k
          by_cases hk : k = i
          · subst hk
            by_cases hkL : k ∈ L <;> simp [hkL, hx]
          · by_cases hkL : k ∈ L <;> simp [hkL, hk]
      | false =>
          simp only [Bool.false_and, Bool.not_false, Bool.true_and, Bool.false_or]
          congr 1
          funext k
          by_cases hk : k = i
          · subst hk
            by_cases hkL : k ∈ L <;> simp [hkL, hx]
          · by_cases hkL : k ∈ L <;> simp [hkL, hk]

