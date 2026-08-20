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

lemma size_juntaCirc {n : ℕ} (h : (Fin n → Bool) → Bool) :
    ∀ (L : List (Fin n)) (ρ : Fin n → Bool),
      size (juntaCirc h L ρ) + 6 ≤ 7 * 2 ^ L.length := by
  intro L
  induction L with
  | nil => intro ρ; simp [juntaCirc]
  | cons i L ih =>
      intro ρ
      have h1 := ih (Function.update ρ i true)
      have h0 := ih (Function.update ρ i false)
      have e1 := size_or (and (var i) (juntaCirc h L (Function.update ρ i true)))
        (and (not (var i)) (juntaCirc h L (Function.update ρ i false)))
      have e2 := size_and (var i) (juntaCirc h L (Function.update ρ i true))
      have e3 := size_and (not (var i)) (juntaCirc h L (Function.update ρ i false))
      have e4 := size_not (var i : Circ n)
      have e5 : size (var i : Circ n) = 1 := size_var i
      have hp : (1:ℕ) ≤ 2 ^ L.length := Nat.one_le_two_pow
      have : (7 : ℕ) * 2 ^ (i :: L).length = 7 * 2 ^ L.length + 7 * 2 ^ L.length := by
        simp [List.length_cons, pow_succ]; ring
      simp only [juntaCirc] at *
      omega

end Circ

/-! ## Real-valued indicators -/

/-- The real-valued indicator of a Boolean. -/
