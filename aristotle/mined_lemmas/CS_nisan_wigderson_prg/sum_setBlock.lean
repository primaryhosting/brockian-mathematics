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

lemma sum_setBlock {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (g : (Fin d → Bool) → ℝ) :
    ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, g (setBlock e z x)
      = 2 ^ ℓ * ∑ z : Fin d → Bool, g z := by
  classical
  set Φ : ((Fin d → Bool) × (Fin ℓ → Bool)) → ((Fin d → Bool) × (Fin ℓ → Bool)) :=
    fun p => (setBlock e p.1 p.2, p.1 ∘ e) with hΦ
  have hinv : Function.Involutive Φ := by
    intro p
    obtain ⟨z, x⟩ := p
    simp only [hΦ]
    exact Prod.ext (setBlock_setBlock e z x) (setBlock_comp e z x)
  have h1 : ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g (Φ p).1
      = ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g p.1 :=
    Equiv.sum_comp (hinv.toPerm Φ) (fun p => g p.1)
  have h2 : ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g (Φ p).1
      = ∑ z : Fin d → Bool, ∑ x : Fin ℓ → Bool, g (setBlock e z x) := by
    rw [Fintype.sum_prod_type]
  have h3 : ∑ p : (Fin d → Bool) × (Fin ℓ → Bool), g p.1
      = 2 ^ ℓ * ∑ z : Fin d → Bool, g z := by
    rw [Fintype.sum_prod_type]
    have hc : (Fintype.card (Fin ℓ → Bool) : ℝ) = 2 ^ ℓ := by simp
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hc]
    rw [← Finset.mul_sum]
  rw [← h2, h1, h3]

/-! ## The Nisan-Wigderson generator and the hybrid argument -/

/-- The `i`-th hybrid string: the first `i` bits are outputs of the generator, the `i`-th bit
is `b`, and the remaining bits are taken from the truly random string `y`. -/
