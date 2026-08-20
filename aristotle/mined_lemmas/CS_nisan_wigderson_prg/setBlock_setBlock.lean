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

lemma setBlock_setBlock {ℓ d : ℕ} (e : Fin ℓ ↪ Fin d) (z : Fin d → Bool) (x : Fin ℓ → Bool) :
    setBlock e (setBlock e z x) (z ∘ e) = z := by
  funext k
  by_cases hk : ∃ t, e t = k
  · obtain ⟨t, rfl⟩ := hk
    simp [setBlock_apply_mem]
  · rw [setBlock_apply_not_mem _ _ _ hk, setBlock_apply_not_mem _ _ _ hk]

/-- Averaging over the seed and over a fresh block value is the same as averaging over the
seed, up to the factor `2 ^ ℓ`. -/
