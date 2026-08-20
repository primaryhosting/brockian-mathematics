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

lemma hybAcc_succ_sub {ℓ d m : ℕ} (e : Fin m → (Fin ℓ ↪ Fin d)) (f : (Fin ℓ → Bool) → Bool)
    (D : Circ m) (i : Fin m) :
    hybAcc e f D ((i : ℕ) + 1) - hybAcc e f D (i : ℕ)
      = (∑ z : Fin d → Bool, ∑ y : Fin m → Bool,
          (b2r (D.eval (nwStr e f i z y (f (z ∘ e i)))) - b2r (D.eval (nwStr e f i z y (y i)))))
        / (2 ^ d * 2 ^ m) := by
  have h1 : ∀ (z : Fin d → Bool) (y : Fin m → Bool),
      (fun j : Fin m => if (j : ℕ) < (i : ℕ) + 1 then f (z ∘ e j) else y j)
        = nwStr e f i z y (f (z ∘ e i)) := by
    intro z y
    funext j
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp [nwStr, hj, Nat.lt_succ_of_lt hj]
    · by_cases hj2 : j = i
      · subst hj2; simp [nwStr]
      · have hlt : ¬ ((j : ℕ) < (i : ℕ) + 1) := by
          have hne : (i : ℕ) ≠ (j : ℕ) := fun h => hj2 (Fin.ext h.symm)
          omega
        simp [nwStr, hj, hj2, hlt]
  have h2 : ∀ (z : Fin d → Bool) (y : Fin m → Bool),
      (fun j : Fin m => if (j : ℕ) < (i : ℕ) then f (z ∘ e j) else y j) = nwStr e f i z y (y i) := by
    intro z y
    funext j
    by_cases hj : (j : ℕ) < (i : ℕ)
    · simp [nwStr, hj]
    · by_cases hj2 : j = i
      · subst hj2; simp [nwStr]
      · simp [nwStr, hj, hj2]
  rw [hybAcc, hybAcc, ← sub_div]
  congr 1
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl (fun y _ => ?_)
  rw [h1, h2]

/-- Construction of the next-bit predictor circuit, together with its size bound. -/
