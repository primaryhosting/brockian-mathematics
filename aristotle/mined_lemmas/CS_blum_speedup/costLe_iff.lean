/-
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Blum Speedup
Category: Frontier Cs
Target: CS.blum_speedup
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Nat.Partrec Nat.Partrec.Code

namespace CS

deriving instance DecidableEq for Nat.Partrec.Code

/-! ## Blum complexity measures -/

/-- A *Blum complexity measure* for the standard numbering `Nat.Partrec.Code.eval` of the
partial computable functions.  `cost c x` is the amount of resource used by the program `c`
on input `x`.  Blum's two axioms are:

* `dom_eq`: `cost c x` is defined exactly when the program `c` halts on `x`;
* the graph of `cost` is decidable, witnessed here by a computable `Bool`-valued `graph`. -/
structure BlumMeasure where
  cost : Code → ℕ →. ℕ
  graph : Code → ℕ → ℕ → Bool
  graph_computable : Computable fun p : (Code × ℕ) × ℕ => graph p.1.1 p.1.2 p.2
  graph_spec : ∀ c x m, graph c x m = true ↔ m ∈ cost c x
  dom_eq : ∀ c x, (cost c x).Dom ↔ (c.eval x).Dom

/-! ## The step-counting measure -/


theorem costLe_iff (M : BlumMeasure) (c : Code) (x b : ℕ) :
    costLe M c x b = true ↔ ∃ m ≤ b, m ∈ M.cost c x := by
  induction b with
  | zero =>
    simp only [costLe, Nat.le_zero]
    constructor
    · intro h; exact ⟨0, rfl, (M.graph_spec _ _ _).mp h⟩
    · rintro ⟨m, hm, h⟩; subst hm; exact (M.graph_spec _ _ _).mpr h
  | succ k ih =>
    show (costLe M c x k || M.graph c x (k + 1)) = true ↔ _
    rw [Bool.or_eq_true, ih, M.graph_spec]
    constructor
    · rintro (⟨m, hm, h⟩ | h)
      · exact ⟨m, by omega, h⟩
      · exact ⟨k + 1, le_refl _, h⟩
    · rintro ⟨m, hm, h⟩
      rcases Nat.lt_or_ge m (k + 1) with hlt | hge
      · exact Or.inl ⟨m, by omega, h⟩
      · have hmk : m = k + 1 := by omega
        subst hmk; exact Or.inr h

