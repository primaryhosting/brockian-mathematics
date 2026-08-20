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


theorem costLe_computable (M : BlumMeasure) :
    Computable fun p : (Code × ℕ) × ℕ => costLe M p.1.1 p.1.2 p.2 := by
  have harg0 : Computable (fun p : (Code × ℕ) × ℕ => (p.1, 0)) :=
    Computable.fst.pair (Computable.const 0)
  have hg := M.graph_computable.comp harg0
  have arg : Computable (fun p : ((Code × ℕ) × ℕ) × (ℕ × Bool) => (p.1.1, p.2.1 + 1)) :=
    (Computable.fst.comp Computable.fst).pair
      (Primrec.succ.to_comp.comp (Computable.fst.comp Computable.snd))
  have h1 := M.graph_computable.comp arg
  have h2 := Primrec.or.to_comp.comp (Computable.snd.comp Computable.snd) h1
  have h3 := Computable.nat_rec (f := fun p : (Code × ℕ) × ℕ => p.2)
    (g := fun p : (Code × ℕ) × ℕ => M.graph p.1.1 p.1.2 0)
    (h := fun (p : (Code × ℕ) × ℕ) (q : ℕ × Bool) => q.2 || M.graph p.1.1 p.1.2 (q.1 + 1))
    Computable.snd hg h2
  exact h3

/-! ## Patched programs -/

/-- The function computed by the program `patchCode C n L`: it follows level `0` of the
construction below the patch length `L`, and level `n` from `L` on. -/
