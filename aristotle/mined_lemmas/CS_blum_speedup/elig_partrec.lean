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


theorem elig_partrec (M : BlumMeasure) {r : ℕ → ℕ} (hr : Computable r) :
    Partrec fun q : Code × ℕ × ℕ => elig M r q.1 q.2.1 q.2.2 := by
  have hb := bound_partrec M hr
  have hi : Computable fun p : (Code × ℕ × ℕ) × ℕ => (ofNat Code p.1.2.1) :=
    (Computable.ofNat Code).comp (Computable.fst.comp (Computable.snd.comp Computable.fst))
  have hy : Computable fun p : (Code × ℕ × ℕ) × ℕ => p.1.2.2 :=
    Computable.snd.comp (Computable.snd.comp Computable.fst)
  have hcl0 := (costLe_computable M).comp ((hi.pair hy).pair Computable.snd)
  have hcl : Computable₂ fun (q : Code × ℕ × ℕ) (b : ℕ) =>
      costLe M (ofNat Code q.2.1) q.2.2 b := hcl0
  have h := Partrec.map hb hcl
  exact h

