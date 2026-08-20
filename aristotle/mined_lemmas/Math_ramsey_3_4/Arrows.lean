/-
# Ramsey 3 4
Category: Pure Mathematics
Target: Math.ramsey_3_4
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Ramsey 3 4

We define the two-colour Ramsey number `Math.ramseyNumber` and prove `R(3,4) = 9`.
-/

open Finset SimpleGraph

namespace Math

/-- `Arrows n r s` says that every simple graph on `n` vertices contains either a clique of
size `r` or an independent set of size `s`, i.e. `n → (r, s)` in Ramsey arrow notation. -/

def Arrows (n r s : ℕ) : Prop :=
  ∀ G : SimpleGraph (Fin n),
    (∃ A : Finset (Fin n), G.IsNClique r A) ∨ (∃ B : Finset (Fin n), G.IsNIndepSet s B)

/-- The two-colour Ramsey number `R(r, s)`: the least `n` such that every graph on `n`
vertices contains an `r`-clique or an `s`-element independent set. -/
