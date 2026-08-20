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


theorem speedCost_not_pad {e : Code} (he : ∀ n, e ≠ padCode n) (x : ℕ) :
    speedCost r e x = (stepCost e x).map (· + bigB r x) := by
  unfold speedCost
  rw [if_neg (padIdx_not_pad e he x)]

end Speedup

/-! ## Blum's speedup phenomenon: a problem with no fastest algorithm -/

/-- **A Blum complexity measure exhibiting speedup.**

For every computable "speedup factor" `r` there is a Blum complexity measure `M` (i.e. a
measure satisfying Blum's axioms for the standard numbering of the partial computable
functions) and a computable function `f` such that *every* program `e` computing `f` is beaten
by another program `e'` computing the very same function `f`: on almost every input `x`, the
cost of `e` is at least `r` applied to the cost of `e'`.

Thus no program for `f` is optimal: each one can be sped up by a factor `r` on almost all
inputs. -/
