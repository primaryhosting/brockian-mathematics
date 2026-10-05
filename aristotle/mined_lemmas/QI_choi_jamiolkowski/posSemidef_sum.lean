import Mathlib

/-!
# Choi Jamiolkowski
Category: Frontier Qi
Target: QI.choi_jamiolkowski
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped ComplexOrder MatrixOrder
open Matrix

namespace QI

variable {n m : Type} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]

/-- The Choi matrix of a linear map `Φ : Mₙ → Mₘ`, indexed by `(n × m) × (n × m)`:
`C (i,a) (j,b) = (Φ (Eᵢⱼ)) a b`. -/

lemma posSemidef_sum {k ι : Type} [Fintype k] (s : Finset ι)
    (f : ι → Matrix k k ℂ) (hf : ∀ i ∈ s, (f i).PosSemidef) :
    (∑ i ∈ s, f i).PosSemidef := by
  classical
  induction s using Finset.induction with
  | empty => simpa using (Matrix.PosSemidef.zero (n := k) (R := ℂ))
  | insert a s ha ih =>
      rw [Finset.sum_insert ha]
      exact (hf a (Finset.mem_insert_self a s)).add
        (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- The entries of a single Kraus term `V * X * Vᴴ`. -/
