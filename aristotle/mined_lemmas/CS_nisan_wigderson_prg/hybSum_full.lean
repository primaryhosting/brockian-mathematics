import Mathlib

/-!
# Nisan Wigderson Prg
Category: Frontier Cs
Target: CS.nisan_wigderson_prg
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

namespace CS

open Finset

/-- Real-valued indicator of a Boolean value. -/

lemma hybSum_full : hybSum G D m = 2 ^ m * ∑ x : Fin ℓ → Bool, ind (D (fun i => G i x)) := by
  unfold hybSum
  have hm : ∀ (x : Fin ℓ → Bool) (r : Fin m → Bool), hybridStr G m x r = fun i => G i x := by
    intro x r; funext j; simp [hybridStr, j.isLt]
  simp [hm, Finset.card_univ, Finset.mul_sum]

end Core

/-- The hardness hypothesis below is satisfiable with `ε = 0`: for the identity generator
(`ℓ = m`, `G i x = x i`) every Nisan–Wigderson next-bit predictor succeeds with probability
exactly `1/2`, because the predictor never looks at the `i`-th seed bit. -/
