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

lemma predProb_identity {m : ℕ} (D : (Fin m → Bool) → Bool) (i : Fin m) (r : Fin m → Bool)
    (c : Bool) : predProb (ℓ := m) (fun j x => x j) D i r c = 1 / 2 := by
  set G : Fin m → (Fin m → Bool) → Bool := fun j x => x j with hG
  set P : (Fin m → Bool) → Bool := fun x => nwPredictor G D i r c x with hP
  have hindep : ∀ (x : Fin m → Bool) (b : Bool), P (Function.update x i b) = P x := by
    intro x b
    have hstr : hybridStr G i (Function.update x i b) r = hybridStr G i x r := by
      funext j
      by_cases hj : (j : ℕ) < (i : ℕ)
      · have hne : j ≠ i := by
          intro h; subst h; omega
        simp [hybridStr, hj, hG, Function.update_of_ne hne]
      · simp [hybridStr, hj]
    simp [hP, nwPredictor, hstr]
  have key := sum_update_bool i (fun x : Fin m → Bool => ind (P x == G i x))
  have hleft : ∑ b : Bool, ∑ x : Fin m → Bool,
      ind (P (Function.update x i b) == G i (Function.update x i b)) = 2 ^ m := by
    rw [Finset.sum_comm]
    have hx : ∀ x : Fin m → Bool, ∑ b : Bool,
        ind (P (Function.update x i b) == G i (Function.update x i b)) = 1 := by
      intro x
      have : ∀ b : Bool, ind (P (Function.update x i b) == G i (Function.update x i b))
          = ind (P x == b) := by
        intro b; rw [hindep x b]; simp [hG]
      rw [Fintype.sum_bool, this true, this false]
      cases P x <;> simp [ind]
    rw [Finset.sum_congr rfl fun x _ => hx x]
    simp [Finset.card_univ]
  rw [hleft] at key
  unfold predProb
  rw [show (∑ x : Fin m → Bool, ind (nwPredictor G D i r c x == G i x))
      = ∑ x : Fin m → Bool, ind (P x == G i x) from rfl]
  have h2 : (0 : ℝ) < 2 ^ m := by positivity
  field_simp
  linarith [key]

/-- **Nisan–Wigderson generator: security from hardness.**

Let `G 0, …, G (m-1)` be the component functions of a generator that maps a seed
`x : Fin ℓ → Bool` to the `m`-bit string `fun i => G i x` (in the Nisan–Wigderson
construction `G i x = f (x restricted to the i-th set of a combinatorial design)`).
Let `D` be any distinguisher.

Hardness hypothesis: no next-bit predictor of Nisan–Wigderson / Yao type — i.e. no function
obtained from `D` by hard-wiring the later random bits `r`, feeding it the earlier generator
bits, and possibly complementing the answer — predicts any output bit `G i` with advantage
more than `ε / m`.

Conclusion: `D` cannot distinguish the generator's output from a uniformly random `m`-bit
string with advantage more than `ε`; i.e. the generator derandomizes `D`. -/
