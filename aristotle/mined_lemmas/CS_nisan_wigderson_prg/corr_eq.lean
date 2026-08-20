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

lemma corr_eq (i : Fin m) :
    ∑ x : Fin ℓ → Bool, ∑ r : Fin m → Bool,
        ind (nwPredictor G D i r false x == G i x)
      = hybSum G D ((i : ℕ) + 1) - hybSum G D i + 2 ^ ℓ * 2 ^ m / 2 := by
  have key : ∀ x : Fin ℓ → Bool,
      ∑ r : Fin m → Bool, ind (nwPredictor G D i r false x == G i x)
        = (∑ r : Fin m → Bool, ind (D (hybridStr G ((i : ℕ) + 1) x r)))
          - (∑ r : Fin m → Bool, ind (D (hybridStr G i x r))) + 2 ^ m / 2 := by
    intro x
    set F : (Fin m → Bool) → ℝ := fun r => ind (D (hybridStr G i x r)) with hF
    set v : Bool := G i x with hv
    -- rewrite the correctness indicator
    have hcorr : ∀ r : Fin m → Bool,
        ind (nwPredictor G D i r false x == G i x)
          = if r i = v then F r else 1 - F r := by
      intro r
      by_cases h : r i = v
      · simp only [nwPredictor, hF, ind, h]
        by_cases hD : D (hybridStr G i x r) <;> simp [hD, ← hv]
      · have h' : r i = !v := by
          cases hrv : r i <;> cases hvv : v <;> simp_all
        simp only [nwPredictor, hF, ind]
        by_cases hD : D (hybridStr G i x r) <;> simp [hD, h', ← hv]
    -- apply the averaging lemma to `g`
    have hg := sum_update_bool i (fun r => if r i = v then F r else 1 - F r)
    have hFsum := sum_update_bool i F
    have hupd : ∀ (b : Bool) (r : Fin m → Bool), (Function.update r i b) i = b := by
      intro b r; simp
    have hgb : ∀ b : Bool, ∑ r : Fin m → Bool,
        (if (Function.update r i b) i = v then F (Function.update r i b)
          else 1 - F (Function.update r i b))
        = if b = v then ∑ r : Fin m → Bool, F (Function.update r i b)
          else (2 : ℝ) ^ m - ∑ r : Fin m → Bool, F (Function.update r i b) := by
      intro b
      by_cases hb : b = v
      · simp [hb]
      · simp only [hupd, if_neg hb, Finset.sum_sub_distrib]
        congr 1
        simp [Finset.card_univ]
    have hsumB : (∑ b : Bool, ∑ r : Fin m → Bool,
        (if (Function.update r i b) i = v then F (Function.update r i b)
          else 1 - F (Function.update r i b)))
        = (∑ r : Fin m → Bool, F (Function.update r i v))
          + ((2 : ℝ) ^ m - ∑ r : Fin m → Bool, F (Function.update r i (!v))) := by
      rw [Fintype.sum_bool, hgb true, hgb false]
      cases v <;> (simp; try ring)
    have hpair : (∑ r : Fin m → Bool, F (Function.update r i v))
        + (∑ r : Fin m → Bool, F (Function.update r i (!v))) = 2 * ∑ r : Fin m → Bool, F r := by
      rw [← hFsum, Fintype.sum_bool]
      cases v <;> (simp; try ring)
    have hsucc : (∑ r : Fin m → Bool, ind (D (hybridStr G ((i : ℕ) + 1) x r)))
        = ∑ r : Fin m → Bool, F (Function.update r i v) := by
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [hybridStr_succ]
    rw [Finset.sum_congr rfl fun r (_ : r ∈ (univ : Finset (Fin m → Bool))) => hcorr r]
    have hgg : ∑ r : Fin m → Bool, (if r i = v then F r else 1 - F r)
        = (1 / 2 : ℝ) * ((∑ r : Fin m → Bool, F (Function.update r i v))
          + ((2 : ℝ) ^ m - ∑ r : Fin m → Bool, F (Function.update r i (!v)))) := by
      rw [← hsumB, hg]; ring
    rw [hgg, hsucc]
    have : (∑ r : Fin m → Bool, F (Function.update r i (!v)))
        = 2 * (∑ r : Fin m → Bool, F r) - ∑ r : Fin m → Bool, F (Function.update r i v) := by
      linarith [hpair]
    rw [this]
    ring
  rw [Finset.sum_congr rfl fun x (_ : x ∈ (univ : Finset (Fin ℓ → Bool))) => key x]
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const,
    Finset.card_univ, nsmul_eq_mul]
  simp [hybSum]
  ring

/-- The complemented predictor is correct exactly when the uncomplemented one is wrong. -/
