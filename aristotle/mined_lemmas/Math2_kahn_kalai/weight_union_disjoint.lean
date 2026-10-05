import Mathlib
import RequestProject.KahnKalai.Iteration

/-!
# Kahn Kalai
Category: Frontier Math
Target: Math2.kahn_kalai
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

Expectation and threshold are within a log factor: a formalisation of the Park–Pham proof
of the Kahn–Kalai conjecture.
-/

open Finset

namespace Math2

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- The `p`-biased measure of a family of subsets. -/

lemma weight_union_disjoint (q : ℝ) {W T : Finset α} (hd : Disjoint T W) :
    weight q W * q ^ T.card = weight q (W ∪ T) * (1 - q) ^ T.card := by
  have hTc : T ⊆ Wᶜ := by
    intro y hy
    simp only [Finset.mem_compl]
    exact fun hyW => (Finset.disjoint_left.1 hd) hy hyW
  have hcard : (W ∪ T).card = W.card + T.card := by
    rw [Finset.card_union_of_disjoint hd.symm]
  have hcompl : (W ∪ T)ᶜ = Wᶜ \ T := by
    ext y; simp only [Finset.mem_compl, Finset.mem_union, Finset.mem_sdiff, not_or]
  have hc2 : (W ∪ T)ᶜ.card + T.card = Wᶜ.card := by
    rw [hcompl]
    exact Finset.card_sdiff_add_card_eq_card hTc
  rw [weight_def, weight_def, hcard, ← hc2, pow_add, pow_add]
  ring

/-- **Key Lemma** (Park–Pham, Lemma 2.1). If `H` is `ℓ`-bounded with `ℓ ≤ 2h+1`, then the
expected cost of the cover `Ufam H h W` formed by the large minimum fragments is at most
`(1/32) * (1/16) ^ h`, where `W` is a random subset with each element present independently
with probability `64 p`. -/
