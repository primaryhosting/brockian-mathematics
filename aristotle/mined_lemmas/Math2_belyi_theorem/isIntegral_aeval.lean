import RequestProject.BelyiPoly

/-!
# Belyi polynomials for finite sets of rational points

A polynomial `f ∈ ℚ[X]` is *Belyi* if it is non-constant and all of its finite critical values
(computed over `ℂ`) lie in `{0, 1}`; viewed as a map `ℙ¹ → ℙ¹` such an `f` is ramified only
above `{0, 1, ∞}`.

The main result of this file is `Math2.exists_belyiPolynomial_of_rat`: for every finite set of
rational numbers there is a Belyi polynomial taking each of them to `0` or `1`.
-/

set_option maxRecDepth 8000

namespace Math2

open Polynomial

/-- `f` is a Belyi polynomial: non-constant, with all finite critical values in `{0, 1}`. -/

lemma isIntegral_aeval {s : ℂ} (hs : IsIntegral ℚ s) (Q : ℚ[X]) : IsIntegral ℚ (aeval s Q) := by
  have hfin : FiniteDimensional ℚ ℚ⟮s⟯ := adjoin.finiteDimensional hs
  have hmem : aeval s Q ∈ ℚ⟮s⟯ :=
    IntermediateField.algebra_adjoin_le_adjoin ℚ {s} (Polynomial.aeval_mem_adjoin_singleton ℚ s)
  have h : IsIntegral ℚ (⟨aeval s Q, hmem⟩ : ℚ⟮s⟯) := IsIntegral.of_finite ℚ _
  exact h.map (IntermediateField.val ℚ⟮s⟯)

/-- A polynomial expression in an algebraic number has degree at most that of the number. -/
