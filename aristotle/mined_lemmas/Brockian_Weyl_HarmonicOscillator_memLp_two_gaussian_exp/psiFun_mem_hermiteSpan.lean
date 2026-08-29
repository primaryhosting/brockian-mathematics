/-
  RequestProject/ESA.lean

  Essential self-adjointness of the harmonic-oscillator core
  `harmonicOscillatorPMap` (the operator `-d²/dx² + x²` on the Schwartz core of
  `L²(ℝ)`).

  The argument is the classical deficiency-index one.  If `g` is in the domain of
  the adjoint with `T* g = z • g` and `Im z ≠ 0`, then pairing against the Hermite
  functions `hermiteFun n` (which lie in the Schwartz core and satisfy
  `H hermiteFun n = (2n+1) hermiteFun n`) forces `⟪g, hermiteFun n⟫ = 0` for every
  `n`, since `conj z ≠ 2n+1`.  The Hermite functions span every monomial
  `xⁿ e^{-x²/2}`, so all the moments of `x ↦ conj (g x) e^{-x²/2}` vanish, and the
  moment theorem gives `g = 0`.
-/
import RequestProject.Corpus
import RequestProject.Hermite
import RequestProject.Moments

open MeasureTheory Complex SchwartzMap ComplexConjugate
open scoped InnerProductSpace

namespace Brockian.Weyl.HarmonicOscillator

open Brockian.Weyl.Operator Brockian.Weyl.SchrodingerMinimal Brockian.Moments

/-! ### Integrability facts for an `L²` function against Gaussian weights -/


theorem psiFun_mem_hermiteSpan (n : ℕ) :
    psiFun n ∈ Submodule.span ℂ (Set.range hermiteFun) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => exact Submodule.subset_span ⟨0, rfl⟩
    | (m + 1) =>
        have h1 := ih m (by omega)
        have h2 := ih (m - 1) (by omega)
        have hrec := creation_psiFun m
        have hval : psiFun (m + 1)
            = (2 : ℂ)⁻¹ • (creationSchwartz (psiFun m) + (m : ℂ) • psiFun (m - 1)) := by
          rw [hrec]
          match_scalars <;> ring
        rw [hval]
        exact Submodule.smul_mem _ _
          (Submodule.add_mem _ (hermiteSpan_creation_mem h1) (Submodule.smul_mem _ _ h2))

end Brockian.Weyl.HarmonicOscillator

/-
  RequestProject/Corpus.lean

  The corpus declarations needed for the harmonic-oscillator goal, reproduced
  here (verbatim where they were supplied, and reconstructed minimally where the
  supplying module was not part of the prompt).

  * `Brockian.Weyl.Operator`            — verbatim from `Brockian/WeylOperator.lean`.
  * `Brockian.Weyl.SchrodingerMinimal`  — the pieces of `Brockian/WeylSchrodingerMinimal.lean`
                                          that the harmonic-oscillator module uses
                                          (`H2`, `schwartzToL2`, `D2`, `inner_toLp`, ...).
  * `Brockian.Weyl.HarmonicOscillator`  — verbatim from `Brockian/WeylHarmonicOscillator.lean`
                                          (the operator itself and its density statement).
-/
import Mathlib

namespace Brockian.Weyl.Operator

open scoped InnerProductSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ### Symmetric densely-defined operators -/

/-- **Symmetric operator.** A partially-defined operator `T : H →ₗ.[ℂ] H` is
*symmetric* when it is its own formal adjoint: `⟪T x, y⟫ = ⟪x, T y⟫` for all
`x, y` in the domain. -/
