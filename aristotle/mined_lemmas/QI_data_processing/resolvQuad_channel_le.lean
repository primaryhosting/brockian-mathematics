import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

theorem resolvQuad_channel_le (hK : ∑ i, (K i)ᴴ * K i = 1) {ρ σ : Matrix n n ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hΦρ : (krausMap K ρ).PosDef)
    (hΦσ : (krausMap K σ).PosDef) {t : ℝ} (ht : 0 < t) :
    resolvQuad (krausMap K ρ) (krausMap K σ) t ≤ resolvQuad ρ σ t := by
  obtain ⟨Z, hZ⟩ := exists_varFun_eq hΦρ hΦσ ht
  calc resolvQuad (krausMap K ρ) (krausMap K σ) t
      = varFun (krausMap K ρ) (krausMap K σ) t Z := hZ
    _ ≤ varFun ρ σ t (krausAdj K Z) :=
        varFun_channel_le hK hρ.posSemidef hσ.posSemidef ht.le Z
    _ ≤ resolvQuad ρ σ t := varFun_le hρ hσ ht _

/-! ### The data-processing inequality -/

/-- **Data-processing inequality**: the Umegaki relative entropy
`relEntropy ρ σ = Tr(ρ log ρ) - Tr(ρ log σ)` is monotone under a CPTP map given in
Kraus (operator-sum) form `Φ X = ∑ i, K i * X * (K i)ᴴ` with `∑ i, (K i)ᴴ * (K i) = 1`. -/
