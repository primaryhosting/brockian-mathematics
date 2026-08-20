import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

import RequestProject.QI.Spectral

/-!
# An integral formula for the relative entropy

The elementary scalar identity

`∫_0^∞ (a²/(b + t a) - a/(1 + t)) dt = a (log a - log b)`  (`QI.integral_scalar`)

for `a, b > 0`, combined with the spectral formulas of `RequestProject.QI.Spectral`, gives the
integral representation

`relEntropy ρ σ = ∫_{t ∈ (0, ∞)} (Rval ρ σ t - (tr ρ).re / (1 + t)) dt`

(`QI.relEntropy_eq_integral`) for positive definite `ρ`, `σ`.  Since `Rval` is monotone under
quantum channels, this immediately yields the data-processing inequality.
-/

namespace QI

open Real MeasureTheory Filter Set Matrix
open scoped Topology ComplexOrder BigOperators MatrixOrder

/-! ### The scalar integral -/

/-- The antiderivative of `t ↦ a²/(b + t a) - a/(1 + t)`. -/

theorem exists_sylvester (hρ : ρ.PosDef) (hσ : σ.PosDef) {t : ℝ} (ht : 0 ≤ t) :
    ∃ B₀ : Matrix n n ℂ, σ * B₀ + (t : ℂ) • (B₀ * ρ) = ρ ∧
      (Matrix.trace (ρ * B₀)).re =
        ∑ j, ∑ i, ‖eigOverlap hρ.isHermitian hσ.isHermitian i j‖ ^ 2 *
          (hρ.isHermitian.eigenvalues j ^ 2 /
            (hσ.isHermitian.eigenvalues i + t * hρ.isHermitian.eigenvalues j)) := by
  classical
  have hρ' : ρ.IsHermitian := hρ.isHermitian
  have hσ' : σ.IsHermitian := hσ.isHermitian
  set p : n → ℝ := hρ'.eigenvalues with hp
  set q : n → ℝ := hσ'.eigenvalues with hq
  set U : Matrix n n ℂ := (hρ'.eigenvectorUnitary : Matrix n n ℂ) with hUdef
  set V : Matrix n n ℂ := (hσ'.eigenvectorUnitary : Matrix n n ℂ) with hVdef
  set W : Matrix n n ℂ := eigOverlap hρ' hσ' with hWdef
  have hpos : ∀ i j, (0:ℝ) < q i + t * p j := by
    intro i j
    have h1 : 0 < q i := hσ.eigenvalues_pos i
    have h2 : 0 < p j := hρ.eigenvalues_pos j
    nlinarith
  have hne : ∀ i j, ((q i : ℂ) + (t : ℂ) * (p j : ℂ)) ≠ 0 := by
    intro i j
    have : ((q i : ℂ) + (t : ℂ) * (p j : ℂ)) = ((q i + t * p j : ℝ) : ℂ) := by push_cast; ring
    rw [this]
    exact_mod_cast (hpos i j).ne'
  have hUU : star U * U = 1 := UnitaryGroup.star_mul_self _
  have hVV' : V * star V = 1 := (Unitary.mem_iff.mp hσ'.eigenvectorUnitary.2).2
  have hVV : star V * V = 1 := UnitaryGroup.star_mul_self _
  have hspecρ : ρ = U * diagonal (RCLike.ofReal ∘ p) * star U := hρ'.spectral_theorem
  have hspecσ : σ = V * diagonal (RCLike.ofReal ∘ q) * star V := hσ'.spectral_theorem
  have hVW : V * W = U := by
    rw [hWdef, eigOverlap, ← Matrix.mul_assoc, hVV', Matrix.one_mul]
  set C : Matrix n n ℂ :=
    Matrix.of (fun i j => W i j * (p j : ℂ) / ((q i : ℂ) + (t : ℂ) * (p j : ℂ))) with hC
  refine ⟨V * C * star U, ?_, ?_⟩
  · -- the Sylvester equation
    have key : diagonal (RCLike.ofReal ∘ q) * C + (t : ℂ) • (C * diagonal (RCLike.ofReal ∘ p))
        = W * diagonal (RCLike.ofReal ∘ p) := by
      ext i j
      simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal,
        Function.comp_apply, smul_eq_mul, hC, Matrix.of_apply,
        show ∀ x : ℝ, (RCLike.ofReal x : ℂ) = (x : ℂ) from fun _ => rfl]
      simp only [div_mul_eq_mul_div, mul_div_assoc']
      rw [← add_div, div_eq_iff (hne i j)]
      ring
    calc σ * (V * C * star U) + (t : ℂ) • (V * C * star U * ρ)
        = V * (diagonal (RCLike.ofReal ∘ q) * C) * star U
          + (t : ℂ) • (V * (C * diagonal (RCLike.ofReal ∘ p)) * star U) := by
          rw [hspecσ]
          conv_lhs => rw [hspecρ]
          simp only [Matrix.mul_assoc]
          rw [← Matrix.mul_assoc (star V) V, hVV, Matrix.one_mul,
            ← Matrix.mul_assoc (star U) U, hUU, Matrix.one_mul]
      _ = V * (diagonal (RCLike.ofReal ∘ q) * C
            + (t : ℂ) • (C * diagonal (RCLike.ofReal ∘ p))) * star U := by
          rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = V * (W * diagonal (RCLike.ofReal ∘ p)) * star U := by rw [key]
      _ = ρ := by
          rw [← Matrix.mul_assoc, hVW, hspecρ]
  · -- the value of the trace
    rw [hspecρ]
    rw [trace_conj_mul_gen U V C hUU]
    have hWH : star U * V = Wᴴ := by
      rw [hWdef, eigOverlap]
      simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_mul, hUdef, hVdef]
    rw [hWH, trace_diag_mul_mul]
    have : ∀ j i, (RCLike.ofReal (p j) : ℂ) * (Wᴴ j i * C i j)
        = ((‖W i j‖ ^ 2 * (p j ^ 2 / (q i + t * p j)) : ℝ) : ℂ) := by
      intro j i
      simp only [hC, Matrix.of_apply, Matrix.conjTranspose_apply, RCLike.star_def]
      rw [div_eq_mul_inv, div_eq_mul_inv]
      push_cast
      rw [show ((starRingEnd ℂ) (W i j)) * ((W i j) * (p j : ℂ) *
          ((q i : ℂ) + (t : ℂ) * (p j : ℂ))⁻¹)
          = (((starRingEnd ℂ) (W i j)) * (W i j)) * ((p j : ℂ) *
            ((q i : ℂ) + (t : ℂ) * (p j : ℂ))⁻¹) by ring]
      rw [conj_mul_self]
      push_cast
      simp only [show ∀ x : ℝ, (RCLike.ofReal x : ℂ) = (x : ℂ) from fun _ => rfl]
      ring
    simp only [Function.comp_apply]
    rw [Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => this j i]
    simp only [← Complex.ofReal_sum, Complex.ofReal_re]

end QI

import RequestProject.QI.Integral

/-!
# The data-processing inequality for the quantum relative entropy

The main result of this development is `QI.data_processing`: for a quantum channel `Φ`
(a completely positive trace preserving map, given in Kraus form) and positive definite
matrices `ρ`, `σ`,

`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`,

where `D` is the Umegaki relative entropy `QI.relEntropy`.

The proof combines two ingredients:

* the integral representation
  `relEntropy ρ σ = ∫_{t>0} (Rval ρ σ t - (tr ρ).re/(1+t)) dt` (`QI.relEntropy_eq_integral`),
  where `Rval ρ σ t` is the supremum of an explicit quadratic functional;
* the monotonicity `Rval (Φ ρ) (Φ σ) t ≤ Rval ρ σ t` (`QI.Rval_apply_le`), which follows from
  the Kadison–Schwarz inequality for the adjoint (Heisenberg picture) map of the channel.

Trace preservation of the channel makes the subtracted terms `(tr ρ).re/(1+t)` agree.
-/

namespace QI

open Matrix MeasureTheory Set
open scoped ComplexOrder BigOperators MatrixOrder

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]

/-- **Data-processing inequality (monotonicity of the quantum relative entropy under CPTP
maps).** For a quantum channel `Φ` given in Kraus form and positive definite `ρ`, `σ` such that
`Φ(σ)` is positive definite, the Umegaki relative entropy satisfies
`D(Φ(ρ) ‖ Φ(σ)) ≤ D(ρ ‖ σ)`. -/
