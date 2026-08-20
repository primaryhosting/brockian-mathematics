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

import RequestProject.QI.KadisonSchwarz

/-!
# A variational formula for the resolvent quantity `G`

For positive semidefinite `ρ`, `σ` and `t ≥ 0` we consider the concave functional

`energy ρ σ t X = 2 Re Tr (ρ X) - Re Tr (Xᴴ σ X) - t Re Tr (Xᴴ X ρ)`

and its supremum `Gfun ρ σ t`.  This is a variational form of
`⟪ρ^{1/2}, (Δ + t)⁻¹ ρ^{1/2}⟫` for the relative modular operator `Δ : Z ↦ σ Z ρ⁻¹`.

Two facts are proved here:

* `Gfun` is computed by any stationary point (`Gfun_eq_of_stationary`), and a stationary
  point exists whenever `σ` is positive definite, with an explicit spectral value
  (`Gfun_spectral`);
* `Gfun` is monotone under quantum channels (`Gfun_krausMap_le`).
-/

set_option maxHeartbeats 1000000

open Matrix
open scoped ComplexOrder MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m] [Fintype ι]
  [DecidableEq ι]

/-- The concave functional whose supremum is `Gfun`. -/

theorem integral_entropyTerm {r s : ℝ} (hr : 0 ≤ r) (hs : 0 < s) :
    ∫ t in Ioi (0 : ℝ), (r ^ 2 / (s + t * r) - r / (1 + t))
      = r * Real.log r - r * Real.log s := by
  rcases eq_or_lt_of_le hr with hr0 | hr0
  · simp [← hr0]
  have hderiv : ∀ t ∈ Ici (0 : ℝ), HasDerivAt (logAnti r s)
      (r ^ 2 / (s + t * r) - r / (1 + t)) t := fun t ht => hasDerivAt_logAnti hr0 hs ht
  rw [integral_Ioi_of_hasDerivAt_of_tendsto' hderiv (integrableOn_entropyTerm hr hs)
    (tendsto_logAnti hr0 hs)]
  simp [logAnti]

end QI

/-
# Data Processing
Category: Frontier Qi
Target: QI.data_processing
Statement: Quantum relative entropy is monotone under CPTP maps (data-processing inequality).
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import RequestProject.QI.IntegralFormula

/-!
The data-processing inequality for the Umegaki relative entropy

`relEntropy ρ σ = Re Tr (ρ log ρ - ρ log σ)`

of matrices, with respect to a completely positive trace-preserving map given in Kraus form
`krausMap K A = ∑ i, K i * A * (K i)ᴴ` with `∑ i, (K i)ᴴ * (K i) = 1`.

(The header comment at the top of this file uses plain block-comment delimiters rather than
module-docstring delimiters, since Lean requires `import` commands to precede any doc comment.)
-/

set_option maxHeartbeats 1000000

open Matrix MeasureTheory Set
open scoped ComplexOrder MatrixOrder

namespace QI

/-- **Data-processing inequality.** The Umegaki relative entropy of two states is
non-increasing under a completely positive trace-preserving map, presented in Kraus form
`Φ(A) = ∑ i, K i * A * (K i)ᴴ` with `∑ i, (K i)ᴴ * (K i) = 1`.

Here `ρ` is positive semidefinite and `σ` is positive definite; the image `Φ σ` is assumed
positive definite as well, which is the usual non-degeneracy condition making both sides finite
(a channel may map a full-rank `σ` to a singular matrix, in which case the left-hand relative
entropy is `+∞` informally and the `Real.log 0 = 0` convention used here would not represent it). -/
