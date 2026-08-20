/-
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Gromov Nonsqueezing
Category: Frontier Math
Target: Math2.gromov_nonsqueezing
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped RealInnerProductSpace

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Math2

variable {n : ℕ}

/-- The standard symplectic vector space `ℝ^(2n+2)`, realised as the Euclidean space with
index set `Fin (n+1) ⊕ Fin (n+1)`: the `Sum.inl` coordinates are the positions `q₀,…,qₙ`
and the `Sum.inr` coordinates are the conjugate momenta `p₀,…,pₙ`. -/
abbrev SymplecticSpace (n : ℕ) := EuclideanSpace ℝ (Fin (n + 1) ⊕ Fin (n + 1))

/-- The standard symplectic form `ω(x, y) = ∑ᵢ (x_{qᵢ} y_{pᵢ} - x_{pᵢ} y_{qᵢ})`. -/

noncomputable def Jmap (p : SymplecticSpace n) : SymplecticSpace n :=
  WithLp.toLp 2 (fun j => Sum.elim (fun i => p (Sum.inr i)) (fun i => -p (Sum.inl i)) j)

