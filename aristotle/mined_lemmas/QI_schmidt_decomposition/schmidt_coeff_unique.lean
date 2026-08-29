import Mathlib

/-!
# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise
open scoped ComplexOrder

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Finset Matrix

variable {m n : ℕ}

/-- `IsSchmidtDecomp psi s e f` says that the bipartite pure state `psi` (a vector in
`ℂ^m ⊗ ℂ^n`, written as its coordinate array) has the Schmidt decomposition
`psi = ∑ k, s k • (e k ⊗ f k)`, where the Schmidt coefficients `s k` are strictly positive
and `e`, `f` are orthonormal families in the two factors. -/
structure IsSchmidtDecomp {ι : Type} [Fintype ι] (psi : Fin m → Fin n → ℂ)
    (s : ι → ℝ) (e : ι → EuclideanSpace ℂ (Fin m)) (f : ι → EuclideanSpace ℂ (Fin n)) :
    Prop where
  coeff_pos : ∀ k, 0 < s k
  orthonormal_left : Orthonormal ℂ e
  orthonormal_right : Orthonormal ℂ f
  decomp : ∀ i j, psi i j = ∑ k, (s k : ℂ) * e k i * f k j

/-- The self-adjoint operator `∑ k, c k • ⟪e k, ·⟫ • e k`. -/

theorem schmidt_coeff_unique (psi : Fin m → Fin n → ℂ) {r r' : ℕ}
    {s : Fin r → ℝ} {e : Fin r → EuclideanSpace ℂ (Fin m)} {f : Fin r → EuclideanSpace ℂ (Fin n)}
    {s' : Fin r' → ℝ} {e' : Fin r' → EuclideanSpace ℂ (Fin m)}
    {f' : Fin r' → EuclideanSpace ℂ (Fin n)}
    (H : IsSchmidtDecomp psi s e f) (H' : IsSchmidtDecomp psi s' e' f') :
    (univ : Finset (Fin r)).val.map s = (univ : Finset (Fin r')).val.map s' := by
  classical
  have hop : specOp (fun k => (s k) ^ 2) e = specOp (fun k => (s' k) ^ 2) e' := by
    refine LinearMap.ext fun v => ?_
    ext i
    rw [H.specOp_apply_eq v i, H'.specOp_apply_eq v i]
  have hm := multiset_map_eq_of_specOp_eq (fun k => (s k) ^ 2) e (fun k => (s' k) ^ 2) e'
    H.orthonormal_left H'.orthonormal_left (fun k => pow_pos (H.coeff_pos k) 2)
    (fun k => pow_pos (H'.coeff_pos k) 2) hop
  have h2 := congrArg (Multiset.map Real.sqrt) hm
  rw [Multiset.map_map, Multiset.map_map] at h2
  have e1 : (Real.sqrt ∘ fun k => (s k) ^ 2) = s :=
    funext fun k => Real.sqrt_sq (le_of_lt (H.coeff_pos k))
  have e2 : (Real.sqrt ∘ fun k => (s' k) ^ 2) = s' :=
    funext fun k => Real.sqrt_sq (le_of_lt (H'.coeff_pos k))
  rwa [e1, e2] at h2

/-- **Schmidt decomposition.**  Every bipartite pure state `psi ∈ ℂ^m ⊗ ℂ^n` admits a Schmidt
decomposition `psi = ∑ k, s k • (e k ⊗ f k)` with strictly positive coefficients `s k` and
orthonormal families `e`, `f`; moreover the Schmidt coefficients are unique as a multiset
(in particular their number, the Schmidt rank, is uniquely determined). -/
