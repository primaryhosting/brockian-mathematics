/-
Header (Lean requires `import` to precede any command, including a module docstring,
so the required header is reproduced verbatim as a module docstring just below the import):

# Schmidt Decomposition
Category: Frontier Qi
Target: QI.schmidt_decomposition
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
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
set_option synthInstance.maxHeartbeats 400000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace QI

open Matrix

/-- The standard Hermitian inner product on `ℂ^d`, `⟪x, y⟫ = ∑ i, conj (x i) * y i`. -/

theorem card_eq_finrank_eigenspace {m n r : ℕ} {ψ : Fin m → Fin n → ℂ} {σ : Fin r → ℝ}
    {u : Fin r → Fin m → ℂ} {v : Fin r → Fin n → ℂ} (h : IsSchmidt ψ σ u v) {t : ℝ} (ht : 0 < t) :
    (Finset.univ.filter fun k => σ k = t).card =
      Module.finrank ℂ (Module.End.eigenspace (Matrix.mulVecLin (rho ψ)) ((t : ℂ) ^ 2)) := by
  classical
  rw [eigenspace_eq_span h ht,
    show (Set.range fun k : {k : Fin r // σ k = t} => u k.1)
      = Set.range (u ∘ (fun k : {k : Fin r // σ k = t} => k.1)) from rfl,
    finrank_span_eq_card
      ((linearIndependent_of_isON h.onu).comp (fun k : {k : Fin r // σ k = t} => k.1)
        Subtype.val_injective),
    Fintype.card_subtype]

/-- **Uniqueness of the Schmidt coefficients**: any two Schmidt decompositions of the same
bipartite vector have the same multiset of Schmidt coefficients. -/
