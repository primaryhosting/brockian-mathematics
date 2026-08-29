/-
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# Quantum Singleton
Category: Frontier Qi
Target: QI.quantum_singleton
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)

An `[[n, k, d]]_q` quantum error-correcting code is a subspace `C` of the `n`-qudit space
`(ℂ^q)^{⊗ n}`, here modelled as `EuclideanSpace ℂ (Fin n → Fin q)` (functions on the set of
classical configurations), of dimension `q ^ k`, such that every set `A` of at most `d - 1`
sites is *correctable*, i.e. satisfies the Knill–Laflamme condition
`P E P = λ(E) P` for all operators `E` supported on `A` (equivalently, for all matrix units,
which is the form used below).

The main result `QI.quantum_singleton` is the quantum Singleton bound `n - k ≥ 2 (d - 1)`.

The proof is the rank version of the standard entropic argument: for two disjoint correctable
sets `A`, `B`, writing `K` for the dimension of the code, `r_A`, `r_B` for the ranks of the
reduced density matrices on `A`, `B` and `γ` for the configuration space of the remaining
sites, one has `K * r_A ≤ |γ| * r_B` and `K * r_B ≤ |γ| * r_A`, whence `K ≤ |γ|`.
-/

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

set_option grind.warning false

open scoped ComplexConjugate
open Module (finrank)

namespace QI

noncomputable section Core

variable {X α β γ Ya Yb : Type*} [Fintype X] [Fintype α] [Fintype β] [Fintype γ]
  [Fintype Ya] [Fintype Yb]

/-- The slice of `f` along the cut `e : X ≃ α × Y` at the value `a`: the vector
`y ↦ f (e.symm (a, y))`. -/

theorem finrank_le_of_two_correctable (q : ℕ) (C : Submodule ℂ (EuclideanSpace ℂ (ι → Fin q)))
    (hC : C ≠ ⊥) (A B : Finset ι) (hAB : Disjoint A B)
    (hA : Correctable q C A) (hB : Correctable q C B) :
    finrank ℂ C ≤ q ^ (Fintype.card ι - A.card - B.card) := by
  have hcard : Fintype.card ({i : ι // i ∉ A ∧ i ∉ B} → Fin q)
      = q ^ (Fintype.card ι - A.card - B.card) := by
    have h1 : Fintype.card {i : ι // i ∉ A ∧ i ∉ B} = Fintype.card ι - A.card - B.card := by
      have h2 : Fintype.card {i : ι // i ∉ A ∧ i ∉ B} = ((A ∪ B)ᶜ : Finset ι).card := by
        rw [Fintype.card_subtype]
        congr 1
        ext i
        simp
      rw [h2, Finset.card_compl, Finset.card_union_of_disjoint hAB]
      omega
    rw [Fintype.card_fun, h1, Fintype.card_fin]
  rw [← hcard]
  exact core_bound (cutEquiv q A) (cutEquiv q B) (splitCompl q A B hAB) (splitCompl' q A B hAB)
    (split_compat q A B hAB) C hC (corrCut_of_correctable q C A hA) (corrCut_of_correctable q C B hB)

end Concrete

/-- **Quantum Singleton bound**, strong form: an `[[n, k, d]]_q` code with `q ≥ 2` and `k ≥ 1`
satisfies `k + 2 (d - 1) ≤ n`. -/
