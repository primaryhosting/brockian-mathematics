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

theorem quantum_singleton' {q n k d : ℕ} (hq : 2 ≤ q) (hk : 1 ≤ k)
    (C : Submodule ℂ (EuclideanSpace ℂ (Fin n → Fin q)))
    (hdim : finrank ℂ C = q ^ k)
    (hcorr : ∀ A : Finset (Fin n), A.card ≤ d - 1 → Correctable q C A) :
    k + 2 * (d - 1) ≤ n := by
  set t := d - 1 with ht
  have hq1 : 1 < q := hq
  have hCne : C ≠ ⊥ := by
    intro h
    rw [h] at hdim
    simp only [finrank_bot] at hdim
    have hpos : 0 < q ^ k := Nat.pow_pos (by omega)
    omega
  -- choose two disjoint sets of sites, each of size at most `t`
  obtain ⟨A, -, hAcard⟩ :=
    Finset.le_card_iff_exists_subset_card.mp
      (show min t n ≤ (Finset.univ : Finset (Fin n)).card by
        rw [Finset.card_univ, Fintype.card_fin]; exact min_le_right _ _)
  obtain ⟨B, hBsub, hBcard⟩ :=
    Finset.le_card_iff_exists_subset_card.mp
      (show min t (n - min t n) ≤ (Aᶜ : Finset (Fin n)).card by
        rw [Finset.card_compl, hAcard]
        simp only [Fintype.card_fin]
        exact min_le_right _ _)
  have hAB : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro i hiA hiB
    exact (Finset.mem_compl.mp (hBsub hiB)) hiA
  have hcA : Correctable q C A := hcorr A (by rw [hAcard]; exact min_le_left _ _)
  have hcB : Correctable q C B := hcorr B (by rw [hBcard]; exact min_le_left _ _)
  have hbound := finrank_le_of_two_correctable q C hCne A B hAB hcA hcB
  rw [hdim, hAcard, hBcard] at hbound
  simp only [Fintype.card_fin] at hbound
  have hk' : k ≤ n - min t n - min t (n - min t n) := (Nat.pow_le_pow_iff_right hq1).mp hbound
  omega

/-- **Quantum Singleton bound**: an `[[n, k, d]]_q` quantum code (`q ≥ 2`, `k ≥ 1`) obeys
`n - k ≥ 2 (d - 1)`. -/
