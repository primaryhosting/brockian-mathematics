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

lemma correctable_span_singleton (q : ℕ) (f : EuclideanSpace ℂ (ι → Fin q)) (hf : f ≠ 0)
    (A : Finset ι) : Correctable q (Submodule.span ℂ {f}) A := by
  refine ⟨fun a a' => (∑ y : {i // i ∉ A} → Fin q,
      conj (f (joinAt q A a y)) * f (joinAt q A a' y)) / (inner ℂ f f), ?_⟩
  intro g hg g' hg' a a'
  rw [Submodule.mem_span_singleton] at hg hg'
  obtain ⟨c, rfl⟩ := hg
  obtain ⟨c', rfl⟩ := hg'
  have hff : (inner ℂ f f : ℂ) ≠ 0 := by
    simpa [inner_self_eq_zero] using hf
  have hL : ∑ y : {i // i ∉ A} → Fin q,
      conj ((c • f) (joinAt q A a y)) * ((c' • f) (joinAt q A a' y))
      = conj c * c' * ∑ y : {i // i ∉ A} → Fin q,
          conj (f (joinAt q A a y)) * f (joinAt q A a' y) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun y _ => ?_
    simp only [PiLp.smul_apply, smul_eq_mul, map_mul]
    ring
  rw [hL, inner_smul_left, inner_smul_right]
  field_simp

/-- Split the configurations off `A` into those on `B` and those off both. -/
