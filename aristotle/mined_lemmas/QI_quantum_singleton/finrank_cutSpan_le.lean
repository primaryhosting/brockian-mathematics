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

lemma finrank_cutSpan_le (eA : X ≃ α × Ya) (eB : X ≃ β × Yb)
    (hA : Ya ≃ β × γ) (hB : Yb ≃ α × γ)
    (compat : ∀ (a : α) (b : β) (c : γ), eA.symm (a, hA.symm (b, c)) = eB.symm (b, hB.symm (a, c)))
    (C : Submodule ℂ (EuclideanSpace ℂ X)) :
    finrank ℂ (cutSpan eA C) ≤ Fintype.card γ * cutRank eB C := by
  have hmem : ∀ v ∈ cutSpan eA C, ∀ c : γ, sliceAt hA c v ∈ (nullSp eB C)ᗮ := by
    intro v hv c
    have hsub : cutSpan eA C ≤ Submodule.comap (sliceAt hA c) ((nullSp eB C)ᗮ) := by
      rw [cutSpan, Submodule.span_le]
      rintro x ⟨f, hf, a, rfl⟩
      simp only [SetLike.mem_coe, Submodule.mem_comap, Submodule.mem_orthogonal]
      intro u hu
      have h0 : psiv eB f u = 0 := hu f hf
      have hval : (inner ℂ u (sliceAt hA c (cutSlice eA f a)) : ℂ)
          = psiv eB f u (hB.symm (a, c)) := by
        rw [psiv_apply]
        simp [PiLp.inner_apply, RCLike.inner_apply, compat a _ c, mul_comm]
      rw [hval, h0]
      simp
    exact hsub hv
  let L : ↥(cutSpan eA C) →ₗ[ℂ] (γ → ↥((nullSp eB C)ᗮ)) :=
    { toFun := fun v c => ⟨sliceAt hA c (v : EuclideanSpace ℂ Ya), hmem v v.2 c⟩
      map_add' := by intro v w; funext c; apply Subtype.ext; simp
      map_smul' := by intro r v; funext c; apply Subtype.ext; simp }
  have hinj : Function.Injective L := by
    intro v w h
    apply Subtype.ext
    ext y
    have h1 := congrFun h (hA y).2
    have h2 := congrArg (fun z : ↥((nullSp eB C)ᗮ) => (z : EuclideanSpace ℂ β) (hA y).1) h1
    simpa [L] using h2
  calc finrank ℂ ↥(cutSpan eA C) ≤ finrank ℂ (γ → ↥((nullSp eB C)ᗮ)) :=
        LinearMap.finrank_le_finrank_of_injective hinj
    _ = Fintype.card γ * cutRank eB C := by
        simp [Module.finrank_pi_fintype, cutRank]

