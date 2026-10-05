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
-/


open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Classical
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 40000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace QI

open Matrix Module ComplexConjugate
open scoped ComplexOrder

/-! ## Part I : linear algebra over `ℂ`

The mathematical core of the quantum Singleton bound is a statement about the ranks of the
various flattenings of a four-index complex tensor.  This part develops the required
rank inequalities.
-/

/-- Every column of a complex matrix can be expanded in a family of `X.rank` vectors, with
coefficients that are (fixed) linear functionals applied to the column. -/

theorem exists_col_expansion {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    (X : Matrix m n ℂ) :
    ∃ e cf : Fin X.rank → m → ℂ,
      ∀ i j, X i j = ∑ p, e p i * (∑ β, cf p β * X β j) := by
  classical
  set V : Submodule ℂ (m → ℂ) := Submodule.span ℂ (Set.range X.col) with hV
  have hfr : finrank ℂ V = X.rank := (Matrix.rank_eq_finrank_span_cols X).symm
  let bas : Basis (Fin X.rank) ℂ V := (Module.finBasis ℂ V).reindex (finCongr hfr)
  have hext : ∀ p : Fin X.rank, ∃ g : (m → ℂ) →ₗ[ℂ] ℂ, g.comp V.subtype = bas.coord p :=
    fun p => (bas.coord p).exists_extend
  choose g hg using hext
  refine ⟨fun p => (bas p : m → ℂ), fun p β => g p (Pi.single β 1), ?_⟩
  intro i j
  have hc : X.col j ∈ V := Submodule.subset_span ⟨j, rfl⟩
  have hrepr : ((⟨X.col j, hc⟩ : V) : m → ℂ)
      = ∑ p, (bas.coord p ⟨X.col j, hc⟩) • ((bas p : V) : m → ℂ) := by
    have h1 := bas.sum_repr ⟨X.col j, hc⟩
    calc ((⟨X.col j, hc⟩ : V) : m → ℂ)
        = ((∑ p, (bas.repr ⟨X.col j, hc⟩ p) • bas p : V) : m → ℂ) := by rw [h1]
      _ = _ := by push_cast [Submodule.coe_sum]; rfl
  have hcoord : ∀ p, (bas.coord p ⟨X.col j, hc⟩ : ℂ) = ∑ β, g p (Pi.single β 1) * X β j := by
    intro p
    have h2 : (bas.coord p) ⟨X.col j, hc⟩ = g p (X.col j) := by
      have := congrArg (fun (f : V →ₗ[ℂ] ℂ) => f ⟨X.col j, hc⟩) (hg p)
      simpa using this.symm
    rw [h2]
    have hsplit : (X.col j : m → ℂ) = ∑ β, (X β j) • (Pi.single β (1:ℂ) : m → ℂ) := by
      funext b; simp [Pi.single_apply, Matrix.col]
    rw [hsplit, map_sum]
    simp [mul_comm]
  have h3 := congrFun hrepr i
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul] at h3
  rw [show X i j = X.col j i from rfl, h3]
  exact Finset.sum_congr rfl (fun p _ => by rw [hcoord p]; ring)

/-- A block matrix with `card R` identical diagonal blocks `σ` has rank at least
`card R * σ.rank`. -/
