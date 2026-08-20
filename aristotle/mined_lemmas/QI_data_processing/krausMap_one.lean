import RequestProject.Kron

/-!
# Vectorization, the modular operator and relative entropy

We vectorize matrices, express the relative entropy `Tr ρ log ρ - Tr ρ log σ` as (minus) a
quadratic form of `log (σ ⊗ (ρ⁻¹)ᵀ)` at the vectorization of `√ρ`, and record the
variational ("completing the square") characterization of resolvent quadratic forms.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m N : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype N] [DecidableEq N]

/-! ### Vectorization -/

/-- Vectorization of a matrix: the vector of all its entries, indexed by pairs. -/

lemma krausMap_one (X : Matrix n n ℂ) :
    krausMap (fun _ : Unit => (1 : Matrix n n ℂ)) X = X := by
  simp [krausMap]

/-- All the hypotheses of `data_processing` are simultaneously satisfiable. -/
example {ρ σ : Matrix n n ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    ∃ K : Unit → Matrix n n ℂ, (∑ i, (K i)ᴴ * K i = 1) ∧
      (krausMap K ρ).PosDef ∧ (krausMap K σ).PosDef :=
  ⟨fun _ => 1, by simp, by rw [krausMap_one]; exact hρ, by rw [krausMap_one]; exact hσ⟩

end QI

import RequestProject.Modular

/-!
# Quantum channels in Kraus form

A CPTP map (quantum channel) `Φ : Matrix n n ℂ → Matrix m m ℂ` in operator-sum (Kraus) form,
its adjoint, the Kadison–Schwarz inequality for the unital adjoint, and the trace
inequalities used in the proof of the data-processing inequality.
-/

open Matrix
open scoped Kronecker ComplexOrder BigOperators MatrixOrder

namespace QI

variable {n m ι : Type*} [Fintype n] [DecidableEq n] [Fintype m] [DecidableEq m]
  [Fintype ι] [DecidableEq ι]

/-! ### Traces of products of positive matrices -/

/-- The trace of a product of two positive semidefinite matrices is a nonnegative real. -/
