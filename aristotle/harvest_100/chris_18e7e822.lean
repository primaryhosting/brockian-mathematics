import Mathlib

/-!
# Ghz Nonlocal
Category: Quantum Computing
Target: QC.ghz_nonlocal
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

namespace QC

/-- Index type for the computational basis of three qubits;
`false` stands for `|0⟩` and `true` for `|1⟩`. -/
abbrev Idx : Type := Bool × Bool × Bool

/-- The Pauli `X` matrix in the computational basis. -/
def pauliX : Matrix Bool Bool ℂ := fun i j => if i = j then 0 else 1

/-- The Pauli `Y` matrix in the computational basis. -/
def pauliY : Matrix Bool Bool ℂ :=
  fun i j => if i = j then 0 else if i then Complex.I else -Complex.I

/-- Measurement settings: setting `false` measures `X`, setting `true` measures `Y`. -/
def pauli : Bool → Matrix Bool Bool ℂ
  | false => pauliX
  | true => pauliY

/-- Threefold tensor product of single-qubit operators. -/
def tensor3 (M N P : Matrix Bool Bool ℂ) : Matrix Idx Idx ℂ :=
  fun i j => M i.1 j.1 * N i.2.1 j.2.1 * P i.2.2 j.2.2

/-- The three-qubit GHZ state `(|000⟩ + |111⟩)/√2`. -/
noncomputable def ghz : Idx → ℂ :=
  fun i => if i = (false, false, false) ∨ i = (true, true, true)
    then ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ else 0

/-- The quantum expectation value `⟨GHZ| σ_{s₁} ⊗ σ_{s₂} ⊗ σ_{s₃} |GHZ⟩`. -/
noncomputable def ghzExpect (s₁ s₂ s₃ : Bool) : ℂ :=
  ∑ i : Idx, ∑ j : Idx,
    (starRingEnd ℂ) (ghz i) * tensor3 (pauli s₁) (pauli s₂) (pauli s₃) i j * ghz j

private lemma sqrt2_inv_sq : ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ * ((Real.sqrt 2 : ℝ) : ℂ)⁻¹ = 1 / 2 := by
  have h : (Real.sqrt 2 : ℝ) * Real.sqrt 2 = 2 := Real.mul_self_sqrt (by norm_num)
  have hr : ((Real.sqrt 2)⁻¹ * (Real.sqrt 2)⁻¹ : ℝ) = 1 / 2 := by
    rw [← mul_inv, h]; norm_num
  rw [← Complex.ofReal_inv, ← Complex.ofReal_mul, hr]
  norm_num

/-- The GHZ state is a unit vector. -/
lemma ghz_normalized : ∑ i : Idx, (starRingEnd ℂ) (ghz i) * ghz i = 1 := by
  simp only [ghz, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [sqrt2_inv_sq]

/-- The GHZ state is an eigenstate of `X ⊗ X ⊗ X` with eigenvalue `+1`. -/
lemma ghzExpect_XXX : ghzExpect false false false = 1 := by
  simp only [ghzExpect, ghz, tensor3, pauli, pauliX, Fintype.sum_prod_type, Fintype.sum_bool]
  norm_num [sqrt2_inv_sq]

/-- The GHZ state is an eigenstate of `X ⊗ Y ⊗ Y` with eigenvalue `-1`. -/
lemma ghzExpect_XYY : ghzExpect false true true = -1 := by
  simp only [ghzExpect, ghz, tensor3, pauli, pauliX, pauliY, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [sqrt2_inv_sq, Complex.ext_iff]

/-- The GHZ state is an eigenstate of `Y ⊗ X ⊗ Y` with eigenvalue `-1`. -/
lemma ghzExpect_YXY : ghzExpect true false true = -1 := by
  simp only [ghzExpect, ghz, tensor3, pauli, pauliX, pauliY, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [sqrt2_inv_sq, Complex.ext_iff]

/-- The GHZ state is an eigenstate of `Y ⊗ Y ⊗ X` with eigenvalue `-1`. -/
lemma ghzExpect_YYX : ghzExpect true true false = -1 := by
  simp only [ghzExpect, ghz, tensor3, pauli, pauliX, pauliY, Fintype.sum_prod_type,
    Fintype.sum_bool]
  norm_num [sqrt2_inv_sq, Complex.ext_iff]

/--
**Mermin's GHZ paradox: the three-qubit GHZ state admits no local hidden-variable model.**

Suppose each of the three parties deterministically assigns an outcome `±1` to each of its two
measurement settings (`false = X`, `true = Y`), the assignment of one party being independent of
the settings chosen by the others (this is the locality assumption, encoded by the outcome
functions `a`, `b`, `c` depending only on that party's own setting).  Then the products of the
outcomes cannot reproduce the four quantum expectation values of the GHZ state,
`⟨XXX⟩ = 1` and `⟨XYY⟩ = ⟨YXY⟩ = ⟨YYX⟩ = -1`, which are computed above from the state vector
itself.  The contradiction is deterministic: no inequality or statistics are involved.
-/
theorem ghz_nonlocal
    (a b c : Bool → ℤ)
    (ha : ∀ s, a s = 1 ∨ a s = -1)
    (hb : ∀ s, b s = 1 ∨ b s = -1)
    (hc : ∀ s, c s = 1 ∨ c s = -1)
    (hXXX : ((a false * b false * c false : ℤ) : ℂ) = ghzExpect false false false)
    (hXYY : ((a false * b true * c true : ℤ) : ℂ) = ghzExpect false true true)
    (hYXY : ((a true * b false * c true : ℤ) : ℂ) = ghzExpect true false true)
    (hYYX : ((a true * b true * c false : ℤ) : ℂ) = ghzExpect true true false) :
    False := by
  rw [ghzExpect_XXX] at hXXX
  rw [ghzExpect_XYY] at hXYY
  rw [ghzExpect_YXY] at hYXY
  rw [ghzExpect_YYX] at hYYX
  have e1 : a false * b false * c false = 1 := by exact_mod_cast hXXX
  have e2 : a false * b true * c true = -1 := by exact_mod_cast hXYY
  have e3 : a true * b false * c true = -1 := by exact_mod_cast hYXY
  have e4 : a true * b true * c false = -1 := by exact_mod_cast hYYX
  rcases ha false with h1 | h1 <;> rcases ha true with h2 | h2 <;>
    rcases hb false with h3 | h3 <;> rcases hb true with h4 | h4 <;>
    rcases hc false with h5 | h5 <;> rcases hc true with h6 | h6 <;>
    simp only [h1, h2, h3, h4, h5, h6] at e1 e2 e3 e4 <;> omega

end QC

