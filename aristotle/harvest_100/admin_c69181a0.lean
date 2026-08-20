/-
# Huckel C 20
Category: Chemistry
Target: Chem.huckel_C20
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
-- (Lean requires `import` to precede any module docstring `/-! ... -/`, so the header above is
-- written as an ordinary block comment.)

import Mathlib

open scoped BigOperators
open scoped Real
open scoped Nat
open scoped Pointwise

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 20000
set_option synthInstance.maxSize 128

set_option relaxedAutoImplicit false
set_option autoImplicit false

namespace Chem

open Finset Matrix

/-!
## Setup

In Hückel theory for the (hypothetical) monocyclic annulene `C₂₀`, the π-system Hamiltonian is
`α • I + β • A`, where `A` is the adjacency matrix of the cycle graph `C₂₀`.  Thus the Hückel
spectrum is determined by the adjacency spectrum of `C₂₀`, which we compute here.

The index type `Fin 20` of `SimpleGraph.cycleGraph 20` is definitionally `ZMod 20`, and we use the
ring structure of `ZMod 20` throughout, so that the adjacency matrix is a circulant matrix which is
diagonalised by the discrete Fourier transform matrix.
-/

/-- The standard additive character `w m = exp (2 π i m / 20)` on `ZMod 20`. -/
noncomputable def w (m : ZMod 20) : ℂ := ZMod.stdAddChar m

lemma w_add (a b : ZMod 20) : w (a + b) = w a * w b := AddChar.map_add_eq_mul _ _ _

lemma w_eq (l : ZMod 20) : w l = Complex.exp (((2 * Real.pi * l.val / 20 : ℝ) : ℂ) * Complex.I) := by
  rw [w, ZMod.stdAddChar_apply, ZMod.toCircle_apply]
  push_cast
  ring_nf

/-- Orthogonality relation for the character `w`. -/
lemma w_sum (t : ZMod 20) : ∑ k : ZMod 20, w (t * k) = if t = 0 then 20 else 0 := by
  split_ifs with h
  · subst h; simp [w]
  · exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar 20 h)

lemma w_mul_w_neg (l : ZMod 20) : w l * w (-l) = 1 := by
  rw [← w_add, add_neg_cancel]; simp [w]

/-- `w l + w (-l) = 2 cos (2 π l / 20)`: this is the eigenvalue attached to the `l`-th Fourier
mode. -/
lemma w_add_w_neg (l : ZMod 20) :
    w l + w (-l) = ((2 * Real.cos (2 * Real.pi * l.val / 20) : ℝ) : ℂ) := by
  set t : ℂ := ((2 * Real.pi * l.val / 20 : ℝ) : ℂ) with ht
  have h1 : w l = Complex.exp (t * Complex.I) := w_eq l
  have hexp : Complex.exp (t * Complex.I) * Complex.exp (-(t * Complex.I)) = 1 := by
    rw [← Complex.exp_add]; simp
  have h2 : w (-l) = Complex.exp (-t * Complex.I) := by
    have hmul := w_mul_w_neg l
    rw [h1] at hmul
    refine mul_left_cancel₀ (Complex.exp_ne_zero (t * Complex.I)) ?_
    rw [hmul, neg_mul, hexp]
  have hcos : ((2 * Real.cos (2 * Real.pi * l.val / 20) : ℝ) : ℂ) = 2 * Complex.cos t := by
    rw [ht]; push_cast [Complex.ofReal_cos]; ring
  rw [h1, h2, hcos, Complex.two_cos]

/-- The adjacency matrix of the cycle `C₂₀`, written as a circulant matrix over `ZMod 20`. -/
noncomputable def A20 : Matrix (ZMod 20) (ZMod 20) ℂ :=
  Matrix.of fun i j => if i - j = 1 ∨ j - i = 1 then 1 else 0

lemma A20_eq : A20 = (SimpleGraph.cycleGraph 20).adjMatrix ℂ := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  simp only [A20, Matrix.of_apply]
  congr 1
  exact propext (Iff.symm SimpleGraph.cycleGraph_adj)

/-- The discrete Fourier transform matrix, `F j k = exp (2 π i j k / 20)`. -/
noncomputable def dftM : Matrix (ZMod 20) (ZMod 20) ℂ := Matrix.of fun j k => w (j * k)

/-- The inverse discrete Fourier transform matrix. -/
noncomputable def dftInvM : Matrix (ZMod 20) (ZMod 20) ℂ :=
  Matrix.of fun j k => (20 : ℂ)⁻¹ * w (-(j * k))

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2 π k / 20)`. -/
noncomputable def eigM : Matrix (ZMod 20) (ZMod 20) ℂ :=
  Matrix.diagonal fun k : ZMod 20 => ((2 * Real.cos (2 * Real.pi * k.val / 20) : ℝ) : ℂ)

lemma dftM_mul_dftInvM : dftM * dftInvM = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 20, dftM j k * dftInvM k l = (20 : ℂ)⁻¹ * w ((j - l) * k) := by
    intro k
    simp only [dftM, dftInvM, Matrix.of_apply]
    rw [show (j - l) * k = j * k + -(k * l) by ring, w_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.mul_sum, w_sum]
  by_cases hjl : j = l
  · subst hjl; simp
  · rw [if_neg (by simpa [sub_eq_zero] using hjl), Matrix.one_apply_ne hjl]
    ring

lemma dftInvM_mul_dftM : dftInvM * dftM = 1 := by
  ext j l
  rw [Matrix.mul_apply]
  have h : ∀ k : ZMod 20, dftInvM j k * dftM k l = (20 : ℂ)⁻¹ * w ((l - j) * k) := by
    intro k
    simp only [dftM, dftInvM, Matrix.of_apply]
    rw [show (l - j) * k = -(j * k) + k * l by ring, w_add]
    ring
  rw [Finset.sum_congr rfl fun k _ => h k, ← Finset.mul_sum, w_sum]
  by_cases hjl : j = l
  · subst hjl; simp
  · rw [if_neg (by simpa [sub_eq_zero, eq_comm] using hjl), Matrix.one_apply_ne hjl]
    ring

/-- The Fourier matrix diagonalises the adjacency matrix of `C₂₀`. -/
lemma A20_mul_dftM : A20 * dftM = dftM * eigM := by
  ext i l
  have hne : (i - 1 : ZMod 20) ≠ i + 1 := by
    intro h
    have h2 : (2 : ZMod 20) = 0 := by linear_combination -h
    revert h2; decide
  have hstep : ∀ j : ZMod 20, A20 i j * dftM j l
      = if j ∈ ({i - 1, i + 1} : Finset (ZMod 20)) then dftM j l else 0 := by
    intro j
    have e1 : (i - j = 1) ↔ j = i - 1 := by constructor <;> intro h <;> linear_combination -h
    have e2 : (j - i = 1) ↔ j = i + 1 := by constructor <;> intro h <;> linear_combination h
    simp only [A20, Matrix.of_apply, Finset.mem_insert, Finset.mem_singleton, e1, e2]
    split_ifs <;> simp
  rw [Matrix.mul_apply, Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_ite_mem,
    Finset.univ_inter, Finset.sum_pair hne, eigM, Matrix.mul_diagonal]
  simp only [dftM, Matrix.of_apply]
  rw [show (i - 1) * l = i * l + -l by ring, show (i + 1) * l = i * l + l by ring, w_add, w_add,
    ← mul_add, add_comm (w (-l)) (w l), w_add_w_neg]

/-- `C₂₀`'s adjacency matrix is conjugate to the diagonal matrix of Hückel eigenvalues. -/
lemma A20_conj : A20 = dftM * eigM * dftInvM := by
  rw [← A20_mul_dftM, Matrix.mul_assoc, dftM_mul_dftInvM, Matrix.mul_one]

/-- The Fourier matrix as a unit of the matrix algebra. -/
noncomputable def dftUnit : (Matrix (ZMod 20) (ZMod 20) ℂ)ˣ where
  val := dftM
  inv := dftInvM
  val_inv := dftM_mul_dftInvM
  inv_val := dftInvM_mul_dftM

lemma spectrum_A20 :
    spectrum ℂ A20 =
      Set.range fun k : ZMod 20 => ((2 * Real.cos (2 * Real.pi * k.val / 20) : ℝ) : ℂ) := by
  have hu : A20 = (dftUnit : Matrix (ZMod 20) (ZMod 20) ℂ) * eigM
      * ((dftUnit⁻¹ : (Matrix (ZMod 20) (ZMod 20) ℂ)ˣ) : Matrix (ZMod 20) (ZMod 20) ℂ) := A20_conj
  rw [hu, spectrum.units_conjugate, eigM]
  exact spectrum_diagonal _

/-!
## Main result

The adjacency eigenvalues of the cycle graph `C₂₀` are exactly the `20` Hückel values
`2 cos (2 π k / 20)`, `k = 0, …, 19`.
-/

/-- **Hückel theory for C₂₀.**  The spectrum of the adjacency matrix of the cycle graph `C₂₀`
is exactly `{2 cos (2 π k / 20) : k = 0, 1, …, 19}`.  (In Hückel theory the π-orbital energies are
then `α + β · 2 cos (2 π k / 20)`.) -/
theorem huckel_C20 :
    spectrum ℂ ((SimpleGraph.cycleGraph 20).adjMatrix ℂ) =
      {z : ℂ | ∃ k : ℕ, k < 20 ∧ z = 2 * Real.cos (2 * Real.pi * k / 20)} := by
  rw [← A20_eq, spectrum_A20]
  ext z
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨k.val, ZMod.val_lt k, by push_cast; ring⟩
  · rintro ⟨k, hk, rfl⟩
    refine ⟨(k : ZMod 20), ?_⟩
    rw [ZMod.val_natCast_of_lt hk]
    push_cast
    ring

end Chem

