import Mathlib

/-!
# Huckel Cycle Spectrum
Category: Chemistry
Target: Chem.huckel_cycle_spectrum
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

namespace Chem

open Matrix Complex

/-! ## The `n`-th root of unity and its basic arithmetic -/

section Roots

variable (n : ℕ) [NeZero n]

/-- The primitive `n`-th root of unity `exp (2 π i / n)`. -/
noncomputable def zeta : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)

lemma isPrimitiveRoot_zeta : IsPrimitiveRoot (zeta n) n :=
  Complex.isPrimitiveRoot_exp n (NeZero.ne n)

lemma zeta_pow_n : (zeta n) ^ n = 1 := (isPrimitiveRoot_zeta n).pow_eq_one

omit [NeZero n] in
lemma zeta_ne_zero : zeta n ≠ 0 := Complex.exp_ne_zero _

variable {n}

/-- `ζ ^ ·` only depends on the exponent modulo `n`. -/
lemma zeta_pow_modEq {a b : ℕ} (h : Nat.ModEq n a b) : (zeta n) ^ a = (zeta n) ^ b := by
  have key : ∀ m : ℕ, (zeta n) ^ (m % n) = (zeta n) ^ m := by
    intro m
    conv_rhs => rw [← Nat.div_add_mod m n]
    rw [pow_add, pow_mul, zeta_pow_n, one_pow, one_mul]
  rw [← key a, ← key b, h]

lemma zeta_pow_inj {j l : Fin n} (h : (zeta n) ^ (j : ℕ) = (zeta n) ^ (l : ℕ)) : j = l :=
  Fin.ext ((isPrimitiveRoot_zeta n).pow_inj j.isLt l.isLt h)

lemma zeta_pow_pow_n (m : ℕ) : ((zeta n) ^ m) ^ n = 1 := by
  rw [← pow_mul, mul_comm, pow_mul, zeta_pow_n, one_pow]

omit [NeZero n] in
/-- Geometric sums of an `n`-th root of unity over `Fin n`. -/
lemma sum_pow_val (u : ℂ) (hu : u ^ n = 1) :
    (∑ k : Fin n, u ^ (k : ℕ)) = if u = 1 then (n : ℂ) else 0 := by
  rw [← Finset.sum_range fun i => u ^ i]
  by_cases h : u = 1
  · simp [h]
  · rw [if_neg h, geom_sum_eq h, hu]; simp

lemma val_one_eq (hn : 2 ≤ n) : ((1 : Fin n) : ℕ) = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt hn]

omit [NeZero n] in
lemma val_add_modEq (a b : Fin n) : Nat.ModEq n ((a + b : Fin n) : ℕ) ((a : ℕ) + b) := by
  rw [Fin.val_add]
  exact Nat.mod_modEq _ _

lemma val_sub_add_modEq (a b : Fin n) : Nat.ModEq n (((a - b : Fin n) : ℕ) + b) (a : ℕ) := by
  have h := val_add_modEq (a - b) b
  rw [sub_add_cancel] at h
  exact h.symm

omit [NeZero n] in
/-- `ζ^k + ζ^(-k) = 2 cos (2πk/n)`. -/
lemma zeta_pow_add_inv (k : Fin n) :
    (zeta n) ^ (k : ℕ) + ((zeta n) ^ (k : ℕ))⁻¹
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ) := by
  have hexp : (zeta n) ^ (k : ℕ)
      = Complex.exp (((2 * Real.pi * (k : ℕ) / n : ℝ) : ℂ) * Complex.I) := by
    rw [zeta, ← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  rw [hexp, ← Complex.exp_neg]
  push_cast [Complex.ofReal_cos]
  rw [Complex.two_cos]
  ring_nf

end Roots

/-! ## The Fourier matrix diagonalizes the cycle adjacency matrix -/

section Diagonalize

variable (n : ℕ) [NeZero n]

/-- The (unnormalized) discrete Fourier matrix `F j k = ζ^(jk)`. -/
noncomputable def fourierMat : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => (zeta n) ^ ((j : ℕ) * (k : ℕ))

/-- Its inverse `n⁻¹ ζ^(-jk)`. -/
noncomputable def fourierMatInv : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.of fun j k => (n : ℂ)⁻¹ * ((zeta n) ^ ((j : ℕ) * (k : ℕ)))⁻¹

/-- The diagonal matrix of Hückel eigenvalues `2 cos (2πk/n)`. -/
noncomputable def huckelDiag : Matrix (Fin n) (Fin n) ℂ :=
  Matrix.diagonal fun k => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)

lemma fourierMat_mul_inv : fourierMat n * fourierMatInv n = 1 := by
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne n)
  have hz : zeta n ≠ 0 := zeta_ne_zero n
  ext j l
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hpt : ∀ k : Fin n, fourierMat n j k * fourierMatInv n k l
      = (n : ℂ)⁻¹ * ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) ^ (k : ℕ) := by
    intro k
    have hpow : ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) ^ (k : ℕ)
        = (zeta n) ^ ((j : ℕ) * (k : ℕ)) * ((zeta n) ^ ((k : ℕ) * (l : ℕ)))⁻¹ := by
      rw [mul_pow, ← pow_mul, inv_pow, ← pow_mul, mul_comm (l : ℕ) (k : ℕ)]
    simp only [fourierMat, fourierMatInv, Matrix.of_apply]
    rw [hpow]
    ring
  have hun : ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) ^ n = 1 := by
    rw [mul_pow, inv_pow, zeta_pow_pow_n, zeta_pow_pow_n, inv_one, mul_one]
  rw [Finset.sum_congr rfl fun k _ => hpt k, ← Finset.mul_sum, sum_pow_val _ hun]
  have huiff : ((zeta n) ^ (j : ℕ) * ((zeta n) ^ (l : ℕ))⁻¹) = 1 ↔ j = l := by
    rw [mul_inv_eq_one₀ (pow_ne_zero _ hz)]
    exact ⟨zeta_pow_inj, fun h => by rw [h]⟩
  by_cases h : j = l
  · rw [if_pos (huiff.mpr h), if_pos h, inv_mul_cancel₀ hn0]
  · rw [if_neg (fun hc => h (huiff.mp hc)), if_neg h, mul_zero]

lemma fourierMat_shift_add (hn : 2 ≤ n) (i k : Fin n) :
    fourierMat n (i + 1) k = fourierMat n i k * (zeta n) ^ (k : ℕ) := by
  simp only [fourierMat, Matrix.of_apply]
  rw [← pow_add]
  refine zeta_pow_modEq ?_
  have h : Nat.ModEq n ((i + 1 : Fin n) : ℕ) ((i : ℕ) + 1) := by
    have := val_add_modEq i (1 : Fin n)
    rwa [val_one_eq hn] at this
  calc ((i + 1 : Fin n) : ℕ) * (k : ℕ) ≡ ((i : ℕ) + 1) * (k : ℕ) [MOD n] := h.mul_right _
    _ = (i : ℕ) * (k : ℕ) + (k : ℕ) := by ring

lemma fourierMat_shift_sub (hn : 2 ≤ n) (i k : Fin n) :
    fourierMat n (i - 1) k = fourierMat n i k * ((zeta n) ^ (k : ℕ))⁻¹ := by
  have hz : ((zeta n) ^ (k : ℕ)) ≠ 0 := pow_ne_zero _ (zeta_ne_zero n)
  rw [eq_mul_inv_iff_mul_eq₀ hz]
  simp only [fourierMat, Matrix.of_apply]
  rw [← pow_add]
  refine zeta_pow_modEq ?_
  have h : Nat.ModEq n (((i - 1 : Fin n) : ℕ) + 1) (i : ℕ) := by
    have := val_sub_add_modEq i (1 : Fin n)
    rwa [val_one_eq hn] at this
  calc ((i - 1 : Fin n) : ℕ) * (k : ℕ) + (k : ℕ)
      = (((i - 1 : Fin n) : ℕ) + 1) * (k : ℕ) := by ring
    _ ≡ (i : ℕ) * (k : ℕ) [MOD n] := h.mul_right _

lemma cycle_adj_iff (hn : 3 ≤ n) (i j : Fin n) :
    (SimpleGraph.cycleGraph n).Adj i j ↔ (j = i + 1 ∨ j = i - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 3 := ⟨n - 3, by omega⟩
  rw [SimpleGraph.cycleGraph_adj]
  constructor
  · rintro (h | h)
    · right
      rw [eq_sub_iff_add_eq, ← h]
      abel
    · left
      rw [← h]
      abel
  · rintro (rfl | rfl)
    · right; abel
    · left; abel

lemma succ_ne_pred (hn : 3 ≤ n) (i : Fin n) : (i + 1 : Fin n) ≠ i - 1 := by
  intro h
  have h2 : ((1 : Fin n) + 1 : Fin n) = 0 := by
    have : (i + 1 : Fin n) - (i - 1) = 0 := by rw [h, sub_self]
    calc ((1 : Fin n) + 1 : Fin n) = (i + 1 : Fin n) - (i - 1) := by abel
      _ = 0 := this
  have hv : (((1 : Fin n) + 1 : Fin n) : ℕ) = 2 := by
    rw [Fin.val_add, val_one_eq (by omega)]
    exact Nat.mod_eq_of_lt (by omega)
  rw [h2] at hv
  simp at hv

lemma adj_mul_fourier (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ) * fourierMat n = fourierMat n * huckelDiag n := by
  ext i k
  rw [Matrix.mul_apply, huckelDiag, Matrix.mul_diagonal]
  have hpt : ∀ j : Fin n, ((SimpleGraph.cycleGraph n).adjMatrix ℂ) i j * fourierMat n j k
      = (if j = i + 1 then fourierMat n j k else 0)
        + (if j = i - 1 then fourierMat n j k else 0) := by
    intro j
    rw [SimpleGraph.adjMatrix_apply]
    have hiff := cycle_adj_iff n hn i j
    have hne := succ_ne_pred n hn i
    by_cases h1 : j = i + 1
    · rw [if_pos (hiff.mpr (Or.inl h1)), if_pos h1, if_neg (by rw [h1]; exact hne), one_mul,
        add_zero]
    · by_cases h2 : j = i - 1
      · rw [if_pos (hiff.mpr (Or.inr h2)), if_pos h2, if_neg h1, one_mul, zero_add]
      · rw [if_neg (fun hc => (hiff.mp hc).elim h1 h2), if_neg h1, if_neg h2, zero_mul, add_zero]
  rw [Finset.sum_congr rfl fun j _ => hpt j, Finset.sum_add_distrib]
  rw [Finset.sum_ite_eq' Finset.univ (i + 1) (fun j => fourierMat n j k),
    Finset.sum_ite_eq' Finset.univ (i - 1) (fun j => fourierMat n j k)]
  rw [if_pos (Finset.mem_univ _), if_pos (Finset.mem_univ _)]
  rw [fourierMat_shift_add n (by omega) i k, fourierMat_shift_sub n (by omega) i k,
    ← mul_add, zeta_pow_add_inv k]

/-- The Fourier matrix, as a unit of the matrix algebra. -/
noncomputable def fourierUnit : (Matrix (Fin n) (Fin n) ℂ)ˣ where
  val := fourierMat n
  inv := fourierMatInv n
  val_inv := fourierMat_mul_inv n
  inv_val := mul_eq_one_comm.mp (fourierMat_mul_inv n)

/-- The adjacency matrix of `C n` is conjugate (by the Fourier matrix) to the diagonal
matrix of Hückel eigenvalues. -/
lemma adjMatrix_eq_conj (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ)
      = (fourierUnit n : Matrix (Fin n) (Fin n) ℂ) * huckelDiag n
        * ((fourierUnit n)⁻¹ : (Matrix (Fin n) (Fin n) ℂ)ˣ) := by
  have hFG : fourierMat n * fourierMatInv n = 1 := fourierMat_mul_inv n
  calc ((SimpleGraph.cycleGraph n).adjMatrix ℂ)
      = ((SimpleGraph.cycleGraph n).adjMatrix ℂ) * (fourierMat n * fourierMatInv n) := by
        rw [hFG, mul_one]
    _ = (((SimpleGraph.cycleGraph n).adjMatrix ℂ) * fourierMat n) * fourierMatInv n :=
        (mul_assoc _ _ _).symm
    _ = (fourierMat n * huckelDiag n) * fourierMatInv n := by rw [adj_mul_fourier n hn]

end Diagonalize

/-- **Hückel spectrum of the cycle graph.**  For `n ≥ 3`, the eigenvalues (spectrum) of the
adjacency matrix of the cycle graph `C n` are exactly the numbers `2 cos (2 π k / n)`
for `k = 0, …, n - 1`.  These are the Hückel π-electron energy levels (in units of the
resonance integral `β`, measured relative to the Coulomb integral `α`). -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ ((SimpleGraph.cycleGraph n).adjMatrix ℂ) =
      Set.range fun k : Fin n => ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [adjMatrix_eq_conj n hn, spectrum.units_conjugate, huckelDiag, spectrum_diagonal]

/-- The characteristic polynomial of the adjacency matrix of `C n` factors completely, with the
`n` Hückel energies `2 cos (2 π k / n)`, `k = 0, …, n - 1`, as its roots counted with
multiplicity. -/
theorem huckel_cycle_charpoly (n : ℕ) (hn : 3 ≤ n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ).charpoly
      = ∏ k : Fin n, (Polynomial.X
          - Polynomial.C ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ)) := by
  haveI : NeZero n := ⟨by omega⟩
  rw [adjMatrix_eq_conj n hn, Matrix.charpoly_units_conj, huckelDiag, Matrix.charpoly_diagonal]

/-- The explicit Hückel molecular orbitals: the vector `j ↦ ζ^(jk)` (with `ζ = exp (2πi/n)`)
is an eigenvector of the adjacency matrix of `C n` with eigenvalue `2 cos (2 π k / n)`. -/
theorem huckel_cycle_eigenvector (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    ((SimpleGraph.cycleGraph n).adjMatrix ℂ) *ᵥ (fun j : Fin n => (zeta n) ^ ((j : ℕ) * (k : ℕ)))
      = ((2 * Real.cos (2 * Real.pi * (k : ℕ) / n) : ℝ) : ℂ) •
        (fun j : Fin n => (zeta n) ^ ((j : ℕ) * (k : ℕ))) := by
  haveI : NeZero n := ⟨by omega⟩
  funext i
  have hi : (((SimpleGraph.cycleGraph n).adjMatrix ℂ) * fourierMat n) i k
      = (fourierMat n * huckelDiag n) i k := by rw [adj_mul_fourier n hn]
  rw [Matrix.mul_apply, huckelDiag, Matrix.mul_diagonal] at hi
  simpa [Matrix.mulVec, dotProduct, fourierMat, mul_comm] using hi

end Chem

