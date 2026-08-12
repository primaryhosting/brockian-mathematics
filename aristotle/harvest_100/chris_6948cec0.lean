import Mathlib

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

namespace Chem

open Matrix

/-- `ec n m = exp (2 π i m / n)`, an `n`-th root of unity raised to the power `m`. -/
noncomputable def ec (n : ℕ) (m : ℤ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I * (m : ℂ) / (n : ℂ))

/-- The Hückel π-energy levels of the cycle `C n` (in units of the resonance integral β,
relative to the Coulomb integral α): `2 cos (2 π k / n)`. -/
noncomputable def huckelEnergy (n : ℕ) (k : ℕ) : ℝ :=
  2 * Real.cos (2 * Real.pi * k / n)

/-- The (unnormalised) discrete Fourier transform matrix, whose columns are the Hückel
molecular orbitals of the cycle. -/
noncomputable def dftMatrix (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun i j => ec n (i.val * j.val)

lemma ec_add (n : ℕ) (a b : ℤ) : ec n (a + b) = ec n a * ec n b := by
  unfold ec
  rw [← Complex.exp_add]
  push_cast
  ring_nf

lemma ec_zero (n : ℕ) : ec n 0 = 1 := by
  simp [ec]

lemma ec_ne_zero (n : ℕ) (m : ℤ) : ec n m ≠ 0 := Complex.exp_ne_zero _

lemma ec_eq_one_iff {n : ℕ} (hn : 0 < n) (m : ℤ) : ec n m = 1 ↔ (n : ℤ) ∣ m := by
  have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hpi : ((Real.pi : ℝ) : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  rw [ec, Complex.exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, ?_⟩
    field_simp at hk
    exact_mod_cast hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by push_cast; field_simp⟩

lemma ec_congr {n : ℕ} (hn : 0 < n) {a b : ℤ} (h : (n : ℤ) ∣ a - b) : ec n a = ec n b := by
  have : ec n (a - b) = 1 := (ec_eq_one_iff hn _).2 h
  calc ec n a = ec n ((a - b) + b) := by ring_nf
    _ = ec n (a - b) * ec n b := ec_add n _ _
    _ = ec n b := by rw [this, one_mul]

lemma ec_mul_nat (n : ℕ) (a : ℤ) (m : ℕ) : ec n (a * m) = (ec n a) ^ m := by
  induction m with
  | zero => simp [ec_zero]
  | succ m ih =>
      have : a * ((m : ℤ) + 1) = a * m + a := by ring
      push_cast
      rw [this, ec_add, ih, pow_succ]

/-- The two conjugate `n`-th roots of unity add up to twice a cosine. -/
lemma ec_add_neg (n : ℕ) (k : ℕ) : ec n k + ec n (-(k : ℤ)) = (huckelEnergy n k : ℂ) := by
  have h : ((2 * Real.pi * k / n : ℝ) : ℂ) * Complex.I
      = 2 * Real.pi * Complex.I * (k : ℂ) / (n : ℂ) := by push_cast; ring
  rw [ec, ec, huckelEnergy]
  push_cast
  rw [← h, show (2 * (Real.pi : ℂ) * Complex.I * (-(k : ℂ)) / (n : ℂ))
      = -(((2 * Real.pi * k / n : ℝ) : ℂ)) * Complex.I by push_cast; ring,
    ← Complex.two_cos]
  push_cast
  ring

/-- Orthogonality of the additive characters of `ZMod n`. -/
lemma sum_ec_eq {n : ℕ} (hn : 0 < n) (i k : Fin n) :
    ∑ j : Fin n, ec n (((i.val : ℤ) - k.val) * j.val) = if i = k then (n : ℂ) else 0 := by
  set d : ℤ := (i.val : ℤ) - k.val with hd
  have hterm : ∀ j : Fin n, ec n (d * j.val) = (ec n d) ^ j.val := fun j => ec_mul_nat n d j.val
  rw [Finset.sum_congr rfl (fun j _ => hterm j),
    Fin.sum_univ_eq_sum_range (fun m => (ec n d) ^ m) n]
  by_cases h : i = k
  · have : d = 0 := by simp [hd, h]
    simp [this, ec_zero, h]
  · have hdne : d ≠ 0 := by
      simp only [hd, sub_ne_zero]
      exact_mod_cast fun hc => h (Fin.ext (by exact_mod_cast hc))
    have hndvd : ¬ ((n : ℤ) ∣ d) := by
      intro hdvd
      exact hdne (Int.eq_zero_of_abs_lt_dvd hdvd (by
        have h1 : i.val < n := i.isLt
        have h2 : k.val < n := k.isLt
        rw [abs_lt]
        constructor <;> [skip; skip] <;> simp only [hd] <;> omega))
    have hz : ec n d ≠ 1 := fun hc => hndvd ((ec_eq_one_iff hn d).1 hc)
    have hzn : (ec n d) ^ n = 1 := by
      rw [← ec_mul_nat]
      exact (ec_eq_one_iff hn _).2 ⟨d, by ring⟩
    rw [geom_sum_eq hz, hzn, if_neg h]
    simp

/-! ### Arithmetic in `Fin n` -/

lemma nat_mod_cong (n x : ℕ) : (n : ℤ) ∣ ((x % n : ℕ) : ℤ) - x := by
  have hx : ((x % n : ℕ) : ℤ) = (x : ℤ) % (n : ℤ) := by push_cast; ring
  rw [hx, Int.emod_def]
  exact ⟨-((x : ℤ) / n), by ring⟩

lemma fin_val_add_cong {n : ℕ} (a b : Fin n) :
    (n : ℤ) ∣ (((a + b).val : ℤ) - ((a.val : ℤ) + b.val)) := by
  rw [Fin.val_add]
  have h := nat_mod_cong n (a.val + b.val)
  push_cast at h ⊢
  exact h

lemma fin_val_sub_cong {n : ℕ} (a b : Fin n) :
    (n : ℤ) ∣ (((a - b).val : ℤ) - ((a.val : ℤ) - b.val)) := by
  rw [Fin.sub_def]
  have h := nat_mod_cong n (n - b.val + a.val)
  have hb : ((n - b.val + a.val : ℕ) : ℤ) = (n : ℤ) - b.val + a.val := by
    have hble : b.val ≤ n := b.isLt.le
    push_cast [Nat.cast_sub hble]; ring
  simp only []
  rw [hb] at h
  obtain ⟨c, hc⟩ := h
  exact ⟨c + 1, by push_cast at hc ⊢; linarith [hc]⟩

lemma fin_val_one {n : ℕ} [NeZero n] (hn : 2 ≤ n) : ((1 : Fin n) : ℕ) = 1 := by
  rw [Fin.val_one', Nat.mod_eq_of_lt hn]

/-- In a cycle of length at least 3 a vertex has two distinct neighbours. -/
lemma cycle_neighbors_ne {n : ℕ} [NeZero n] (hn : 3 ≤ n) (i : Fin n) : i - 1 ≠ i + 1 := by
  intro h
  have h1 : ((1 : Fin n) : ℕ) = 1 := fin_val_one (by omega)
  have hs := fin_val_sub_cong i 1
  have ha := fin_val_add_cong i 1
  have h1' : (((1 : Fin n) : ℕ) : ℤ) = 1 := by exact_mod_cast h1
  rw [h, h1'] at hs
  rw [h1'] at ha
  have h2 : (n : ℤ) ∣ 2 := by
    have hd := dvd_sub hs ha
    have : (((i + 1).val : ℤ) - ((i.val : ℤ) - 1)) - (((i + 1).val : ℤ) - ((i.val : ℤ) + 1))
        = 2 := by ring
    rwa [this] at hd
  have := Int.le_of_dvd (by norm_num) h2
  omega

/-! ### The eigenvector relation -/

/-- Shifting the row index of the DFT matrix multiplies the entry by a root of unity. -/
lemma dft_shift {n : ℕ} (hn : 0 < n) (a i k : Fin n) (t : ℤ)
    (h : (n : ℤ) ∣ ((a.val : ℤ) - ((i.val : ℤ) + t))) :
    dftMatrix n a k = dftMatrix n i k * ec n (t * k.val) := by
  have h1 : ec n ((a.val : ℤ) * k.val) = ec n (((i.val : ℤ) + t) * k.val) := by
    refine ec_congr hn ?_
    have : (a.val : ℤ) * k.val - ((i.val : ℤ) + t) * k.val
        = ((a.val : ℤ) - ((i.val : ℤ) + t)) * k.val := by ring
    rw [this]
    exact Dvd.dvd.mul_right h _
  have h2 : ((i.val : ℤ) + t) * k.val = (i.val : ℤ) * k.val + t * k.val := by ring
  simp only [dftMatrix]
  rw [h1, h2, ec_add]

/-- Each column of the DFT matrix is an eigenvector of the adjacency matrix of the cycle. -/
lemma adjMatrix_mul_dft {m : ℕ} (hm : 1 ≤ m) (i k : Fin (m + 2)) :
    ((SimpleGraph.cycleGraph (m + 2)).adjMatrix ℂ * dftMatrix (m + 2)) i k
      = (huckelEnergy (m + 2) k.val : ℂ) * dftMatrix (m + 2) i k := by
  have hn : 0 < m + 2 := by omega
  have h1 : (((1 : Fin (m + 2)) : ℕ) : ℤ) = 1 := by
    exact_mod_cast fin_val_one (n := m + 2) (by omega)
  have hne : i - 1 ≠ i + 1 := cycle_neighbors_ne (n := m + 2) (by omega) i
  rw [SimpleGraph.adjMatrix_mul_apply, SimpleGraph.cycleGraph_neighborFinset,
    Finset.sum_pair hne]
  have hplus : dftMatrix (m + 2) (i + 1) k = dftMatrix (m + 2) i k * ec (m + 2) (1 * k.val) := by
    refine dft_shift hn _ _ _ 1 ?_
    have := fin_val_add_cong i 1
    rwa [h1] at this
  have hminus : dftMatrix (m + 2) (i - 1) k
      = dftMatrix (m + 2) i k * ec (m + 2) ((-1 : ℤ) * k.val) := by
    refine dft_shift hn _ _ _ (-1) ?_
    have := fin_val_sub_cong i 1
    rw [h1] at this
    have heq : ((i.val : ℤ) - 1) = ((i.val : ℤ) + (-1)) := by ring
    rwa [heq] at this
  rw [hplus, hminus, ← mul_add]
  have : ec (m + 2) ((-1 : ℤ) * k.val) + ec (m + 2) (1 * k.val)
      = (huckelEnergy (m + 2) k.val : ℂ) := by
    rw [show ((-1 : ℤ) * k.val) = -(k.val : ℤ) by ring, show ((1 : ℤ) * k.val) = (k.val : ℤ) by ring,
      add_comm]
    exact ec_add_neg (m + 2) k.val
  rw [this, mul_comm]

/-! ### Invertibility of the DFT matrix -/

/-- The inverse of the (unnormalised) DFT matrix. -/
noncomputable def dftInv (n : ℕ) : Matrix (Fin n) (Fin n) ℂ :=
  fun j k => (n : ℂ)⁻¹ * ec n (-((j.val : ℤ) * k.val))

lemma dft_mul_dftInv {n : ℕ} (hn : 0 < n) : dftMatrix n * dftInv n = 1 := by
  have hnc : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  ext i k
  rw [Matrix.mul_apply]
  have hterm : ∀ j : Fin n, dftMatrix n i j * dftInv n j k
      = (n : ℂ)⁻¹ * ec n (((i.val : ℤ) - k.val) * j.val) := by
    intro j
    simp only [dftMatrix, dftInv]
    rw [show (((i.val : ℤ) - k.val) * j.val)
        = ((i.val : ℤ) * j.val) + (-((j.val : ℤ) * k.val)) by ring, ec_add]
    ring
  rw [Finset.sum_congr rfl (fun j _ => hterm j), ← Finset.mul_sum, sum_ec_eq hn]
  rw [Matrix.one_apply]
  by_cases h : i = k
  · rw [if_pos h, if_pos h]; field_simp
  · rw [if_neg h, if_neg h]; ring

lemma isUnit_dftMatrix {n : ℕ} (hn : 0 < n) : IsUnit (dftMatrix n) :=
  IsUnit.of_mul_eq_one _ (dft_mul_dftInv hn)

/-! ### The Hückel spectrum of the cycle -/

/-- The columns of the DFT matrix diagonalise the adjacency matrix of the cycle. -/
lemma adjMatrix_mul_dft_eq {n : ℕ} (hn : 3 ≤ n) :
    (SimpleGraph.cycleGraph n).adjMatrix ℂ * dftMatrix n
      = dftMatrix n * Matrix.diagonal (fun k : Fin n => ((huckelEnergy n k.val : ℝ) : ℂ)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  ext i k
  rw [adjMatrix_mul_dft (by omega) i k, Matrix.mul_diagonal, mul_comm]

/-- **Hückel theory for annulenes.** For `n ≥ 3`, the eigenvalues (spectrum) of the adjacency
matrix of the cycle graph `C n` are exactly the numbers `2 cos (2 π k / n)`, `k = 0, …, n - 1`.
In Hückel π-electron theory these are the orbital energies `α + 2 β cos (2 π k / n)` measured in
units of `β` relative to `α`.

The hypothesis `3 ≤ n` is necessary: in Mathlib `SimpleGraph.cycleGraph n` is a *simple* graph, so
for `n ≤ 2` it degenerates (`cycleGraph 1` has no edge and `cycleGraph 2` is a single edge rather
than a double edge) and the formula fails. -/
theorem huckel_cycle_spectrum (n : ℕ) (hn : 3 ≤ n) :
    spectrum ℂ ((SimpleGraph.cycleGraph n).adjMatrix ℂ)
      = Set.range (fun k : Fin n => ((2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ)) := by
  have hn0 : 0 < n := by omega
  obtain ⟨u, hu⟩ := isUnit_dftMatrix hn0
  set D : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.diagonal (fun k : Fin n => ((huckelEnergy n k.val : ℝ) : ℂ)) with hD
  have hAu : (SimpleGraph.cycleGraph n).adjMatrix ℂ * (u : Matrix (Fin n) (Fin n) ℂ)
      = (u : Matrix (Fin n) (Fin n) ℂ) * D := by
    rw [hu]; exact adjMatrix_mul_dft_eq hn
  have hconj : (SimpleGraph.cycleGraph n).adjMatrix ℂ
      = (u : Matrix (Fin n) (Fin n) ℂ) * D * (↑u⁻¹ : Matrix (Fin n) (Fin n) ℂ) := by
    rw [← hAu, mul_assoc, Units.mul_inv, mul_one]
  rw [hconj, spectrum.units_conjugate, hD, spectrum_diagonal]
  rfl

/-- The explicit Hückel molecular orbitals: for every `k`, the vector
`j ↦ exp (2 π i k j / n)` is an eigenvector of the adjacency matrix of `C n` with
eigenvalue `2 cos (2 π k / n)`. -/
theorem huckel_cycle_eigenvector (n : ℕ) (hn : 3 ≤ n) (k : Fin n) :
    (SimpleGraph.cycleGraph n).adjMatrix ℂ *ᵥ (fun j : Fin n => ec n ((k.val : ℤ) * j.val))
      = ((2 * Real.cos (2 * Real.pi * k.val / n) : ℝ) : ℂ) •
        (fun j : Fin n => ec n ((k.val : ℤ) * j.val)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  funext i
  have h := adjMatrix_mul_dft (m := m) (by omega) i k
  rw [Matrix.mul_apply] at h
  simp only [dftMatrix] at h
  simp only [Matrix.mulVec, dotProduct, Pi.smul_apply, smul_eq_mul]
  rw [show (∑ j : Fin (m + 2), (SimpleGraph.cycleGraph (m + 2)).adjMatrix ℂ i j *
      ec (m + 2) ((k.val : ℤ) * j.val))
      = ∑ j : Fin (m + 2), (SimpleGraph.cycleGraph (m + 2)).adjMatrix ℂ i j *
        ec (m + 2) ((j.val : ℤ) * k.val) from
    Finset.sum_congr rfl (fun j _ => by rw [mul_comm (j.val : ℤ)]), h]
  rw [huckelEnergy, mul_comm (k.val : ℤ)]

end Chem

