/-
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

import Mathlib

/-!
# Monogamy Ckw
Category: Frontier Qi
Target: QI.monogamy_ckw
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-!
## Overview

A three-qubit pure state `ψ` is described by its amplitudes `ψ i j k`.  Tracing out one
qubit gives the two-qubit density operators `rhoAB ψ` and `rhoAC ψ`, whose entanglement is
measured by Wootters' concurrence `concurrence`, defined here as the convex roof of the
pure-state concurrence `2|det|`.  The entanglement of qubit `A` with the pair `BC` is
measured by the tangle `tangleA ψ = 2(1 - Tr ρ_A²)`.  The theorem `QI.monogamy_ckw` states
the Coffman–Kundu–Wootters inequality

`concurrence (rhoAB ψ) ^ 2 + concurrence (rhoAC ψ) ^ 2 ≤ tangleA ψ`.

The proof has two ingredients.

* An upper bound for the convex roof (`concSq_le`).  Writing `ρ_AB = |φ₀⟩⟨φ₀| + |φ₁⟩⟨φ₁|`
  for the two slices `φ_k = ψ · · k`, every `2 × 2` unitary mixing of the two slices is again
  a decomposition of `ρ_AB`.  Factoring the binary quadratic form
  `(x,y) ↦ det (x φ₀ + y φ₁) = a x² + b x y + c y²` into linear forms `(p x + q y)(r x + s y)`
  (`exists_factor`) and rotating the first member of the decomposition onto the root `(q, -p)`
  of that form leaves a single nonzero determinant, equal to `r p̄ + s q̄`.  Hence
  `concurrence (ρ_AB) ≤ 2‖r p̄ + s q̄‖`, and `key_ineq` bounds this by
  `4 (‖a‖² + ‖c‖² + ‖b‖²/2) = 4 · Sof φ₀ φ₁`.

* A polynomial identity (`detA_identity`): `det ρ_A` is exactly the sum of the two Frobenius
  invariants `Sof` belonging to the `B`-slicing and the `C`-slicing of `ψ`.

Combining them with `tangleA ψ = 4 det ρ_A` for normalized `ψ` gives the inequality.
-/

open scoped BigOperators
open ComplexConjugate

namespace QI

/-- A (possibly sub-normalized) two-qubit pure state, given by its amplitudes
`z i j = ⟨ij|z⟩`. -/
abbrev State2 := Fin 2 → Fin 2 → ℂ

/-- A three-qubit pure state, given by its amplitudes `ψ i j k = ⟨ijk|ψ⟩`. -/
abbrev State3 := Fin 2 → Fin 2 → Fin 2 → ℂ

/-- The determinant of the `2 × 2` amplitude array of a two-qubit pure state. -/
noncomputable def det2 (z : State2) : ℂ := z 0 0 * z 1 1 - z 0 1 * z 1 0

/-- The polarization of `det2`: `det2 (x • z + y • w) = x² det2 z + x y (mix z w) + y² det2 w`. -/
noncomputable def mix (z w : State2) : ℂ :=
  z 0 0 * w 1 1 + w 0 0 * z 1 1 - z 0 1 * w 1 0 - w 0 1 * z 1 0

/-- Concurrence of a two-qubit pure state `z`, in the sub-normalized convention: for a
normalized state this is Wootters' concurrence `2|z₀₀z₁₁ - z₀₁z₁₀|`, and for
`z = √p ψ` it equals `p · C(ψ)`. -/
noncomputable def pureConc (z : State2) : ℝ := 2 * ‖det2 z‖

/-- The two-qubit density operator `∑ₘ |zₘ⟩⟨zₘ|` of a family of sub-normalized pure states,
written in components: `rhoOf z i j i' j' = ⟨ij|ρ|i'j'⟩`. -/
noncomputable def rhoOf {n : ℕ} (z : Fin n → State2) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun i j i' j' => ∑ m, z m i j * conj (z m i' j')

/-- Wootters' concurrence of a two-qubit density operator, defined as the convex roof
of the pure-state concurrence: the infimum of `∑ₘ pₘ C(ψₘ)` over all decompositions
`ρ = ∑ₘ pₘ |ψₘ⟩⟨ψₘ|` (encoded with sub-normalized vectors `zₘ = √pₘ ψₘ`). -/
noncomputable def concurrence (R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ) : ℝ :=
  sInf {s : ℝ | ∃ (n : ℕ) (z : Fin n → State2), rhoOf z = R ∧ s = ∑ m, pureConc (z m)}

/-- The reduced density operator of qubits `A, B`, obtained by tracing out `C`. -/
noncomputable def rhoAB (ψ : State3) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun i j i' j' => ∑ k, ψ i j k * conj (ψ i' j' k)

/-- The reduced density operator of qubits `A, C`, obtained by tracing out `B`. -/
noncomputable def rhoAC (ψ : State3) : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ :=
  fun i k i' k' => ∑ j, ψ i j k * conj (ψ i' j k')

/-- The reduced density matrix of qubit `A`, obtained by tracing out `B` and `C`. -/
noncomputable def rhoA (ψ : State3) : Matrix (Fin 2) (Fin 2) ℂ :=
  Matrix.of fun i i' => ∑ j, ∑ k, ψ i j k * conj (ψ i' j k)

/-- The tangle of the bipartite cut `A|BC` of a three-qubit pure state, i.e. the squared
concurrence `C²_{A|BC} = 2(1 - Tr ρ_A²)` of that cut. -/
noncomputable def tangleA (ψ : State3) : ℝ := 2 * (1 - ((rhoA ψ * rhoA ψ).trace).re)

/-- The invariant `‖det z‖² + ‖det w‖² + ‖mix z w‖²/2`, i.e. the squared Frobenius norm of the
symmetric matrix attached to the quadratic form `(x,y) ↦ det2 (x z + y w)`. -/
noncomputable def Sof (z w : State2) : ℝ := ‖det2 z‖ ^ 2 + ‖det2 w‖ ^ 2 + ‖mix z w‖ ^ 2 / 2

/-! ### Basic facts about the convex roof -/

lemma pureConc_nonneg (z : State2) : 0 ≤ pureConc z := by
  unfold pureConc; positivity

lemma concurrence_nonneg (R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ) : 0 ≤ concurrence R := by
  apply Real.sInf_nonneg
  rintro x ⟨n, z, -, rfl⟩
  exact Finset.sum_nonneg fun m _ => pureConc_nonneg (z m)

lemma concurrence_le {n : ℕ} (z : Fin n → State2) (R : Fin 2 → Fin 2 → Fin 2 → Fin 2 → ℂ)
    (h : rhoOf z = R) : concurrence R ≤ ∑ m, pureConc (z m) := by
  apply csInf_le
  · refine ⟨0, ?_⟩
    rintro x ⟨m, y, -, rfl⟩
    exact Finset.sum_nonneg fun m _ => pureConc_nonneg (y m)
  · exact ⟨n, z, h, rfl⟩

/-! ### The algebraic ingredients -/

lemma det2_lin (x y : ℂ) (z w : State2) :
    det2 (fun i j => x * z i j + y * w i j)
      = x ^ 2 * det2 z + x * y * mix z w + y ^ 2 * det2 w := by
  simp only [det2, mix]; ring

/-- Every binary quadratic form over `ℂ` factors into two linear forms, and the first
factor can be chosen nonzero. -/
lemma exists_factor (a b c : ℂ) :
    ∃ p q r s : ℂ, (p ≠ 0 ∨ q ≠ 0) ∧ p * r = a ∧ p * s + q * r = b ∧ q * s = c := by
  by_cases ha : a = 0
  · exact ⟨0, 1, b, c, Or.inr one_ne_zero, by simp [ha], by ring, by ring⟩
  · obtain ⟨d, hd⟩ : ∃ d : ℂ, d ^ 2 = b ^ 2 - 4 * a * c :=
      IsSepClosed.exists_pow_nat_eq _ 2
    refine ⟨a, (b + d) / 2, 1, (b - d) / (2 * a), Or.inl ha, by ring, by field_simp; ring, ?_⟩
    field_simp
    linear_combination -hd

lemma key_ineq (p q r s : ℂ) :
    ‖r * conj p + s * conj q‖ ^ 2 ≤ ‖p * r‖ ^ 2 + ‖q * s‖ ^ 2 + ‖p * s + q * r‖ ^ 2 / 2 := by
  have h1 : ‖r * conj p + s * conj q‖ ^ 2
      = ‖r * conj p‖ ^ 2 + ‖s * conj q‖ ^ 2 + 2 * ((r * conj p) * conj (s * conj q)).re := by
    simp [Complex.sq_norm, Complex.normSq_add, mul_pow]
  have h2 : ‖p * s + q * r‖ ^ 2 = ‖p * s‖ ^ 2 + ‖q * r‖ ^ 2 + 2 * ((p * s) * conj (q * r)).re := by
    simp [Complex.sq_norm, Complex.normSq_add, mul_pow]
  have h3 : ((r * conj p) * conj (s * conj q)).re = ((p * s) * conj (q * r)).re := by
    have h : (p * s) * conj (q * r) = conj ((r * conj p) * conj (s * conj q)) := by
      simp [map_mul]; ring
    rw [h, Complex.conj_re]
  have h4 : ((p * s) * conj (q * r)).re ≤ ‖p * s‖ * ‖q * r‖ := by
    calc ((p * s) * conj (q * r)).re ≤ ‖(p * s) * conj (q * r)‖ := Complex.re_le_norm _
      _ = ‖p * s‖ * ‖q * r‖ := by simp
  have h5 : ‖r * conj p‖ = ‖p * r‖ := by simp; ring
  have h6 : ‖s * conj q‖ = ‖q * s‖ := by simp; ring
  rw [h1, h2, h3, h5, h6]
  nlinarith [sq_nonneg (‖p * s‖ - ‖q * r‖), h4]

/-- The core bound: the convex-roof concurrence of a rank-≤2 two-qubit state is controlled by
the Frobenius invariant of its associated quadratic form. -/
lemma concSq_le (z w : State2) : concurrence (rhoOf ![z, w]) ^ 2 ≤ 4 * Sof z w := by
  obtain ⟨p, q, r, s, hpq, hpr, hb, hqs⟩ := exists_factor (det2 z) (mix z w) (det2 w)
  have hN : (0:ℝ) < ‖p‖ ^ 2 + ‖q‖ ^ 2 := by
    rcases hpq with h | h
    · have : 0 < ‖p‖ := norm_pos_iff.mpr h
      positivity
    · have : 0 < ‖q‖ := norm_pos_iff.mpr h
      positivity
  set t : ℝ := Real.sqrt (‖p‖ ^ 2 + ‖q‖ ^ 2)⁻¹ with htdef
  have hts : t ^ 2 = (‖p‖ ^ 2 + ‖q‖ ^ 2)⁻¹ := Real.sq_sqrt (by positivity)
  have ht2 : (t : ℂ) ^ 2 * (p * conj p + q * conj q) = 1 := by
    have h1 : p * conj p + q * conj q = ((‖p‖ ^ 2 + ‖q‖ ^ 2 : ℝ) : ℂ) := by
      simp [Complex.mul_conj, Complex.sq_norm]
    rw [h1, ← Complex.ofReal_pow, hts, ← Complex.ofReal_mul, inv_mul_cancel₀ (ne_of_gt hN),
      Complex.ofReal_one]
  have hd1 : det2 (fun i j => ((t:ℂ) * q) * z i j + (-((t:ℂ) * p)) * w i j) = 0 := by
    rw [det2_lin, ← hpr, ← hb, ← hqs]; ring
  have hd2 : det2 (fun i j => ((t:ℂ) * conj p) * z i j + ((t:ℂ) * conj q) * w i j)
      = r * conj p + s * conj q := by
    rw [det2_lin, ← hpr, ← hb, ← hqs]
    linear_combination (r * conj p + s * conj q) * ht2
  have hdecomp : rhoOf ![fun i j => ((t:ℂ) * q) * z i j + (-((t:ℂ) * p)) * w i j,
      fun i j => ((t:ℂ) * conj p) * z i j + ((t:ℂ) * conj q) * w i j] = rhoOf ![z, w] := by
    funext i j i' j'
    simp only [rhoOf, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      map_add, map_mul, map_neg, Complex.conj_conj, Complex.conj_ofReal]
    linear_combination (z i j * conj (z i' j') + w i j * conj (w i' j')) * ht2
  have hle : concurrence (rhoOf ![z, w]) ≤ 2 * ‖r * conj p + s * conj q‖ := by
    have h := concurrence_le _ _ hdecomp
    rw [Fin.sum_univ_two] at h
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, pureConc, hd1, hd2] at h
    simpa using h
  have h0 := concurrence_nonneg (rhoOf ![z, w])
  have hk := key_ineq p q r s
  have hS : Sof z w = ‖p * r‖ ^ 2 + ‖q * s‖ ^ 2 + ‖p * s + q * r‖ ^ 2 / 2 := by
    rw [Sof, hpr, hb, hqs]
  rw [hS]
  nlinarith [norm_nonneg (r * conj p + s * conj q)]

/-- The key polynomial identity: `det ρ_A` splits as the sum of the two Frobenius invariants
belonging to the `A|B` and `A|C` slicings. -/
lemma Sof_coe (z w : State2) : ((Sof z w : ℝ) : ℂ)
    = det2 z * conj (det2 z) + det2 w * conj (det2 w) + mix z w * conj (mix z w) / 2 := by
  simp [Sof, Complex.mul_conj, Complex.sq_norm]

lemma detA_identity (ψ : State3) :
    (rhoA ψ).det
      = ((Sof (fun i j => ψ i j 0) (fun i j => ψ i j 1)
          + Sof (fun i k => ψ i 0 k) (fun i k => ψ i 1 k) : ℝ) : ℂ) := by
  push_cast
  rw [Sof_coe, Sof_coe]
  simp only [rhoA, Matrix.det_fin_two, Matrix.of_apply, Fin.sum_univ_two, det2, mix, map_sub,
    map_add, map_mul]
  ring

lemma trace_rhoA (ψ : State3) (hψ : ∑ i, ∑ j, ∑ k, ‖ψ i j k‖ ^ 2 = 1) :
    (rhoA ψ).trace = 1 := by
  have h : ((∑ i, ∑ j, ∑ k, ‖ψ i j k‖ ^ 2 : ℝ) : ℂ) = 1 := by rw [hψ]; norm_num
  rw [← h]
  simp [rhoA, Matrix.trace, Matrix.diag, Fin.sum_univ_two, Complex.mul_conj, Complex.sq_norm]

lemma tangleA_eq (ψ : State3) (hψ : ∑ i, ∑ j, ∑ k, ‖ψ i j k‖ ^ 2 = 1) :
    tangleA ψ = 4 * (rhoA ψ).det.re := by
  have htr := trace_rhoA ψ hψ
  have h : (rhoA ψ * rhoA ψ).trace = (rhoA ψ).trace ^ 2 - 2 * (rhoA ψ).det := by
    simp [Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two]
    ring
  rw [tangleA, h, htr]
  simp [Complex.sub_re]
  ring

lemma rhoAB_eq (ψ : State3) :
    rhoAB ψ = rhoOf ![fun i j => ψ i j 0, fun i j => ψ i j 1] := by
  funext i j i' j'
  simp [rhoAB, rhoOf, Fin.sum_univ_two]

lemma rhoAC_eq (ψ : State3) :
    rhoAC ψ = rhoOf ![fun i k => ψ i 0 k, fun i k => ψ i 1 k] := by
  funext i k i' k'
  simp [rhoAC, rhoOf, Fin.sum_univ_two]

/-- **Monogamy of entanglement (Coffman–Kundu–Wootters inequality).**
For any three-qubit pure state `ψ`, the squared concurrences of the two-qubit reduced states
`ρ_AB` and `ρ_AC` (Wootters' concurrence, defined as a convex roof) sum to at most the tangle
`C²_{A|BC} = 2(1 - Tr ρ_A²)` of the cut separating qubit `A` from the pair `BC`. -/
theorem monogamy_ckw (ψ : State3) (hψ : ∑ i, ∑ j, ∑ k, ‖ψ i j k‖ ^ 2 = 1) :
    concurrence (rhoAB ψ) ^ 2 + concurrence (rhoAC ψ) ^ 2 ≤ tangleA ψ := by
  have h1 := concSq_le (fun i j => ψ i j 0) (fun i j => ψ i j 1)
  have h2 := concSq_le (fun i k => ψ i 0 k) (fun i k => ψ i 1 k)
  rw [rhoAB_eq, rhoAC_eq]
  have hdet : (rhoA ψ).det.re
      = Sof (fun i j => ψ i j 0) (fun i j => ψ i j 1)
        + Sof (fun i k => ψ i 0 k) (fun i k => ψ i 1 k) := by
    rw [detA_identity]; simp
  rw [tangleA_eq ψ hψ, hdet]
  linarith

/-! ### Sanity checks: the convex roof is non-degenerate

The convex roof is exactly attained on pure states, so `concurrence` is not identically zero.
-/

lemma rhoOf_single (z : State2) (i j i' j' : Fin 2) :
    rhoOf ![z] i j i' j' = z i j * conj (z i' j') := by
  simp [rhoOf]

lemma rhoOf_apply_single {n : ℕ} (z : State2) (y : Fin n → State2) (h : rhoOf y = rhoOf ![z]) :
    ∀ a b c d, ∑ m, y m a b * conj (y m c d) = z a b * conj (z c d) := by
  intro a b c d
  have h' := congrFun (congrFun (congrFun (congrFun h a) b) c) d
  rw [rhoOf_single] at h'
  simpa [rhoOf] using h'

/-- In any decomposition of a rank-one two-qubit state every member is proportional to the
generating vector. -/
lemma rhoOf_parallel {n : ℕ} (z : State2) (y : Fin n → State2) (h : rhoOf y = rhoOf ![z])
    (m : Fin n) (i j i' j' : Fin 2) : y m i j * z i' j' = y m i' j' * z i j := by
  have hR := rhoOf_apply_single z y h
  have hsum : ∑ m, Complex.normSq (y m i j * z i' j' - y m i' j' * z i j) = 0 := by
    have hC : ((∑ m, Complex.normSq (y m i j * z i' j' - y m i' j' * z i j) : ℝ) : ℂ) = 0 := by
      push_cast
      have e : ∀ m : Fin n, ((Complex.normSq (y m i j * z i' j' - y m i' j' * z i j) : ℝ) : ℂ)
          = (y m i j * z i' j' - y m i' j' * z i j)
            * conj (y m i j * z i' j' - y m i' j' * z i j) := fun m => by rw [Complex.mul_conj]
      rw [Finset.sum_congr rfl (fun m _ => e m)]
      have expand : ∀ m : Fin n, (y m i j * z i' j' - y m i' j' * z i j)
          * conj (y m i j * z i' j' - y m i' j' * z i j)
          = (z i' j' * conj (z i' j')) * (y m i j * conj (y m i j))
            - (z i' j' * conj (z i j)) * (y m i j * conj (y m i' j'))
            - (z i j * conj (z i' j')) * (y m i' j' * conj (y m i j))
            + (z i j * conj (z i j)) * (y m i' j' * conj (y m i' j')) := by
        intro m; simp [map_sub, map_mul]; ring
      rw [Finset.sum_congr rfl (fun m _ => expand m)]
      simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      rw [hR, hR, hR, hR]
      ring
    exact_mod_cast hC
  have hm := (Finset.sum_eq_zero_iff_of_nonneg (fun m _ => Complex.normSq_nonneg _)).mp hsum m
      (Finset.mem_univ m)
  have h0 : y m i j * z i' j' - y m i' j' * z i j = 0 := by
    simpa [Complex.normSq_eq_zero] using hm
  exact sub_eq_zero.mp h0

/-- On a pure two-qubit state the convex roof is attained by the trivial decomposition:
`C(|z⟩⟨z|) = 2|det z|`. -/
lemma concurrence_pure (z : State2) : concurrence (rhoOf ![z]) = pureConc z := by
  refine le_antisymm (by simpa using concurrence_le ![z] _ rfl) ?_
  rw [concurrence]
  refine le_csInf ⟨pureConc z, 1, ![z], rfl, by simp⟩ ?_
  rintro s ⟨n, y, hy, rfl⟩
  by_cases hz : ∀ i j, z i j = 0
  · have h0 : pureConc z = 0 := by simp [pureConc, det2, hz]
    rw [h0]
    exact Finset.sum_nonneg fun m _ => pureConc_nonneg _
  · push_neg at hz
    obtain ⟨i0, j0, hz0⟩ := hz
    set c : Fin n → ℂ := fun m => y m i0 j0 / z i0 j0 with hc
    have hym : ∀ m i j, y m i j = c m * z i j := by
      intro m i j
      have hp := rhoOf_parallel z y hy m i j i0 j0
      rw [hc, div_mul_eq_mul_div, eq_div_iff hz0]
      linear_combination hp
    have hdet : ∀ m, det2 (y m) = c m ^ 2 * det2 z := by
      intro m; simp only [det2, hym]; ring
    have hne : Complex.normSq (z i0 j0) ≠ 0 := by simpa [Complex.normSq_eq_zero] using hz0
    have h1 := rhoOf_apply_single z y hy i0 j0 i0 j0
    have h1' : ∑ m, Complex.normSq (y m i0 j0) = Complex.normSq (z i0 j0) := by
      have hcast : ((∑ m, Complex.normSq (y m i0 j0) : ℝ) : ℂ)
          = ((Complex.normSq (z i0 j0) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        simp only [← Complex.mul_conj]
        exact h1
      exact_mod_cast hcast
    have h2 : ∀ m : Fin n, Complex.normSq (y m i0 j0)
        = Complex.normSq (c m) * Complex.normSq (z i0 j0) := by
      intro m; rw [hym m i0 j0, Complex.normSq_mul]
    rw [Finset.sum_congr rfl (fun m _ => h2 m), ← Finset.sum_mul] at h1'
    have hcsum : ∑ m, Complex.normSq (c m) = 1 := by
      have h3 : (∑ m, Complex.normSq (c m)) * Complex.normSq (z i0 j0)
          = 1 * Complex.normSq (z i0 j0) := by rw [one_mul]; exact h1'
      exact mul_right_cancel₀ hne h3
    have hfin : pureConc z = ∑ m, pureConc (y m) := by
      have hterm : ∀ m : Fin n, pureConc (y m) = Complex.normSq (c m) * pureConc z := by
        intro m
        rw [pureConc, pureConc, hdet m, norm_mul, norm_pow, ← Complex.sq_norm]
        ring
      rw [Finset.sum_congr rfl (fun m _ => hterm m), ← Finset.sum_mul, hcsum, one_mul]
    exact hfin.le

/-- The maximally entangled (Bell) state has concurrence one. -/
example : concurrence (rhoOf ![fun i j => if i = j then ((Real.sqrt 2)⁻¹ : ℂ) else 0]) = 1 := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    ring
  rw [concurrence_pure]
  simp [pureConc, det2, h2]

/-- The GHZ state is normalized. -/
example : ∑ i : Fin 2, ∑ j : Fin 2, ∑ k : Fin 2,
    ‖(if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0)‖ ^ 2 = 1 := by
  simp [Fin.sum_univ_two]
  norm_num

/-- The GHZ state has maximal `A|BC` tangle. -/
example : tangleA (fun i j k => if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0) = 1 := by
  have h2 : ((Real.sqrt 2)⁻¹ : ℂ) * ((Real.sqrt 2)⁻¹ : ℂ) = ((2⁻¹ : ℝ) : ℂ) := by
    rw [← mul_inv, ← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0:ℝ) ≤ 2)]
    push_cast
    ring
  simp [tangleA, rhoA, Matrix.trace, Matrix.diag, Matrix.mul_apply, Fin.sum_univ_two, h2]
  norm_num

/-- Its two-qubit reduced states carry no entanglement, in accordance with monogamy. -/
example : concurrence (rhoAB (fun i j k => if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0))
    = 0 := by
  refine le_antisymm ?_ (concurrence_nonneg _)
  have h := concurrence_le _ _
    (rhoAB_eq (fun i j k => if i = j ∧ j = k then ((Real.sqrt 2)⁻¹ : ℂ) else 0)).symm
  simpa [Fin.sum_univ_two, pureConc, det2] using h

end QI

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

set_option pp.fullNames true
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

