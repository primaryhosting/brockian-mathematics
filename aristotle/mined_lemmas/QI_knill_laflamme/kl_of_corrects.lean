/-
# Knill Laflamme
Category: Frontier Qi
Target: QI.knill_laflamme
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/
import Mathlib

/-!
# The Knill–Laflamme theorem

A quantum code (given by the orthogonal projector `P` onto the code space) corrects an
error set `E : ι → Matrix n n ℂ` **iff** the Knill–Laflamme conditions
`P * (E i)ᴴ * (E j) * P = c i j • P` hold for some matrix of scalars `c`.
-/

namespace QI

open Matrix Finset

variable {n ι : Type} [Fintype n] [DecidableEq n] [Fintype ι] [DecidableEq ι]

/-- The standard inner product on `n → ℂ`, conjugate linear in the first argument. -/

theorem kl_of_corrects {P : Matrix n n ℂ} (hP : IsProj P) {E : ι → Matrix n n ℂ}
    (h : Corrects P E) : KLCond P E := by
  classical
  obtain ⟨m, R, h1, h2⟩ := h
  -- Each `R k * E i` acts as a scalar on the code space.
  have hscal : ∀ (k : Fin m) (i : ι), ∃ c : ℂ, ∀ v : n → ℂ, P *ᵥ v = v →
      (R k * E i) *ᵥ v = c • v := by
    intro k i
    apply scalar_on_code
    intro v hv hn
    have hsum := h2 v hv hn
    rw [← Fintype.sum_prod_type (fun p : Fin m × ι => outer ((R p.1 * E p.2) *ᵥ v))] at hsum
    exact ⟨_, eq_smul_of_sum_outer (u := fun p : Fin m × ι => (R p.1 * E p.2) *ᵥ v)
      hn hsum (k, i)⟩
  choose lam hlam using hscal
  -- inserting the resolution of the identity given by the Kraus operators
  have hins : ∀ a b : n → ℂ, ip a b = ∑ k, ip (R k *ᵥ a) (R k *ᵥ b) := by
    intro a b
    conv_lhs => rw [show b = (∑ k, (R k)ᴴ * R k) *ᵥ b by rw [h1, one_mulVec]]
    rw [Matrix.sum_mulVec, ip_sum_right]
    exact Finset.sum_congr rfl fun k _ => by
      rw [← mulVec_mulVec, ip_mulVec_right, conjTranspose_conjTranspose]
  refine ⟨Matrix.of fun i j => ∑ k, (starRingEnd ℂ) (lam k i) * lam k j, ?_⟩
  intro i j
  apply matrix_ext_ip
  intro v w
  have hPx : P *ᵥ (P *ᵥ w) = P *ᵥ w := by rw [mulVec_mulVec, hP.idem]
  have hPy : P *ᵥ (P *ᵥ v) = P *ᵥ v := by rw [mulVec_mulVec, hP.idem]
  have hyx : ip (P *ᵥ v) (P *ᵥ w) = ip v (P *ᵥ w) := by
    rw [ip_mulVec_left, hP.herm, hPx]
  rw [ip_sandwich hP, hins]
  have hterm : ∀ k : Fin m, ip (R k *ᵥ (E i *ᵥ (P *ᵥ v))) (R k *ᵥ (E j *ᵥ (P *ᵥ w)))
      = (starRingEnd ℂ) (lam k i) * lam k j * ip v (P *ᵥ w) := by
    intro k
    rw [mulVec_mulVec (P *ᵥ v) (R k) (E i), mulVec_mulVec (P *ᵥ w) (R k) (E j),
      hlam k i _ hPy, hlam k j _ hPx,
      ip_smul_left, ip_smul_right, hyx]
    ring
  rw [Finset.sum_congr rfl fun k _ => hterm k, ← Finset.sum_mul]
  simp [Matrix.of_apply, smul_mulVec, ip_smul_right]

/-! ## The converse: the Knill–Laflamme conditions imply correctability -/

omit [DecidableEq ι] in
/-- Convenience constructor for `Corrects` allowing an arbitrary finite index type. -/
