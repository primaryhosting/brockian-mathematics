import Mathlib

/-!
# Pos Index Conj Le
Category: Brockian Corpus
Target: Zeta23Core.posIndex_conj_le
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

open Matrix Module Submodule

namespace Zeta23Core

variable {𝕜 : Type*} [RCLike 𝕜] {m d : Type*} [Fintype m] [DecidableEq m] [Fintype d]

/-- The (real) quadratic form `x ↦ xᴴ Q x` associated with a square matrix `Q`. -/

lemma card_pos_add_card_nonpos {Q : Matrix m m 𝕜} (hQ : Q.IsHermitian) :
    Nat.card {i // 0 < hQ.eigenvalues i} + Nat.card {i // hQ.eigenvalues i ≤ 0}
      = Fintype.card m := by
  classical
  haveI : Fintype {i // 0 < hQ.eigenvalues i} := Fintype.ofFinite _
  haveI : Fintype {i // ¬ (0 < hQ.eigenvalues i)} := Fintype.ofFinite _
  haveI : Fintype {i // hQ.eigenvalues i ≤ 0} := Fintype.ofFinite _
  have hcongr : Nat.card {i // hQ.eigenvalues i ≤ 0} = Nat.card {i // ¬ (0 < hQ.eigenvalues i)} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun i => by simp [not_lt])
  have hcompl : Fintype.card {i // ¬ (0 < hQ.eigenvalues i)}
      = Fintype.card m - Fintype.card {i // 0 < hQ.eigenvalues i} :=
    Fintype.card_subtype_compl _
  have hle : Fintype.card {i // 0 < hQ.eigenvalues i} ≤ Fintype.card m :=
    Fintype.card_subtype_le _
  rw [hcongr, Nat.card_eq_fintype_card, Nat.card_eq_fintype_card, hcompl]
  omega

/-- **Key lemma** (hard direction of Sylvester's law of inertia): the dimension of any subspace
on which `Q` is positive definite is at most the positive index of inertia of `Q`. -/
