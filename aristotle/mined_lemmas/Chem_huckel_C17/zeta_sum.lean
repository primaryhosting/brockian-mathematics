import Mathlib

/-!
# Huckel C 17
Category: Chemistry
Target: Chem.huckel_C17
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` commands to come before any other command
(including module doc comments), so the header comment above is placed immediately after
the single `import Mathlib` line; its text is otherwise verbatim.

Mathematical content: the adjacency matrix `C17` of the cycle graph on 17 vertices is the
circulant matrix `A i j = 1` iff `i - j = ±1` (indices in `ZMod 17`).  It is diagonalised by
the discrete Fourier matrix `F i k = ζ^{ik}` (`ζ = exp (2πi/17)`), with eigenvalues
`ζ^k + ζ^{-k} = 2 cos (2πk/17)`.  Hence `det (μ - A) = ∏ (μ - 2 cos (2πk/17))`, and the
spectrum is exactly the set of these 17 numbers.
-/

namespace Chem

open Complex Matrix

/-- A primitive 17-th root of unity. -/

lemma zeta_sum (m : ZMod 17) : ∑ j : ZMod 17, zeta (j * m) = if m = 0 then 17 else 0 := by
  by_cases hm : m = 0
  · subst hm; simp [zeta_zero]
  · simp only [hm, if_false]
    have h1 : ∀ j ∈ (Finset.univ : Finset (ZMod 17)), zeta (j * m) = (zeta m) ^ j.val :=
      fun j _ => by rw [mul_comm, zeta_mul]
    have h2 : ∑ j : ZMod 17, (zeta m) ^ (ZMod.val j) = ∑ i ∈ Finset.range 17, (zeta m) ^ i :=
      Fin.sum_univ_eq_sum_range (fun i => (zeta m) ^ i) 17
    rw [Finset.sum_congr rfl h1, h2]
    have hne : m.val ≠ 0 := fun h => hm ((ZMod.val_eq_zero m).mp h)
    have hlt : m.val < 17 := ZMod.val_lt m
    have hnd : ¬ (17 ∣ m.val) := fun hd => by
      have := Nat.le_of_dvd (Nat.pos_of_ne_zero hne) hd; omega
    have hcop : Nat.Coprime m.val 17 :=
      Nat.coprime_comm.mp (((by norm_num : Nat.Prime 17).coprime_iff_not_dvd).mpr hnd)
    exact (hw.pow_of_coprime m.val hcop).geom_sum_eq_zero (by norm_num)

