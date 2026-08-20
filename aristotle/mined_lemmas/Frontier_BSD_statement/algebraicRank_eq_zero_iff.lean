import Mathlib
/-!
# BSD Statement
Category: Frontier — Moonshot
Target: Frontier.BSD_statement
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on the header: Lean 4 requires `import` to be the very first command in a file, and a
module docstring `/-! ... -/` may not precede it.  The requested header is therefore placed
immediately after the single `import Mathlib` line, which is as close to the beginning of the
file as the language permits.

Mathlib coverage: as of this Mathlib revision there is no Hasse-Weil L-function of an elliptic
curve, no Mordell-Weil theorem, and no BSD statement (`Mathlib/NumberTheory/LSeries/` covers
only Riemann/Hurwitz zeta and Dirichlet L-functions; `Mathlib/AlgebraicGeometry/EllipticCurve/`
provides the group of nonsingular points `WeierstrassCurve.Affine.Point` but nothing analytic).
So no existing lemma closes or nearly closes this goal; the analytic input is isolated below in
the structure `Frontier.LFunctionDatum`, and the Mordell-Weil theorem appears as the explicit
hypothesis `Module.Finite ℤ (MordellWeil E)`.
-/

open scoped Classical

namespace Frontier

open WeierstrassCurve

/-! ## The Mordell–Weil group and its rank -/

/-- The Mordell–Weil group `E(ℚ)` of an elliptic curve given by an integral Weierstrass
equation `E` over `ℤ`: the group of nonsingular rational points of the base change of `E`
to `ℚ`, in affine coordinates (including the point at infinity). -/
abbrev MordellWeil (E : WeierstrassCurve ℤ) : Type :=
  (E.map (Int.castRingHom ℚ)).toAffine.Point

/-- The algebraic rank of `E`: the rank of the finitely generated abelian group `E(ℚ)`. -/

theorem algebraicRank_eq_zero_iff (E : WeierstrassCurve ℤ)
    (hfg : Module.Finite ℤ (MordellWeil E)) :
    algebraicRank E = 0 ↔ ∀ P : MordellWeil E, ∃ n : ℕ, 0 < n ∧ n • P = 0 := by
  rw [algebraicRank, Module.finrank_eq_zero_iff_isTorsion]
  constructor
  · intro h P
    obtain ⟨⟨m, hm⟩, hmP⟩ := @h P
    have hmP' : m • P = 0 := hmP
    refine ⟨m.natAbs, Int.natAbs_pos.mpr (mem_nonZeroDivisors_iff_ne_zero.mp hm), ?_⟩
    have : (m.natAbs : ℤ) • P = 0 := by
      rcases Int.natAbs_eq m with h' | h'
      · rw [← h']; exact hmP'
      · rw [show ((m.natAbs : ℤ)) = -m by omega, neg_smul, hmP', neg_zero]
    simpa [← natCast_zsmul] using this
  · intro h P
    obtain ⟨n, hn, hnP⟩ := h P
    refine ⟨⟨(n : ℤ), mem_nonZeroDivisors_iff_ne_zero.mpr (by exact_mod_cast hn.ne')⟩, ?_⟩
    simpa [natCast_zsmul] using hnP

/-- **BSD statement, with a Lean-checked reduction to its rank-zero base case.**

For an elliptic curve given by an integral Weierstrass model `E` over `ℤ`, with a Hasse–Weil
L-function datum `D` (an analytic continuation of `∑ a n n^{-s}` to a neighbourhood of `s = 1`),
assuming the Mordell–Weil theorem for `E` (finite generation of `E(ℚ)`), the Birch and
Swinnerton-Dyer conjecture `ord_{s=1} L(E,s) = rank E(ℚ)` implies its rank-zero base case:

  `L(E, 1) ≠ 0 ↔ E(ℚ) is a torsion group`,

and, complementarily, `L(E, 1) = 0` exactly when `E(ℚ)` has positive rank. -/
