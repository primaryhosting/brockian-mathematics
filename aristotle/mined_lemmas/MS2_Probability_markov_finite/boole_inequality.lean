import Mathlib
open Finset
namespace MS2.Probability
/-- Finite Markov inequality. The hypothesis `0 < a` is kept as stated, although the
proof does not need it (nonnegativity of `x` alone suffices). -/

theorem boole_inequality {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {n : ℕ} (A : Fin n → Finset Ω) :
    (Finset.univ.biUnion A).card ≤ ∑ i, (A i).card :=
  Finset.card_biUnion_le

