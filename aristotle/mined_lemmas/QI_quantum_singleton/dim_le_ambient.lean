import Mathlib

/-!
Rank tools and the core decoupling lemma behind the quantum Singleton bound.
-/

open Matrix Module
open scoped ComplexOrder

namespace QI

variable {X Y Z R : Type*}

section RankTools

/-- Vectors on `Z × X` all of whose `Z`-slices lie in `W`. -/

lemma dim_le_ambient {d : ℕ} (Q : QCode q n K d) : K ≤ q ^ n := by
  have h2 := Matrix.rank_mul_le_right Q.encᴴ Q.enc
  rw [Q.isometry, Matrix.rank_one] at h2
  have h3 : Q.enc.rank ≤ Fintype.card (Fin n → Fin q) := Matrix.rank_le_card_height Q.enc
  simp only [Fintype.card_fun, Fintype.card_fin] at h3
  simpa using h2.trans h3

/-- **Quantum Singleton bound** (Knill–Laflamme bound).
An `[[n, k, d]]_q` quantum code with `q ≥ 2`, `k ≥ 1` and distance at least `d` satisfies
`n - k ≥ 2 (d - 1)`, here in the subtraction-free form `k + 2 * (d - 1) ≤ n`. -/
