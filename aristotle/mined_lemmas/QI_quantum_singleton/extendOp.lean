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

def extendOp (S : Finset (Fin n)) (O : Matrix (S → Fin q) (S → Fin q) ℂ) :
    Matrix (Fin n → Fin q) (Fin n → Fin q) ℂ :=
  fun x y => if (∀ i, i ∉ S → x i = y i) then O (fun i => x i) (fun i => y i) else 0

/-- A `q`-ary quantum code on `n` qudits with `K`-dimensional code space and distance at
least `d`.

`enc` is the encoding isometry from the `K`-dimensional logical space into the `n`-qudit
space `(ℂ^q)^{⊗ n}` (whose canonical basis is indexed by `Fin n → Fin q`), and `detects` is the
Knill–Laflamme error-detection condition: for every operator `O` acting on at most `d - 1`
qudits, `P O P = c(O) P`, where `P = enc * encᴴ` is the projection onto the code space;
equivalently `encᴴ * O * enc` is a multiple of the identity. -/
structure QCode (q n K d : ℕ) where
  /-- The encoding map. -/
  enc : Matrix (Fin n → Fin q) (Fin K) ℂ
  /-- The encoding map is an isometry. -/
  isometry : encᴴ * enc = 1
  /-- Knill–Laflamme error-detection condition for all errors of weight at most `d - 1`. -/
  detects : ∀ S : Finset (Fin n), S.card + 1 ≤ d → ∀ O : Matrix (S → Fin q) (S → Fin q) ℂ,
    ∃ c : ℂ, encᴴ * extendOp S O * enc = c • 1

/-- Restriction to `SB` of an assembled configuration. -/
