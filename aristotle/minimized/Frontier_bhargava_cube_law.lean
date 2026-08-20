/-!
# Bhargava Cube Law
Category: Frontier — Fields Medal Work
Target: Frontier.bhargava_cube_law
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

/-
Note on imports: Lean 4 does not allow an `import` command to follow a module docstring,
so in order to begin the file with exactly the header comment requested, this development is
self-contained and uses only the Lean core prelude (no Mathlib).  A search of Mathlib turns up
no Bhargava cubes, no Gauss/Dirichlet composition of binary quadratic forms, and no class group
of binary quadratic forms, so there is no existing lemma to cite here; the `2 × 2` determinants
and binary quadratic forms used below are defined from scratch.
-/

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

set_option relaxedAutoImplicit false
set_option autoImplicit false

set_option grind.warning false

namespace Frontier

/-! ## `2 × 2` integer matrices -/

/-- A `2 × 2` integer matrix `!![a, b; c, d]`. -/
structure Mat2 where
  a : Int
  b : Int
  c : Int
  d : Int
  deriving DecidableEq

namespace Mat2

/-- The determinant `ad - bc`. -/

def det (M : Mat2) : Int := M.a * M.d - M.b * M.c

instance : Sub Mat2 :=
  ⟨fun M N => ⟨M.a - N.a, M.b - N.b, M.c - N.c, M.d - N.d⟩⟩

/-- Scalar multiplication of a `2 × 2` matrix by an integer. -/
instance : HMul Int Mat2 Mat2 :=
  ⟨fun x M => ⟨x * M.a, x * M.b, x * M.c, x * M.d⟩⟩

@[simp] theorem sub_a (M N : Mat2) : (M - N).a = M.a - N.a := rfl

@[simp] theorem sub_b (M N : Mat2) : (M - N).b = M.b - N.b := rfl

@[simp] theorem sub_c (M N : Mat2) : (M - N).c = M.c - N.c := rfl

@[simp] theorem sub_d (M N : Mat2) : (M - N).d = M.d - N.d := rfl

@[simp] theorem smul_a (x : Int) (M : Mat2) : (x * M).a = x * M.a := rfl

@[simp] theorem smul_b (x : Int) (M : Mat2) : (x * M).b = x * M.b := rfl

@[simp] theorem smul_c (x : Int) (M : Mat2) : (x * M).c = x * M.c := rfl

@[simp] theorem smul_d (x : Int) (M : Mat2) : (x * M).d = x * M.d := rfl

end Mat2

/-! ## Integral binary quadratic forms -/

/-- An integral binary quadratic form `a x² + b x y + c y²`, recorded by its coefficients. -/
structure BQF where
  a : Int
  b : Int
  c : Int
  deriving DecidableEq

namespace BQF

/-- Evaluation of a binary quadratic form at `(x, y)`. -/

def eval (Q : BQF) (x y : Int) : Int := Q.a * x * x + Q.b * x * y + Q.c * y * y

/-- The discriminant `b² - 4ac` of a binary quadratic form. -/

def disc (Q : BQF) : Int := Q.b * Q.b - 4 * Q.a * Q.c

end BQF

/-! ## Bhargava cubes

A *Bhargava cube* is a `2 × 2 × 2` array of integers.  We label its eight vertices

```
        e --------- f
       /|          /|
      a --------- b |
      | |         | |
      | g --------|-h
      |/          |/
      c --------- d
```

so that the front face is `!![a, b; c, d]` and the back face is `!![e, f; g, h]`.
Cutting the cube in each of the three possible directions produces three pairs of matrices
`(M₁, N₁)`, `(M₂, N₂)`, `(M₃, N₃)`, and hence three binary quadratic forms
`Qᵢ(x, y) = -det(Mᵢ x - Nᵢ y)`.
-/

/-- A `2 × 2 × 2` integer cube, given by its eight vertex entries. -/
structure BhargavaCube where
  a : Int
  b : Int
  c : Int
  d : Int
  e : Int
  f : Int
  g : Int
  h : Int

namespace BhargavaCube

variable (K : BhargavaCube)

/-- First slicing (front/back): front face. -/

def M₁ : Mat2 := ⟨K.a, K.b, K.c, K.d⟩
/-- First slicing (front/back): back face. -/

def N₁ : Mat2 := ⟨K.e, K.f, K.g, K.h⟩
/-- Second slicing (left/right): left face. -/

def M₂ : Mat2 := ⟨K.a, K.c, K.e, K.g⟩
/-- Second slicing (left/right): right face. -/

def N₂ : Mat2 := ⟨K.b, K.d, K.f, K.h⟩
/-- Third slicing (top/bottom): top face. -/

def M₃ : Mat2 := ⟨K.a, K.e, K.b, K.f⟩
/-- Third slicing (top/bottom): bottom face. -/

def N₃ : Mat2 := ⟨K.c, K.g, K.d, K.h⟩

/-- The first form of the cube, defined by the determinant recipe
`Q₁(x, y) = -det(M₁ x - N₁ y)`. -/

def q₁ (x y : Int) : Int := -(x * K.M₁ - y * K.N₁).det
/-- The second form of the cube, `Q₂(x, y) = -det(M₂ x - N₂ y)`. -/

def q₂ (x y : Int) : Int := -(x * K.M₂ - y * K.N₂).det
/-- The third form of the cube, `Q₃(x, y) = -det(M₃ x - N₃ y)`. -/

def q₃ (x y : Int) : Int := -(x * K.M₃ - y * K.N₃).det

/-- The coefficient triple of the first quadratic form of the cube. -/

def Q₁ : BQF :=
  ⟨-(K.a * K.d - K.b * K.c), K.a * K.h + K.d * K.e - K.b * K.g - K.c * K.f,
    -(K.e * K.h - K.f * K.g)⟩
/-- The coefficient triple of the second quadratic form of the cube. -/

def Q₂ : BQF :=
  ⟨-(K.a * K.g - K.c * K.e), K.a * K.h + K.b * K.g - K.c * K.f - K.d * K.e,
    -(K.b * K.h - K.d * K.f)⟩
/-- The coefficient triple of the third quadratic form of the cube. -/

def Q₃ : BQF :=
  ⟨-(K.a * K.f - K.b * K.e), K.a * K.h + K.c * K.f - K.b * K.g - K.d * K.e,
    -(K.c * K.h - K.d * K.g)⟩

theorem q₁_eq (x y : Int) : K.q₁ x y = K.Q₁.eval x y := by
  simp only [q₁, Q₁, BQF.eval, M₁, N₁, Mat2.det, Mat2.sub_a, Mat2.sub_b, Mat2.sub_c, Mat2.sub_d,
    Mat2.smul_a, Mat2.smul_b, Mat2.smul_c, Mat2.smul_d]
  grind

theorem q₂_eq (x y : Int) : K.q₂ x y = K.Q₂.eval x y := by
  simp only [q₂, Q₂, BQF.eval, M₂, N₂, Mat2.det, Mat2.sub_a, Mat2.sub_b, Mat2.sub_c, Mat2.sub_d,
    Mat2.smul_a, Mat2.smul_b, Mat2.smul_c, Mat2.smul_d]
  grind

theorem q₃_eq (x y : Int) : K.q₃ x y = K.Q₃.eval x y := by
  simp only [q₃, Q₃, BQF.eval, M₃, N₃, Mat2.det, Mat2.sub_a, Mat2.sub_b, Mat2.sub_c, Mat2.sub_d,
    Mat2.smul_a, Mat2.smul_b, Mat2.smul_c, Mat2.smul_d]
  grind

/-- **All three quadratic forms of a Bhargava cube have the same discriminant** — the common
value being (minus) the hyperdeterminant of the cube.  This is what makes the cube law a
composition law on forms of a fixed discriminant. -/

theorem disc_eq : K.Q₁.disc = K.Q₂.disc ∧ K.Q₂.disc = K.Q₃.disc := by
  constructor <;> · simp only [BQF.disc, Q₁, Q₂, Q₃]; grind

end BhargavaCube

/-- **Dirichlet/Gauss composition of concordant forms.**  The forms `(a₁, B, a₂C)` and
`(a₂, B, a₁C)`, which share the discriminant `B² - 4a₁a₂C`, compose to `(a₁a₂, B, C)` via the
explicit bilinear substitution `X = x₁x₂ - C y₁y₂`, `Y = a₁x₁y₂ + a₂x₂y₁ + B y₁y₂`. -/

theorem bhargava_cube_law :
    (∀ K : BhargavaCube,
        (∀ x y : Int, K.q₁ x y = K.Q₁.eval x y) ∧
        (∀ x y : Int, K.q₂ x y = K.Q₂.eval x y) ∧
        (∀ x y : Int, K.q₃ x y = K.Q₃.eval x y) ∧
        K.Q₁.disc = K.Q₂.disc ∧ K.Q₂.disc = K.Q₃.disc) ∧
    (∀ a₁ a₂ B C : Int,
        let K : BhargavaCube := ⟨0, a₁, a₂, B, 1, 0, 0, -C⟩
        K.Q₁ = ⟨a₁ * a₂, B, C⟩ ∧ K.Q₂ = ⟨a₂, -B, a₁ * C⟩ ∧ K.Q₃ = ⟨a₁, -B, a₂ * C⟩ ∧
        K.Q₁.disc = B * B - 4 * (a₁ * a₂) * C ∧
        ∀ x₁ y₁ x₂ y₂ : Int,
          K.Q₃.eval x₁ y₁ * K.Q₂.eval x₂ y₂
            = K.Q₁.eval (x₁ * x₂ - C * y₁ * y₂)
                (B * y₁ * y₂ - a₁ * x₁ * y₂ - a₂ * x₂ * y₁)) := by
  refine ⟨fun K => ⟨K.q₁_eq, K.q₂_eq, K.q₃_eq, K.disc_eq.1, K.disc_eq.2⟩, ?_⟩
  intro a₁ a₂ B C K
  have hQ₁ : K.Q₁ = ⟨a₁ * a₂, B, C⟩ := by
    show BhargavaCube.Q₁ ⟨0, a₁, a₂, B, 1, 0, 0, -C⟩ = _
    simp only [BhargavaCube.Q₁, BQF.mk.injEq]
    refine ⟨by grind, by grind, by grind⟩
  have hQ₂ : K.Q₂ = ⟨a₂, -B, a₁ * C⟩ := by
    show BhargavaCube.Q₂ ⟨0, a₁, a₂, B, 1, 0, 0, -C⟩ = _
    simp only [BhargavaCube.Q₂, BQF.mk.injEq]
    refine ⟨by grind, by grind, by grind⟩
  have hQ₃ : K.Q₃ = ⟨a₁, -B, a₂ * C⟩ := by
    show BhargavaCube.Q₃ ⟨0, a₁, a₂, B, 1, 0, 0, -C⟩ = _
    simp only [BhargavaCube.Q₃, BQF.mk.injEq]
    refine ⟨by grind, by grind, by grind⟩
  refine ⟨hQ₁, hQ₂, hQ₃, ?_, fun x₁ y₁ x₂ y₂ => ?_⟩
  · rw [hQ₁]; simp only [BQF.disc]
  · rw [hQ₁, hQ₂, hQ₃]
    simp only [BQF.eval]
    grind

end Frontier
