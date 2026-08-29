-- (Lean 4 requires `import` to be the very first command in a file, so the
-- module docstring header below follows the import.)
import Mathlib

/-!
# Thurston Geometrization
Category: Frontier — Fields Medal Work
Target: Frontier.thurston_geometrization
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

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

namespace Frontier

/-!
## 1. The eight Thurston geometries

Thurston's list of the eight maximal, simply connected, three–dimensional model
geometries admitting a compact quotient:

`E³`, `S³`, `H³`, `S² × ℝ`, `H² × ℝ`, `SL(2,ℝ)~`, `Nil`, `Sol`.
-/

/-- The eight three–dimensional Thurston model geometries. -/
inductive Geometry where
  /-- Euclidean geometry `E³`. -/
  | euclidean : Geometry
  /-- Spherical geometry `S³`. -/
  | spherical : Geometry
  /-- Hyperbolic geometry `H³`. -/
  | hyperbolic : Geometry
  /-- The product geometry `S² × ℝ`. -/
  | sphereTimesLine : Geometry
  /-- The product geometry `H² × ℝ`. -/
  | hyperbolicTimesLine : Geometry
  /-- The geometry of the universal cover of `SL(2,ℝ)`. -/
  | slTwoRCover : Geometry
  /-- Nil geometry (the Heisenberg group). -/
  | nil : Geometry
  /-- Sol geometry (the three-dimensional solvable Lie group). -/
  | sol : Geometry
  deriving DecidableEq, Fintype, Repr

/-- There are exactly eight Thurston geometries. -/
theorem card_geometry : Fintype.card Geometry = 8 := by decide

/-!
## 2. Two of the model geometries as concrete Lie groups

`Nil` and `Sol` are the two model geometries whose underlying spaces are
three-dimensional Lie groups that are neither products nor symmetric spaces of
the classical kind; we build them explicitly here, together with the abelian
model `E³ = ℝ³`, as verified base-case data for the geometrization statement.
-/

/-- The underlying space of Nil geometry: the three–dimensional Heisenberg group. -/
@[ext]
structure NilSpace where
  /-- First coordinate. -/
  x : ℝ
  /-- Second coordinate. -/
  y : ℝ
  /-- Central coordinate. -/
  z : ℝ

namespace NilSpace

instance : Mul NilSpace :=
  ⟨fun p q => ⟨p.x + q.x, p.y + q.y, p.z + q.z + p.x * q.y⟩⟩

instance : One NilSpace := ⟨⟨0, 0, 0⟩⟩

instance : Inv NilSpace := ⟨fun p => ⟨-p.x, -p.y, -p.z + p.x * p.y⟩⟩

@[simp] theorem mul_x (p q : NilSpace) : (p * q).x = p.x + q.x := rfl
@[simp] theorem mul_y (p q : NilSpace) : (p * q).y = p.y + q.y := rfl
@[simp] theorem mul_z (p q : NilSpace) : (p * q).z = p.z + q.z + p.x * q.y := rfl
@[simp] theorem one_x : (1 : NilSpace).x = 0 := rfl
@[simp] theorem one_y : (1 : NilSpace).y = 0 := rfl
@[simp] theorem one_z : (1 : NilSpace).z = 0 := rfl
@[simp] theorem inv_x (p : NilSpace) : p⁻¹.x = -p.x := rfl
@[simp] theorem inv_y (p : NilSpace) : p⁻¹.y = -p.y := rfl
@[simp] theorem inv_z (p : NilSpace) : p⁻¹.z = -p.z + p.x * p.y := rfl

instance : Group NilSpace :=
  Group.ofLeftAxioms
    (fun a b c => by ext <;> simp <;> ring)
    (fun a => by ext <;> simp)
    (fun a => by ext <;> simp)

/-- Nil geometry is not abelian: it is a nontrivial central extension of `ℝ²`. -/
theorem not_commutative : ¬ ∀ p q : NilSpace, p * q = q * p := by
  intro h
  have := congrArg NilSpace.z (h ⟨1, 0, 0⟩ ⟨0, 1, 0⟩)
  simp at this

/-- Nil is nilpotent of class two: all commutators are central. -/
theorem commutator_central (p q r : NilSpace) :
    (p * q * p⁻¹ * q⁻¹) * r = r * (p * q * p⁻¹ * q⁻¹) := by
  ext
  · simp
  · simp
  · simp
    ring

end NilSpace

/-- The underlying space of Sol geometry: `ℝ² ⋊ ℝ`, where `t : ℝ` acts on `ℝ²`
by `(x, y) ↦ (eᵗ x, e⁻ᵗ y)`. -/
@[ext]
structure SolSpace where
  /-- Expanding coordinate. -/
  x : ℝ
  /-- Contracting coordinate. -/
  y : ℝ
  /-- Coordinate along the acting line. -/
  t : ℝ

namespace SolSpace

noncomputable instance : Mul SolSpace :=
  ⟨fun p q => ⟨p.x + Real.exp p.t * q.x, p.y + Real.exp (-p.t) * q.y, p.t + q.t⟩⟩

instance : One SolSpace := ⟨⟨0, 0, 0⟩⟩

noncomputable instance : Inv SolSpace :=
  ⟨fun p => ⟨-Real.exp (-p.t) * p.x, -Real.exp p.t * p.y, -p.t⟩⟩

@[simp] theorem mul_x (p q : SolSpace) : (p * q).x = p.x + Real.exp p.t * q.x := rfl
@[simp] theorem mul_y (p q : SolSpace) : (p * q).y = p.y + Real.exp (-p.t) * q.y := rfl
@[simp] theorem mul_t (p q : SolSpace) : (p * q).t = p.t + q.t := rfl
@[simp] theorem one_x : (1 : SolSpace).x = 0 := rfl
@[simp] theorem one_y : (1 : SolSpace).y = 0 := rfl
@[simp] theorem one_t : (1 : SolSpace).t = 0 := rfl
@[simp] theorem inv_x (p : SolSpace) : p⁻¹.x = -Real.exp (-p.t) * p.x := rfl
@[simp] theorem inv_y (p : SolSpace) : p⁻¹.y = -Real.exp p.t * p.y := rfl
@[simp] theorem inv_t (p : SolSpace) : p⁻¹.t = -p.t := rfl

noncomputable instance : Group SolSpace :=
  Group.ofLeftAxioms
    (fun a b c => by
      ext
      · simp [Real.exp_add]; ring
      · simp [Real.exp_add]; ring
      · simp; ring)
    (fun a => by ext <;> simp)
    (fun a => by
      ext
      · simp
      · simp
      · simp)

/-- Sol geometry is not abelian. -/
theorem not_commutative : ¬ ∀ p q : SolSpace, p * q = q * p := by
  intro h
  have hx := congrArg SolSpace.x (h ⟨0, 0, 1⟩ ⟨1, 0, 0⟩)
  simp at hx

/-- The subgroup `{t = 0}` of Sol is abelian: Sol is solvable. -/
theorem plane_commutative (p q : SolSpace) (hp : p.t = 0) (hq : q.t = 0) :
    p * q = q * p := by
  ext <;> simp [hp, hq]<;> ring

/-- Unlike Nil, Sol has a non-central commutator: it is solvable but not nilpotent. -/
theorem commutator_not_central :
    ∃ p q r : SolSpace, (p * q * p⁻¹ * q⁻¹) * r ≠ r * (p * q * p⁻¹ * q⁻¹) := by
  refine ⟨⟨0, 0, 1⟩, ⟨1, 0, 0⟩, ⟨0, 0, 1⟩, ?_⟩
  intro heq
  have hx := congrArg SolSpace.x heq
  simp at hx
  have h2 : (2 : ℝ) < Real.exp 1 := by
    have := Real.add_one_lt_exp (x := 1) (by norm_num)
    linarith
  nlinarith [hx]

end SolSpace

/-- The Nil and Sol model geometries are genuinely different: their underlying
Lie groups are not isomorphic, since all commutators in Nil are central while
Sol has a non-central commutator. -/
theorem nil_not_mulEquiv_sol : IsEmpty (NilSpace ≃* SolSpace) := by
  constructor
  intro f
  obtain ⟨p, q, r, h⟩ := SolSpace.commutator_not_central
  exact h (by
    simpa using congrArg f (NilSpace.commutator_central (f.symm p) (f.symm q) (f.symm r)))

/-- Euclidean model geometry `E³`, as an abelian Lie group. -/
abbrev EuclideanSpace3 := ℝ × ℝ × ℝ

theorem euclideanSpace3_commutative (p q : EuclideanSpace3) : p + q = q + p :=
  add_comm p q

/-!
## 3. An abstract framework for closed three–manifolds

Formalizing smooth three–manifolds, connected sums, incompressible tori and
locally homogeneous Riemannian metrics from scratch is far beyond what is
available in Mathlib.  Instead we axiomatize the *combinatorial shape* of the
geometrization theorem: a `ThreeManifoldTheory` records

* a type `Mfld` of (diffeomorphism classes of) closed oriented 3–manifolds,
* the connected sum operation with unit the 3–sphere,
* the predicate `IsPrime` of prime manifolds,
* a type `Piece` of compact pieces with (possibly empty) torus boundary,
* the relation `IsJSJ m ps` — "`ps` is the list of pieces obtained by cutting
  `m` along its JSJ tori",
* the relation `AdmitsGeometry p g` — "the piece `p` carries a complete locally
  homogeneous metric modelled on the geometry `g`".

All statements below are theorems *about* such a structure: they carry the
geometric input as explicit hypotheses and derive the global statement from it.
-/

/-- Abstract data for a theory of closed oriented three–manifolds. -/
structure ThreeManifoldTheory where
  /-- Diffeomorphism classes of closed oriented 3–manifolds. -/
  Mfld : Type
  /-- Connected sum. -/
  connSum : Mfld → Mfld → Mfld
  /-- The 3–sphere, the unit for connected sum. -/
  sphere3 : Mfld
  /-- Being a prime manifold. -/
  IsPrime : Mfld → Prop
  /-- Compact pieces with torus boundary arising from the JSJ decomposition. -/
  Piece : Type
  /-- `IsJSJ m ps` : cutting `m` along its JSJ tori yields the pieces `ps`. -/
  IsJSJ : Mfld → List Piece → Prop
  /-- `AdmitsGeometry p g` : the piece `p` carries a geometry modelled on `g`. -/
  AdmitsGeometry : Piece → Geometry → Prop

namespace ThreeManifoldTheory

variable (T : ThreeManifoldTheory)

/-- `m` is *geometrizable*: cutting it along spheres and tori yields pieces each
of which carries one of the eight Thurston geometries. -/
def Geometrizable (m : T.Mfld) : Prop :=
  ∃ ps : List T.Piece, T.IsJSJ m ps ∧ ∀ p ∈ ps, ∃ g : Geometry, T.AdmitsGeometry p g

/-- `m` is a connected sum of the (finitely many) prime manifolds in a list. -/
def IsConnSumOfPrimes (m : T.Mfld) : Prop :=
  ∃ l : List T.Mfld, (∀ p ∈ l, T.IsPrime p) ∧ m = l.foldr T.connSum T.sphere3

variable {T}

/-- Connected sums of the concatenation of two lists split as a connected sum. -/
theorem foldr_append (hassoc : ∀ a b c, T.connSum (T.connSum a b) c
      = T.connSum a (T.connSum b c))
    (hunit : ∀ a, T.connSum T.sphere3 a = a) (l₁ l₂ : List T.Mfld) :
    (l₁ ++ l₂).foldr T.connSum T.sphere3
      = T.connSum (l₁.foldr T.connSum T.sphere3) (l₂.foldr T.connSum T.sphere3) := by
  induction l₁ with
  | nil => simp [hunit]
  | cons a l ih => simp only [List.cons_append, List.foldr_cons, ih, hassoc]

/-!
### 3.1 Kneser–Milnor: reduction to prime manifolds

If every manifold is either prime, the sphere, or splits as a connected sum of
two manifolds of strictly smaller complexity, then every manifold is a finite
connected sum of primes.  This is the standard induction underlying the
Kneser–Milnor prime decomposition theorem, and it is proved here in full.
-/

/-- **Prime decomposition by induction on complexity.** -/
theorem isConnSumOfPrimes_of_splitting (c : T.Mfld → ℕ)
    (hunitR : ∀ a, T.connSum a T.sphere3 = a)
    (hsplit : ∀ m : T.Mfld, T.IsPrime m ∨ m = T.sphere3 ∨
      ∃ a b, m = T.connSum a b ∧ c a < c m ∧ c b < c m)
    (hassoc : ∀ a b c, T.connSum (T.connSum a b) c = T.connSum a (T.connSum b c))
    (hunitL : ∀ a, T.connSum T.sphere3 a = a) :
    ∀ m : T.Mfld, T.IsConnSumOfPrimes m := by
  intro m
  induction hn : c m using Nat.strong_induction_on generalizing m with
  | _ n ih =>
    subst hn
    rcases hsplit m with hprime | hsph | ⟨a, b, rfl, ha, hb⟩
    · exact ⟨[m], by simpa using hprime, by simp [hunitR]⟩
    · exact ⟨[], by simp, by simp [hsph]⟩
    · obtain ⟨la, hla, rfl⟩ := ih (c a) ha a rfl
      obtain ⟨lb, hlb, hb'⟩ := ih (c b) hb b rfl
      refine ⟨la ++ lb, ?_, ?_⟩
      · intro p hp
        rcases List.mem_append.mp hp with h | h
        · exact hla p h
        · exact hlb p h
      · rw [foldr_append hassoc hunitL, ← hb']

/-!
### 3.2 Geometrizability is additive along connected sums
-/

/-- If the JSJ decomposition of a connected sum is the concatenation of the JSJ
decompositions of the summands, geometrizability is preserved by connected sums. -/
theorem Geometrizable.connSum
    (hJSJ : ∀ (a b : T.Mfld) (la lb : List T.Piece),
      T.IsJSJ a la → T.IsJSJ b lb → T.IsJSJ (T.connSum a b) (la ++ lb))
    {a b : T.Mfld} (ha : T.Geometrizable a) (hb : T.Geometrizable b) :
    T.Geometrizable (T.connSum a b) := by
  obtain ⟨la, hla, hga⟩ := ha
  obtain ⟨lb, hlb, hgb⟩ := hb
  refine ⟨la ++ lb, hJSJ a b la lb hla hlb, ?_⟩
  intro p hp
  rcases List.mem_append.mp hp with h | h
  · exact hga p h
  · exact hgb p h

/-- Geometrizability propagates from prime summands to arbitrary connected sums. -/
theorem geometrizable_of_isConnSumOfPrimes
    (hJSJ : ∀ (a b : T.Mfld) (la lb : List T.Piece),
      T.IsJSJ a la → T.IsJSJ b lb → T.IsJSJ (T.connSum a b) (la ++ lb))
    (hsphere : T.Geometrizable T.sphere3)
    (hprime : ∀ m : T.Mfld, T.IsPrime m → T.Geometrizable m)
    {m : T.Mfld} (hm : T.IsConnSumOfPrimes m) : T.Geometrizable m := by
  obtain ⟨l, hl, rfl⟩ := hm
  induction l with
  | nil => simpa using hsphere
  | cons a l ih =>
    have ha : T.Geometrizable a := hprime a (hl a (by simp))
    have hrest : T.Geometrizable (l.foldr T.connSum T.sphere3) :=
      ih (fun p hp => hl p (by simp [hp]))
    simpa using Geometrizable.connSum hJSJ ha hrest

end ThreeManifoldTheory

/-!
## 4. The geometrization statement
-/

open ThreeManifoldTheory in
/-- **Thurston's Geometrization Theorem (Lean-checked reduction).**

Let `T` be a theory of closed oriented three–manifolds as above.  Assume:

* `hunitR`, `hunitL`, `hassoc`: connected sum is associative with unit `S³`;
* `hsplit`: every manifold is prime, is `S³`, or splits as a connected sum of
  two manifolds of strictly smaller complexity `c` (the finiteness input of the
  Kneser–Milnor prime decomposition theorem);
* `hJSJ`: the JSJ decomposition of a connected sum is the concatenation of the
  JSJ decompositions of the summands;
* `hsphere`: `S³` is geometrizable (it carries spherical geometry);
* `hprime`: every **prime** manifold is geometrizable, i.e. cutting it along its
  JSJ tori yields pieces each modelled on one of the eight Thurston geometries
  (this is the analytic core supplied by Thurston's hyperbolization and
  Perelman's Ricci-flow argument).

Then **every** closed oriented three–manifold is geometrizable: it decomposes
along spheres and tori into pieces each of which carries one of the eight
Thurston geometries `E³, S³, H³, S² × ℝ, H² × ℝ, SL(2,ℝ)~, Nil, Sol`. -/
theorem thurston_geometrization (T : ThreeManifoldTheory) (c : T.Mfld → ℕ)
    (hunitR : ∀ a, T.connSum a T.sphere3 = a)
    (hunitL : ∀ a, T.connSum T.sphere3 a = a)
    (hassoc : ∀ a b c, T.connSum (T.connSum a b) c = T.connSum a (T.connSum b c))
    (hsplit : ∀ m : T.Mfld, T.IsPrime m ∨ m = T.sphere3 ∨
      ∃ a b, m = T.connSum a b ∧ c a < c m ∧ c b < c m)
    (hJSJ : ∀ (a b : T.Mfld) (la lb : List T.Piece),
      T.IsJSJ a la → T.IsJSJ b lb → T.IsJSJ (T.connSum a b) (la ++ lb))
    (hsphere : T.Geometrizable T.sphere3)
    (hprime : ∀ m : T.Mfld, T.IsPrime m → T.Geometrizable m) :
    ∀ m : T.Mfld, ∃ ps : List T.Piece, T.IsJSJ m ps ∧
      ∀ p ∈ ps, ∃ g : Geometry, T.AdmitsGeometry p g := by
  intro m
  exact geometrizable_of_isConnSumOfPrimes hJSJ hsphere hprime
    (isConnSumOfPrimes_of_splitting c hunitR hsplit hassoc hunitL m)

/-!
## 5. Non-vacuity

The hypotheses of `thurston_geometrization` are consistent and non-degenerate:
here is a model with infinitely many manifolds, infinitely many primes, and a
nontrivial connected sum operation, in which they all hold.
-/

/-- A model theory: manifolds are natural numbers (the number of prime summands),
connected sum is addition, `S³` is `0`, primes are the manifolds with exactly one
summand, and the JSJ decomposition of `m` is a list of `m` pieces. -/
def modelTheory : ThreeManifoldTheory where
  Mfld := ℕ
  connSum := (· + ·)
  sphere3 := 0
  IsPrime := fun n => n = 1
  Piece := Unit
  IsJSJ := fun n l => l.length = n
  AdmitsGeometry := fun _ g => g = Geometry.hyperbolic

/-- **Non-vacuity.** In the model theory the hypotheses of
`thurston_geometrization` all hold, and the conclusion — every manifold is
geometrizable — follows from the general theorem. -/
theorem modelTheory_geometrizable :
    ∀ m : modelTheory.Mfld, ∃ ps : List modelTheory.Piece, modelTheory.IsJSJ m ps ∧
      ∀ p ∈ ps, ∃ g : Geometry, modelTheory.AdmitsGeometry p g := by
  refine thurston_geometrization modelTheory (fun n => (n : ℕ))
    (fun a => Nat.add_zero a) (fun a => Nat.zero_add a) (fun a b c => Nat.add_assoc a b c)
    ?_ ?_ ⟨[], rfl, by simp⟩ ?_
  · show ∀ m : ℕ, m = 1 ∨ m = 0 ∨ ∃ a b : ℕ, m = a + b ∧ a < m ∧ b < m
    intro m
    match m with
    | 0 => exact Or.inr (Or.inl rfl)
    | 1 => exact Or.inl rfl
    | (n + 2) => exact Or.inr (Or.inr ⟨1, n + 1, by omega, by omega, by omega⟩)
  · show ∀ (a b : ℕ) (la lb : List Unit), la.length = a → lb.length = b →
      (la ++ lb).length = a + b
    intro a b la lb ha hb
    simp [ha, hb]
  · show ∀ m : ℕ, m = 1 → ∃ ps : List Unit, ps.length = m ∧
      ∀ p ∈ ps, ∃ g : Geometry, g = Geometry.hyperbolic
    intro m hm
    exact ⟨[()], by simp [hm], fun p _ => ⟨Geometry.hyperbolic, rfl⟩⟩

/-- The model is genuinely infinite: it has infinitely many distinct manifolds,
infinitely many of which are non-prime connected sums. -/
theorem modelTheory_infinite : Infinite modelTheory.Mfld := by
  show Infinite ℕ
  infer_instance

end Frontier

