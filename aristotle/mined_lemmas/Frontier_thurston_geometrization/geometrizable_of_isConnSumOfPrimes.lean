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
