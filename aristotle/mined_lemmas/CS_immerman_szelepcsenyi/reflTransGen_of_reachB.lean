import Mathlib

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

import Mathlib

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

set_option maxHeartbeats 1000000

namespace CS

/-! ## Reachability in a finite directed graph

We work with a directed graph on the vertex set `{0, 1, ..., n-1}` given by a Boolean
adjacency function `g`.  `reachB n g s i v` says that `v` is reachable from `s` by a walk of
length *at most* `i` (we allow "staying put" at each step, so walks of length exactly `i`
with lazy steps are the same thing as walks of length at most `i`). -/

section Graph

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s : ℕ)

/-- `reachB n g s i v = true` iff `v` is reachable from `s` in at most `i` steps
(inside the vertex set `{0,…,n-1}`). -/

lemma reflTransGen_of_reachB {m v : ℕ} (h : reachB n g s m v = true) :
    Relation.ReflTransGen (fun a b => g a b = true) s v := by
  induction m generalizing v with
  | zero => simp only [reachB_zero, beq_iff_eq] at h; subst h; exact Relation.ReflTransGen.refl
  | succ m ih =>
      obtain ⟨-, u, -, hu, huv⟩ := (reachB_succ_iff m v).1 h
      rcases huv with rfl | huv
      · exact ih hu
      · exact Relation.ReflTransGen.tail (ih hu) huv

end Graph

/-! ## The Immerman-Szelepcsenyi machine

The configurations below are those of the nondeterministic *inductive counting* machine.
All the numeric components of a configuration stay bounded by `n + 1`, so the machine has only
polynomially many (in `n`) reachable configurations, i.e. it runs in space `O(log n)`; each
transition inspects the graph in at most one place.  The machine accepts (i.e. `St.acc` is
reachable from the initial configuration) if and only if `t` is *not* reachable from `s`.
This is exactly the Immerman-Szelepcsenyi theorem `NL = coNL`, since `s-t` reachability is
`NL`-complete and the configuration graph of an arbitrary `NL` machine is a graph of this kind. -/

/-- Configurations of the Immerman-Szelepcsenyi machine.

* `levelStart i c`: the count `c = |R_i|` of vertices reachable in `≤ i` steps has been
  established; start working on level `i + 1`.
* `outer i c d j`: computing `|R_{i+1}|`; vertices `< j` have been processed and `d` of them
  were found in `R_{i+1}`.
* `walkYes i c d j w r`: certifying `j ∈ R_{i+1}` by guessing a walk; currently at vertex `w`
  with `r` steps to go.
* `inner i c d j u e`: certifying `j ∉ R_{i+1}`; scanning candidate members `u` of `R_i`, of
  which `e` have been certified so far (all of them different from `j` and non-adjacent to `j`).
* `walkIn i c d j u e w r`: certifying `u ∈ R_i` by guessing a walk.
* `acc`: the accepting configuration. -/
inductive St where
  | levelStart (i c : ℕ)
  | outer (i c d j : ℕ)
  | walkYes (i c d j w r : ℕ)
  | inner (i c d j u e : ℕ)
  | walkIn (i c d j u e w r : ℕ)
  | acc
  deriving DecidableEq

section Machine

variable (n : ℕ) (g : ℕ → ℕ → Bool) (s t : ℕ)

/-- The transition relation of the machine.  Every transition is a local test:
comparing two numbers `< n + 2`, or a single query to the adjacency function `g`. -/
inductive Step : St → St → Prop
  | startLevel {i c : ℕ} (h : i < n) : Step (.levelStart i c) (.outer i c 0 0)
  | startFinal {c : ℕ} : Step (.levelStart n c) (.inner n c 0 t 0 0)
  | outerYes {i c d j : ℕ} (h : j < n) : Step (.outer i c d j) (.walkYes i c d j s (i + 1))
  | outerNo {i c d j : ℕ} (h : j < n) : Step (.outer i c d j) (.inner i c d j 0 0)
  | outerDone {i c d : ℕ} : Step (.outer i c d n) (.levelStart (i + 1) d)
  | walkYesStep {i c d j w r w' : ℕ} (h : w' < n) (hg : w = w' ∨ g w w' = true) :
      Step (.walkYes i c d j w (r + 1)) (.walkYes i c d j w' r)
  | walkYesDone {i c d j w : ℕ} (hw : w = j) :
      Step (.walkYes i c d j w 0) (.outer i c (d + 1) (j + 1))
  | innerSkip {i c d j u e : ℕ} (h : u < n) : Step (.inner i c d j u e) (.inner i c d j (u + 1) e)
  | innerCert {i c d j u e : ℕ} (h : u < n) : Step (.inner i c d j u e) (.walkIn i c d j u e s i)
  | walkInStep {i c d j u e w r w' : ℕ} (h : w' < n) (hg : w = w' ∨ g w w' = true) :
      Step (.walkIn i c d j u e w (r + 1)) (.walkIn i c d j u e w' r)
  | walkInDone {i c d j u e w : ℕ} (hw : w = u) (hne : u ≠ j) (hgj : g u j = false) :
      Step (.walkIn i c d j u e w 0) (.inner i c d j (u + 1) (e + 1))
  | innerDone {i c d j e : ℕ} (h : i < n) (he : e = c) :
      Step (.inner i c d j n e) (.outer i c d (j + 1))
  | innerAccept {c d j e : ℕ} (he : e = c) : Step (.inner n c d j n e) .acc

/-- The initial configuration: `|R_0| = 1`. -/
