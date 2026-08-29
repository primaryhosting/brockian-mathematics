import Mathlib

/-!
# Iit Phi Partition
Category: Frontier Mind
Target: Frontier.iit_phi_partition
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

set_option pp.fullNames false
set_option pp.structureInstances true
set_option pp.coercions.types true
set_option pp.funBinderTypes true
set_option pp.letVarTypes true
set_option pp.piBinderTypes true

set_option grind.warning false

namespace Frontier

/-!
## Setting

A *system* consists of a finite set `V` of elements, each of which can be in one of
finitely many states `S`; a global state of the system is a function `V → S`.

The dynamics of the system are given by a transition kernel
`T : (V → S) → (V → S) → ℝ`, where `T s t` is the probability of moving to state `t`
from state `s`.

A *bipartition* of the system is a map `p : V → Bool` which is neither constantly
`true` nor constantly `false`; the two parts are `{v // p v = true}` and
`{v // p v = false}`.

The *effective information* of a bipartition `p` measures how far the dynamics is
from being the product of the dynamics of the two parts taken separately: it is the
(weighted) average over current states `s` of the `ℓ¹`-distance between the true
next-state distribution `T s ·` and the product of its two marginals on the parts.

*Integrated information* `Φ` is the infimum of the effective information over all
bipartitions ("the minimum information partition").

The target theorem states that a system which is *disconnected*, i.e. whose state
space splits into two nonempty parts that evolve independently of one another,
has `Φ = 0`.
-/

section Defs

variable {V S : Type*}

/-- Restriction of a global state `t : V → S` to the part `{v // p v = b}` of the
bipartition `p`. -/
def restrictPart (p : V → Bool) (b : Bool) (t : V → S) : {v // p v = b} → S :=
  fun v => t v.1

/-- Assemble a global state from states of the two parts of the bipartition `p`. -/
def combineParts (p : V → Bool) (x : {v // p v = true} → S) (y : {v // p v = false} → S) :
    V → S :=
  fun v => if h : p v = true then x ⟨v, h⟩ else y ⟨v, by simpa using h⟩

@[simp] lemma restrictPart_true_combineParts (p : V → Bool) (x : {v // p v = true} → S)
    (y : {v // p v = false} → S) : restrictPart p true (combineParts p x y) = x := by
  funext v
  simp [restrictPart, combineParts, v.2]

@[simp] lemma restrictPart_false_combineParts (p : V → Bool) (x : {v // p v = true} → S)
    (y : {v // p v = false} → S) : restrictPart p false (combineParts p x y) = y := by
  funext v
  have hv : ¬ (p v.1 = true) := by simp [v.2]
  simp [restrictPart, combineParts, hv]

@[simp] lemma combineParts_restrictPart (p : V → Bool) (t : V → S) :
    combineParts p (restrictPart p true t) (restrictPart p false t) = t := by
  funext v
  by_cases h : p v = true <;> simp [restrictPart, combineParts, h]

variable [Fintype V] [Fintype S]

/-- The marginal, on the part `{v // p v = b}`, of the next-state distribution
`T s ·`: the probability that the part `b` of the next state equals `x`. -/
noncomputable def marginalPart (T : (V → S) → (V → S) → ℝ) (p : V → Bool) (b : Bool)
    (s : V → S) (x : {v // p v = b} → S) : ℝ :=
  ∑ t ∈ Finset.univ.filter (fun t : V → S => restrictPart p b t = x), T s t

/-- `p` is a bipartition of the system: both parts are nonempty. -/
def IsBipartition (p : V → Bool) : Prop := (∃ v, p v = true) ∧ (∃ v, p v = false)

/-- The effective information of the bipartition `p`: the `w`-average over current
states `s` of the `ℓ¹`-distance between the actual next-state distribution and the
product of the two marginal distributions on the parts of `p`. -/
noncomputable def effectiveInfo (w : (V → S) → ℝ) (T : (V → S) → (V → S) → ℝ)
    (p : V → Bool) : ℝ :=
  ∑ s : V → S, w s *
    ∑ t : V → S, |T s t -
      marginalPart T p true s (restrictPart p true t) *
        marginalPart T p false s (restrictPart p false t)|

/-- Integrated information `Φ`: the minimum, over all bipartitions, of the effective
information. -/
noncomputable def phi (w : (V → S) → ℝ) (T : (V → S) → (V → S) → ℝ) : ℝ :=
  sInf {r : ℝ | ∃ p : V → Bool, IsBipartition p ∧ r = effectiveInfo w T p}

/-- The system `T` is *disconnected along `p`*: `p` is a bipartition, and the dynamics
factors as a product of two independent kernels, one acting on each part. -/
structure Disconnected (T : (V → S) → (V → S) → ℝ) (p : V → Bool) : Prop where
  isBipartition : IsBipartition p
  factors : ∃ f : ({v // p v = true} → S) → ({v // p v = true} → S) → ℝ,
      ∃ g : ({v // p v = false} → S) → ({v // p v = false} → S) → ℝ,
        (∀ a, ∑ x, f a x = 1) ∧ (∀ b, ∑ y, g b y = 1) ∧
          ∀ s t : V → S, T s t =
            f (restrictPart p true s) (restrictPart p true t) *
              g (restrictPart p false s) (restrictPart p false t)

end Defs

section Lemmas

variable {V S : Type*} [Fintype V] [Fintype S]

/-- Summing a function of the `false`-part of a state over all states whose `true`-part
is fixed amounts to summing over all states of the `false` part. -/
lemma sum_filter_restrict_true (p : V → Bool) (x : {v // p v = true} → S)
    (h : ({v // p v = false} → S) → ℝ) :
    ∑ t ∈ Finset.univ.filter (fun t : V → S => restrictPart p true t = x),
        h (restrictPart p false t) = ∑ y, h y := by
  refine Finset.sum_nbij' (i := fun t => restrictPart p false t)
    (j := fun y => combineParts p x y) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro b _; simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    show combineParts p x (restrictPart p false a) = a
    rw [← ha.2, combineParts_restrictPart]
  · intro b _; simp
  · intro a _; rfl

/-- Summing a function of the `true`-part of a state over all states whose `false`-part
is fixed amounts to summing over all states of the `true` part. -/
lemma sum_filter_restrict_false (p : V → Bool) (y : {v // p v = false} → S)
    (h : ({v // p v = true} → S) → ℝ) :
    ∑ t ∈ Finset.univ.filter (fun t : V → S => restrictPart p false t = y),
        h (restrictPart p true t) = ∑ x, h x := by
  refine Finset.sum_nbij' (i := fun t => restrictPart p true t)
    (j := fun x => combineParts p x y) ?_ ?_ ?_ ?_ ?_
  · intro a _; exact Finset.mem_univ _
  · intro b _; simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    show combineParts p (restrictPart p true a) y = a
    rw [← ha.2, combineParts_restrictPart]
  · intro b _; simp
  · intro a _; rfl

variable {T : (V → S) → (V → S) → ℝ} {p : V → Bool}

/-- If the dynamics factors along `p`, the marginal on the `true` part is the first
factor. -/
lemma marginalPart_true_of_factors
    {f : ({v // p v = true} → S) → ({v // p v = true} → S) → ℝ}
    {g : ({v // p v = false} → S) → ({v // p v = false} → S) → ℝ}
    (hg : ∀ b, ∑ y, g b y = 1)
    (hT : ∀ s t : V → S, T s t =
      f (restrictPart p true s) (restrictPart p true t) *
        g (restrictPart p false s) (restrictPart p false t))
    (s : V → S) (x : {v // p v = true} → S) :
    marginalPart T p true s x = f (restrictPart p true s) x := by
  have h1 : marginalPart T p true s x
      = ∑ t ∈ Finset.univ.filter (fun t : V → S => restrictPart p true t = x),
          f (restrictPart p true s) x * g (restrictPart p false s) (restrictPart p false t) := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    simp only [Finset.mem_filter] at ht
    rw [hT s t, ht.2]
  rw [h1, ← Finset.mul_sum,
    sum_filter_restrict_true p x (fun y => g (restrictPart p false s) y), hg, mul_one]

/-- If the dynamics factors along `p`, the marginal on the `false` part is the second
factor. -/
lemma marginalPart_false_of_factors
    {f : ({v // p v = true} → S) → ({v // p v = true} → S) → ℝ}
    {g : ({v // p v = false} → S) → ({v // p v = false} → S) → ℝ}
    (hf : ∀ a, ∑ x, f a x = 1)
    (hT : ∀ s t : V → S, T s t =
      f (restrictPart p true s) (restrictPart p true t) *
        g (restrictPart p false s) (restrictPart p false t))
    (s : V → S) (y : {v // p v = false} → S) :
    marginalPart T p false s y = g (restrictPart p false s) y := by
  have h1 : marginalPart T p false s y
      = ∑ t ∈ Finset.univ.filter (fun t : V → S => restrictPart p false t = y),
          f (restrictPart p true s) (restrictPart p true t) * g (restrictPart p false s) y := by
    refine Finset.sum_congr rfl ?_
    intro t ht
    simp only [Finset.mem_filter] at ht
    rw [hT s t, ht.2]
  rw [h1, ← Finset.sum_mul,
    sum_filter_restrict_false p y (fun x => f (restrictPart p true s) x), hf, one_mul]

/-- The effective information of a bipartition along which the dynamics factors is `0`. -/
lemma effectiveInfo_eq_zero_of_disconnected (w : (V → S) → ℝ) (hd : Disconnected T p) :
    effectiveInfo w T p = 0 := by
  obtain ⟨f, g, hf, hg, hT⟩ := hd.factors
  have key : ∀ s t : V → S, T s t -
      marginalPart T p true s (restrictPart p true t) *
        marginalPart T p false s (restrictPart p false t) = 0 := by
    intro s t
    rw [marginalPart_true_of_factors hg hT, marginalPart_false_of_factors hf hT, hT s t, sub_self]
  simp [effectiveInfo, key]

/-- Effective information is nonnegative for any nonnegative weighting of states. -/
lemma effectiveInfo_nonneg {w : (V → S) → ℝ} (hw : ∀ s, 0 ≤ w s) (T : (V → S) → (V → S) → ℝ)
    (p : V → Bool) : 0 ≤ effectiveInfo w T p := by
  refine Finset.sum_nonneg ?_
  intro s _
  exact mul_nonneg (hw s) (Finset.sum_nonneg fun t _ => abs_nonneg _)

/-- Non-vacuity: for any bipartition `p`, the "frozen" dynamics (each state maps to
itself with probability one) is disconnected along `p`, since it acts independently
on the two parts. -/
lemma disconnected_frozen [DecidableEq V] [DecidableEq S] (q : V → Bool)
    (hq : IsBipartition q) :
    Disconnected (fun s t : V → S => if t = s then (1 : ℝ) else 0) q := by
  refine ⟨hq, ⟨fun a x => if x = a then (1 : ℝ) else 0,
    fun b y => if y = b then (1 : ℝ) else 0, ?_, ?_, ?_⟩⟩
  · intro a; simp
  · intro b; simp
  · intro s t
    by_cases h : t = s
    · subst h; simp
    · have h1 : ¬ (restrictPart q true t = restrictPart q true s ∧
          restrictPart q false t = restrictPart q false s) := by
        rintro ⟨ht, hf⟩
        exact h (by rw [← combineParts_restrictPart q t, ht, hf, combineParts_restrictPart])
      rcases not_and_or.mp h1 with h2 | h2 <;> simp [h, h2]

end Lemmas

/-- **Integrated information of a disconnected system vanishes.**

Let a system consist of finitely many elements `V`, each with finitely many possible
states `S`, evolving according to a transition kernel `T` (`T s t` = probability of
the next state being `t` given the current state `s`), and let `w` be any nonnegative
weighting of the current states.

Effective information `effectiveInfo w T p` of a bipartition `p` is the `w`-average
`ℓ¹`-distance between the true next-state distribution and the product of the
next-state marginals of the two parts of `p`, and integrated information
`Φ = phi w T` is the infimum of the effective information over all bipartitions
(the minimum information partition).

If the system is disconnected, i.e. there is a bipartition `p` (both parts nonempty)
along which the dynamics factors into two independent kernels, then `Φ = 0`. -/
theorem iit_phi_partition {V S : Type*} [Fintype V] [Fintype S]
    {w : (V → S) → ℝ} (hw : ∀ s, 0 ≤ w s) {T : (V → S) → (V → S) → ℝ} {p : V → Bool}
    (hd : Disconnected T p) : phi w T = 0 := by
  have hmem : (0 : ℝ) ∈ {r : ℝ | ∃ q : V → Bool, IsBipartition q ∧ r = effectiveInfo w T q} :=
    ⟨p, hd.isBipartition, (effectiveInfo_eq_zero_of_disconnected w hd).symm⟩
  have hlb : ∀ r ∈ {r : ℝ | ∃ q : V → Bool, IsBipartition q ∧ r = effectiveInfo w T q}, 0 ≤ r := by
    rintro r ⟨q, -, rfl⟩
    exact effectiveInfo_nonneg hw T q
  refine le_antisymm ?_ ?_
  · exact csInf_le ⟨0, hlb⟩ hmem
  · exact le_csInf ⟨0, hmem⟩ hlb

/-- A concrete instance of the theorem: a two-element system whose elements never
influence each other has zero integrated information. -/
example : phi (fun _ => (1 : ℝ)) (fun s t : Bool → Bool => if t = s then (1 : ℝ) else 0) = 0 :=
  iit_phi_partition (fun _ => zero_le_one)
    (disconnected_frozen (V := Bool) (S := Bool) id ⟨⟨true, rfl⟩, ⟨false, rfl⟩⟩)

end Frontier

