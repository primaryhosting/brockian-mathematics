import Mathlib

/-!
# Jones Polynomial Invariant
Category: Frontier — Fields Medal Work
Target: Frontier.jones_polynomial_invariant
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

We formalise Kauffman's state-sum model of the Kauffman bracket and the resulting
Jones polynomial, and prove that the writhe-normalised bracket is invariant under the
three Reidemeister moves.

A *link diagram* is recorded by the combinatorial data that the state sum needs: a finite
set `Fin m` of crossings, and, for every *state* `s : Fin m → Bool` (a choice of an `A`- or
`B`-smoothing at each crossing), the number `loops s` of closed curves in the completely
smoothed diagram.  The Kauffman bracket is then

`⟨D⟩ = ∑_s A^(#A-smoothings - #B-smoothings) · δ^(loops s - 1)`,  `δ = -A² - A⁻²`,

with values in the ring `ℤ[A, A⁻¹]` of Laurent polynomials.

The Reidemeister moves are encoded as relations between such data: each move is a purely
local modification of a diagram, and its effect on the state sum is exactly a statement
about how the loop counts of the diagrams before and after the move are related.  These
loop-count relations are the (planar, geometric) input to Kauffman's argument, and they
are what the constructors of `Frontier.Move` below record.
-/

/-- The coefficient ring `ℤ[A, A⁻¹]` of the Kauffman bracket. -/
abbrev Lau := LaurentPolynomial ℤ

/-- The monomial `A ^ n` inside `ℤ[A, A⁻¹]`. -/
noncomputable def Amon (n : ℤ) : Lau := LaurentPolynomial.T n

@[simp] lemma Amon_zero : Amon 0 = 1 := LaurentPolynomial.T_zero

lemma Amon_add (a b : ℤ) : Amon (a + b) = Amon a * Amon b := LaurentPolynomial.T_add a b

lemma Amon_mul (a b : ℤ) : Amon a * Amon b = Amon (a + b) := (Amon_add a b).symm

/-- The loop value `δ = -A² - A⁻²` of the Kauffman bracket. -/
noncomputable def delta : Lau := -Amon 2 - Amon (-2)

/-- Combinatorial data of a link diagram, as used by the Kauffman state sum:
`n` crossings, and for each state (a smoothing choice at every crossing) the number of
closed loops of the resulting crossingless diagram. -/
structure Dgm where
  /-- number of crossings -/
  n : ℕ
  /-- number of loops of the diagram obtained by smoothing according to a state -/
  loops : (Fin n → Bool) → ℕ
  /-- a smoothed diagram always contains at least one loop -/
  loops_pos : ∀ s, 0 < loops s

/-- The exponent `#{A-smoothings} - #{B-smoothings}` attached to a state. -/
def stateExp {m : ℕ} (s : Fin m → Bool) : ℤ := ∑ i, if s i then (1 : ℤ) else -1

/-- The Kauffman bracket state sum of a loop-count function. -/
noncomputable def br {m : ℕ} (L : (Fin m → Bool) → ℕ) : Lau :=
  ∑ s : Fin m → Bool, Amon (stateExp s) * delta ^ (L s - 1)

/-- The Kauffman bracket of a diagram. -/
noncomputable def bracket (D : Dgm) : Lau := br D.loops

/-- The unknot diagram: no crossings, one loop. -/
def unknot : Dgm := ⟨0, fun _ => 1, fun _ => Nat.one_pos⟩

/-- `-A³`, as a unit of `ℤ[A, A⁻¹]`; this is the factor by which the Kauffman bracket
changes under a Reidemeister move of type I. -/
noncomputable def negA3 : Lauˣ where
  val := -Amon 3
  inv := -Amon (-3)
  val_inv := by rw [neg_mul_neg, Amon_mul]; norm_num
  inv_val := by rw [neg_mul_neg, Amon_mul]; norm_num

/-- The Jones polynomial (in Kauffman's normalisation) of a diagram with writhe `w`:
`(-A³)^(-w) ⟨D⟩`. -/
noncomputable def jones (D : Dgm) (w : ℤ) : Lau := ((negA3 ^ (-w) : Lauˣ) : Lau) * bracket D

/-- Reidemeister moves, recorded through their effect on the state-sum data.

In each constructor the distinguished crossing(s) involved in the move are the first
one(s), and `L`, `U`, `V`, `V'` are the loop-count functions of the diagrams obtained
locally after the move; the hypotheses say how the loop counts of the smoothings of the
distinguished crossings are expressed through them. The second and fourth arguments are
the writhes of the two diagrams. -/
inductive Move : Dgm → ℤ → Dgm → ℤ → Prop where
  /-- Reidemeister I, positive kink: smoothing the kink one way creates an extra loop,
  the other way removes the kink; the writhe drops by one. -/
  | r1pos {m : ℕ} (w : ℤ) (L : (Fin m → Bool) → ℕ) (hL : ∀ s, 0 < L s)
      (f : (Fin (m + 1) → Bool) → ℕ) (hf : ∀ s, 0 < f s)
      (htrue : ∀ s, f (Fin.cons true s) = L s + 1)
      (hfalse : ∀ s, f (Fin.cons false s) = L s) :
      Move ⟨m + 1, f, hf⟩ (w + 1) ⟨m, L, hL⟩ w
  /-- Reidemeister I, negative kink. -/
  | r1neg {m : ℕ} (w : ℤ) (L : (Fin m → Bool) → ℕ) (hL : ∀ s, 0 < L s)
      (f : (Fin (m + 1) → Bool) → ℕ) (hf : ∀ s, 0 < f s)
      (htrue : ∀ s, f (Fin.cons true s) = L s)
      (hfalse : ∀ s, f (Fin.cons false s) = L s + 1) :
      Move ⟨m + 1, f, hf⟩ (w - 1) ⟨m, L, hL⟩ w
  /-- Reidemeister II: two crossings of opposite sign are removed; the writhe is unchanged.
  Of the four smoothings of the two crossings, one gives the diagram `U` obtained after the
  move, two give the other local resolution `V`, and the remaining one gives `V` with an
  extra closed loop. -/
  | r2 {m : ℕ} (w : ℤ) (U V : (Fin m → Bool) → ℕ) (hU : ∀ s, 0 < U s) (hV : ∀ s, 0 < V s)
      (f : (Fin (m + 2) → Bool) → ℕ) (hf : ∀ s, 0 < f s)
      (hTT : ∀ s, f (Fin.cons true (Fin.cons true s)) = V s)
      (hTF : ∀ s, f (Fin.cons true (Fin.cons false s)) = V s + 1)
      (hFT : ∀ s, f (Fin.cons false (Fin.cons true s)) = U s)
      (hFF : ∀ s, f (Fin.cons false (Fin.cons false s)) = V s) :
      Move ⟨m + 2, f, hf⟩ w ⟨m, U, hU⟩ w
  /-- Reidemeister III: the two diagrams `f` and `g` agree after smoothing the distinguished
  crossing one way (the resulting diagrams are planar isotopic), and after smoothing it the
  other way both contain a Reidemeister II pair reducing to the same diagram `U`.
  The writhe is unchanged. -/
  | r3 {m : ℕ} (w : ℤ) (U V V' : (Fin m → Bool) → ℕ)
      (hU : ∀ s, 0 < U s) (hV : ∀ s, 0 < V s) (hV' : ∀ s, 0 < V' s)
      (f g : (Fin (m + 3) → Bool) → ℕ) (hf : ∀ s, 0 < f s) (hg : ∀ s, 0 < g s)
      (hiso : ∀ s, f (Fin.cons true s) = g (Fin.cons true s))
      (hfTT : ∀ s, f (Fin.cons false (Fin.cons true (Fin.cons true s))) = V s)
      (hfTF : ∀ s, f (Fin.cons false (Fin.cons true (Fin.cons false s))) = V s + 1)
      (hfFT : ∀ s, f (Fin.cons false (Fin.cons false (Fin.cons true s))) = U s)
      (hfFF : ∀ s, f (Fin.cons false (Fin.cons false (Fin.cons false s))) = V s)
      (hgTT : ∀ s, g (Fin.cons false (Fin.cons true (Fin.cons true s))) = V' s)
      (hgTF : ∀ s, g (Fin.cons false (Fin.cons true (Fin.cons false s))) = V' s + 1)
      (hgFT : ∀ s, g (Fin.cons false (Fin.cons false (Fin.cons true s))) = U s)
      (hgFF : ∀ s, g (Fin.cons false (Fin.cons false (Fin.cons false s))) = V' s) :
      Move ⟨m + 3, f, hf⟩ w ⟨m + 3, g, hg⟩ w
  /-- Planar isotopy: diagrams with the same state sum data. -/
  | refl (D : Dgm) (w : ℤ) : Move D w D w
  | symm {D E : Dgm} {w v : ℤ} : Move D w E v → Move E v D w
  | trans {D E F : Dgm} {w v u : ℤ} : Move D w E v → Move E v F u → Move D w F u

/-! ## Basic computations -/

lemma stateExp_cons {m : ℕ} (b : Bool) (s : Fin m → Bool) :
    stateExp (Fin.cons b s) = (if b then (1 : ℤ) else -1) + stateExp s := by
  simp [stateExp, Fin.sum_univ_succ]

lemma sum_bool_cons {m : ℕ} (F : (Fin (m + 1) → Bool) → Lau) :
    ∑ s : Fin (m + 1) → Bool, F s
      = ∑ s : Fin m → Bool, (F (Fin.cons true s) + F (Fin.cons false s)) := by
  rw [← Equiv.sum_comp (Fin.consEquiv (fun _ : Fin (m + 1) => Bool)) F, Fintype.sum_prod_type]
  simp [Fin.consEquiv, Finset.sum_add_distrib, add_comm]

/-- Expansion of the state sum at the first crossing: the Kauffman skein relation. -/
lemma br_expand {m : ℕ} (f : (Fin (m + 1) → Bool) → ℕ) :
    br f = Amon 1 * br (fun s => f (Fin.cons true s))
      + Amon (-1) * br (fun s => f (Fin.cons false s)) := by
  rw [br, sum_bool_cons, br, br, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun s _ => ?_)
  rw [stateExp_cons, stateExp_cons]
  simp only [if_true, Bool.false_eq_true, if_false, Amon_add]
  ring

@[simp] lemma bracket_unknot : bracket unknot = 1 := by
  simp [bracket, unknot, br, stateExp]

/-- An extra closed loop multiplies the state sum by `δ`. -/
lemma delta_pow_add_one {x : ℕ} (hx : 0 < x) : delta ^ (x + 1 - 1) = delta * delta ^ (x - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hx.ne'
  simp [pow_succ, mul_comm]

/-- Two state sums whose loop counts agree termwise coincide. -/
lemma br_congr {m : ℕ} {L L' : (Fin m → Bool) → ℕ} (h : ∀ s, L s = L' s) : br L = br L' := by
  simp only [br]
  exact Finset.sum_congr rfl fun s _ => by rw [h s]

/-- Adding one loop to every smoothing multiplies the state sum by `δ`. -/
lemma br_add_loop {m : ℕ} {L L' : (Fin m → Bool) → ℕ} (hL : ∀ s, 0 < L s)
    (h : ∀ s, L' s = L s + 1) : br L' = delta * br L := by
  simp only [br, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [h s, delta_pow_add_one (hL s)]
  ring

/-! ## Effect of the moves on the Kauffman bracket -/

lemma kauffman_r1pos_coeff : Amon 1 * delta + Amon (-1) = -Amon 3 := by
  rw [delta, mul_sub, mul_neg, Amon_mul, Amon_mul]
  norm_num

lemma kauffman_r1neg_coeff : Amon 1 + Amon (-1) * delta = -Amon (-3) := by
  rw [delta, mul_sub, mul_neg, Amon_mul, Amon_mul]
  norm_num
  ring

lemma kauffman_r2_coeff :
    Amon 1 * Amon 1 + Amon 1 * (Amon (-1) * delta) + Amon (-1) * Amon (-1) = 0 := by
  have e1 : Amon 1 * Amon 1 = Amon 2 := by rw [Amon_mul]; norm_num
  have e2 : Amon (-1) * Amon (-1) = Amon (-2) := by rw [Amon_mul]; norm_num
  have e3 : Amon 1 * Amon (-1) = 1 := by rw [Amon_mul]; norm_num
  rw [delta, ← mul_assoc, e3, e1, e2, one_mul]
  ring

lemma br_r1pos {m : ℕ} (L : (Fin m → Bool) → ℕ) (hL : ∀ s, 0 < L s)
    (f : (Fin (m + 1) → Bool) → ℕ)
    (htrue : ∀ s, f (Fin.cons true s) = L s + 1)
    (hfalse : ∀ s, f (Fin.cons false s) = L s) :
    br f = (-Amon 3) * br L := by
  rw [br_expand f, br_add_loop hL htrue, br_congr hfalse, ← kauffman_r1pos_coeff]
  ring

lemma br_r1neg {m : ℕ} (L : (Fin m → Bool) → ℕ) (hL : ∀ s, 0 < L s)
    (f : (Fin (m + 1) → Bool) → ℕ)
    (htrue : ∀ s, f (Fin.cons true s) = L s)
    (hfalse : ∀ s, f (Fin.cons false s) = L s + 1) :
    br f = (-Amon (-3)) * br L := by
  rw [br_expand f, br_add_loop hL hfalse, br_congr htrue, ← kauffman_r1neg_coeff]
  ring

lemma br_r2 {m : ℕ} (U V : (Fin m → Bool) → ℕ) (hV : ∀ s, 0 < V s)
    (f : (Fin (m + 2) → Bool) → ℕ)
    (hTT : ∀ s, f (Fin.cons true (Fin.cons true s)) = V s)
    (hTF : ∀ s, f (Fin.cons true (Fin.cons false s)) = V s + 1)
    (hFT : ∀ s, f (Fin.cons false (Fin.cons true s)) = U s)
    (hFF : ∀ s, f (Fin.cons false (Fin.cons false s)) = V s) :
    br f = br U := by
  rw [br_expand f, br_expand (fun s => f (Fin.cons true s)),
    br_expand (fun s => f (Fin.cons false s))]
  rw [br_congr hTT, br_add_loop hV hTF, br_congr hFT, br_congr hFF]
  have h0 : Amon 1 * Amon 1 * br V + Amon 1 * (Amon (-1) * delta) * br V
      + Amon (-1) * Amon (-1) * br V = 0 := by
    rw [← add_mul, ← add_mul, kauffman_r2_coeff, zero_mul]
  have h1 : Amon (-1) * Amon 1 = 1 := by rw [Amon_mul]; norm_num
  calc Amon 1 * (Amon 1 * br V + Amon (-1) * (delta * br V))
        + Amon (-1) * (Amon 1 * br U + Amon (-1) * br V)
      = (Amon 1 * Amon 1 * br V + Amon 1 * (Amon (-1) * delta) * br V
        + Amon (-1) * Amon (-1) * br V) + (Amon (-1) * Amon 1) * br U := by ring
    _ = br U := by rw [h0, h1]; ring

lemma br_r3 {m : ℕ} (U V V' : (Fin m → Bool) → ℕ) (hV : ∀ s, 0 < V s) (hV' : ∀ s, 0 < V' s)
    (f g : (Fin (m + 3) → Bool) → ℕ)
    (hiso : ∀ s, f (Fin.cons true s) = g (Fin.cons true s))
    (hfTT : ∀ s, f (Fin.cons false (Fin.cons true (Fin.cons true s))) = V s)
    (hfTF : ∀ s, f (Fin.cons false (Fin.cons true (Fin.cons false s))) = V s + 1)
    (hfFT : ∀ s, f (Fin.cons false (Fin.cons false (Fin.cons true s))) = U s)
    (hfFF : ∀ s, f (Fin.cons false (Fin.cons false (Fin.cons false s))) = V s)
    (hgTT : ∀ s, g (Fin.cons false (Fin.cons true (Fin.cons true s))) = V' s)
    (hgTF : ∀ s, g (Fin.cons false (Fin.cons true (Fin.cons false s))) = V' s + 1)
    (hgFT : ∀ s, g (Fin.cons false (Fin.cons false (Fin.cons true s))) = U s)
    (hgFF : ∀ s, g (Fin.cons false (Fin.cons false (Fin.cons false s))) = V' s) :
    br f = br g := by
  rw [br_expand f, br_expand g, br_congr hiso,
    br_r2 U V hV (fun s => f (Fin.cons false s)) hfTT hfTF hfFT hfFF,
    br_r2 U V' hV' (fun s => g (Fin.cons false s)) hgTT hgTF hgFT hgFF]

/-! ## Behaviour of the normalisation factor -/

lemma negA3_val : ((negA3 : Lauˣ) : Lau) = -Amon 3 := rfl

lemma negA3_inv_val : ((negA3⁻¹ : Lauˣ) : Lau) = -Amon (-3) := rfl

lemma negA3_zpow_succ (w : ℤ) :
    ((negA3 ^ (-(w + 1)) : Lauˣ) : Lau) * (-Amon 3) = ((negA3 ^ (-w) : Lauˣ) : Lau) := by
  have h : (negA3 ^ (-(w + 1)) * negA3 : Lauˣ) = negA3 ^ (-w) := by
    rw [← zpow_add_one]
    congr 1
    ring
  calc ((negA3 ^ (-(w + 1)) : Lauˣ) : Lau) * (-Amon 3)
      = ((negA3 ^ (-(w + 1)) * negA3 : Lauˣ) : Lau) := by rw [Units.val_mul, negA3_val]
    _ = ((negA3 ^ (-w) : Lauˣ) : Lau) := by rw [h]

lemma negA3_zpow_pred (w : ℤ) :
    ((negA3 ^ (-(w - 1)) : Lauˣ) : Lau) * (-Amon (-3)) = ((negA3 ^ (-w) : Lauˣ) : Lau) := by
  have h : (negA3 ^ (-(w - 1)) * negA3⁻¹ : Lauˣ) = negA3 ^ (-w) := by
    rw [← zpow_neg_one, ← zpow_add]
    congr 1
    ring
  calc ((negA3 ^ (-(w - 1)) : Lauˣ) : Lau) * (-Amon (-3))
      = ((negA3 ^ (-(w - 1)) * negA3⁻¹ : Lauˣ) : Lau) := by
        rw [Units.val_mul, negA3_inv_val]
    _ = ((negA3 ^ (-w) : Lauˣ) : Lau) := by rw [h]

/-! ## Main theorem -/

/-- **The Jones polynomial is a link invariant**: the writhe-normalised Kauffman bracket
`(-A³)^(-w) ⟨D⟩` is unchanged by all three Reidemeister moves (and hence by any finite
sequence of them). -/
theorem jones_polynomial_invariant {D E : Dgm} {w v : ℤ} (h : Move D w E v) :
    jones D w = jones E v := by
  induction h with
  | r1pos w L hL f hf htrue hfalse =>
      simp only [jones, bracket]
      rw [br_r1pos L hL f htrue hfalse, ← mul_assoc, negA3_zpow_succ]
  | r1neg w L hL f hf htrue hfalse =>
      simp only [jones, bracket]
      rw [br_r1neg L hL f htrue hfalse, ← mul_assoc, negA3_zpow_pred]
  | r2 w U V hU hV f hf hTT hTF hFT hFF =>
      simp only [jones, bracket]
      rw [br_r2 U V hV f hTT hTF hFT hFF]
  | r3 w U V V' hU hV hV' f g hf hg hiso hfTT hfTF hfFT hfFF hgTT hgTF hgFT hgFF =>
      simp only [jones, bracket]
      rw [br_r3 U V V' hV hV' f g hiso hfTT hfTF hfFT hfFF hgTT hgTF hgFT hgFF]
  | refl D w => rfl
  | symm _ ih => exact ih.symm
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂

/-- The Jones polynomial of the unknot (writhe `0`) is `1`. -/
@[simp] lemma jones_unknot : jones unknot 0 = 1 := by
  simp [jones, negA3]

/-! ## Concrete instances

The following examples show that the data recorded by `Frontier.Dgm` and the hypotheses of
the constructors of `Frontier.Move` are satisfied by genuine link diagrams, so that the main
theorem is not vacuous.
-/

lemma br_zero (L : (Fin 0 → Bool) → ℕ) (c : Fin 0 → Bool) : br L = delta ^ (L c - 1) := by
  have key : ∀ d : Fin 0 → Bool, Amon (stateExp d) * delta ^ (L d - 1) = delta ^ (L c - 1) := by
    intro d
    have hd : d = c := funext fun i => i.elim0
    subst hd
    simp [stateExp, Amon]
  rw [br, Finset.sum_congr rfl (fun d _ => key d)]
  simp

/-- The standard diagram of the unknot with one positive kink: one crossing, and the two
smoothings have two, resp. one, loops. -/
def kink : Dgm where
  n := 1
  loops := fun s => if s 0 then 2 else 1
  loops_pos := by intro s; split <;> norm_num

/-- Removing the kink is a Reidemeister I move. -/
lemma move_kink_unknot : Move kink 1 unknot 0 := by
  have h : Move ⟨0 + 1, kink.loops, kink.loops_pos⟩ (0 + 1)
      ⟨0, unknot.loops, unknot.loops_pos⟩ 0 := by
    refine Move.r1pos 0 unknot.loops unknot.loops_pos kink.loops kink.loops_pos ?_ ?_ <;>
      intro s <;> simp [kink, unknot]
  simpa using h

/-- The Kauffman bracket of the kinked unknot is `-A³`, but its Jones polynomial is that of
the unknot, namely `1`. -/
example : jones kink 1 = 1 := by
  rw [jones_polynomial_invariant move_kink_unknot, jones_unknot]

/-- The standard two-crossing diagram of the Hopf link: the two "equal" states have two
loops, the two "unequal" states have one. -/
def hopf : Dgm where
  n := 2
  loops := fun s => if s 0 = s 1 then 2 else 1
  loops_pos := by intro s; split <;> norm_num

/-- The Kauffman bracket of the Hopf link diagram is `-A⁴ - A⁻⁴`. -/
lemma bracket_hopf : bracket hopf = -Amon 4 - Amon (-4) := by
  rw [bracket, show hopf.loops = fun s : Fin 2 → Bool => if s 0 = s 1 then 2 else 1 from rfl,
    br_expand, br_expand, br_expand]
  rw [br_zero _ (fun _ => false), br_zero _ (fun _ => false), br_zero _ (fun _ => false),
    br_zero _ (fun _ => false)]
  norm_num
  rw [kauffman_r1pos_coeff, kauffman_r1neg_coeff, mul_neg, mul_neg, Amon_mul, Amon_mul]
  norm_num
  ring


/-- The loop-count data of a diagram exhibiting the Reidemeister II pattern over the local
diagrams `U` (the result of the move) and `V` (the other local resolution). -/
def r2Data {m : ℕ} (U V : (Fin m → Bool) → ℕ) : (Fin (m + 2) → Bool) → ℕ := fun s =>
  if s 0 then
    (if Fin.tail s 0 then V (Fin.tail (Fin.tail s)) else V (Fin.tail (Fin.tail s)) + 1)
  else
    (if Fin.tail s 0 then U (Fin.tail (Fin.tail s)) else V (Fin.tail (Fin.tail s)))

lemma r2Data_pos {m : ℕ} (U V : (Fin m → Bool) → ℕ) (hU : ∀ s, 0 < U s) (hV : ∀ s, 0 < V s) :
    ∀ s, 0 < r2Data U V s := by
  intro s
  unfold r2Data
  split <;> split
  · exact hV _
  · exact Nat.succ_pos _
  · exact hU _
  · exact hV _

/-- Every pair of local diagrams `U`, `V` is realised by a Reidemeister II move: the
hypotheses of the constructor `Frontier.Move.r2` are satisfiable. -/
lemma move_r2 {m : ℕ} (w : ℤ) (U V : (Fin m → Bool) → ℕ) (hU : ∀ s, 0 < U s)
    (hV : ∀ s, 0 < V s) :
    Move ⟨m + 2, r2Data U V, r2Data_pos U V hU hV⟩ w ⟨m, U, hU⟩ w := by
  refine Move.r2 w U V hU hV (r2Data U V) (r2Data_pos U V hU hV) ?_ ?_ ?_ ?_ <;>
    intro t <;> simp [r2Data]

/-- The loop-count data of a diagram exhibiting the Reidemeister III pattern: smoothing the
distinguished crossing with `true` gives the diagram `h`, smoothing it with `false` gives a
diagram containing a Reidemeister II pair over `U` and `V`. -/
def r3Data {m : ℕ} (h : (Fin (m + 2) → Bool) → ℕ) (U V : (Fin m → Bool) → ℕ) :
    (Fin (m + 3) → Bool) → ℕ := fun s =>
  if s 0 then h (Fin.tail s) else r2Data U V (Fin.tail s)

lemma r3Data_pos {m : ℕ} (h : (Fin (m + 2) → Bool) → ℕ) (hh : ∀ s, 0 < h s)
    (U V : (Fin m → Bool) → ℕ) (hU : ∀ s, 0 < U s) (hV : ∀ s, 0 < V s) :
    ∀ s, 0 < r3Data h U V s := by
  intro s
  unfold r3Data
  split
  · exact hh _
  · exact r2Data_pos U V hU hV _

/-- The Reidemeister III pattern is satisfiable, with genuinely different local resolutions
`V`, `V'` on the two sides of the move: the hypotheses of `Frontier.Move.r3` are consistent. -/
lemma move_r3 {m : ℕ} (w : ℤ) (h : (Fin (m + 2) → Bool) → ℕ) (hh : ∀ s, 0 < h s)
    (U V V' : (Fin m → Bool) → ℕ) (hU : ∀ s, 0 < U s) (hV : ∀ s, 0 < V s)
    (hV' : ∀ s, 0 < V' s) :
    Move ⟨m + 3, r3Data h U V, r3Data_pos h hh U V hU hV⟩ w
      ⟨m + 3, r3Data h U V', r3Data_pos h hh U V' hU hV'⟩ w := by
  refine Move.r3 w U V V' hU hV hV' (r3Data h U V) (r3Data h U V')
    (r3Data_pos h hh U V hU hV) (r3Data_pos h hh U V' hU hV')
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
      intro t <;> simp [r3Data, r2Data]

end Frontier

