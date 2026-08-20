import RequestProject.ISMachine

/-!
# Completeness of the counting machine

If `t` is not reachable from `s`, then the counting machine has an accepting computation:
all the guesses it has to make are correct guesses, and all the certificates it has to
produce do exist.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

lemma val_zero' (m : ℕ) : ((0 : Fin (m + 2)) : ℕ) = 0 := by simp

lemma val_one' (m : ℕ) : ((1 : Fin (m + 2)) : ℕ) = 1 := by simp [Nat.mod_eq_of_lt]

variable {n m : ℕ} (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool)

/-! ### The individual transitions -/

lemma stepT1 (i c j c' : Fin (m + 2)) (hj : (j : ℕ) = 0) (hc' : (c' : ℕ) = 0) :
    (cmach r s t).Step x (St.lvl i c) (St.outer i c j c') := by
  show (E r s t (St.lvl i c) (St.outer i c j c')).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, hj, hc'⟩]
  trivial

lemma stepT5' (i c j c' jj d : Fin (m + 2)) (hj : (j : ℕ) = 0) (hc' : (c' : ℕ) = 0)
    (hjj : (jj : ℕ) = 0) (hd : (d : ℕ) = 0) :
    (cmach r s t).Step x (St.lvl i c) (St.no i c j c' t jj d) := by
  show (E r s t (St.lvl i c) (St.no i c j c' t jj d)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, hj, hc', trivial, hjj, hd⟩]
  trivial

lemma stepT2 (i c j c' k : Fin (m + 2)) (hk : (k : ℕ) = 0) (hjm : (j : ℕ) < m) :
    (cmach r s t).Step x (St.outer i c j c') (St.walkY i c j c' s k) := by
  show (E r s t (St.outer i c j c') (St.walkY i c j c' s k)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, hk, hjm⟩]
  trivial

lemma stepT3 (i c j c' k k2 : Fin (m + 2)) (u w : Fin m) (hk2 : (k2 : ℕ) = (k : ℕ) + 1)
    (huw : u = w ∨ Rl r x u w) :
    (cmach r s t).Step x (St.walkY i c j c' u k) (St.walkY i c j c' w k2) := by
  show (E r s t (St.walkY i c j c' u k) (St.walkY i c j c' w k2)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, hk2⟩]
  by_cases hwu : w = u
  · rw [if_pos hwu]; trivial
  · rw [if_neg hwu]
    rcases huw with rfl | hs
    · exact absurd rfl hwu
    · exact hs

lemma stepT4 (i c j c' j2 c2' k : Fin (m + 2)) (w : Fin m) (hk : (k : ℕ) = (i : ℕ) + 1)
    (hw : (w : ℕ) = (j : ℕ)) (hj2 : (j2 : ℕ) = (j : ℕ) + 1)
    (hc2' : (c2' : ℕ) = (c' : ℕ) + 1) :
    (cmach r s t).Step x (St.walkY i c j c' w k) (St.outer i c j2 c2') := by
  show (E r s t (St.walkY i c j c' w k) (St.outer i c j2 c2')).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, hk, hw, hj2, hc2'⟩]
  trivial

lemma stepT5 (i c j c' jj d : Fin (m + 2)) (v : Fin m) (hv : (v : ℕ) = (j : ℕ))
    (hjm : (j : ℕ) < m) (hjj : (jj : ℕ) = 0) (hd : (d : ℕ) = 0) :
    (cmach r s t).Step x (St.outer i c j c') (St.no i c j c' v jj d) := by
  show (E r s t (St.outer i c j c') (St.no i c j c' v jj d)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, hv, hjm, hjj, hd⟩]
  trivial

lemma stepT6 (i c j c' jj jj2 d : Fin (m + 2)) (v : Fin m)
    (hjj2 : (jj2 : ℕ) = (jj : ℕ) + 1) (hjm : (jj : ℕ) < m) :
    (cmach r s t).Step x (St.no i c j c' v jj d) (St.no i c j c' v jj2 d) := by
  show (E r s t (St.no i c j c' v jj d) (St.no i c j c' v jj2 d)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, hjj2, hjm⟩]
  trivial

lemma stepT7 (i c j c' jj d k : Fin (m + 2)) (v : Fin m) (hk : (k : ℕ) = 0)
    (hjm : (jj : ℕ) < m) :
    (cmach r s t).Step x (St.no i c j c' v jj d) (St.walkN i c j c' v jj d s k) := by
  show (E r s t (St.no i c j c' v jj d) (St.walkN i c j c' v jj d s k)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, trivial, hk, hjm⟩]
  trivial

lemma stepT8 (i c j c' jj d k k2 : Fin (m + 2)) (v u w : Fin m)
    (hk2 : (k2 : ℕ) = (k : ℕ) + 1) (huw : u = w ∨ Rl r x u w) :
    (cmach r s t).Step x (St.walkN i c j c' v jj d u k) (St.walkN i c j c' v jj d w k2) := by
  show (E r s t (St.walkN i c j c' v jj d u k) (St.walkN i c j c' v jj d w k2)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, trivial, trivial, hk2⟩]
  by_cases hwu : w = u
  · rw [if_pos hwu]; trivial
  · rw [if_neg hwu]
    rcases huw with rfl | hs
    · exact absurd rfl hwu
    · exact hs

lemma stepT9 (i c j c' jj jj2 d d2 k : Fin (m + 2)) (v w : Fin m)
    (hk : (k : ℕ) = (i : ℕ)) (hw : (w : ℕ) = (jj : ℕ)) (hjj2 : (jj2 : ℕ) = (jj : ℕ) + 1)
    (hd2 : (d2 : ℕ) = (d : ℕ) + 1) (hwv : w ≠ v) (hnr : ¬ Rl r x w v) :
    (cmach r s t).Step x (St.walkN i c j c' v jj d w k) (St.no i c j c' v jj2 d2) := by
  show (E r s t (St.walkN i c j c' v jj d w k) (St.no i c j c' v jj2 d2)).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, trivial, trivial, hk, hw, hjj2, hd2⟩, if_neg hwv]
  exact (Lit.holds_neg x (r w v)).mpr hnr

lemma stepT10 (i c j c' jj d j2 : Fin (m + 2)) (v : Fin m) (hjj : (jj : ℕ) = m) (hd : d = c)
    (hv : (v : ℕ) = (j : ℕ)) (hj2 : (j2 : ℕ) = (j : ℕ) + 1) :
    (cmach r s t).Step x (St.no i c j c' v jj d) (St.outer i c j2 c') := by
  show (E r s t (St.no i c j c' v jj d) (St.outer i c j2 c')).holds x
  simp only [E]
  rw [if_pos ⟨trivial, trivial, trivial, hjj, hd, hv, hj2⟩]
  trivial

lemma stepT11 (i c j c' i2 : Fin (m + 2)) (hj : (j : ℕ) = m) (hi2 : (i2 : ℕ) = (i : ℕ) + 1) :
    (cmach r s t).Step x (St.outer i c j c') (St.lvl i2 c') := by
  show (E r s t (St.outer i c j c') (St.lvl i2 c')).holds x
  simp only [E]
  rw [if_pos ⟨hj, hi2, trivial⟩]
  trivial

lemma stepT12 (i c j c' jj d : Fin (m + 2)) (hi : (i : ℕ) = m) (hjj : (jj : ℕ) = m)
    (hd : d = c) :
    (cmach r s t).Step x (St.no i c j c' t jj d) St.acc := by
  show (E r s t (St.no i c j c' t jj d) St.acc).holds x
  simp only [E]
  rw [if_pos ⟨hi, hjj, hd, trivial⟩]
  trivial

/-! ### Walks -/

/-- A vertex of level `K` can be reached by a walk of exactly `K` steps. -/
lemma walkY_reach (i c j c' : Fin (m + 2)) :
    ∀ (K : ℕ) (w : Fin m) (kf : Fin (m + 2)), (kf : ℕ) = K → RS r s x K w →
      Relation.ReflTransGen ((cmach r s t).Step x)
        (St.walkY i c j c' s 0) (St.walkY i c j c' w kf) := by
  intro K
  induction K with
  | zero =>
      intro w kf hkf hw
      have h1 : w = s := hw
      have h2 : kf = 0 := Fin.ext (by rw [hkf, val_zero'])
      rw [h1, h2]
  | succ K ih =>
      intro w kf hkf hw
      obtain ⟨u, hu, hstep⟩ := hw
      have hKlt : K < m + 2 := by omega
      have hpath := ih u ⟨K, hKlt⟩ rfl hu
      exact hpath.tail (stepT3 r s t x i c j c' ⟨K, hKlt⟩ kf u w (by rw [hkf]) hstep)

/-- The same for the walks used in negative certificates. -/
lemma walkN_reach (i c j c' jj d : Fin (m + 2)) (v : Fin m) :
    ∀ (K : ℕ) (w : Fin m) (kf : Fin (m + 2)), (kf : ℕ) = K → RS r s x K w →
      Relation.ReflTransGen ((cmach r s t).Step x)
        (St.walkN i c j c' v jj d s 0) (St.walkN i c j c' v jj d w kf) := by
  intro K
  induction K with
  | zero =>
      intro w kf hkf hw
      have h1 : w = s := hw
      have h2 : kf = 0 := Fin.ext (by rw [hkf, val_zero'])
      rw [h1, h2]
  | succ K ih =>
      intro w kf hkf hw
      obtain ⟨u, hu, hstep⟩ := hw
      have hKlt : K < m + 2 := by omega
      have hpath := ih u ⟨K, hKlt⟩ rfl hu
      exact hpath.tail
        (stepT8 r s t x i c j c' jj d ⟨K, hKlt⟩ kf v u w (by rw [hkf]) hstep)

/-! ### The inner loop: certifying that `v` is not in level `i+1` -/

lemma no_loop (i c j c' : Fin (m + 2)) (v : Fin m) (hv : ¬ RS r s x ((i : ℕ) + 1) v) :
    ∀ (J : ℕ), J ≤ m → ∀ (jf df : Fin (m + 2)), (jf : ℕ) = J →
      (df : ℕ) = cntb (RS r s x (i : ℕ)) J →
      Relation.ReflTransGen ((cmach r s t).Step x)
        (St.no i c j c' v 0 0) (St.no i c j c' v jf df) := by
  intro J
  induction J with
  | zero =>
      intro _ jf df hjf hdf
      have h1 : jf = 0 := Fin.ext (by rw [hjf, val_zero'])
      have h2 : df = 0 := Fin.ext (by rw [hdf, cntb_zero, val_zero'])
      rw [h1, h2]
  | succ J ih =>
      intro hJ jf df hjf hdf
      have hJm : J < m := by omega
      have hJlt : J < m + 2 := by omega
      have hilt : (i : ℕ) < m + 2 := i.isLt
      have hcJ : cntb (RS r s x (i : ℕ)) J ≤ m := cntb_le _ _
      obtain ⟨u, hu⟩ : ∃ u : Fin m, (u : ℕ) = J := ⟨⟨J, hJm⟩, rfl⟩
      obtain ⟨jf0, hjf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = J := ⟨⟨J, hJlt⟩, rfl⟩
      obtain ⟨df0, hdf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cntb (RS r s x (i : ℕ)) J :=
        ⟨⟨cntb (RS r s x (i : ℕ)) J, by omega⟩, rfl⟩
      have hpath := ih (by omega) jf0 df0 hjf0 hdf0
      by_cases hmem : RS r s x (i : ℕ) u
      · -- certify that `u` belongs to level `i`, and count it
        have hwv : u ≠ v := fun h => hv ⟨u, hmem, Or.inl h⟩
        have hnrl : ¬ Rl r x u v := fun h => hv ⟨u, hmem, Or.inr h⟩
        obtain ⟨kf, hkf⟩ : ∃ f : Fin (m + 2), (f : ℕ) = (i : ℕ) := ⟨⟨(i : ℕ), by omega⟩, rfl⟩
        have hstart := hpath.tail
          (stepT7 r s t x i c j c' jf0 df0 0 v (val_zero' m) (by rw [hjf0]; exact hJm))
        have hwalk := walkN_reach r s t x i c j c' jf0 df0 v (i : ℕ) u kf hkf hmem
        refine (hstart.trans hwalk).tail ?_
        refine stepT9 r s t x i c j c' jf0 jf df0 df kf v u hkf (by rw [hu, hjf0])
          (by rw [hjf, hjf0]) ?_ hwv hnrl
        rw [hdf, hdf0]
        exact cntb_succ_mem _ _ u hmem hu
      · -- skip `u`
        have hdfeq : df = df0 :=
          Fin.ext (by rw [hdf, hdf0]; exact cntb_succ_not _ _ u hmem hu)
        rw [hdfeq]
        exact hpath.tail
          (stepT6 r s t x i c j c' jf0 jf df0 v (by rw [hjf, hjf0]) (by rw [hjf0]; exact hJm))

/-! ### The outer loop: computing the size of level `i+1` -/

lemma outer_loop (i c : Fin (m + 2)) (hi : (i : ℕ) ≤ m)
    (hc : (c : ℕ) = cnt (RS r s x (i : ℕ))) :
    ∀ (J : ℕ), J ≤ m → ∀ (jf cf : Fin (m + 2)), (jf : ℕ) = J →
      (cf : ℕ) = cntb (RS r s x ((i : ℕ) + 1)) J →
      Relation.ReflTransGen ((cmach r s t).Step x)
        (St.outer i c 0 0) (St.outer i c jf cf) := by
  intro J
  induction J with
  | zero =>
      intro _ jf cf hjf hcf
      have h1 : jf = 0 := Fin.ext (by rw [hjf, val_zero'])
      have h2 : cf = 0 := Fin.ext (by rw [hcf, cntb_zero, val_zero'])
      rw [h1, h2]
  | succ J ih =>
      intro hJ jf cf hjf hcf
      have hJm : J < m := by omega
      have hJlt : J < m + 2 := by omega
      have hilt : (i : ℕ) < m + 2 := i.isLt
      have hcJ : cntb (RS r s x ((i : ℕ) + 1)) J ≤ m := cntb_le _ _
      obtain ⟨v, hvJ⟩ : ∃ v : Fin m, (v : ℕ) = J := ⟨⟨J, hJm⟩, rfl⟩
      obtain ⟨jf0, hjf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = J := ⟨⟨J, hJlt⟩, rfl⟩
      obtain ⟨cf0, hcf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cntb (RS r s x ((i : ℕ) + 1)) J :=
        ⟨⟨cntb (RS r s x ((i : ℕ) + 1)) J, by omega⟩, rfl⟩
      have hpath := ih (by omega) jf0 cf0 hjf0 hcf0
      by_cases hmem : RS r s x ((i : ℕ) + 1) v
      · -- guess that `v` belongs to level `i+1` and certify it by a walk
        obtain ⟨kf, hkf⟩ : ∃ f : Fin (m + 2), (f : ℕ) = (i : ℕ) + 1 :=
          ⟨⟨(i : ℕ) + 1, by omega⟩, rfl⟩
        have hstart := hpath.tail
          (stepT2 r s t x i c jf0 cf0 0 (val_zero' m) (by rw [hjf0]; exact hJm))
        have hwalk := walkY_reach r s t x i c jf0 cf0 ((i : ℕ) + 1) v kf hkf hmem
        refine (hstart.trans hwalk).tail ?_
        refine stepT4 r s t x i c jf0 cf0 jf cf kf v hkf (by rw [hvJ, hjf0])
          (by rw [hjf, hjf0]) ?_
        rw [hcf, hcf0]
        exact cntb_succ_mem _ _ v hmem hvJ
      · -- guess that `v` does not belong to level `i+1` and run the inner loop
        have hcfeq : cf = cf0 :=
          Fin.ext (by rw [hcf, hcf0]; exact cntb_succ_not _ _ v hmem hvJ)
        obtain ⟨jm, hjm⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
        have hstart := hpath.tail
          (stepT5 r s t x i c jf0 cf0 0 0 v (by rw [hvJ, hjf0]) (by rw [hjf0]; exact hJm)
            (val_zero' m) (val_zero' m))
        have hloop := no_loop r s t x i c jf0 cf0 v hmem m le_rfl jm c hjm
          (by rw [hc, cntb_full])
        rw [hcfeq]
        exact (hstart.trans hloop).tail
          (stepT10 r s t x i c jf0 cf0 jm c jf v hjm rfl (by rw [hvJ, hjf0])
            (by rw [hjf, hjf0]))

/-! ### The outermost loop: going through the levels -/

lemma level_loop :
    ∀ (I : ℕ), I ≤ m → ∀ (jf cf : Fin (m + 2)), (jf : ℕ) = I →
      (cf : ℕ) = cnt (RS r s x I) →
      Relation.ReflTransGen ((cmach r s t).Step x) (St.lvl 0 1) (St.lvl jf cf) := by
  intro I
  induction I with
  | zero =>
      intro _ jf cf hjf hcf
      have h1 : jf = 0 := Fin.ext (by rw [hjf, val_zero'])
      have hset : {v : Fin m | RS r s x 0 v} = {s} := by
        ext v; simp [RS_zero]
      have h2 : cf = 1 :=
        Fin.ext (by rw [hcf, cnt, hset, Set.ncard_singleton, val_one'])
      rw [h1, h2]
  | succ I ih =>
      intro hI jf cf hjf hcf
      have hIlt : I < m + 2 := by omega
      have hcI : cnt (RS r s x I) ≤ m := cnt_le _
      obtain ⟨if0, hif0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = I := ⟨⟨I, hIlt⟩, rfl⟩
      obtain ⟨cf0, hcf0⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cnt (RS r s x I) :=
        ⟨⟨cnt (RS r s x I), by omega⟩, rfl⟩
      obtain ⟨jm, hjm⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
      have hpath := ih (by omega) if0 cf0 hif0 hcf0
      have hstart := hpath.tail (stepT1 r s t x if0 cf0 0 0 (val_zero' m) (val_zero' m))
      have hloop := outer_loop r s t x if0 cf0 (by rw [hif0]; omega) (by rw [hcf0, hif0])
        m le_rfl jm cf hjm
        (by rw [hcf, hif0, cntb_full])
      exact (hstart.trans hloop).tail
        (stepT11 r s t x if0 cf0 jm cf jf hjm (by rw [hjf, hif0]))

/-! ### Completeness -/

/-- If `t` is not reachable from `s`, the counting machine accepts. -/
theorem cmach_complete (hnr : ¬ Relation.ReflTransGen (Rl r x) s t) :
    (cmach r s t).Accepts x := by
  have hcm : cnt (RS r s x m) ≤ m := cnt_le _
  obtain ⟨im, him⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
  obtain ⟨cm, hcmv⟩ : ∃ f : Fin (m + 2), (f : ℕ) = cnt (RS r s x m) :=
    ⟨⟨cnt (RS r s x m), by omega⟩, rfl⟩
  obtain ⟨jm, hjm⟩ : ∃ f : Fin (m + 2), (f : ℕ) = m := ⟨⟨m, by omega⟩, rfl⟩
  have hlevels := level_loop r s t x m le_rfl im cm him hcmv
  have hstart := hlevels.tail
    (stepT5' r s t x im cm 0 0 0 0 (val_zero' m) (val_zero' m) (val_zero' m) (val_zero' m))
  have hnotin : ¬ RS r s x ((im : ℕ) + 1) t := by
    rw [him]
    intro hmem
    exact hnr ((reach_iff_RS r s x t).mpr hmem)
  have hloop := no_loop r s t x im cm 0 0 t hnotin m le_rfl jm cm hjm
    (by rw [hcmv, him, cntb_full])
  exact (hstart.trans hloop).tail (stepT12 r s t x im cm 0 0 jm cm him hjm rfl)

end CS

import Mathlib

/-!
# A model of nondeterministic logarithmic space

We model a nondeterministic space bounded machine by its *configuration graph*.

For an input length `n`, a machine is a finite set `V` of configurations, an initial
configuration, an accepting configuration, and, for each ordered pair of configurations,
a *guard*: an atomic condition on the input, which is either "never", "always", or
"the `i`-th input bit equals `b`".  This is exactly the way a space bounded machine
depends on its input: a transition out of a configuration is determined by the finite
control together with the single input bit currently scanned.

The machine accepts an input `x` when the accepting configuration is reachable from the
initial one in the graph of the guards that hold under `x`.

The class `NL` is the class of languages recognised by such machines whose configuration
graph has polynomially many vertices, i.e. `O(log n)` space.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

/-- An atomic guard on an input of length `n`: an edge of a configuration graph is
either absent, present unconditionally, or present exactly when the `i`-th input bit
equals `b`. -/
inductive Lit (n : ℕ) where
  | never : Lit n
  | always : Lit n
  | test : Fin n → Bool → Lit n
  deriving DecidableEq

/-- Whether a guard holds on the input `x`. -/
def Lit.holds {n : ℕ} (x : Fin n → Bool) : Lit n → Prop
  | .never => False
  | .always => True
  | .test i b => x i = b

instance {n : ℕ} (x : Fin n → Bool) (l : Lit n) : Decidable (l.holds x) := by
  cases l <;> unfold Lit.holds <;> infer_instance

/-- The negation of a guard: guards are closed under complement, which is what makes it
possible for a machine to *test* whether a transition of another machine exists. -/
def Lit.neg {n : ℕ} : Lit n → Lit n
  | .never => .always
  | .always => .never
  | .test i b => .test i (!b)

@[simp] lemma Lit.holds_neg {n : ℕ} (x : Fin n → Bool) (l : Lit n) :
    (l.neg).holds x ↔ ¬ l.holds x := by
  cases l with
  | never => simp [Lit.neg, Lit.holds]
  | always => simp [Lit.neg, Lit.holds]
  | test i b => cases hb : x i <;> cases b <;> simp [Lit.neg, Lit.holds, hb]

@[simp] lemma Lit.holds_never {n : ℕ} (x : Fin n → Bool) :
    (Lit.never (n := n)).holds x ↔ False := Iff.rfl

@[simp] lemma Lit.holds_always {n : ℕ} (x : Fin n → Bool) :
    (Lit.always (n := n)).holds x ↔ True := Iff.rfl

/-- A nondeterministic machine on inputs of length `n`, presented by its configuration
graph. -/
structure Mach (n : ℕ) where
  /-- The set of configurations. -/
  V : Type
  /-- Configurations form a finite type. -/
  fV : Fintype V
  /-- The initial configuration. -/
  start : V
  /-- The accepting configuration. -/
  acc : V
  /-- The guard controlling the transition from one configuration to another. -/
  edge : V → V → Lit n

attribute [instance] Mach.fV

/-- One computation step of `M` on input `x`. -/
def Mach.Step {n : ℕ} (M : Mach n) (x : Fin n → Bool) (u v : M.V) : Prop :=
  (M.edge u v).holds x

/-- `M` accepts `x` when the accepting configuration is reachable from the initial one. -/
def Mach.Accepts {n : ℕ} (M : Mach n) (x : Fin n → Bool) : Prop :=
  Relation.ReflTransGen (M.Step x) M.start M.acc

/-- A language: for each input length, a set of inputs of that length. -/
def Lang : Type := (n : ℕ) → (Fin n → Bool) → Prop

/-- The class of languages recognised by nondeterministic machines with polynomially
many configurations, that is, nondeterministic logarithmic space. -/
def NL (L : Lang) : Prop :=
  ∃ k : ℕ, ∀ n : ℕ, ∃ M : Mach n,
    Fintype.card M.V ≤ (n + 2) ^ k ∧ ∀ x, L n x ↔ M.Accepts x

/-- The class of languages whose complement is in `NL`. -/
def coNL (L : Lang) : Prop := NL (fun n x => ¬ L n x)

/-- Reachability can be transported along an equivalence of vertex sets. -/
theorem reflTransGen_equiv {α β : Type} (e : α ≃ β) (R : α → α → Prop) (a b : α) :
    Relation.ReflTransGen R a b ↔
      Relation.ReflTransGen (fun u v => R (e.symm u) (e.symm v)) (e a) (e b) := by
  constructor
  · intro h
    exact h.lift (f := fun a => e a) (fun u v huv => by simpa using huv)
  · intro h
    have := h.lift (f := fun u => e.symm u) (fun u v huv => huv)
    simpa using this

end CS

import RequestProject.ISModel

/-!
# A sanity check on the model

The class `NL` defined in `RequestProject/ISModel.lean` is not degenerate: it contains
languages that genuinely depend on the input.  Here we check that the language "the first
input bit is `true`" is in `NL`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

/-- A two-configuration machine testing the first input bit. -/
noncomputable def firstBitMach (n : ℕ) : Mach n where
  V := Bool
  fV := inferInstance
  start := false
  acc := true
  edge := fun u v =>
    if u = false ∧ v = true then
      (if h : 0 < n then Lit.test ⟨0, h⟩ true else Lit.never)
    else Lit.never

lemma firstBitMach_accepts (n : ℕ) (x : Fin n → Bool) :
    (firstBitMach n).Accepts x ↔ ∃ h : 0 < n, x ⟨0, h⟩ = true := by
  have hedge : ((firstBitMach n).edge false true).holds x ↔ ∃ h : 0 < n, x ⟨0, h⟩ = true := by
    by_cases h : 0 < n
    · simp [firstBitMach, h, Lit.holds]
    · simp [firstBitMach, h, Lit.holds]
  rw [← hedge]
  constructor
  · intro hacc
    rcases hacc.cases_head with hcon | ⟨c, hc, _⟩
    · exact absurd hcon (by simp)
    · have : c = true := by
        by_contra hne
        have hc' : c = false := by
          cases c with
          | false => rfl
          | true => exact absurd rfl hne
        rw [hc'] at hc
        exact absurd hc (by simp [Mach.Step, firstBitMach, Lit.holds])
      rw [this] at hc
      exact hc
  · intro hstep
    exact Relation.ReflTransGen.single hstep

/-- The language "the first input bit is `true`" belongs to `NL`. -/
theorem NL_firstBit : NL (fun n x => ∃ h : 0 < n, x ⟨0, h⟩ = true) := by
  refine ⟨1, fun n => ⟨firstBitMach n, ?_, fun x => (firstBitMach_accepts n x).symm⟩⟩
  have : Fintype.card (firstBitMach n).V = 2 := rfl
  simp only [this, pow_one]
  omega

end CS

import RequestProject.ISModel

/-!
# Level sets of reachability

For a guarded graph `r` on `Fin m` and an input `x`, `RS r s x i` is the set of vertices
reachable from `s` in at most `i` steps (we allow "waiting", so the level sets are
increasing by construction).

The main result is that the level sets stabilise at level `m + 1`, so that
`RS r s x (m+1)` is exactly the set of vertices reachable from `s`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

variable {n m : ℕ}

/-- The one step relation of a guarded graph on the input `x`. -/
def Rl (r : Fin m → Fin m → Lit n) (x : Fin n → Bool) (u v : Fin m) : Prop :=
  (r u v).holds x

/-- `RS r s x i v` says that `v` is reachable from `s` in at most `i` steps. -/
def RS (r : Fin m → Fin m → Lit n) (s : Fin m) (x : Fin n → Bool) : ℕ → Fin m → Prop
  | 0 => fun v => v = s
  | (i + 1) => fun v => ∃ u, RS r s x i u ∧ (u = v ∨ Rl r x u v)

variable (r : Fin m → Fin m → Lit n) (s : Fin m) (x : Fin n → Bool)

lemma RS_zero (v : Fin m) : RS r s x 0 v ↔ v = s := Iff.rfl

lemma RS_succ (i : ℕ) (v : Fin m) :
    RS r s x (i + 1) v ↔ ∃ u, RS r s x i u ∧ (u = v ∨ Rl r x u v) := Iff.rfl

lemma RS_self : RS r s x 0 s := rfl

lemma RS_mono_one {i : ℕ} {v : Fin m} (h : RS r s x i v) : RS r s x (i + 1) v :=
  ⟨v, h, Or.inl rfl⟩

lemma RS_mono {i j : ℕ} (hij : i ≤ j) {v : Fin m} (h : RS r s x i v) : RS r s x j v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  induction d with
  | zero => simpa using h
  | succ d ih => exact RS_mono_one r s x ih

lemma RS_step {i : ℕ} {u v : Fin m} (h : RS r s x i u) (huv : Rl r x u v) :
    RS r s x (i + 1) v := ⟨u, h, Or.inr huv⟩

/-- Everything in a level set is reachable. -/
lemma RS_reach {i : ℕ} {v : Fin m} (h : RS r s x i v) :
    Relation.ReflTransGen (Rl r x) s v := by
  induction i generalizing v with
  | zero => exact ((RS_zero r s x v).mp h) ▸ Relation.ReflTransGen.refl
  | succ i ih =>
      obtain ⟨u, hu, hstep⟩ := h
      rcases hstep with rfl | hstep
      · exact ih hu
      · exact (ih hu).tail hstep

/-- Everything reachable lies in some level set. -/
lemma reach_RS {v : Fin m} (h : Relation.ReflTransGen (Rl r x) s v) :
    ∃ i, RS r s x i v := by
  induction h with
  | refl => exact ⟨0, rfl⟩
  | tail _ hstep ih =>
      obtain ⟨i, hi⟩ := ih
      exact ⟨i + 1, RS_step r s x hi hstep⟩

/-- The level sets, as sets. -/
def SS (i : ℕ) : Set (Fin m) := {v | RS r s x i v}

lemma SS_zero : SS r s x 0 = {s} := by
  ext v; simp [SS, RS_zero]

lemma SS_subset_succ (i : ℕ) : SS r s x i ⊆ SS r s x (i + 1) :=
  fun _ hv => RS_mono_one r s x hv

lemma SS_subset {i j : ℕ} (hij : i ≤ j) : SS r s x i ⊆ SS r s x j :=
  fun _ hv => RS_mono r s x hij hv

lemma SS_ncard_le (i : ℕ) : (SS r s x i).ncard ≤ m := by
  have h1 : (SS r s x i).ncard ≤ (Set.univ : Set (Fin m)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  simpa [Set.ncard_univ] using h1

/-- If two consecutive level sets agree, so do the next two. -/
lemma SS_stall (i : ℕ) (h : SS r s x i = SS r s x (i + 1)) :
    SS r s x (i + 1) = SS r s x (i + 2) := by
  have hmem : ∀ u, RS r s x i u ↔ RS r s x (i + 1) u := by
    intro u
    constructor
    · intro hu; exact (Set.ext_iff.mp h u).mp hu
    · intro hu; exact (Set.ext_iff.mp h u).mpr hu
  ext v
  simp only [SS, Set.mem_setOf_eq, RS_succ]
  constructor
  · rintro ⟨u, hu, hstep⟩; exact ⟨u, (hmem u).mp hu, hstep⟩
  · rintro ⟨u, hu, hstep⟩; exact ⟨u, (hmem u).mpr hu, hstep⟩

lemma SS_stall_iter (i : ℕ) (h : SS r s x i = SS r s x (i + 1)) :
    ∀ d, SS r s x (i + d) = SS r s x (i + d + 1) := by
  intro d
  induction d with
  | zero => simpa using h
  | succ d ih =>
      have := SS_stall r s x (i + d) ih
      have e : i + (d + 1) = i + d + 1 := by omega
      rw [e]
      exact this

lemma SS_stall_forever (i : ℕ) (h : SS r s x i = SS r s x (i + 1)) :
    ∀ d, SS r s x (i + d) = SS r s x i := by
  intro d
  induction d with
  | zero => rfl
  | succ d ih =>
      have e : i + (d + 1) = i + d + 1 := by omega
      rw [e, ← SS_stall_iter r s x i h d, ih]

/-- As long as the level sets keep growing, their cardinality grows. -/
lemma SS_ncard_growth (i : ℕ) (hgrow : ∀ j < i, SS r s x j ≠ SS r s x (j + 1)) :
    i + 1 ≤ (SS r s x i).ncard := by
  induction i with
  | zero => simp [SS_zero]
  | succ i ih =>
      have hih : i + 1 ≤ (SS r s x i).ncard := ih (fun j hj => hgrow j (by omega))
      have hss : SS r s x i ⊂ SS r s x (i + 1) :=
        ⟨SS_subset_succ r s x i, fun hsup =>
          hgrow i (by omega) (Set.Subset.antisymm (SS_subset_succ r s x i) hsup)⟩
      have := Set.ncard_lt_ncard hss (Set.toFinite _)
      omega

lemma exists_stall : ∃ i ≤ m, SS r s x i = SS r s x (i + 1) := by
  by_contra hcon
  push_neg at hcon
  have hgrow : ∀ j < m + 1, SS r s x j ≠ SS r s x (j + 1) := by
    intro j hj
    exact hcon j (by omega)
  have h1 : (m + 1) + 1 ≤ (SS r s x (m + 1)).ncard := SS_ncard_growth r s x (m + 1) hgrow
  have h2 := SS_ncard_le r s x (m + 1)
  omega

/-- The level sets stabilise at level `m + 1`. -/
lemma RS_stab (i : ℕ) {v : Fin m} (h : RS r s x i v) : RS r s x (m + 1) v := by
  obtain ⟨i0, hi0, hstall⟩ := exists_stall r s x
  rcases Nat.lt_or_ge (m + 1) i with hlt | hge
  · have e1 : SS r s x i = SS r s x i0 := by
      have : i = i0 + (i - i0) := by omega
      rw [this]; exact SS_stall_forever r s x i0 hstall _
    have e2 : SS r s x (m + 1) = SS r s x i0 := by
      have : m + 1 = i0 + (m + 1 - i0) := by omega
      rw [this]; exact SS_stall_forever r s x i0 hstall _
    have : v ∈ SS r s x i := h
    rw [e1, ← e2] at this
    exact this
  · exact RS_mono r s x hge h

/-- Reachability is exactly membership in the level set of index `m + 1`. -/
lemma reach_iff_RS (t : Fin m) :
    Relation.ReflTransGen (Rl r x) s t ↔ RS r s x (m + 1) t := by
  constructor
  · intro h
    obtain ⟨i, hi⟩ := reach_RS r s x h
    exact RS_stab r s x i hi
  · intro h; exact RS_reach r s x h

end CS

import RequestProject.ISMachine

/-!
# Soundness of the counting machine

We exhibit an invariant of the counting machine which holds at the initial configuration,
is preserved by every transition, and which at the accepting configuration says that `t`
is not reachable from `s`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

variable {n m : ℕ} (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool)

/-- The invariant attached to the loop over vertices: `c` is the exact number of vertices
of level `i`, and `c'` is the exact number of vertices of level `i+1` among the first `j`
vertices. -/
def OInv (i c j c' : Fin (m + 2)) : Prop :=
  (c : ℕ) = cnt (RS r s x (i : ℕ)) ∧ (c' : ℕ) = cntb (RS r s x ((i : ℕ) + 1)) (j : ℕ)

/-- Vertices of level `I` that neither are `v` nor have an edge to `v`. -/
def NPred (I : ℕ) (v : Fin m) : Fin m → Prop :=
  fun u => RS r s x I u ∧ ¬(u = v ∨ Rl r x u v)

/-- The invariant of the counting machine. -/
def Inv : St m → Prop
  | .lvl i c => (c : ℕ) = cnt (RS r s x (i : ℕ))
  | .outer i c j c' => OInv r s x i c j c'
  | .walkY i c j c' w k => OInv r s x i c j c' ∧ RS r s x (k : ℕ) w
  | .no i c j c' v jj d =>
      OInv r s x i c j c' ∧ (d : ℕ) ≤ cntb (NPred r s x (i : ℕ) v) (jj : ℕ)
  | .walkN i c j c' v jj d w k =>
      (OInv r s x i c j c' ∧ (d : ℕ) ≤ cntb (NPred r s x (i : ℕ) v) (jj : ℕ)) ∧
        RS r s x (k : ℕ) w
  | .acc => ¬ Relation.ReflTransGen (Rl r x) s t

/-- The heart of the argument: if the machine has enumerated as many vertices of level
`I` unrelated to `v` as there are vertices of level `I` altogether, then *every* vertex
of level `I` is unrelated to `v`, so `v` does not belong to level `I + 1`. -/
lemma not_next (I : ℕ) (v : Fin m) (N : ℕ) (hN : N = cnt (RS r s x I))
    (hle : N ≤ cntb (NPred r s x I v) m) : ¬ RS r s x (I + 1) v := by
  rw [cntb_full] at hle
  have h : cnt (RS r s x I) ≤ cnt (fun u => RS r s x I u ∧ ¬(u = v ∨ Rl r x u v)) := by
    rw [← hN]; exact hle
  have hall := forall_of_cnt_le _ _ h
  rintro ⟨u, hu, hstep⟩
  exact (hall u hu) hstep

lemma inv_start : Inv r s t x (St.lvl 0 1) := by
  show ((1 : Fin (m + 2)) : ℕ) = cnt (RS r s x ((0 : Fin (m + 2)) : ℕ))
  have h0 : ((0 : Fin (m + 2)) : ℕ) = 0 := rfl
  have h1 : ((1 : Fin (m + 2)) : ℕ) = 1 := by
    simp [Nat.mod_eq_of_lt]
  have hset : {v : Fin m | RS r s x 0 v} = {s} := by
    ext v; simp [RS_zero]
  rw [h0, h1, cnt, hset, Set.ncard_singleton]

lemma inv_step (a b : St m) (h : (E r s t a b).holds x) (ha : Inv r s t x a) :
    Inv r s t x b := by
  cases a <;> cases b <;> simp only [E, Lit.holds_never] at h <;>
    simp only [Inv, OInv] at ha ⊢
  -- T1 : `lvl → outer`, start the loop over the vertices
  · next i c i2 c2 j c' =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hj, hc'⟩ := hc
      rw [hi2, hc2, hj, hc', cntb_zero]
      exact ⟨ha, rfl⟩
    · exact absurd h (by simp)
  -- T5' : `lvl → no`, start the final check
  · next i c i2 c2 j c' v jj d =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hj, hc', -, hjj, hd⟩ := hc
      rw [hi2, hc2, hj, hc', hjj, hd, cntb_zero, cntb_zero]
      exact ⟨⟨ha, rfl⟩, le_refl 0⟩
    · exact absurd h (by simp)
  -- T11 : `outer → lvl`, the level is finished
  · next i c j c' i2 c2 =>
    split_ifs at h with hc
    · obtain ⟨hj, hi2, hc2⟩ := hc
      rw [hc2, hi2, ha.2, hj, cntb_full]
    · exact absurd h (by simp)
  -- T2 : `outer → walkY`, start a positive certificate
  · next i c j c' i2 c2 j2 c2' w k =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hj2, hc2', hw, hk, -⟩ := hc
      rw [hi2, hc2, hj2, hc2', hw, hk]
      exact ⟨ha, RS_self r s x⟩
    · exact absurd h (by simp)
  -- T5 : `outer → no`, start a negative certificate
  · next i c j c' i2 c2 j2 c2' v jj d =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hj2, hc2', -, -, hjj, hd⟩ := hc
      rw [hi2, hc2, hj2, hc2', hjj, hd, cntb_zero]
      exact ⟨ha, le_refl 0⟩
    · exact absurd h (by simp)
  -- T4 : `walkY → outer`, the vertex is counted
  · next i c j c' w k i2 c2 j2 c2' =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hk, hw, hj2, hc2'⟩ := hc
      have hw' : RS r s x ((i : ℕ) + 1) w := by rw [← hk]; exact ha.2
      rw [hi2, hc2]
      refine ⟨ha.1.1, ?_⟩
      rw [hc2', hj2, cntb_succ_mem _ _ w hw' hw, ha.1.2]
    · exact absurd h (by simp)
  -- T3 : one step of a positive walk
  · next i c j c' w k i2 c2 j2 c2' w2 k2 =>
    split_ifs at h with hc hw2
    · obtain ⟨hi2, hc2, hj2, hc2', hk2⟩ := hc
      rw [hi2, hc2, hj2, hc2']
      exact ⟨ha.1, by rw [hk2, hw2]; exact RS_mono_one r s x ha.2⟩
    · obtain ⟨hi2, hc2, hj2, hc2', hk2⟩ := hc
      rw [hi2, hc2, hj2, hc2']
      exact ⟨ha.1, by rw [hk2]; exact RS_step r s x ha.2 h⟩
    · exact absurd h (by simp)
  -- T10 : `no → outer`, the vertex is certified absent from level `i+1`
  · next i c j c' v jj d i2 c2 j2 c2' =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hc2', hjj, hd, hv, hj2⟩ := hc
      have h2 := ha.2
      rw [hjj] at h2
      have hdc : (d : ℕ) = cnt (RS r s x (i : ℕ)) := by rw [hd]; exact ha.1.1
      have hnot : ¬ RS r s x ((i : ℕ) + 1) v := not_next r s x (i : ℕ) v (d : ℕ) hdc h2
      rw [hi2, hc2, hc2']
      refine ⟨ha.1.1, ?_⟩
      rw [hj2, cntb_succ_not _ _ v hnot hv, ha.1.2]
    · exact absurd h (by simp)
  -- T6 : `no → no`, the vertex is skipped
  · next i c j c' v jj d i2 c2 j2 c2' v2 jj2 d2 =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hj2, hc2', hv2, hd2, hjj2, -⟩ := hc
      rw [hi2, hc2, hj2, hc2', hv2, hd2, hjj2]
      exact ⟨ha.1, le_trans ha.2 (cntb_mono _ (by omega))⟩
    · exact absurd h (by simp)
  -- T7 : `no → walkN`, start certifying membership in level `i`
  · next i c j c' v jj d i2 c2 j2 c2' v2 jj2 d2 w k =>
    split_ifs at h with hc
    · obtain ⟨hi2, hc2, hj2, hc2', hv2, hjj2, hd2, hw, hk, -⟩ := hc
      rw [hi2, hc2, hj2, hc2', hv2, hjj2, hd2, hw, hk]
      exact ⟨ha, RS_self r s x⟩
    · exact absurd h (by simp)
  -- T12 : `no → acc`
  · next i c j c' v jj d =>
    split_ifs at h with hc
    · obtain ⟨hi, hjj, hd, hv⟩ := hc
      have h2 := ha.2
      rw [hjj] at h2
      have hdc : (d : ℕ) = cnt (RS r s x (i : ℕ)) := by rw [hd]; exact ha.1.1
      have hnot : ¬ RS r s x ((i : ℕ) + 1) v := not_next r s x (i : ℕ) v (d : ℕ) hdc h2
      rw [hi, hv] at hnot
      intro hreach
      exact hnot ((reach_iff_RS r s x t).mp hreach)
    · exact absurd h (by simp)
  -- T9 : `walkN → no`, the vertex of level `i` is counted
  · next i c j c' v jj d w k i2 c2 j2 c2' v2 jj2 d2 =>
    split_ifs at h with hc hwv
    · exact absurd h (by simp)
    · obtain ⟨hi2, hc2, hj2, hc2', hv2, hk, hw, hjj2, hd2⟩ := hc
      have hmem : NPred r s x (i : ℕ) v w := by
        refine ⟨by rw [← hk]; exact ha.2, ?_⟩
        rintro (rfl | hstep)
        · exact hwv rfl
        · exact ((Lit.holds_neg x (r w v)).mp h) hstep
      rw [hi2, hc2, hj2, hc2', hv2]
      refine ⟨ha.1.1, ?_⟩
      rw [hd2, hjj2, cntb_succ_mem _ _ w hmem hw]
      exact Nat.succ_le_succ ha.1.2
    · exact absurd h (by simp)
  -- T8 : one step of a negative walk
  · next i c j c' v jj d w k i2 c2 j2 c2' v2 jj2 d2 w2 k2 =>
    split_ifs at h with hc hw2
    · obtain ⟨hi2, hc2, hj2, hc2', hv2, hjj2, hd2, hk2⟩ := hc
      rw [hi2, hc2, hj2, hc2', hv2, hjj2, hd2]
      exact ⟨ha.1, by rw [hk2, hw2]; exact RS_mono_one r s x ha.2⟩
    · obtain ⟨hi2, hc2, hj2, hc2', hv2, hjj2, hd2, hk2⟩ := hc
      rw [hi2, hc2, hj2, hc2', hv2, hjj2, hd2]
      exact ⟨ha.1, by rw [hk2]; exact RS_step r s x ha.2 h⟩
    · exact absurd h (by simp)

/-- If the counting machine accepts, then `t` is not reachable from `s`. -/
theorem cmach_sound (hacc : (cmach r s t).Accepts x) :
    ¬ Relation.ReflTransGen (Rl r x) s t := by
  have hinv : ∀ (b : St m), Relation.ReflTransGen ((cmach r s t).Step x) (St.lvl 0 1) b →
      Inv r s t x b := by
    intro b hb
    induction hb with
    | refl => exact inv_start r s t x
    | tail _ hstep ih => exact inv_step r s t x _ _ hstep ih
  exact hinv St.acc hacc

end CS

import RequestProject.ISSound
import RequestProject.ISComplete

/-!
# Complementing a nondeterministic machine

Combining soundness and completeness of the counting machine, every nondeterministic
machine can be complemented at a polynomial cost in the number of configurations.
This is the Immerman–Szelepcsényi theorem, and it gives `NL = coNL`.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

variable {n m : ℕ}

/-- The counting machine decides the complement of reachability. -/
theorem cmach_correct (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool) :
    (cmach r s t).Accepts x ↔ ¬ Relation.ReflTransGen (Rl r x) s t :=
  ⟨cmach_sound r s t x, cmach_complete r s t x⟩

/-- The machine complementing `M`: the counting machine run on the configuration graph
of `M`, transported to `Fin (Fintype.card M.V)`. -/
noncomputable def complMach (M : Mach n) : Mach n :=
  let e : M.V ≃ Fin (Fintype.card M.V) := Fintype.equivFin M.V
  cmach (fun u v => M.edge (e.symm u) (e.symm v)) (e M.start) (e M.acc)

lemma complMach_card (M : Mach n) :
    Fintype.card (complMach M).V ≤ 6 * (Fintype.card M.V + 2) ^ 9 :=
  card_St _

lemma complMach_accepts (M : Mach n) (x : Fin n → Bool) :
    (complMach M).Accepts x ↔ ¬ M.Accepts x := by
  let e : M.V ≃ Fin (Fintype.card M.V) := Fintype.equivFin M.V
  show (cmach (fun u v => M.edge (e.symm u) (e.symm v)) (e M.start) (e M.acc)).Accepts x ↔ _
  rw [cmach_correct]
  have h : Relation.ReflTransGen (Rl (fun u v => M.edge (e.symm u) (e.symm v)) x)
      (e M.start) (e M.acc) ↔ M.Accepts x :=
    (reflTransGen_equiv e (M.Step x) M.start M.acc).symm
  rw [h]

/-- **Complementation of nondeterministic machines.** For every machine `M` there is a
machine `M'`, with polynomially many configurations in the number of configurations of
`M`, accepting exactly the inputs rejected by `M`. -/
theorem exists_complement_mach (M : Mach n) :
    ∃ M' : Mach n, Fintype.card M'.V ≤ 6 * (Fintype.card M.V + 2) ^ 9 ∧
      ∀ x, M'.Accepts x ↔ ¬ M.Accepts x :=
  ⟨complMach M, complMach_card M, complMach_accepts M⟩

/-- `NL` is closed under complementation. -/
theorem NL_compl {L : Lang} (h : NL L) : NL (fun n x => ¬ L n x) := by
  obtain ⟨k, hk⟩ := h
  refine ⟨9 * k + 21, ?_⟩
  intro n
  obtain ⟨M, hcard, hM⟩ := hk n
  obtain ⟨M', hcard', hM'⟩ := exists_complement_mach M
  refine ⟨M', ?_, ?_⟩
  · -- the polynomial bound
    have hb : 2 ≤ n + 2 := by omega
    have h1 : 1 ≤ (n + 2) ^ k := Nat.one_le_pow _ _ (by omega)
    have h2 : (2 : ℕ) ^ 2 ≤ (n + 2) ^ 2 := Nat.pow_le_pow_left hb 2
    have h3 : Fintype.card M.V + 2 ≤ (n + 2) ^ (k + 2) := by
      have : (n + 2) ^ (k + 2) = (n + 2) ^ k * (n + 2) ^ 2 := by ring
      rw [this]
      have h4 : (n + 2) ^ k * 4 ≤ (n + 2) ^ k * (n + 2) ^ 2 :=
        Nat.mul_le_mul_left _ (by omega)
      omega
    have h5 : (Fintype.card M.V + 2) ^ 9 ≤ ((n + 2) ^ (k + 2)) ^ 9 :=
      Nat.pow_le_pow_left h3 9
    have h6 : (6 : ℕ) ≤ (n + 2) ^ 3 := by
      have : (2 : ℕ) ^ 3 ≤ (n + 2) ^ 3 := Nat.pow_le_pow_left hb 3
      omega
    have h7 : 6 * (Fintype.card M.V + 2) ^ 9 ≤ (n + 2) ^ 3 * ((n + 2) ^ (k + 2)) ^ 9 :=
      Nat.mul_le_mul h6 h5
    have h8 : (n + 2) ^ 3 * ((n + 2) ^ (k + 2)) ^ 9 = (n + 2) ^ (9 * k + 21) := by
      rw [← pow_mul, ← pow_add]
      ring_nf
    omega
  · intro x
    show ¬ L n x ↔ M'.Accepts x
    rw [hM' x, hM x]

/-- **Immerman–Szelepcsényi**: nondeterministic logarithmic space is closed under
complementation, `NL = coNL`. -/
theorem NL_eq_coNL : NL = coNL := by
  funext L
  rw [eq_iff_iff]
  constructor
  · intro h
    exact NL_compl h
  · intro h
    have h2 := NL_compl h
    have heq : (fun n x => ¬ ¬ L n x) = L := by
      funext n x
      simp
    rwa [heq] at h2

end CS

import Mathlib
import RequestProject.ISCore

/-!
# Immerman Szelepcsenyi
Category: Frontier Cs
Target: CS.immerman_szelepcsenyi
Verification: pending
Provenance: Aristotle theorem prover (Harmonic)
-/

-- (Lean requires `import` commands to precede every other command, including the module
-- documentation above.)

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
set_option pp.piBinderTypes true

set_option grind.warning false

namespace CS

/-!
## The statement

`NL` is formalised through configuration graphs (see `RequestProject/ISModel.lean`).
A machine on inputs of length `n` is a finite set of configurations together with an
initial and an accepting configuration and, for each ordered pair of configurations, a
guard which is either "absent", "present", or "present exactly when the `i`-th input bit
is `b`": this is precisely how a space bounded machine may depend on its input, namely
through the single input bit currently scanned.  A machine accepts an input when its
accepting configuration is reachable from its initial configuration along the guards that
hold.  A language belongs to `NL` when it is recognised by machines whose configuration
graphs have polynomially many vertices, i.e. logarithmic space; `coNL` is the class of
languages whose complement belongs to `NL`.

Since the machines are given for each input length separately, the class formalised here
is the nonuniform version of nondeterministic logarithmic space.  The proof is the
inductive counting argument of Immerman and Szelepcsényi: for every machine `M` we build
a machine `M'` with polynomially many configurations that accepts exactly the inputs
rejected by `M`.  The construction of `M'` is explicit (see
`RequestProject/ISMachine.lean`) and its correctness is proved in both directions in
`RequestProject/ISSound.lean` and `RequestProject/ISComplete.lean`.
-/

/-- **Immerman–Szelepcsényi theorem**: nondeterministic logarithmic space is closed
under complementation, `NL = coNL`. -/
theorem immerman_szelepcsenyi : NL = coNL := NL_eq_coNL

end CS

import RequestProject.ISReach

/-!
# The counting machine

This file defines the machine implementing the inductive counting argument of
Immerman and Szelepcsényi, for a guarded graph `r` on `Fin m` with distinguished
vertices `s` and `t`.

The machine walks through levels `i = 0, 1, …, m`.  At the beginning of level `i` it
holds the exact number `c` of vertices reachable from `s` in at most `i` steps.  It
recomputes this number for level `i+1` by looping over all vertices `v`, guessing for
each whether `v` belongs to level `i+1`; a positive guess is certified by guessing a
walk, a negative guess is certified by enumerating *all* the `c` vertices of level `i`
and checking that none of them is `v` or has an edge to `v`.  Finally, knowing the
number of vertices of level `m`, the same negative certificate for `v = t` at level
`m + 1` proves that `t` is unreachable.
-/

set_option maxRecDepth 8000
set_option autoImplicit false

namespace CS

variable {n m : ℕ}

/-! ### Counting -/

/-- The number of vertices satisfying `P`. -/
noncomputable def cnt (P : Fin m → Prop) : ℕ := {v : Fin m | P v}.ncard

/-- The number of vertices satisfying `P` among the first `J` vertices. -/
noncomputable def cntb (P : Fin m → Prop) (J : ℕ) : ℕ := cnt (fun v => P v ∧ (v : ℕ) < J)

lemma cnt_le (P : Fin m → Prop) : cnt P ≤ m := by
  have h1 : cnt P ≤ (Set.univ : Set (Fin m)).ncard :=
    Set.ncard_le_ncard (Set.subset_univ _) (Set.toFinite _)
  simpa [Set.ncard_univ] using h1

lemma cntb_le (P : Fin m → Prop) (J : ℕ) : cntb P J ≤ m := cnt_le _

@[simp] lemma cntb_zero (P : Fin m → Prop) : cntb P 0 = 0 := by
  have h0 : {v : Fin m | P v ∧ (v : ℕ) < 0} = ∅ := by
    ext v; simp
  simp only [cntb, cnt, h0, Set.ncard_empty]

lemma cntb_succ_mem (P : Fin m → Prop) (J : ℕ) (w : Fin m) (hw : P w) (hJ : (w : ℕ) = J) :
    cntb P (J + 1) = cntb P J + 1 := by
  have hset : {v : Fin m | P v ∧ (v : ℕ) < J + 1} = insert w {v : Fin m | P v ∧ (v : ℕ) < J} := by
    ext u
    simp only [Set.mem_insert_iff, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hlt⟩
      rcases Nat.lt_or_ge (u : ℕ) J with h | h
      · exact Or.inr ⟨hP, h⟩
      · exact Or.inl (Fin.ext (by omega))
    · rintro (rfl | ⟨hP, hlt⟩)
      · exact ⟨hw, by omega⟩
      · exact ⟨hP, by omega⟩
  have hnot : w ∉ {v : Fin m | P v ∧ (v : ℕ) < J} := by simp [hJ]
  simp only [cntb, cnt, hset]
  exact Set.ncard_insert_of_notMem hnot (Set.toFinite _)

lemma cntb_succ_not (P : Fin m → Prop) (J : ℕ) (w : Fin m) (hw : ¬ P w) (hJ : (w : ℕ) = J) :
    cntb P (J + 1) = cntb P J := by
  have hset : {v : Fin m | P v ∧ (v : ℕ) < J + 1} = {v : Fin m | P v ∧ (v : ℕ) < J} := by
    ext u
    simp only [Set.mem_setOf_eq]
    constructor
    · rintro ⟨hP, hlt⟩
      refine ⟨hP, ?_⟩
      rcases Nat.lt_or_ge (u : ℕ) J with h | h
      · exact h
      · exact absurd (show P w from (Fin.ext (show (u:ℕ) = (w:ℕ) by omega) : u = w) ▸ hP) hw
    · rintro ⟨hP, hlt⟩; exact ⟨hP, by omega⟩
  simp only [cntb, cnt, hset]

lemma cntb_mono (P : Fin m → Prop) {J J' : ℕ} (h : J ≤ J') : cntb P J ≤ cntb P J' := by
  simp only [cntb, cnt]
  refine Set.ncard_le_ncard ?_ (Set.toFinite _)
  rintro v ⟨h1, h2⟩
  exact ⟨h1, by omega⟩

lemma cntb_full (P : Fin m → Prop) : cntb P m = cnt P := by
  have : {v : Fin m | P v ∧ (v : ℕ) < m} = {v : Fin m | P v} := by
    ext v; simp
  simp only [cntb, cnt, this]

/-- If `P` has at most as many elements as `P ∧ Q`, then `P` implies `Q`. -/
lemma forall_of_cnt_le (P Q : Fin m → Prop) (h : cnt P ≤ cnt (fun u => P u ∧ Q u)) :
    ∀ u, P u → Q u := by
  have hsub : {u : Fin m | P u ∧ Q u} ⊆ {u : Fin m | P u} := fun _ hu => hu.1
  have heq := Set.eq_of_subset_of_ncard_le hsub h (Set.toFinite _)
  intro u hu
  have : u ∈ {u : Fin m | P u ∧ Q u} := by rw [heq]; exact hu
  exact this.2

/-! ### The state space -/

/-- Configurations of the counting machine.

* `lvl i c` : starting level `i`, having established that level `i` has `c` vertices.
* `outer i c j c'` : looping over vertices, `j` vertices processed, `c'` of which were
  found to be in level `i+1`.
* `walkY i c j c' w k` : certifying that vertex number `j` is in level `i+1`, currently
  at vertex `w` after `k` steps.
* `no i c j c' v jj d` : certifying that `v` is not in level `i+1`, having processed `jj`
  vertices and certified `d` of them to be in level `i` and unrelated to `v`.
* `walkN i c j c' v jj d w k` : certifying that vertex number `jj` is in level `i`,
  currently at vertex `w` after `k` steps.
* `acc` : the accepting configuration.
-/
inductive St (m : ℕ) where
  | lvl (i c : Fin (m + 2)) : St m
  | outer (i c j c' : Fin (m + 2)) : St m
  | walkY (i c j c' : Fin (m + 2)) (w : Fin m) (k : Fin (m + 2)) : St m
  | no (i c j c' : Fin (m + 2)) (v : Fin m) (jj d : Fin (m + 2)) : St m
  | walkN (i c j c' : Fin (m + 2)) (v : Fin m) (jj d : Fin (m + 2)) (w : Fin m)
      (k : Fin (m + 2)) : St m
  | acc : St m
  deriving DecidableEq

/-- A vertex, viewed as an index. -/
def vtx (v : Fin m) : Fin (m + 2) := ⟨v.val, by omega⟩

/-- An encoding of the configurations into a product of index types, used only to bound
the number of configurations. -/
def enc : St m →
    Fin 6 × Fin (m+2) × Fin (m+2) × Fin (m+2) × Fin (m+2) × Fin (m+2) × Fin (m+2) ×
      Fin (m+2) × Fin (m+2) × Fin (m+2)
  | .lvl i c => (0, i, c, 0, 0, 0, 0, 0, 0, 0)
  | .outer i c j c' => (1, i, c, j, c', 0, 0, 0, 0, 0)
  | .walkY i c j c' w k => (2, i, c, j, c', vtx w, k, 0, 0, 0)
  | .no i c j c' v jj d => (3, i, c, j, c', vtx v, jj, d, 0, 0)
  | .walkN i c j c' v jj d w k => (4, i, c, j, c', vtx v, jj, d, vtx w, k)
  | .acc => (5, 0, 0, 0, 0, 0, 0, 0, 0, 0)

lemma enc_inj : Function.Injective (enc (m := m)) := by
  intro a b h
  cases a <;> cases b <;>
    simp only [enc, Prod.mk.injEq] at h <;>
    (try exact absurd h.1 (by decide)) <;>
    obtain ⟨-, h⟩ := h <;>
    simp_all [vtx, Fin.ext_iff]

noncomputable instance : Fintype (St m) := Fintype.ofInjective _ (enc_inj (m := m))

lemma card_St (m : ℕ) : Fintype.card (St m) ≤ 6 * (m + 2) ^ 9 := by
  have := Fintype.card_le_of_injective _ (enc_inj (m := m))
  simpa [Fintype.card_prod, pow_succ, Nat.mul_assoc] using this

/-! ### The transitions -/

/-- The guarded transitions of the counting machine. -/
noncomputable def E (r : Fin m → Fin m → Lit n) (s t : Fin m) : St m → St m → Lit n
  -- start the loop over vertices at the current level
  | .lvl i c, .outer i2 c2 j c2' =>
      if i2 = i ∧ c2 = c ∧ (j : ℕ) = 0 ∧ (c2' : ℕ) = 0 then .always else .never
  -- start the final check that `t` is not in level `i+1`
  | .lvl i c, .no i2 c2 j c2' v jj d =>
      if i2 = i ∧ c2 = c ∧ (j : ℕ) = 0 ∧ (c2' : ℕ) = 0 ∧ v = t ∧ (jj : ℕ) = 0 ∧ (d : ℕ) = 0
        then .always else .never
  -- guess that vertex number `j` is in level `i+1`, and start certifying it
  | .outer i c j c', .walkY i2 c2 j2 c2' w k =>
      if i2 = i ∧ c2 = c ∧ j2 = j ∧ c2' = c' ∧ w = s ∧ (k : ℕ) = 0 ∧ (j : ℕ) < m
        then .always else .never
  -- one step of the walk (waiting is allowed)
  | .walkY i c j c' w k, .walkY i2 c2 j2 c2' w2 k2 =>
      if i2 = i ∧ c2 = c ∧ j2 = j ∧ c2' = c' ∧ (k2 : ℕ) = (k : ℕ) + 1 then
        (if w2 = w then .always else r w w2) else .never
  -- the walk arrived at vertex number `j` in exactly `i+1` steps: count it
  | .walkY i c j c' w k, .outer i2 c2 j2 c2' =>
      if i2 = i ∧ c2 = c ∧ (k : ℕ) = (i : ℕ) + 1 ∧ (w : ℕ) = (j : ℕ) ∧ (j2 : ℕ) = (j : ℕ) + 1 ∧
          (c2' : ℕ) = (c' : ℕ) + 1 then .always else .never
  -- guess that vertex number `j` is not in level `i+1`, and start certifying it
  | .outer i c j c', .no i2 c2 j2 c2' v jj d =>
      if i2 = i ∧ c2 = c ∧ j2 = j ∧ c2' = c' ∧ (v : ℕ) = (j : ℕ) ∧ (j : ℕ) < m ∧
          (jj : ℕ) = 0 ∧ (d : ℕ) = 0 then .always else .never
  -- skip vertex number `jj`, guessing it is not in level `i`
  | .no i c j c' v jj d, .no i2 c2 j2 c2' v2 jj2 d2 =>
      if i2 = i ∧ c2 = c ∧ j2 = j ∧ c2' = c' ∧ v2 = v ∧ d2 = d ∧ (jj2 : ℕ) = (jj : ℕ) + 1 ∧
          (jj : ℕ) < m then .always else .never
  -- guess that vertex number `jj` is in level `i`, and start certifying it
  | .no i c j c' v jj d, .walkN i2 c2 j2 c2' v2 jj2 d2 w k =>
      if i2 = i ∧ c2 = c ∧ j2 = j ∧ c2' = c' ∧ v2 = v ∧ jj2 = jj ∧ d2 = d ∧ w = s ∧
          (k : ℕ) = 0 ∧ (jj : ℕ) < m then .always else .never
  -- one step of the walk (waiting is allowed)
  | .walkN i c j c' v jj d w k, .walkN i2 c2 j2 c2' v2 jj2 d2 w2 k2 =>
      if i2 = i ∧ c2 = c ∧ j2 = j ∧ c2' = c' ∧ v2 = v ∧ jj2 = jj ∧ d2 = d ∧
          (k2 : ℕ) = (k : ℕ) + 1 then (if w2 = w then .always else r w w2) else .never
  -- the walk arrived at vertex number `jj` in exactly `i` steps, and that vertex is
  -- neither `v` nor a predecessor of `v`: count it
  | .walkN i c j c' v jj d w k, .no i2 c2 j2 c2' v2 jj2 d2 =>
      if i2 = i ∧ c2 = c ∧ j2 = j ∧ c2' = c' ∧ v2 = v ∧ (k : ℕ) = (i : ℕ) ∧
          (w : ℕ) = (jj : ℕ) ∧ (jj2 : ℕ) = (jj : ℕ) + 1 ∧ (d2 : ℕ) = (d : ℕ) + 1 then
        (if w = v then .never else (r w v).neg) else .never
  -- all vertices of level `i` have been enumerated and none of them reaches `v`:
  -- `v` is not in level `i+1`
  | .no i c j c' v jj d, .outer i2 c2 j2 c2' =>
      if i2 = i ∧ c2 = c ∧ c2' = c' ∧ (jj : ℕ) = m ∧ d = c ∧ (v : ℕ) = (j : ℕ) ∧
          (j2 : ℕ) = (j : ℕ) + 1 then .always else .never
  -- the level is finished: `c'` is the number of vertices of level `i+1`
  | .outer i _ j c', .lvl i2 c2 =>
      if (j : ℕ) = m ∧ (i2 : ℕ) = (i : ℕ) + 1 ∧ c2 = c' then .always else .never
  -- `t` is not in level `m+1`, hence unreachable: accept
  | .no i c _ _ v jj d, .acc =>
      if (i : ℕ) = m ∧ (jj : ℕ) = m ∧ d = c ∧ v = t then .always else .never
  | _, _ => .never

/-- The counting machine. -/
noncomputable def cmach (r : Fin m → Fin m → Lit n) (s t : Fin m) : Mach n where
  V := St m
  fV := inferInstance
  start := .lvl 0 1
  acc := .acc
  edge := E r s t

lemma cmach_step (r : Fin m → Fin m → Lit n) (s t : Fin m) (x : Fin n → Bool) (a b : St m) :
    (cmach r s t).Step x a b ↔ (E r s t a b).holds x := Iff.rfl

end CS

