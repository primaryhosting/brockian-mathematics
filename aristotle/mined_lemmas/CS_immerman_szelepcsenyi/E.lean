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
