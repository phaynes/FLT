import Mathlib

/-!
# Binary transport for the normalized EDS window invariant

This file isolates the polynomial certificates needed to transport Ward's product relation and its
symmetric-sum companion through Mathlib's binary `preΨ` recursion.  The theorems are deliberately
generic over a commutative ring: the elliptic-curve module only has to instantiate the local window
variables and discharge index/parity bookkeeping.
-/

namespace FLTMethodology.Torsion

variable {R : Type*} [CommRing R]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The expanded ideal-membership certificate needs more normalization budget than the default.
theorem prePsiWindow_evenCenter_products
    (Q C L pm3 pm2 pm1 p0 p1 p2 p3 : R)
    (h0 : p1 * pm3 = Q * (p0 * pm2) - C * pm1 ^ 2)
    (h1 : pm2 ^ 2 * p1 + pm3 * p0 ^ 2 = L * pm2 * pm1 * p0 - pm1 ^ 3)
    (h2 : p2 * pm2 = p1 * pm1 - C * p0 ^ 2)
    (h3 : pm1 ^ 2 * p2 + pm2 * p1 ^ 2 = L * pm1 * p0 * p1 - Q * p0 ^ 3)
    (h4 : p3 * pm1 = Q * (p2 * p0) - C * p1 ^ 2)
    (h5 : p0 ^ 2 * p3 + pm1 * p2 ^ 2 = L * p0 * p1 * p2 - p1 ^ 3) :
    let em1 := pm2 ^ 2 * pm1 * p1 - pm3 * pm1 * p0 ^ 2
    let om1 := p1 * pm1 ^ 3 - pm2 * p0 ^ 3 * Q
    let e0 := pm1 ^ 2 * p0 * p2 - pm2 * p0 * p1 ^ 2
    let o0 := p2 * p0 ^ 3 * Q - pm1 * p1 ^ 3
    let e1 := p0 ^ 2 * p1 * p3 - pm1 * p1 * p2 ^ 2
    let o1 := p3 * p1 ^ 3 - p0 * p2 ^ 3 * Q
    e1 * em1 = o0 * om1 - C * e0 ^ 2 ∧
      o1 * om1 = Q * (e1 * e0) - C * o0 ^ 2 := by
  dsimp only
  constructor
  · linear_combination
      (-p0 ^ 2 * p2 * (2 * p1 ^ 2 * pm2 - p2 * pm1 ^ 2)) * h0 +
      (-p1 * (Q * p0 ^ 3 * p2 - p1 ^ 3 * pm1 - p1 ^ 2 * p2 * pm2)) * h1 +
      (p1 ^ 4 * pm2 ^ 2) * h2 +
      (Q * p0 ^ 3 * p2 * pm2 + p0 ^ 2 * p1 * p2 * pm3 -
        p1 ^ 3 * pm1 * pm2 - 2 * p1 ^ 2 * p2 * pm2 ^ 2) * h3 +
      (-p1 * pm1 * (p0 ^ 2 * pm3 - p1 * pm2 ^ 2)) * h5
  · linear_combination
      (Q * p0 * p2 * (Q * p0 ^ 3 * p2 - 2 * p1 ^ 3 * pm1)) * h2 +
      (Q * p0 * p1 * p2 ^ 2 * pm1) * h3 +
      (p1 ^ 4 * pm1 ^ 2) * h4 +
      (-Q * p0 * p1 * p2 * pm1 ^ 2) * h5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
-- The expanded ideal-membership certificate needs more normalization budget than the default.
theorem prePsiWindow_oddCenter_products
    (Q C L pm3 pm2 pm1 p0 p1 p2 p3 : R)
    (h0 : p1 * pm3 = p0 * pm2 - C * pm1 ^ 2)
    (h1 : pm2 ^ 2 * p1 + pm3 * p0 ^ 2 = L * pm2 * pm1 * p0 - Q * pm1 ^ 3)
    (h2 : p2 * pm2 = Q * (p1 * pm1) - C * p0 ^ 2)
    (h3 : pm1 ^ 2 * p2 + pm2 * p1 ^ 2 = L * pm1 * p0 * p1 - p0 ^ 3)
    (h4 : p3 * pm1 = p2 * p0 - C * p1 ^ 2)
    (h5 : p0 ^ 2 * p3 + pm1 * p2 ^ 2 = L * p0 * p1 * p2 - Q * p1 ^ 3) :
    let em1 := pm2 ^ 2 * pm1 * p1 - pm3 * pm1 * p0 ^ 2
    let om1 := p1 * pm1 ^ 3 * Q - pm2 * p0 ^ 3
    let e0 := pm1 ^ 2 * p0 * p2 - pm2 * p0 * p1 ^ 2
    let o0 := p2 * p0 ^ 3 - pm1 * p1 ^ 3 * Q
    let e1 := p0 ^ 2 * p1 * p3 - pm1 * p1 * p2 ^ 2
    let o1 := p3 * p1 ^ 3 * Q - p0 * p2 ^ 3
    e1 * em1 = o0 * om1 - C * e0 ^ 2 ∧
      o1 * om1 = Q * (e1 * e0) - C * o0 ^ 2 := by
  dsimp only
  constructor
  · linear_combination
      (-p0 ^ 2 * p2 * (2 * p1 ^ 2 * pm2 - p2 * pm1 ^ 2)) * h0 +
      (-p1 * (-Q * p1 ^ 3 * pm1 + p0 ^ 3 * p2 - p1 ^ 2 * p2 * pm2)) * h1 +
      (p1 ^ 4 * pm2 ^ 2) * h2 +
      (-Q * p1 ^ 3 * pm1 * pm2 + p0 ^ 3 * p2 * pm2 +
        p0 ^ 2 * p1 * p2 * pm3 - 2 * p1 ^ 2 * p2 * pm2 ^ 2) * h3 +
      (-p1 * pm1 * (p0 ^ 2 * pm3 - p1 * pm2 ^ 2)) * h5
  · linear_combination
      (p0 * p2 * (-2 * Q * p1 ^ 3 * pm1 + p0 ^ 3 * p2)) * h2 +
      (Q * p0 * p1 * p2 ^ 2 * pm1) * h3 +
      (Q ^ 2 * p1 ^ 4 * pm1 ^ 2) * h4 +
      (-Q * p0 * p1 * p2 * pm1 ^ 2) * h5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 4000000 in
-- The two symmetric-sum certificates contain higher-degree products of the local window terms.
theorem prePsiWindow_evenCenter_sums
    (Q C L pm3 pm2 pm1 p0 p1 p2 p3 : R)
    (_h0 : p1 * pm3 = Q * (p0 * pm2) - C * pm1 ^ 2)
    (h1 : pm2 ^ 2 * p1 + pm3 * p0 ^ 2 = L * pm2 * pm1 * p0 - pm1 ^ 3)
    (_h2 : p2 * pm2 = p1 * pm1 - C * p0 ^ 2)
    (h3 : pm1 ^ 2 * p2 + pm2 * p1 ^ 2 = L * pm1 * p0 * p1 - Q * p0 ^ 3)
    (_h4 : p3 * pm1 = Q * (p2 * p0) - C * p1 ^ 2)
    (h5 : p0 ^ 2 * p3 + pm1 * p2 ^ 2 = L * p0 * p1 * p2 - p1 ^ 3) :
    let em1 := pm2 ^ 2 * pm1 * p1 - pm3 * pm1 * p0 ^ 2
    let om1 := p1 * pm1 ^ 3 - pm2 * p0 ^ 3 * Q
    let e0 := pm1 ^ 2 * p0 * p2 - pm2 * p0 * p1 ^ 2
    let o0 := p2 * p0 ^ 3 * Q - pm1 * p1 ^ 3
    let e1 := p0 ^ 2 * p1 * p3 - pm1 * p1 * p2 ^ 2
    let o1 := p3 * p1 ^ 3 - p0 * p2 ^ 3 * Q
    om1 ^ 2 * e1 + em1 * o0 ^ 2 = L * om1 * e0 * o0 - Q * e0 ^ 3 ∧
      e0 ^ 2 * o1 + om1 * e1 ^ 2 = L * e0 * o0 * e1 - o0 ^ 3 := by
  dsimp only
  constructor
  · linear_combination
      (-pm1 * (Q ^ 2 * p0 ^ 6 * p2 ^ 2 - 2 * p0 ^ 2 * p1 ^ 3 * p3 * pm1 ^ 2 -
        p1 ^ 6 * pm1 ^ 2 + 2 * p1 ^ 5 * p2 * pm1 * pm2)) * h1 +
      (-Q * p0 ^ 3 * p1 ^ 4 * pm2 ^ 2 + Q * p0 ^ 3 * p2 ^ 2 * pm1 ^ 4 +
        2 * p0 ^ 2 * p1 ^ 3 * p2 * pm1 ^ 2 * pm3 -
        2 * p0 ^ 2 * p1 ^ 2 * p3 * pm1 ^ 3 * pm2 +
        2 * p1 ^ 4 * p2 * pm1 ^ 2 * pm2 ^ 2 -
        2 * p1 ^ 2 * p2 ^ 2 * pm1 ^ 4 * pm2) * h3 +
      (p1 * (Q ^ 2 * p0 ^ 6 * pm2 ^ 2 - 2 * p0 ^ 2 * p1 ^ 2 * pm1 ^ 3 * pm3 -
        p1 ^ 2 * pm1 ^ 6 + 2 * p1 * p2 * pm1 ^ 5 * pm2)) * h5
  · linear_combination
      (Q ^ 2 * p0 ^ 6 * p2 ^ 3 + Q * p0 ^ 5 * p2 ^ 2 * p3 * pm1 -
        2 * Q * p0 ^ 3 * p1 ^ 3 * p2 ^ 2 * pm1 -
        Q * p0 ^ 3 * p1 ^ 2 * p2 ^ 3 * pm2 + p0 ^ 2 * p1 ^ 5 * p3 * pm2 -
        2 * p0 ^ 2 * p1 ^ 3 * p2 * p3 * pm1 ^ 2 +
        p1 ^ 6 * p2 * pm1 ^ 2 + p1 ^ 3 * p2 ^ 3 * pm1 ^ 3) * h3 +
      (-Q ^ 2 * p0 ^ 6 * p2 ^ 2 * pm1 - Q * p0 ^ 5 * p1 ^ 2 * p3 * pm2 +
        2 * Q * p0 ^ 3 * p1 ^ 3 * p2 * pm1 ^ 2 +
        2 * Q * p0 ^ 3 * p1 ^ 2 * p2 ^ 2 * pm1 * pm2 -
        Q * p0 ^ 3 * p2 ^ 3 * pm1 ^ 3 + p0 ^ 2 * p1 ^ 3 * p3 * pm1 ^ 3 -
        p1 ^ 6 * pm1 ^ 3 - p1 ^ 5 * p2 * pm1 ^ 2 * pm2) * h5

set_option maxRecDepth 10000 in
set_option maxHeartbeats 8000000 in
-- The odd-center even-target certificate is the largest of the four symmetric-sum identities.
theorem prePsiWindow_oddCenter_sums
    (Q C L pm3 pm2 pm1 p0 p1 p2 p3 : R)
    (h0 : p1 * pm3 = p0 * pm2 - C * pm1 ^ 2)
    (h1 : pm2 ^ 2 * p1 + pm3 * p0 ^ 2 = L * pm2 * pm1 * p0 - Q * pm1 ^ 3)
    (_h2 : p2 * pm2 = Q * (p1 * pm1) - C * p0 ^ 2)
    (h3 : pm1 ^ 2 * p2 + pm2 * p1 ^ 2 = L * pm1 * p0 * p1 - p0 ^ 3)
    (h4 : p3 * pm1 = p2 * p0 - C * p1 ^ 2)
    (h5 : p0 ^ 2 * p3 + pm1 * p2 ^ 2 = L * p0 * p1 * p2 - Q * p1 ^ 3) :
    let em1 := pm2 ^ 2 * pm1 * p1 - pm3 * pm1 * p0 ^ 2
    let om1 := p1 * pm1 ^ 3 * Q - pm2 * p0 ^ 3
    let e0 := pm1 ^ 2 * p0 * p2 - pm2 * p0 * p1 ^ 2
    let o0 := p2 * p0 ^ 3 - pm1 * p1 ^ 3 * Q
    let e1 := p0 ^ 2 * p1 * p3 - pm1 * p1 * p2 ^ 2
    let o1 := p3 * p1 ^ 3 * Q - p0 * p2 ^ 3
    om1 ^ 2 * e1 + em1 * o0 ^ 2 = L * om1 * e0 * o0 - Q * e0 ^ 3 ∧
      e0 ^ 2 * o1 + om1 * e1 ^ 2 = L * e0 * o0 * e1 - o0 ^ 3 := by
  dsimp only
  constructor
  · linear_combination
      (p0 ^ 2 * p1 ^ 2 *
        (L * p0 ^ 3 * p3 * pm1 * pm2 + Q * p0 ^ 3 * p2 * pm1 ^ 2 -
          p0 ^ 2 * p1 * p3 * pm2 ^ 2 - p1 * p2 ^ 2 * pm1 * pm2 ^ 2)) * h0 +
      (-p0 ^ 2 *
        (p0 ^ 4 * p2 ^ 2 * pm1 + p0 ^ 3 * p1 ^ 2 * p3 * pm2 -
          p0 ^ 3 * p2 * p3 * pm1 ^ 2 + p0 ^ 2 * p3 ^ 2 * pm1 ^ 3 +
          p0 * p1 ^ 2 * p2 ^ 2 * pm1 * pm2 -
          p1 ^ 2 * p2 * p3 * pm1 ^ 2 * pm2)) * h1 +
      (Q ^ 2 * p1 ^ 5 * pm1 ^ 3 * pm2 - Q ^ 2 * p1 ^ 3 * p2 * pm1 ^ 5 -
        Q * p0 ^ 3 * p1 ^ 4 * pm2 ^ 2 +
        Q * p0 ^ 3 * p1 ^ 2 * p2 * pm1 ^ 2 * pm2 +
        Q * p0 ^ 2 * p1 ^ 3 * p2 * pm1 ^ 2 * pm3 -
        Q * p0 ^ 2 * p2 * p3 * pm1 ^ 5 + p0 ^ 4 * p1 ^ 2 * p3 * pm2 * pm3 -
        p0 ^ 4 * p2 * p3 * pm1 ^ 2 * pm3 +
        p0 ^ 2 * p1 ^ 2 * p2 ^ 2 * pm1 * pm2 * pm3 -
        p0 ^ 2 * p1 * p2 * p3 * pm1 ^ 2 * pm2 ^ 2) * h3 +
      (-p0 ^ 2 * pm1 ^ 2 *
        (L * p0 ^ 3 * p3 * pm1 * pm2 + Q * p0 ^ 3 * p2 * pm1 ^ 2 -
          p0 ^ 2 * p1 * p3 * pm2 ^ 2 - p1 * p2 ^ 2 * pm1 * pm2 ^ 2)) * h4 +
      (p0 ^ 2 *
        (-Q * p0 * p1 ^ 2 * pm1 ^ 3 * pm2 + Q * p0 * p2 * pm1 ^ 5 -
          Q * p1 ^ 3 * pm1 ^ 3 * pm3 + Q * p3 * pm1 ^ 6 +
          p0 ^ 4 * p1 * pm2 ^ 2 + p0 ^ 2 * p3 * pm1 ^ 3 * pm3 +
          p0 * p1 * p2 * pm1 ^ 2 * pm2 ^ 2 -
          p1 ^ 2 * p2 * pm1 ^ 2 * pm2 * pm3)) * h5
  · linear_combination
      (Q ^ 2 * p1 ^ 6 * p2 * pm1 ^ 2 - 2 * Q * p0 ^ 3 * p1 ^ 3 * p2 ^ 2 * pm1 +
        Q * p0 ^ 2 * p1 ^ 5 * p3 * pm2 -
        2 * Q * p0 ^ 2 * p1 ^ 3 * p2 * p3 * pm1 ^ 2 +
        Q * p1 ^ 3 * p2 ^ 3 * pm1 ^ 3 + p0 ^ 6 * p2 ^ 3 +
        p0 ^ 5 * p2 ^ 2 * p3 * pm1 - p0 ^ 3 * p1 ^ 2 * p2 ^ 3 * pm2) * h3 +
      (-Q ^ 2 * p1 ^ 6 * pm1 ^ 3 + 2 * Q * p0 ^ 3 * p1 ^ 3 * p2 * pm1 ^ 2 +
        Q * p0 ^ 2 * p1 ^ 3 * p3 * pm1 ^ 3 - Q * p1 ^ 5 * p2 * pm1 ^ 2 * pm2 -
        p0 ^ 6 * p2 ^ 2 * pm1 - p0 ^ 5 * p1 ^ 2 * p3 * pm2 +
        2 * p0 ^ 3 * p1 ^ 2 * p2 ^ 2 * pm1 * pm2 -
        p0 ^ 3 * p2 ^ 3 * pm1 ^ 3) * h5

#print axioms prePsiWindow_evenCenter_products
#print axioms prePsiWindow_oddCenter_products
#print axioms prePsiWindow_evenCenter_sums
#print axioms prePsiWindow_oddCenter_sums

end FLTMethodology.Torsion
