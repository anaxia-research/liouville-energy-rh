import Mathlib

/-!
# The balancing step of the window theorem

This file proves, independently of the formal proof of the window theorem, the elementary
step in which the exponent `1/2` appears: Zhang's Lemma 6.1 with explicit constants, and
the fact that no choice of the free parameter can improve that exponent. It also proves the
elementary part of Zhang's Lemma 2.2 (the gamma tail): the positivity of the rate constant
`c_δ`, the range of the integer `k`, the position of the upper end of the window, and the
final comparison `2 (q e^{c_δ})^{-(k+1)} ≤ σ^{-k}`.

Throughout, `A = x ^ (1/2)`, `E = x ^ (ε/8)` and `W = x ^ (C ε)`. The algebraic forms
`balance_core` and `optimal_core` are stated in these variables, and `zhang_lemma_6_1`
restates the first in the original real-power form.
-/

namespace LiouvilleEnergyRH.WindowBalance

open Real

/-- Zhang's Lemma 6.1 in algebraic form: the balancing inequality forces
`z ≤ 26 A W E²¹`, that is `z ≤ 26 x^{1/2 + (C + 21/8) ε}`. -/
theorem balance_core {A E W n t v₂ m b k a z : ℝ}
    (hA : 0 < A) (hA3 : 3 ≤ A ^ 2) (hE : 1 ≤ E) (hW : 1 ≤ W)
    (hn : 0 < n) (ht : 0 < t) (hv : 0 < v₂) (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (h1 : a ≤ 2 * A ^ 2 * b) (h2 : n ≤ 2 * E * t) (h3 : n ≤ E ^ 8 * v₂) (h4 : v₂ ≤ n)
    (h5 : A ≤ E ^ 8 * m) (h6 : m ≤ A * E ^ 4) (h7 : A ^ 2 * m ≤ k)
    (h8 : E ^ 8 * k ≤ n ^ 2 * A)
    (hz : t * m * b * v₂ / (2 * n) * (z - 4 * A * E ^ 8) ≤
      W * (t * a * (1 + m ^ 2 / k) + m * (2 * n * m * b * E ^ 8 + v₂ * k * b * E ^ 16 / n ^ 2))
        + 2 * t * m * b / A ^ 2) :
    z ≤ 26 * A * W * E ^ 21 := by
  have hE0 : 0 < E := lt_of_lt_of_le one_pos hE
  have hA1 : 1 ≤ A := by nlinarith
  have hQ : 0 < t * m * b := by positivity
  have hE8 : 1 ≤ E ^ 8 := one_le_pow₀ hE
  have hE13 : 1 ≤ E ^ 13 := one_le_pow₀ hE
  have hE8_13 : E ^ 8 ≤ E ^ 13 := pow_le_pow_right₀ hE (by norm_num)
  have hE9_13 : E ^ 9 ≤ E ^ 13 := pow_le_pow_right₀ hE (by norm_num)
  have hE8_21 : E ^ 8 ≤ E ^ 21 := pow_le_pow_right₀ hE (by norm_num)
  have hAE : 1 ≤ A * E ^ 13 := one_le_mul_of_one_le_of_one_le hA1 hE13
  have hWAE : 1 ≤ W * (A * E ^ 13) := one_le_mul_of_one_le_of_one_le hW hAE
  -- first summand: `t a ≤ Q · 2 A E⁸`
  have T1 : t * a ≤ t * m * b * (2 * A * E ^ 8) := by
    have hAA : A ^ 2 ≤ A * (E ^ 8 * m) := by
      rw [pow_two]; exact mul_le_mul_of_nonneg_left h5 hA.le
    have i1 : 2 * b * A ^ 2 ≤ 2 * b * (A * (E ^ 8 * m)) :=
      mul_le_mul_of_nonneg_left hAA (by positivity)
    have : a ≤ m * b * (2 * A * E ^ 8) := by linarith
    calc t * a ≤ t * (m * b * (2 * A * E ^ 8)) := mul_le_mul_of_nonneg_left this ht.le
      _ = t * m * b * (2 * A * E ^ 8) := by ring
  -- second summand: `t a m² / k ≤ 2 Q`
  have T2 : t * a * (m ^ 2 / k) ≤ t * m * b * 2 := by
    have key : a * m ≤ 2 * b * k := by
      have i1 : a * m ≤ 2 * A ^ 2 * b * m := mul_le_mul_of_nonneg_right h1 hm.le
      have i2 : 2 * b * (A ^ 2 * m) ≤ 2 * b * k := mul_le_mul_of_nonneg_left h7 (by positivity)
      linarith
    rw [show t * a * (m ^ 2 / k) = t * m * (a * m) / k by ring, div_le_iff₀ hk]
    have := mul_le_mul_of_nonneg_left key (by positivity : (0:ℝ) ≤ t * m)
    linarith
  -- third summand: `2 n m² b E⁸ ≤ Q · 4 A E¹³`
  have T3 : m * (2 * n * m * b * E ^ 8) ≤ t * m * b * (4 * A * E ^ 13) := by
    have hnm : n * m ≤ (2 * E * t) * (A * E ^ 4) := mul_le_mul h2 h6 hm.le (by positivity)
    calc m * (2 * n * m * b * E ^ 8) = (n * m) * (2 * m * b * E ^ 8) := by ring
      _ ≤ ((2 * E * t) * (A * E ^ 4)) * (2 * m * b * E ^ 8) :=
          mul_le_mul_of_nonneg_right hnm (by positivity)
      _ = t * m * b * (4 * A * E ^ 13) := by ring
  -- fourth summand: `m v₂ k b E¹⁶ / n² ≤ Q · 2 A E⁹`
  have T4 : m * (v₂ * k * b * E ^ 16 / n ^ 2) ≤ t * m * b * (2 * A * E ^ 9) := by
    have hvk : v₂ * (E ^ 8 * k) ≤ n * (n ^ 2 * A) := mul_le_mul h4 h8 (by positivity) hn.le
    have hn2 : 0 < n ^ 2 := by positivity
    calc m * (v₂ * k * b * E ^ 16 / n ^ 2) = m * b * E ^ 8 * (v₂ * (E ^ 8 * k)) / n ^ 2 := by
          ring
      _ ≤ m * b * E ^ 8 * (n * (n ^ 2 * A)) / n ^ 2 := by
          apply div_le_div_of_nonneg_right _ hn2.le
          exact mul_le_mul_of_nonneg_left hvk (by positivity)
      _ = m * b * E ^ 8 * A * n := by field_simp
      _ ≤ m * b * E ^ 8 * A * (2 * E * t) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = t * m * b * (2 * A * E ^ 9) := by ring
  -- the bracket: `B ≤ 10 Q A E¹³`
  have hB : t * a * (1 + m ^ 2 / k) + m * (2 * n * m * b * E ^ 8 + v₂ * k * b * E ^ 16 / n ^ 2)
      ≤ t * m * b * (10 * (A * E ^ 13)) := by
    have e : t * a * (1 + m ^ 2 / k) + m * (2 * n * m * b * E ^ 8 + v₂ * k * b * E ^ 16 / n ^ 2)
        = t * a + t * a * (m ^ 2 / k) + m * (2 * n * m * b * E ^ 8)
          + m * (v₂ * k * b * E ^ 16 / n ^ 2) := by ring
    rw [e]
    have u1 : A * E ^ 8 ≤ A * E ^ 13 := mul_le_mul_of_nonneg_left hE8_13 hA.le
    have u4 : A * E ^ 9 ≤ A * E ^ 13 := mul_le_mul_of_nonneg_left hE9_13 hA.le
    have s1 : t * m * b * (2 * A * E ^ 8) ≤ t * m * b * (2 * (A * E ^ 13)) := by
      apply mul_le_mul_of_nonneg_left _ hQ.le; linarith
    have s2 : t * m * b * 2 ≤ t * m * b * (2 * (A * E ^ 13)) := by
      apply mul_le_mul_of_nonneg_left _ hQ.le; linarith
    have s4 : t * m * b * (2 * A * E ^ 9) ≤ t * m * b * (2 * (A * E ^ 13)) := by
      apply mul_le_mul_of_nonneg_left _ hQ.le; linarith
    linarith [T1, T2, T3, T4, s1, s2, s4]
  -- the right side of the balancing inequality: `R ≤ 11 Q W A E¹³`
  have hR : W * (t * a * (1 + m ^ 2 / k) + m * (2 * n * m * b * E ^ 8
        + v₂ * k * b * E ^ 16 / n ^ 2)) + 2 * t * m * b / A ^ 2
      ≤ t * m * b * (11 * (W * (A * E ^ 13))) := by
    have r1 := mul_le_mul_of_nonneg_left hB (by linarith : (0:ℝ) ≤ W)
    have r2 : 2 * t * m * b / A ^ 2 ≤ t * m * b * (2 / 3) := by
      rw [div_le_iff₀ (by positivity)]
      have := mul_le_mul_of_nonneg_left hA3 hQ.le
      linarith
    have r3 : t * m * b * (2 / 3) ≤ t * m * b * (W * (A * E ^ 13)) := by
      apply mul_le_mul_of_nonneg_left _ hQ.le; linarith
    linarith [r1, r2, r3]
  -- clear the coefficient of `z`
  rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at hz
  have hfin : t * m * b * v₂ * (z - 4 * A * E ^ 8)
      ≤ t * m * b * v₂ * (22 * (W * A * E ^ 21)) := by
    calc t * m * b * v₂ * (z - 4 * A * E ^ 8)
        ≤ (W * (t * a * (1 + m ^ 2 / k) + m * (2 * n * m * b * E ^ 8
            + v₂ * k * b * E ^ 16 / n ^ 2)) + 2 * t * m * b / A ^ 2) * (2 * n) := hz
      _ ≤ t * m * b * (11 * (W * (A * E ^ 13))) * (2 * n) :=
          mul_le_mul_of_nonneg_right hR (by positivity)
      _ ≤ t * m * b * (11 * (W * (A * E ^ 13))) * (2 * (E ^ 8 * v₂)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith
      _ = t * m * b * v₂ * (22 * (W * A * E ^ 21)) := by ring
  have hz' : z - 4 * A * E ^ 8 ≤ 22 * (W * A * E ^ 21) :=
    le_of_mul_le_mul_left hfin (by positivity)
  have hlast : 4 * A * E ^ 8 ≤ 4 * (W * A * E ^ 21) := by
    have : A * E ^ 8 ≤ W * A * E ^ 21 := by
      have i1 : A * E ^ 8 ≤ A * E ^ 21 := mul_le_mul_of_nonneg_left hE8_21 hA.le
      have i2 : A * E ^ 21 ≤ W * (A * E ^ 21) := le_mul_of_one_le_left (by positivity) hW
      linarith
    linarith
  linarith

/-- Zhang's Lemma 6.1 in its original form, with real powers of `x`. -/
theorem zhang_lemma_6_1 {x ε C n t v₂ m b k a z : ℝ}
    (hx : 3 ≤ x) (hε : 0 < ε) (hC : 0 ≤ C)
    (hn : 0 < n) (ht : 0 < t) (hv : 0 < v₂) (hm : 0 < m) (hb : 0 < b) (hk : 0 < k)
    (h1 : a ≤ 2 * x * b) (h2 : n / 2 * x ^ (-(ε / 8)) ≤ t) (h3 : n * x ^ (-ε) ≤ v₂)
    (h4 : v₂ ≤ n) (h5 : x ^ ((1:ℝ) / 2 - ε) ≤ m) (h6 : m ≤ x ^ ((1:ℝ) / 2 + ε / 2))
    (h7 : x * m ≤ k) (h8 : k ≤ n ^ 2 * x ^ ((1:ℝ) / 2 - ε))
    (hz : t * m * b * v₂ / (2 * n) * (z - 4 * x ^ ((1:ℝ) / 2 + ε)) ≤
      x ^ (C * ε) * (t * a * (1 + m ^ 2 / k)
        + m * (2 * n * m * b * x ^ ε + v₂ * k * b * x ^ (2 * ε) / n ^ 2))
        + 2 * t * m * b / x) :
    z ≤ 26 * x ^ ((1:ℝ) / 2 + (C + 21 / 8) * ε) := by
  have hx0 : 0 < x := by linarith
  set A := x ^ ((1:ℝ) / 2) with hAdef
  set E := x ^ (ε / 8) with hEdef
  set W := x ^ (C * ε) with hWdef
  have hpow : ∀ j : ℕ, E ^ j = x ^ (ε / 8 * j) := fun j => by
    rw [hEdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
  have hA0 : 0 < A := Real.rpow_pos_of_pos hx0 _
  have hE0 : 0 < E := Real.rpow_pos_of_pos hx0 _
  have hAsq : A ^ 2 = x := by
    rw [hAdef, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
  have hE1 : 1 ≤ E := Real.one_le_rpow (by linarith) (by positivity)
  have hW1 : 1 ≤ W := Real.one_le_rpow (by linarith) (by positivity)
  have e8 : x ^ ε = E ^ 8 := by rw [hpow]; congr 1; push_cast; ring
  have e16 : x ^ (2 * ε) = E ^ 16 := by rw [hpow]; congr 1; push_cast; ring
  have eneg8 : x ^ (-(ε / 8)) = E⁻¹ := by rw [Real.rpow_neg hx0.le]
  have eneg : x ^ (-ε) = (E ^ 8)⁻¹ := by rw [Real.rpow_neg hx0.le, e8]
  have ehalfm : x ^ ((1:ℝ) / 2 - ε) = A / E ^ 8 := by rw [Real.rpow_sub hx0, e8]
  have ehalfp2 : x ^ ((1:ℝ) / 2 + ε / 2) = A * E ^ 4 := by
    rw [Real.rpow_add hx0, hpow]; congr 2; push_cast; ring
  have ehalfp : x ^ ((1:ℝ) / 2 + ε) = A * E ^ 8 := by rw [Real.rpow_add hx0, e8]
  have egoal : x ^ ((1:ℝ) / 2 + (C + 21 / 8) * ε) = A * W * E ^ 21 := by
    rw [show (1:ℝ) / 2 + (C + 21 / 8) * ε = 1 / 2 + C * ε + ε / 8 * ((21:ℕ):ℝ) by
      push_cast; ring, Real.rpow_add hx0, Real.rpow_add hx0, ← hpow]
  have hE8pos : 0 < E ^ 8 := by positivity
  rw [egoal]
  have h2' : n ≤ 2 * E * t := by
    rw [eneg8] at h2
    have : n / 2 * E⁻¹ * (2 * E) ≤ t * (2 * E) := mul_le_mul_of_nonneg_right h2 (by positivity)
    have e : n / 2 * E⁻¹ * (2 * E) = n := by field_simp
    linarith
  have h3' : n ≤ E ^ 8 * v₂ := by
    rw [eneg] at h3
    have := mul_le_mul_of_nonneg_left h3 hE8pos.le
    have e : E ^ 8 * (n * (E ^ 8)⁻¹) = n := by field_simp
    linarith
  have h5' : A ≤ E ^ 8 * m := by
    rw [ehalfm, div_le_iff₀ hE8pos] at h5; linarith
  have h6' : m ≤ A * E ^ 4 := by rwa [ehalfp2] at h6
  have h7' : A ^ 2 * m ≤ k := by rwa [hAsq]
  have h8' : E ^ 8 * k ≤ n ^ 2 * A := by
    rw [ehalfm] at h8
    have := mul_le_mul_of_nonneg_left h8 hE8pos.le
    have e : E ^ 8 * (n ^ 2 * (A / E ^ 8)) = n ^ 2 * A := by field_simp
    linarith
  have h1' : a ≤ 2 * A ^ 2 * b := by rwa [hAsq]
  have hA3 : 3 ≤ A ^ 2 := by rw [hAsq]; exact hx
  rw [ehalfp, e8, e16, ← hAsq, ← mul_assoc 4 A] at hz
  have := balance_core hA0 hA3 hE1 hW1 hn ht hv hm hb hk h1' h2' h3' h4 h5' h6' h7' h8' hz
  linarith

/-- The last claim of Lemma 6.1: once `26 ≤ x^{3ε/8}`, the bound becomes
`z ≤ x^{1/2 + (C+3) ε}`. -/
theorem balance_core_final {A E W z : ℝ} (hA : 0 < A) (hW : 1 ≤ W) (h26 : 26 ≤ E ^ 3)
    (hz : z ≤ 26 * A * W * E ^ 21) : z ≤ A * W * E ^ 24 := by
  have hAW : 0 ≤ A * W * E ^ 21 := by
    have h3 : 0 < E ^ 3 := by linarith
    have h21 : E ^ 21 = (E ^ 3) ^ 7 := by ring
    have : 0 < E ^ 21 := by rw [h21]; positivity
    have : 0 < W := by linarith
    positivity
  calc z ≤ 26 * A * W * E ^ 21 := hz
    _ = 26 * (A * W * E ^ 21) := by ring
    _ ≤ E ^ 3 * (A * W * E ^ 21) := mul_le_mul_of_nonneg_right h26 hAW
    _ = A * W * E ^ 24 := by ring

/-- Optimality, first step: keeping two of the four summands, `2B/Q ≥ x/m + 2 m x^ε`. -/
theorem optimal_core {A E n t v₂ m b k a : ℝ}
    (hn : 0 < n) (ht : 0 < t) (hv : 0 < v₂) (hm : 0 < m) (hb : 0 < b) (hk : 0 < k) (ha : A ^ 2 * b / 2 ≤ a) (ht2 : t ≤ 2 * n) :
    A ^ 2 / m + 2 * m * E ^ 8 ≤
      2 * (t * a * (1 + m ^ 2 / k) + m * (2 * n * m * b * E ^ 8 + v₂ * k * b * E ^ 16 / n ^ 2))
        / (t * m * b) := by
  have hQ : 0 < t * m * b := by positivity
  rw [le_div_iff₀ hQ]
  have e : (A ^ 2 / m + 2 * m * E ^ 8) * (t * m * b) = A ^ 2 * t * b + 2 * m ^ 2 * E ^ 8 * t * b := by
    field_simp
  rw [e]
  have p1 : 0 ≤ t * a * (m ^ 2 / k) := by
    have : 0 ≤ a := le_trans (by positivity) ha
    positivity
  have p2 : 0 ≤ m * (v₂ * k * b * E ^ 16 / n ^ 2) := by positivity
  have q1 : A ^ 2 * t * b ≤ 2 * (t * a) := by
    have := mul_le_mul_of_nonneg_left ha (by positivity : (0:ℝ) ≤ 2 * t)
    linarith
  have q2 : 2 * m ^ 2 * E ^ 8 * t * b ≤ 2 * (m * (2 * n * m * b * E ^ 8)) := by
    have := mul_le_mul_of_nonneg_left ht2 (by positivity : (0:ℝ) ≤ m ^ 2 * E ^ 8 * b)
    linarith
  have e2 : 2 * (t * a * (1 + m ^ 2 / k) + m * (2 * n * m * b * E ^ 8
      + v₂ * k * b * E ^ 16 / n ^ 2)) = 2 * (t * a) + 2 * (t * a * (m ^ 2 / k))
      + 2 * (m * (2 * n * m * b * E ^ 8)) + 2 * (m * (v₂ * k * b * E ^ 16 / n ^ 2)) := by ring
  rw [e2]
  linarith

/-- Optimality, second step: the arithmetic–geometric mean inequality,
`x/m + 2 m x^ε ≥ 2 √2 x^{1/2 + ε/2}`, whatever the value of `m`. -/
theorem optimal_amgm {A E m : ℝ} (hA : 0 ≤ A) (hm : 0 < m) :
    2 * Real.sqrt 2 * A * E ^ 4 ≤ A ^ 2 / m + 2 * m * E ^ 8 := by
  have hprod : (A ^ 2 / m) * (2 * m * E ^ 8) = 2 * A ^ 2 * E ^ 8 := by
    field_simp
  have hsq : 8 * A ^ 2 * E ^ 8 ≤ (A ^ 2 / m + 2 * m * E ^ 8) ^ 2 := by
    nlinarith [sq_nonneg (A ^ 2 / m - 2 * m * E ^ 8)]
  have hL : 0 ≤ A ^ 2 / m + 2 * m * E ^ 8 := by positivity
  have hs : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hs0 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have hP : 0 ≤ 2 * Real.sqrt 2 * A * E ^ 4 := by
    have : 0 ≤ E ^ 4 := by positivity
    positivity
  have hPsq : (2 * Real.sqrt 2 * A * E ^ 4) ^ 2 = 8 * A ^ 2 * E ^ 8 := by
    have : (2 * Real.sqrt 2 * A * E ^ 4) ^ 2 = 4 * Real.sqrt 2 ^ 2 * A ^ 2 * E ^ 8 := by ring
    rw [this, hs]; ring
  by_contra h
  push Not at h
  have := mul_self_lt_mul_self hL h
  nlinarith

/-! ## The gamma tail (Zhang's Lemma 2.2) -/

/-- The rate function `I(v) = v - 1 - log v` of the gamma distribution is positive
away from `v = 1`. -/
theorem rate_pos {v : ℝ} (hv : 0 < v) (h1 : v ≠ 1) : 0 < v - 1 - Real.log v := by
  have := Real.log_lt_sub_one_of_pos hv h1
  linarith

/-- `c_δ = min (I (1/τ)) (I b_δ) > 0` for `τ = 1 + δ/2` and `b_δ = (1+δ)/(1+3δ/4)`. -/
theorem gamma_rate_pos {δ : ℝ} (hδ : 0 < δ) :
    0 < min ((1 + δ / 2)⁻¹ - 1 - Real.log (1 + δ / 2)⁻¹)
      ((1 + δ) / (1 + 3 * δ / 4) - 1 - Real.log ((1 + δ) / (1 + 3 * δ / 4))) := by
  have hτ : (1 : ℝ) < 1 + δ / 2 := by linarith
  have hτ0 : (0 : ℝ) < 1 + δ / 2 := by linarith
  have hd0 : (0 : ℝ) < 1 + 3 * δ / 4 := by linarith
  apply lt_min
  · apply rate_pos (inv_pos.mpr hτ0)
    intro h
    have h' : (1 + δ / 2) * (1 + δ / 2)⁻¹ = 1 + δ / 2 := by rw [h, mul_one]
    rw [mul_inv_cancel₀ (ne_of_gt hτ0)] at h'
    linarith
  · apply rate_pos (div_pos (by linarith) hd0)
    intro h
    rw [div_eq_one_iff_eq (ne_of_gt hd0)] at h
    linarith

/-- The integer `k = ⌊q τ U⌋` satisfies `U ≤ k ≤ q τ U` once `q τ ≥ 2` and `U ≥ 1`. -/
theorem gamma_k_bounds {q τ U : ℝ} (hq : 2 ≤ q * τ) (hU : 1 ≤ U) :
    U ≤ (⌊q * τ * U⌋₊ : ℝ) ∧ (⌊q * τ * U⌋₊ : ℝ) ≤ q * τ * U := by
  have hprod : 2 * U ≤ q * τ * U :=
    mul_le_mul_of_nonneg_right hq (by linarith)
  have h0 : 0 ≤ q * τ * U := by linarith
  refine ⟨?_, Nat.floor_le h0⟩
  have := Nat.lt_floor_add_one (q * τ * U)
  linarith

/-- The upper end of the window: if `U ≥ 4/(q δ)`, then
`(1+δ)/(τ + 1/(qU)) ≥ b_δ = (1+δ)/(1+3δ/4)`. -/
theorem gamma_window {δ q U : ℝ} (hδ : 0 < δ) (hq : 0 < q) (hU : 4 / (q * δ) ≤ U) :
    (1 + δ) / (1 + 3 * δ / 4) ≤ (1 + δ) / ((1 + δ / 2) + 1 / (q * U)) := by
  have hqδ : 0 < q * δ := mul_pos hq hδ
  have hU0 : 0 < U := lt_of_lt_of_le (div_pos (by norm_num) hqδ) hU
  have hqU : 0 < q * U := mul_pos hq hU0
  have h4 : 4 ≤ U * (q * δ) := (div_le_iff₀ hqδ).mp hU
  have hinv : 1 / (q * U) ≤ δ / 4 := by
    rw [div_le_div_iff₀ hqU (by norm_num)]
    nlinarith
  apply div_le_div_of_nonneg_left (by linarith) (by positivity)
  linarith

/-- The last step of Zhang's Lemma 2.2: if `q ≥ 2`, `c > 0` and `q ≥ 2/(e^c - 1)`, then
`2 (q e^c)^{-(k+1)} ≤ (q+2)^{-k}` for every `k`. -/
theorem gamma_final {q c : ℝ} (k : ℕ) (hq : 2 ≤ q) (hc : 0 < c)
    (hqc : 2 / (Real.exp c - 1) ≤ q) :
    2 * ((q * Real.exp c)⁻¹) ^ (k + 1) ≤ ((q + 2)⁻¹) ^ k := by
  have he : 1 < Real.exp c := by
    have := Real.add_one_lt_exp (ne_of_gt hc)
    linarith
  have hpos : 0 < Real.exp c - 1 := by linarith
  have h1 : 2 ≤ q * (Real.exp c - 1) := by
    have := (div_le_iff₀ hpos).mp hqc
    linarith
  have h2 : q + 2 ≤ q * Real.exp c := by nlinarith
  have hY : 0 < q + 2 := by linarith
  have hX : (q * Real.exp c)⁻¹ ≤ (q + 2)⁻¹ := inv_anti₀ hY h2
  have hX0 : 0 ≤ (q * Real.exp c)⁻¹ := by positivity
  have hp : ((q * Real.exp c)⁻¹) ^ (k + 1) ≤ ((q + 2)⁻¹) ^ (k + 1) :=
    pow_le_pow_left₀ hX0 hX _
  have hY2 : 2 * (q + 2)⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one hY]
    linarith
  have hYk : 0 ≤ ((q + 2)⁻¹) ^ k := by positivity
  calc 2 * ((q * Real.exp c)⁻¹) ^ (k + 1) ≤ 2 * ((q + 2)⁻¹) ^ (k + 1) := by linarith
    _ = (2 * (q + 2)⁻¹) * ((q + 2)⁻¹) ^ k := by ring
    _ ≤ 1 * ((q + 2)⁻¹) ^ k := mul_le_mul_of_nonneg_right hY2 hYk
    _ = ((q + 2)⁻¹) ^ k := one_mul _

end LiouvilleEnergyRH.WindowBalance
