import Mathlib

/-!
# Primes between consecutive powers

Corollary `GH:cor:powers` (i) of the paper. If every interval `[x, x + (22/25) √x log x]`
with `x ≥ 4` contains a prime, which is the theorem of Carneiro, Milinovich and
Soundararajan under the Riemann hypothesis, then for all `m ≥ 3` and `n ≥ 1` the interval
`(n ^ m, (n + 1) ^ m)` contains a prime. The gap bound is taken as a hypothesis.
-/

namespace ReadableRH

/-- `y ^ (k + 1) + (k + 1) y ^ k ≤ (y + 1) ^ (k + 1)` for `y ≥ 0`. -/
theorem pow_add_succ_mul_le (y : ℝ) (hy : 0 ≤ y) (k : ℕ) :
    y ^ (k + 1) + ((k : ℝ) + 1) * y ^ k ≤ (y + 1) ^ (k + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : 0 ≤ y ^ k := pow_nonneg hy k
    have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
    have e1 : (y + 1) * (y ^ (k + 1) + ((k : ℝ) + 1) * y ^ k)
        = y ^ (k + 1 + 1) + (((k + 1 : ℕ) : ℝ) + 1) * y ^ (k + 1) + ((k : ℝ) + 1) * y ^ k := by
      push_cast; ring
    have e2 : (y + 1) * (y + 1) ^ (k + 1) = (y + 1) ^ (k + 1 + 1) := by ring
    have h2 : 0 ≤ ((k : ℝ) + 1) * y ^ k := mul_nonneg (by linarith) h1
    have h3 : (y + 1) * (y ^ (k + 1) + ((k : ℝ) + 1) * y ^ k) ≤ (y + 1) * (y + 1) ^ (k + 1) :=
      mul_le_mul_of_nonneg_left ih (by linarith)
    linarith

/-- `log y ≤ (2 / e) √y` for `y ≥ 0`. -/
theorem log_le_two_div_exp_mul_sqrt (y : ℝ) (hy : 0 < y) :
    Real.log y ≤ 2 / Real.exp 1 * Real.sqrt y := by
  have hs : 0 < Real.sqrt y := Real.sqrt_pos.mpr hy
  have he : 0 < Real.exp 1 := Real.exp_pos 1
  have h1 : Real.log (Real.sqrt y / Real.exp 1) ≤ Real.sqrt y / Real.exp 1 - 1 :=
    Real.log_le_sub_one_of_pos (div_pos hs he)
  rw [Real.log_div hs.ne' he.ne', Real.log_exp, Real.log_sqrt hy.le] at h1
  have h2 : 2 / Real.exp 1 * Real.sqrt y = 2 * (Real.sqrt y / Real.exp 1) := by ring
  rw [h2]
  linarith

/-- Corollary `GH:cor:powers` (i), from the gap bound of Carneiro, Milinovich and
Soundararajan. -/
theorem exists_prime_between_pow_of_gap
    (hgap : ∀ x : ℝ, 4 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x ≤ p ∧ (p : ℝ) ≤ x + 22 / 25 * Real.sqrt x * Real.log x)
    {m n : ℕ} (hm : 3 ≤ m) (hn : 1 ≤ n) :
    ∃ p : ℕ, p.Prime ∧ n ^ m < p ∧ p < (n + 1) ^ m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  have hk : 2 ≤ k := by omega
  rcases Nat.lt_or_ge n 2 with h | h
  · have hn1 : n = 1 := by omega
    subst hn1
    have h8 : (2 : ℕ) ^ 3 ≤ 2 ^ (k + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    refine ⟨2, Nat.prime_two, by simp, ?_⟩
    norm_num at h8 ⊢
    linarith
  · have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast h
    have hn0 : (0 : ℝ) < n := by linarith
    have hx4 : (4 : ℝ) ≤ (n : ℝ) ^ (k + 1) := by
      have h1 : (2 : ℝ) ^ 3 ≤ (2 : ℝ) ^ (k + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      have h2 : (2 : ℝ) ^ (k + 1) ≤ (n : ℝ) ^ (k + 1) := by gcongr
      norm_num at h1
      linarith
    obtain ⟨p, hp, hxp, hpx⟩ := hgap _ hx4
    refine ⟨p, hp, ?_, ?_⟩
    · have hle : n ^ (k + 1) ≤ p := by exact_mod_cast hxp
      rcases hle.lt_or_eq with hlt | heq
      · exact hlt
      · exfalso
        have hdvd : n ∣ p := heq ▸ dvd_pow_self n (by omega)
        rcases hp.eq_one_or_self_of_dvd n hdvd with h1 | h1
        · omega
        · have hsq : n ^ 2 ≤ n ^ (k + 1) := Nat.pow_le_pow_right (by omega) (by omega)
          have hlt2 : n < n ^ 2 := by nlinarith
          linarith
    · -- the gap is shorter than `(n + 1) ^ (k + 1) - n ^ (k + 1)`
      set x : ℝ := (n : ℝ) ^ (k + 1) with hx
      have hx0 : 0 ≤ x := by positivity
      have hlogx : Real.log x = ((k : ℝ) + 1) * Real.log n := by
        rw [hx, Real.log_pow]; push_cast; ring
      have hlogn : Real.log n ≤ 2 / Real.exp 1 * Real.sqrt n :=
        log_le_two_div_exp_mul_sqrt n hn0
      have hsq : Real.sqrt x * Real.sqrt n ≤ (n : ℝ) ^ k := by
        rw [← Real.sqrt_mul hx0]
        have hpow : x * n ≤ ((n : ℝ) ^ k) ^ 2 := by
          have h1 : x * n = (n : ℝ) ^ (k + 2) := by rw [hx]; ring
          have h2 : ((n : ℝ) ^ k) ^ 2 = (n : ℝ) ^ (2 * k) := by ring
          rw [h1, h2]
          exact pow_le_pow_right₀ (by linarith) (by omega)
        calc Real.sqrt (x * n) ≤ Real.sqrt (((n : ℝ) ^ k) ^ 2) := Real.sqrt_le_sqrt hpow
          _ = (n : ℝ) ^ k := Real.sqrt_sq (by positivity)
      have he : (2.7 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have he0 : 0 < Real.exp 1 := Real.exp_pos 1
      have hsx : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
      have hnk : 0 < (n : ℝ) ^ k := by positivity
      have hk1 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
      -- `(22/25) √x log x ≤ (44/(25 e)) (k+1) n^k < (k+1) n^k`
      have hA : 22 / 25 * Real.sqrt x * Real.log x
          ≤ 44 / 25 / Real.exp 1 * (((k : ℝ) + 1) * (n : ℝ) ^ k) := by
        rw [hlogx]
        have h1 : Real.sqrt x * Real.log n ≤ Real.sqrt x * (2 / Real.exp 1 * Real.sqrt n) :=
          mul_le_mul_of_nonneg_left hlogn hsx
        have h2 : Real.sqrt x * (2 / Real.exp 1 * Real.sqrt n)
            = 2 / Real.exp 1 * (Real.sqrt x * Real.sqrt n) := by ring
        have h3 : 2 / Real.exp 1 * (Real.sqrt x * Real.sqrt n) ≤ 2 / Real.exp 1 * (n : ℝ) ^ k :=
          mul_le_mul_of_nonneg_left hsq (by positivity)
        have h4 : 22 / 25 * Real.sqrt x * (((k : ℝ) + 1) * Real.log n)
            = 22 / 25 * ((k : ℝ) + 1) * (Real.sqrt x * Real.log n) := by ring
        have h5 : 44 / 25 / Real.exp 1 * (((k : ℝ) + 1) * (n : ℝ) ^ k)
            = 22 / 25 * ((k : ℝ) + 1) * (2 / Real.exp 1 * (n : ℝ) ^ k) := by ring
        rw [h4, h5]
        exact mul_le_mul_of_nonneg_left (h1.trans (h2 ▸ h3)) (by positivity)
      have hB : 44 / 25 / Real.exp 1 * (((k : ℝ) + 1) * (n : ℝ) ^ k)
          < ((k : ℝ) + 1) * (n : ℝ) ^ k := by
        have hc : 44 / 25 / Real.exp 1 < 1 := by
          rw [div_lt_one he0]; linarith
        have hpos : 0 < ((k : ℝ) + 1) * (n : ℝ) ^ k := mul_pos hk1 hnk
        nlinarith
      have hC := pow_add_succ_mul_le (n : ℝ) hn0.le k
      have hreal : (p : ℝ) < ((n : ℝ) + 1) ^ (k + 1) := by linarith
      exact_mod_cast hreal

end ReadableRH
