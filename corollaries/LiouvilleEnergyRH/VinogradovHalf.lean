import LiouvilleEnergyRH.Hypothesis
import Vinogradov.CharacterSums

/-!
# Vinogradov's character sum conjecture in the full range `θ > 1/2`

Under Hypothesis H no `L(s, χ)` vanishes in `re s > 1/2`. The bounds
`Vinogradov.CharSum.norm_bound` and `Vinogradov.CharSum.charSum_bound` hold to the right of any
zero-free half-plane `re s > a + 2e` with `1/2 ≤ a`; here they are applied with `a = 1/2`. This
gives

* `lindelof_half`: `‖L(s, χ)‖ + ‖L(s, χ)⁻¹‖ ≤ C (q (3 + |t|))^w` for `re s ≥ 1/2 + w`;
* `character_sum_bound_half`: `‖∑_{n ≤ x} χ(n)‖ ≤ C q^w x^{1/2 + w}`;
* `vinogradov_character_sum`: for `θ > 1/2` and `η > 0`, `‖∑_{n ≤ x} χ(n)‖ ≤ C x^θ` for
  every `x ≥ q^η`, which is Vinogradov's character sum conjecture.

Each takes Hypothesis H as an explicit hypothesis.
-/

namespace LiouvilleEnergyRH

open Complex Vinogradov

/-- **Lindelöf bound to the right of `1/2`** under Hypothesis H: for every `w > 0` there is `C`
with `‖L(s, χ)‖ + ‖L(s, χ)⁻¹‖ ≤ C (q (3 + |t|))^w` for every nonprincipal `χ` modulo `q` and
every `s` with `re s ≥ 1/2 + w`, `t = im s`. -/
theorem lindelof_half (h : HypothesisH) {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ s : ℂ, 1 / 2 + w ≤ s.re →
        ‖DirichletCharacter.LFunction χ s‖ + ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤
          C * ((q : ℝ) * (3 + |s.im|)) ^ w := by
  set e := min (w / 8) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he8 : 8 * e ≤ w := by have := min_le_left (w / 8) (1 / 2000); linarith
  obtain ⟨D, hD, hDb⟩ := CharSum.norm_bound he he' (show 0 < w / 2 by linarith)
  set B := Real.exp EulerLog.eulerLogBound with hB
  have hB0 : 0 < B := Real.exp_pos _
  refine ⟨D * 2 ^ w + 2 * B, by positivity, ?_⟩
  intro q _ χ hχ s hs
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  set Y := (q : ℝ) * (3 + |s.im|) with hY
  have hY1 : 1 ≤ Y := by nlinarith [abs_nonneg s.im]
  have hYw : 1 ≤ Y ^ w := Real.one_le_rpow hY1 hw.le
  have hs_eq : (s.re : ℂ) + (s.im : ℂ) * I = s := Complex.re_add_im s
  by_cases h2 : s.re ≤ 2
  · have hb := hDb q χ hχ (1 / 2) le_rfl (by norm_num)
      (fun z hz => h q χ z (by linarith) (Or.inl hχ)) s.re s.im (by linarith) h2
    rw [hs_eq] at hb
    have hle : 2 * (q : ℝ) * (3 + |s.im|) ^ 2 ≤ (2 * Y) ^ 2 := by
      rw [hY]; nlinarith [abs_nonneg s.im]
    have hpow : (2 * (q : ℝ) * (3 + |s.im|) ^ 2) ^ (w / 2) ≤ 2 ^ w * Y ^ w := by
      calc (2 * (q : ℝ) * (3 + |s.im|) ^ 2) ^ (w / 2) ≤ ((2 * Y) ^ 2) ^ (w / 2) :=
            Real.rpow_le_rpow (by positivity) hle (by linarith)
        _ = (2 * Y) ^ w := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
            congr 1
            push_cast
            ring
        _ = 2 ^ w * Y ^ w := Real.mul_rpow (by norm_num) (by positivity)
    calc _ ≤ D * (2 * (q : ℝ) * (3 + |s.im|) ^ 2) ^ (w / 2) := hb
      _ ≤ D * (2 ^ w * Y ^ w) := by gcongr
      _ ≤ (D * 2 ^ w + 2 * B) * Y ^ w := by
          nlinarith [Real.rpow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) w]
  · replace h2 := not_le.mp h2
    have hE := EulerLog.eulerLog_norm_le χ (s := s) (by linarith)
    have hexp := EulerLog.exp_eulerLog χ (s := s) (by linarith)
    set E := EulerLog.eulerLog χ s
    have h1 : ‖DirichletCharacter.LFunction χ s‖ ≤ B := by
      rw [← hexp, Complex.norm_exp]
      exact Real.exp_le_exp.mpr ((Complex.re_le_norm E).trans hE)
    have h2' : ‖(DirichletCharacter.LFunction χ s)⁻¹‖ ≤ B := by
      rw [← hexp, ← Complex.exp_neg, Complex.norm_exp, Complex.neg_re]
      refine Real.exp_le_exp.mpr ?_
      have := Complex.abs_re_le_norm E
      linarith [neg_le_abs E.re]
    have hD2 : 0 ≤ D * 2 ^ w := by positivity
    nlinarith

/-- **Character sums to the right of `1/2`** under Hypothesis H:
`‖∑_{1 ≤ n ≤ x} χ(n)‖ ≤ C q^w x^{1/2 + w}` for every nonprincipal `χ` modulo `q` and `x ≥ 1`. -/
theorem character_sum_bound_half (h : HypothesisH) {w : ℝ} (hw : 0 < w) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * (q : ℝ) ^ w * x ^ (1 / 2 + w) := by
  set d := min w 1 with hd_def
  have hd : 0 < d := lt_min hw one_pos
  have hdw : d ≤ w := min_le_left _ _
  have hd1 : d ≤ 1 := min_le_right _ _
  set e := min (d / 16) (1 / 2000) with he_def
  have he : 0 < e := lt_min (by linarith) (by norm_num)
  have he' : e < 1 / 1000 := (min_le_right _ _).trans_lt (by norm_num)
  have he16 : 16 * e ≤ d := by have := min_le_left (d / 16) (1 / 2000); linarith
  obtain ⟨K, hK, hKb⟩ := CharSum.charSum_bound he he' (show 0 < d / 8 by linarith)
    (show d / 8 ≤ 1 / 8 by linarith)
  refine ⟨K, hK, ?_⟩
  intro q _ χ hχ x hx
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hI : Finset.Icc 1 ⌊x⌋₊ = Finset.Ioc 0 ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [hI]
  have hb := hKb q χ hχ (1 / 2) le_rfl (by linarith)
    (fun z hz => h q χ z (by linarith) (Or.inl hχ)) x hx
  have hqp : (q : ℝ) ^ (d / 8) ≤ (q : ℝ) ^ w :=
    Real.rpow_le_rpow_of_exponent_le hq (by linarith)
  have hxp : x ^ (1 / 2 + 8 * e + 4 * (d / 8)) ≤ x ^ (1 / 2 + w) :=
    Real.rpow_le_rpow_of_exponent_le hx (by linarith)
  calc _ ≤ K * (q : ℝ) ^ (d / 8) * x ^ (1 / 2 + 8 * e + 4 * (d / 8)) := hb
    _ ≤ K * (q : ℝ) ^ w * x ^ (1 / 2 + w) := by gcongr

/-- **Vinogradov's character sum conjecture** under Hypothesis H, in the full range: for every
`η > 0` and `θ > 1/2` there is `C` such that `‖∑_{1 ≤ n ≤ x} χ(n)‖ ≤ C x^θ` for every
nonprincipal `χ` modulo `q` and every `x ≥ q^η`. -/
theorem vinogradov_character_sum (h : HypothesisH) {η θ : ℝ} (hη : 0 < η) (hθ : 1 / 2 < θ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), χ ≠ 1 →
      ∀ x : ℝ, 1 ≤ x → (q : ℝ) ^ η ≤ x →
        ‖∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n‖ ≤ C * x ^ θ := by
  set w := (θ - 1 / 2) * η / (1 + η) with hw_def
  have hw : 0 < w := by
    have : 0 < θ - 1 / 2 := by linarith
    positivity
  obtain ⟨C, hC, hCb⟩ := character_sum_bound_half h hw
  refine ⟨C, hC, ?_⟩
  intro q _ χ hχ x hx hqx
  have hx0 : 0 < x := by linarith
  have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  have hqd : (q : ℝ) ^ w ≤ x ^ (w / η) := by
    calc (q : ℝ) ^ w = ((q : ℝ) ^ η) ^ (w / η) := by
          rw [← Real.rpow_mul hq0]; congr 1; field_simp
      _ ≤ x ^ (w / η) := Real.rpow_le_rpow (by positivity) hqx (by positivity)
  have hexp : w / η + (1 / 2 + w) = θ := by
    rw [hw_def]; field_simp; ring
  calc _ ≤ C * (q : ℝ) ^ w * x ^ (1 / 2 + w) := hCb q χ hχ x hx
    _ ≤ C * x ^ (w / η) * x ^ (1 / 2 + w) := by gcongr
    _ = C * x ^ θ := by rw [mul_assoc, ← Real.rpow_add hx0, hexp]

end LiouvilleEnergyRH
