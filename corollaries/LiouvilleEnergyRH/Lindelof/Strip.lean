import LiouvilleEnergyRH.Mertens.Main

/-!
# Bounds for `ζ` on vertical strips

* `zeta_strip_bound`: under the zero-free half-plane `re s > σa`, `1/2 ≤ σa ≤ 1`, for
  `e, ε > 0` and `b < 1`, `‖ζ(σ + it)‖ ≤ D (2 (3 + |t|)^2)^ε` on `σa + 8e ≤ σ ≤ b`
  (logarithmic control for `|t| > 2`, compactness for `|t| ≤ 2`);
* `norm_riemannZeta_le_quarter`: unconditionally, `‖ζ(s)‖ ≤ 1/‖s - 1‖ + 1 + 4‖s‖` on
  `re s ≥ 1/4`.

From `LiouvilleEnergyRH/Lindelof/Strip.lean` of anaxia-research/lindelof-rh, which treats
`σa = 1/2`, `b = 3/4`. Changed here: the zero-free half-plane is `re s > σa` and the strip is
`σa + 8e ≤ σ ≤ b` for parameters `σa` and `b < 1`.
-/

namespace LiouvilleEnergyRH.Lindelof

open Complex Set Metric Filter Vinogradov

theorem norm_riemannZeta_le_quarter {s : ℂ} (hs : 1 / 4 ≤ s.re) (hs1 : s ≠ 1) :
    ‖riemannZeta s‖ ≤ 1 / ‖s - 1‖ + 1 + 4 * ‖s‖ := by
  have hs0 : 0 < s.re := by linarith
  have hz : riemannZeta s = (s - 1)⁻¹ + 1 + ZetaBound.abel s := by
    rw [ZetaBound.abel_eq hs0, riemannZeta_eq_inv_sub_add hs1]; ring
  have hA : ‖ZetaBound.abel s‖ ≤ 4 * ‖s‖ := by
    calc ‖ZetaBound.abel s‖ ≤ ‖s‖ / s.re := ZetaBound.abel_norm hs0
      _ ≤ ‖s‖ / (1 / 4) := div_le_div_of_nonneg_left (norm_nonneg s) (by norm_num) hs
      _ = 4 * ‖s‖ := by ring
  rw [hz]
  calc ‖(s - 1)⁻¹ + 1 + ZetaBound.abel s‖
      ≤ ‖(s - 1)⁻¹‖ + ‖(1 : ℂ)‖ + ‖ZetaBound.abel s‖ := norm_add₃_le
    _ ≤ 1 / ‖s - 1‖ + 1 + 4 * ‖s‖ := by
        rw [norm_inv, norm_one, one_div]; linarith

/-- **`ζ` on vertical strips** under the zero-free half-plane. -/
theorem zeta_strip_bound {σa b : ℝ} (ha : 1 / 2 ≤ σa) (ha1 : σa ≤ 1) (hb : b < 1)
    (hz : ∀ s : ℂ, σa < s.re → s ≠ 1 → riemannZeta s ≠ 0)
    {e ε : ℝ} (he : 0 < e) (he' : e < 1 / 1000) (hε : 0 < ε) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ σ t : ℝ, σa + 8 * e ≤ σ → σ ≤ b →
      ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D * (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) ^ ε := by
  obtain ⟨D₁, hD₁, hctrl⟩ := OAI.SevenEighths.LogarithmicControl.logarithmic_control
    (e := e) (A := EulerLog.eulerLogBound) (M := 1) (ε := ε) he he'
    EulerLog.eulerLogBound_ge_one le_rfl hε
  set K : Set ℂ := Icc (σa + 8 * e) b ×ℂ Icc (-2) 2 with hK
  have hKc : IsCompact K := isCompact_Icc.reProdIm isCompact_Icc
  have hcont : ContinuousOn riemannZeta K := by
    intro z hzK
    have hre : z.re ≤ b := (Complex.mem_reProdIm.mp hzK).1.2
    have hz1 : z ≠ 1 := by intro h; rw [h] at hre; simp at hre; linarith
    exact (differentiableAt_riemannZeta hz1).continuousAt.continuousWithinAt
  obtain ⟨B, hB⟩ := hKc.exists_bound_of_continuousOn hcont
  refine ⟨D₁ + |B|, by positivity, ?_⟩
  intro σ t hσ hσ'
  set C : ℝ := 2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2 with hCdef
  have hbase : 1 ≤ C := by
    rw [hCdef]; push_cast; nlinarith [abs_nonneg t]
  have hpow : 1 ≤ C ^ ε := Real.one_le_rpow hbase hε.le
  by_cases ht : |t| ≤ 2
  · have hmem : ((σ : ℂ) + (t : ℂ) * I) ∈ K := by
      rw [hK, Complex.mem_reProdIm]
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero, add_im, mul_im, zero_add]
      exact ⟨⟨hσ, hσ'⟩, abs_le.mp ht⟩
    have h1 := hB _ hmem
    have h2 : B ≤ |B| := le_abs_self B
    have h3 : 0 ≤ D₁ * C ^ ε := by positivity
    nlinarith [abs_nonneg B]
  · push Not at ht
    have hC := OAI.SevenEighths.LogarithmicControl.conductor_height_scale_ge_exp
      ((1 : ℕ) : ℝ) t (by simp)
    obtain ⟨hEd, hEe, hEb⟩ := EulerLog.eulerLog_inner_disk (1 : DirichletCharacter ℂ 1) t
    have hLz : DirichletCharacter.LFunction (1 : DirichletCharacter ℂ 1) = riemannZeta :=
      DirichletCharacter.LFunction_modOne_eq
    rw [hLz] at hEe
    have hres := hctrl σa (2 * ((1 : ℕ) : ℝ) * (3 + |t|) ^ 2) riemannZeta
      (EulerLog.eulerLog (1 : DirichletCharacter ℂ 1)) (2 + (t : ℂ) * I) ha ha1 hC
      (fun z hzb => by
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hzb
        have h := Mertens.zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        exact (differentiableAt_riemannZeta h.1).differentiableWithinAt)
      (fun z hzb => by
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hzb
        have h := Mertens.zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        exact hz z (by linarith) h.1)
      (fun z hzb => by
        have hz2 : z ∈ ball (2 + (t : ℂ) * I) (2 - σa - 2 * e) :=
          ball_subset_ball (by linarith) hzb
        have hre := OAI.SevenEighths.LogarithmicControl.disk_re_gt hz2
        have h := Mertens.zeta_norm_on_disk ht (by linarith) hzb (by linarith)
        rw [Real.rpow_one]
        exact_mod_cast h.2)
      hEd hEe hEb
    have hmem := OAI.SevenEighths.LogarithmicControl.same_height_mem_disk (a := σa) (e := e)
      (t := t) (v := 8 * e) le_rfl hσ (by linarith)
    have hb1 := hres.1 _ (closedBall_subset_closedBall (by linarith) hmem)
    have hz1 : ‖riemannZeta ((σ : ℂ) + (t : ℂ) * I)‖ ≤ D₁ * C ^ ε :=
      le_trans (le_add_of_nonneg_right (norm_nonneg _)) hb1
    have hBC : 0 ≤ |B| * C ^ ε := by positivity
    nlinarith

end LiouvilleEnergyRH.Lindelof
