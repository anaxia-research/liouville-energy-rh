import LiouvilleEnergyRH.Unconditional
import OAI.NumberTheory.TwoPointCorrelations.FinalMain

/-!
# Two-point sign patterns of the Liouville function

OpenAI's theorem `OAI.OrdinaryTwoPointCorrelations.liouville_log_saving` (the Lean library of
https://github.com/openai/math, Apache 2.0) bounds the Liouville correlation on any two
nonproportional affine forms by `O(X / (log X)^c)`. With `a₁ = a₂ = 1`, `b₁ = 0`, `b₂ = h` it
gives the two-point Chowla conjecture `∑_{n ≤ N} λ(n) λ(n + h) = o(N)` for every `h ≥ 1`
(`liouville_two_point`). Together with the one-point case `chowla_one`, which follows from the
zero-free half-plane `re s > 7/8`, the sign-pattern theorem `ChowlaRH.tendsto_pattern` gives
`#{n ≤ x : λ(n) = ε₁, λ(n + h) = ε₂} / x → 1/4` for all signs `ε₁, ε₂`
(`liouville_sign_pair`, `liouville_sign_pair_real`).
-/

namespace LiouvilleEnergyRH.Unconditional

open Filter Topology Finset ArithmeticFunction

/-- **OpenAI's two-point theorem.** There is `c > 0` such that for nonproportional affine forms
`a₁ n + b₁`, `a₂ n + b₂` (`a₁, a₂ > 0`, `a₁ b₂ ≠ a₂ b₁`),
`|∑_{n ≤ X} λ(a₁ n + b₁) λ(a₂ n + b₂)| ≤ C X / (log X)^c` for `X ≥ 3`. -/
theorem liouville_affine_correlation :
    ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
        |∑ n ∈ Icc 1 ⌊X⌋₊, (liouville (a₁ * n + b₁) : ℝ) * liouville (a₂ * n + b₂)| ≤
          C * X / Real.log X ^ c := by
  obtain ⟨c, hc, hL⟩ := OAI.OrdinaryTwoPointCorrelations.liouville_log_saving
  refine ⟨c, hc, fun a₁ a₂ b₁ b₂ ha₁ ha₂ hne => ?_⟩
  obtain ⟨C, hC, hb⟩ := hL a₁ a₂ b₁ b₂ ha₁ ha₂ hne
  refine ⟨C, hC, fun X hX => ?_⟩
  have h := hb X hX
  have hcast : OAI.TwoPointCorrelations.affineSum OAI.TwoPointCorrelations.liouville
      OAI.TwoPointCorrelations.liouville a₁ a₂ b₁ b₂ ⌊X⌋₊ =
      ((∑ n ∈ Icc 1 ⌊X⌋₊, (liouville (a₁ * n + b₁) : ℝ) * liouville (a₂ * n + b₂) : ℝ) : ℂ) := by
    simp only [OAI.TwoPointCorrelations.affineSum, OAI.TwoPointCorrelations.liouville]
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at h
  exact h

/-- **Two-point Chowla**: `(1/N) ∑_{n ≤ N} λ(n) λ(n + h) → 0` for every `h ≥ 1`. -/
theorem liouville_two_point (h : ℕ) (hh : 1 ≤ h) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc 1 N, (liouville n : ℝ) * liouville (n + h)) / N) atTop
      (𝓝 0) := by
  obtain ⟨c, hc, hL⟩ := liouville_affine_correlation
  obtain ⟨C, -, hb⟩ := hL 1 1 0 h one_pos one_pos (by omega)
  have hlim : Tendsto (fun N : ℕ => C * (Real.log N ^ c)⁻¹) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.log N ^ c) atTop atTop :=
      (tendsto_rpow_atTop hc).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
    have h2 := h1.inv_tendsto_atTop.const_mul C
    rw [mul_zero] at h2
    exact h2
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hb' := hb N hN3
  rw [Nat.floor_natCast] at hb'
  simp only [one_mul, add_zero] at hb'
  rw [Real.norm_eq_abs, abs_div, abs_of_pos hNpos, div_le_iff₀ hNpos]
  calc _ ≤ C * N / Real.log N ^ c := hb'
    _ = C * (Real.log N ^ c)⁻¹ * N := by ring

/-- Two-point Chowla in the notation of `ChowlaRH`. -/
theorem chowlaAt_pair (h : ℕ) (hh : 1 ≤ h) : ChowlaRH.ChowlaAt ChowlaRH.natW {0, h} := by
  unfold ChowlaRH.ChowlaAt
  refine (liouville_two_point h hh).congr' (Eventually.of_forall fun N => ?_)
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  have h0 : (0 : ℕ) ∉ ({h} : Finset ℕ) := by simp; omega
  simp only [ChowlaRH.wavg, ChowlaRH.natW, ChowlaRH.corr, prod_insert h0, prod_singleton,
    add_zero, one_mul, sum_const, Nat.card_Ioc, Nat.sub_zero, nsmul_eq_mul, mul_one, hI,
    ChowlaRH.lam]

/-- **Two-point sign patterns of `λ`**: for every `h ≥ 1` and signs `ε₁, ε₂ ∈ {1, -1}`,
`#{n ≤ N : λ(n) = ε₁, λ(n + h) = ε₂} / N → 1/4`. -/
theorem liouville_sign_pair (h : ℕ) (hh : 1 ≤ h) {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1)
    (h₂ : ε₂ = 1 ∨ ε₂ = -1) :
    Tendsto (fun N : ℕ =>
      (((Icc 1 N).filter (fun n => liouville n = ε₁ ∧ liouville (n + h) = ε₂)).card : ℝ) / N)
      atTop (𝓝 (1 / 4)) := by
  have hh0 : h ≠ 0 := by omega
  set ε : ℕ → ℝ := fun x => if x = 0 then (ε₁ : ℝ) else (ε₂ : ℝ) with hεdef
  have hH : ({0, h} : Finset ℕ).card = 2 := card_pair (Ne.symm hh0)
  have hsv : ChowlaRH.IsSignVec {0, h} ε := by
    intro x _
    simp only [hεdef]
    split_ifs
    · rcases h₁ with h₁ | h₁ <;> simp [h₁]
    · rcases h₂ with h₂ | h₂ <;> simp [h₂]
  have hC : ∀ S ⊆ ({0, h} : Finset ℕ), S.Nonempty → ChowlaRH.ChowlaAt ChowlaRH.natW S := by
    intro S hS hne
    rcases Nat.lt_or_ge S.card 2 with hlt | hge
    · exact chowla_one S (by have := hne.card_pos; omega)
    · have hSH : S = {0, h} := eq_of_subset_of_card_le hS (by rw [hH]; exact hge)
      rw [hSH]
      exact chowlaAt_pair h hh
  have hT := ChowlaRH.tendsto_pattern ChowlaRH.natW ChowlaRH.natW_pos {0, h} hsv hC
  rw [hH, show ((1 : ℝ) / 2) ^ 2 = 1 / 4 by norm_num] at hT
  refine hT.congr' (Eventually.of_forall fun N => ?_)
  have hI : Icc 1 N = Ioc 0 N := by ext n; simp only [mem_Icc, mem_Ioc]; omega
  have hpt : ∀ n, ChowlaRH.patternInd {0, h} ε n =
      if (liouville n = ε₁ ∧ liouville (n + h) = ε₂) then 1 else 0 := by
    intro n
    unfold ChowlaRH.patternInd
    have hiff : (∀ x ∈ ({0, h} : Finset ℕ), ChowlaRH.lam (n + x) = ε x) ↔
        (liouville n = ε₁ ∧ liouville (n + h) = ε₂) := by
      simp [hεdef, hh0, ChowlaRH.lam]
    simp only [hiff]
  simp only [ChowlaRH.wavg, ChowlaRH.natW, one_mul, sum_const, Nat.card_Ioc, Nat.sub_zero,
    nsmul_eq_mul, mul_one, hI, hpt, sum_boole]

/-- **Two-point sign patterns of `λ`**, real form:
`#{n ≤ x : λ(n) = ε₁, λ(n + h) = ε₂} / x → 1/4` as `x → ∞`. -/
theorem liouville_sign_pair_real (h : ℕ) (hh : 1 ≤ h) {ε₁ ε₂ : ℤ} (h₁ : ε₁ = 1 ∨ ε₁ = -1)
    (h₂ : ε₂ = 1 ∨ ε₂ = -1) :
    Tendsto (fun x : ℝ =>
      (((Icc 1 ⌊x⌋₊).filter (fun n => liouville n = ε₁ ∧ liouville (n + h) = ε₂)).card : ℝ) / x)
      atTop (𝓝 (1 / 4)) := by
  have h1 := (liouville_sign_pair h hh h₁ h₂).comp (tendsto_nat_floor_atTop (α := ℝ))
  have h2 := h1.mul (tendsto_nat_floor_div_atTop (R := ℝ))
  rw [mul_one] at h2
  refine h2.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with x hx
  have hfl : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast Nat.floor_pos.mpr hx
  have hx0 : (0 : ℝ) < x := by linarith
  simp only [Function.comp]
  field_simp

end LiouvilleEnergyRH.Unconditional
