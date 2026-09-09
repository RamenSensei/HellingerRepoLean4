import Hellinger.BentFourFinal
import Hellinger.BentLowExact

/-! The additional explicit lower constants and strict posterior-root bounds
stated within the manuscript proofs, with their actual BSC quantities. -/
set_option autoImplicit false
noncomputable section
namespace Hellinger.PaperQuantitativeBounds
open Fourier

theorem dimension_constant_chain (n : ℕ) (hn : 6 ≤ n) :
    1 < (4 : ℝ) / Real.sqrt 14 ∧
    (4 : ℝ) / Real.sqrt 14 ≤ 2 * n / (3 * Real.sqrt (2 * ((n : ℝ) + 1))) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have h14 : 0 < Real.sqrt (14 : ℝ) := by positivity
  have hd : 0 < Real.sqrt (2 * ((n : ℝ) + 1)) := by positivity
  have hs14 := Real.sq_sqrt (show (0 : ℝ) ≤ 14 by norm_num)
  have hsd := Real.sq_sqrt (show 0 ≤ 2 * ((n : ℝ) + 1) by positivity)
  constructor
  · apply (lt_div_iff₀ h14).mpr
    nlinarith only [hs14, h14]
  · apply (div_le_div_iff₀ h14 (show 0 < 3 * Real.sqrt (2 * ((n : ℝ) + 1)) by positivity)).mpr
    have hprod := mul_nonneg (show 0 ≤ (n : ℝ) - 6 by linarith)
      (show 0 ≤ 7 * (n : ℝ) + 6 by positivity)
    have hsL : (4 * (3 * Real.sqrt (2 * ((n : ℝ) + 1)))) ^ 2 = 288 * ((n : ℝ) + 1) := by
      nlinarith only [hsd]
    have hsR : (2 * (n : ℝ) * Real.sqrt 14) ^ 2 = 56 * (n : ℝ) ^ 2 := by
      rw [mul_pow, hs14]
      ring
    have hs : (4 * (3 * Real.sqrt (2 * ((n : ℝ) + 1)))) ^ 2 ≤
        (2 * (n : ℝ) * Real.sqrt 14) ^ 2 := by
      rw [hsL, hsR]
      nlinarith only [hprod]
    have hr : 0 ≤ 2 * (n : ℝ) * Real.sqrt 14 := by positivity
    nlinarith only [hs, hr]

theorem bent_low_noise_ratio (n : ℕ) (hn : 6 ≤ n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (hlo : 1 - 2 / (3 * (n : ℝ)) ≤ ρ) :
    2 * n / (3 * Real.sqrt (2 * ((n : ℝ) + 1))) ≤
      mean (fun x => root ((cubeBSC n ρ hρ).apply f x)) / root ρ := by
  have hc : 0 < root ρ := Real.sqrt_pos.mpr (by nlinarith [hρ.1])
  have hp := BentLow.low_noise_power_lower n (by omega) ρ hρ hlo
  have hs := Flatness.sensitivity_sqrt_mean_lower hf hb
  have hfac := mul_le_mul hp hs
    (show 0 ≤ (n : ℝ) / Real.sqrt (2 * ((n : ℝ) + 1)) by positivity)
    (show 0 ≤ ((1 + ρ) / 2) ^ (n - 1) by positivity)
  have he := BentLow.posterior_root_mean_lower (show 1 ≤ n by omega) hf ρ hρ
  have hmul := mul_le_mul_of_nonneg_left hfac hc.le
  apply (le_div_iff₀ hc).mpr
  have heq : 2 * (n : ℝ) / (3 * Real.sqrt (2 * ((n : ℝ) + 1))) =
      (2 / 3 : ℝ) * ((n : ℝ) / Real.sqrt (2 * ((n : ℝ) + 1))) := by ring
  rw [heq]
  nlinarith only [hmul, he]

theorem bent_low_noise_full_constant_chain (n : ℕ) (hn : 6 ≤ n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (hlo : 1 - 2 / (3 * (n : ℝ)) ≤ ρ) :
    1 < (4 : ℝ) / Real.sqrt 14 ∧
    (4 : ℝ) / Real.sqrt 14 ≤ 2 * n / (3 * Real.sqrt (2 * ((n : ℝ) + 1))) ∧
    2 * n / (3 * Real.sqrt (2 * ((n : ℝ) + 1))) ≤
      mean (fun x => root ((cubeBSC n ρ hρ).apply f x)) / root ρ :=
  ⟨(dimension_constant_chain n hn).1, (dimension_constant_chain n hn).2,
    bent_low_noise_ratio n hn f hf hb ρ hρ hρlt hlo⟩

theorem four_low_noise_explicit_ratio (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1) (hlo : 5 / 6 ≤ ρ) :
    1 < (1331 : ℝ) / 1296 ∧
    (1331 : ℝ) / 1296 < mean (fun x => root ((cubeBSC 4 ρ hρ).apply f x)) / root ρ := by
  have hc : 0 < root ρ := Real.sqrt_pos.mpr (by nlinarith [hρ.1])
  have hs : (4 : ℝ) / 3 < mean (fun x => Real.sqrt (Flatness.sensitivity f x)) := by
    rw [BentFourStructure.bent_four_sensitivity_mean f hf hb]
    exact BentEstimates.four_sensitivity_constant
  have hp : ((11 : ℝ) / 12) ^ 3 ≤ ((1 + ρ) / 2) ^ 3 :=
    pow_le_pow_left₀ (by norm_num) (by linarith) 3
  have hmul := mul_le_mul_of_nonneg_right hp
    (show 0 ≤ mean (fun x => Real.sqrt (Flatness.sensitivity f x)) by linarith)
  norm_num at hmul
  have hfac : (1331 : ℝ) / 1296 < ((1 + ρ) / 2) ^ 3 *
      mean (fun x => Real.sqrt (Flatness.sensitivity f x)) := by linarith
  have he := BentLow.posterior_root_mean_lower (show 1 ≤ 4 by omega) hf ρ hρ
  have hstrict := mul_lt_mul_of_pos_left hfac hc
  refine ⟨by norm_num, (lt_div_iff₀ hc).mpr ?_⟩
  change root ρ * ((1 + ρ) / 2) ^ 3 * mean (fun x => Real.sqrt (Flatness.sensitivity f x)) ≤ _ at he
  nlinarith only [hstrict, he]

open BentLarge

/-- The scalar second-moment estimate throughout the full middle-noise range. -/
theorem middle_scalar_strict (n : ℕ) (hn : 6 ≤ n) (c : ℝ)
    (hc₀ : 0 ≤ c) (hc₁ : c ≤ 24 / 25)
    (hscale : 17 / 27 ≤ (n : ℝ) * c ^ 2 / 2) :
    (1 - c ^ 2 / 2) ^ n < 1 - c := by
  have hb₀ : 0 ≤ 1 - c ^ 2 / 2 := by nlinarith
  have hb₁ : 1 - c ^ 2 / 2 ≤ 1 := by nlinarith [sq_nonneg c]
  by_cases hc : c ≤ 23 / 50
  · have he : 1 - c ^ 2 / 2 ≤ Real.exp (-(c ^ 2 / 2)) := by
      simpa only [neg_add_rev, sub_eq_add_neg, add_comm] using
        Real.add_one_le_exp (-(c ^ 2 / 2))
    have hp := pow_le_pow_left₀ hb₀ he n
    rw [← Real.exp_nat_mul] at hp
    have hexp : Real.exp ((n : ℝ) * -(c ^ 2 / 2)) ≤ Real.exp (-(17 : ℝ) / 27) := by
      apply Real.exp_le_exp.mpr
      nlinarith only [hscale]
    linarith only [hp.trans hexp, exp_neg_seventeen_twentyseven_lt, hc]
  · have hp := pow_le_pow_of_le_one hb₀ hb₁ hn
    have hq := middle_six_polynomial c (le_of_not_ge hc) hc₁
    linarith only [hp, hq]

/-- Conversion of the original dimension-dependent interval to the scalar range. -/
theorem middle_noise_second_moment_strict (n : ℕ) (hn : 6 ≤ n) (ρ : ℝ)
    (hρ₀ : 3 / 10 ≤ ρ) (hρ₁ : ρ ≤ 1 - 2 / (3 * (n : ℝ))) :
    ((1 + ρ ^ 2) / 2) ^ n < 1 - Real.sqrt (1 - ρ ^ 2) := by
  have hnR : (6 : ℝ) ≤ n := by exact_mod_cast hn
  have hnpos : 0 < (n : ℝ) := by linarith
  have hdiv : 0 < 2 / (3 * (n : ℝ)) := by positivity
  have hρnonneg : 0 ≤ ρ := by linarith
  have hρle : ρ ≤ 1 := by linarith
  have hrad : 0 ≤ 1 - ρ ^ 2 := by nlinarith
  have hs := Real.sq_sqrt hrad
  have hs0 := Real.sqrt_nonneg (1 - ρ ^ 2)
  have hs1 : Real.sqrt (1 - ρ ^ 2) ≤ 24 / 25 := by nlinarith
  have hm : ρ * (3 * (n : ℝ)) ≤ 3 * (n : ℝ) - 2 := by
    have h := (le_div_iff₀ (show 0 < 3 * (n : ℝ) by positivity)).1
      (show ρ ≤ (3 * (n : ℝ) - 2) / (3 * (n : ℝ)) by
        convert hρ₁ using 1
        field_simp)
    exact h
  have hendpoint : (17 : ℝ) / 27 ≤ (n : ℝ) * (1 - ρ ^ 2) / 2 := by
    have hprod := mul_nonneg
      (show 0 ≤ 3 * (n : ℝ) - 2 - 3 * (n : ℝ) * ρ by nlinarith only [hm])
      (show 0 ≤ 3 * (n : ℝ) - 2 + 3 * (n : ℝ) * ρ by
        have hmul := mul_nonneg (le_of_lt hnpos) hρnonneg
        nlinarith only [hnR, hmul])
    have hN := mul_nonneg (show 0 ≤ (n : ℝ) - 6 by linarith) (show 0 ≤ (n : ℝ) by positivity)
    nlinarith only [hprod, hN, hnR]
  have h := middle_scalar_strict n hn (Real.sqrt (1 - ρ ^ 2)) hs0 hs1
    (by rw [hs]; exact hendpoint)
  convert h using 1
  rw [hs]
  ring


theorem bent_middle_root_strict (n : ℕ) (hn : 6 ≤ n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hlo : 3 / 10 ≤ ρ) (hhi : ρ ≤ 1 - 2 / (3 * (n : ℝ))) :
    root ρ < mean (fun x => root ((cubeBSC n ρ hρ).apply f x)) := by
  have hu : ∀ x, (cubeBSC n ρ hρ).apply f x ∈ Set.Icc (-1 : ℝ) 1 := by
    apply UniformChannel.apply_mem_Icc
    intro x
    rcases hf x with h | h <;> rw [h] <;> norm_num
  have hl := BentLarge.mean_root_lower ((cubeBSC n ρ hρ).apply f) hu
  have hQ : mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 2) =
      ((1 + ρ ^ 2) / 2) ^ n := by
    rw [Flatness.noise_second_moment hb ρ hρ, div_pow, div_eq_mul_inv]
    ring
  rw [hQ] at hl
  have hm := middle_noise_second_moment_strict n hn ρ hlo hhi
  change Real.sqrt (1 - ρ ^ 2) < _
  linarith only [hl, hm]

#print axioms bent_low_noise_full_constant_chain
#print axioms four_low_noise_explicit_ratio
#print axioms bent_middle_root_strict

theorem bent_high_noise_quadratic_strict {n : ℕ} (hn : 4 ≤ n)
    (f : Cube n → ℝ) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρ₁ : ρ ≤ 3 / 10) (hρpos : 0 < ρ) :
    objective ((cubeBSC n ρ hρ).apply f) < ρ ^ 2 / 2 := by
  let M : ℝ := (169 / 200) ^ 2
  let u := (cubeBSC n ρ hρ).apply f
  have hu : ∀ x, u x ∈ Set.Icc (-M) M := by
    intro x
    exact abs_le.mp (high_noise_posterior_bound hn hb ρ hρ hρ₁ x)
  have hc := mean_curvature_bound u M (by norm_num [M]) (by norm_num [M]) hu
  have hvar : mean (fun x => (u x) ^ 2) - (mean u) ^ 2 =
      ((2 : ℝ) ^ n)⁻¹ * ((1 + ρ ^ 2) ^ n - 1) := by
    rw [Flatness.noise_second_moment hb ρ hρ, Flatness.noisy_mean_sq hb ρ hρ]
    ring
  rw [hvar] at hc
  have hv := high_noise_variance n hn ρ hρ.1 hρ₁
  have hroot : 0 < root M := by unfold root M; apply Real.sqrt_pos.2; norm_num
  have hden : 0 < 2 * root M ^ 3 := by positivity
  have hcv := div_le_div_of_nonneg_right hv (le_of_lt hden)
  have hconst : (109 ^ 3 / 4000000 : ℝ) < root M ^ 3 := high_noise_constant_lt
  have hcoeff : (109 ^ 3 / 4000000 : ℝ) * ρ ^ 2 / (2 * root M ^ 3) < ρ ^ 2 / 2 := by
    apply (div_lt_iff₀ hden).2
    have hmul := mul_lt_mul_of_pos_right hconst (sq_pos_of_pos hρpos)
    nlinarith only [hmul]
  exact lt_of_le_of_lt (hc.trans hcv) hcoeff

#print axioms bent_high_noise_quadratic_strict

end Hellinger.PaperQuantitativeBounds
