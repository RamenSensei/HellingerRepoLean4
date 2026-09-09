import Hellinger.BentFourGraphs
import Hellinger.BentFourStructure

/-! Complete four-dimensional bent Hellinger theorem for the actual cube BSC. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.BentFourFinal
open Fourier BentFour BentFourStructure

/-- The actual posterior fourth moment, expressed through the dual quadratic phase. -/
theorem bent_fourth_moment_identity (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC 4 ρ hρ).apply f x) ^ 4) =
      (∑ s : Cube 4, noiseDerivativeSum (mixedTerms (dual f)) ρ s ^ 2) / 256 := by
  have hg := dual_boolean f hb
  have hgb := dual_bent f hf
  have hrep := bent_quadratic_representation (dual f) hg hgb
  obtain ⟨hc, hl, he⟩ := coefficient_squares (dual f) hg
  rw [FourierProducts.noise_fourth_moment]
  have hterm (s a : Cube 4) :
      (ρ ^ degree a * walsh f a) * (ρ ^ degree (translate s a) * walsh f (translate s a)) =
        (1 / 16 : ℝ) * (ρ ^ (degree a + degree (translate s a)) *
          (dual f a * dual f (translate s a))) := by
    simp only [dual, pow_add]
    ring
  simp_rw [hterm, ← Finset.mul_sum, mul_pow]
  have hsum : (∑ s : Cube 4, (1 / 16 : ℝ) ^ 2 *
      (∑ a, ρ ^ (degree a + degree (translate s a)) * (dual f a * dual f (translate s a))) ^ 2) =
      (1 / 256 : ℝ) * ∑ s : Cube 4,
        (∑ a, ρ ^ (degree a + degree (translate s a)) * (dual f a * dual f (translate s a))) ^ 2 := by
    rw [← Finset.mul_sum]
    norm_num
  rw [hsum]
  conv_lhs => rw [hrep]
  simp_rw [quadratic_weighted_derivative _ _ _ hc hl he]
  ring

/-- The fourth-moment bound is now derived from Boolean flatness, rather than assumed. -/
theorem bent_fourth_moment_upper (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC 4 ρ hρ).apply f x) ^ 4) ≤
      BentEstimates.bentH (ρ ^ 2) ^ 2 / 256 := by
  rw [bent_fourth_moment_identity f hf hb]
  have hg := dual_boolean f hb
  have hgb := dual_bent f hf
  have hrep := bent_quadratic_representation (dual f) hg hgb
  obtain ⟨hc, hl, he⟩ := coefficient_squares (dual f) hg
  have hnd := quadratic_bent_nondegenerate (constantTerm (dual f))
    (linearTerms (dual f)) (mixedTerms (dual f)) hc hl he (by rw [← hrep]; exact hgb)
  exact BentFourGraphs.derivative_moment_upper _ he hnd ρ

/-- The complete continuous middle interval with genuine posterior moments and mean. -/
theorem bent_four_middle_strict (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (ht₀ : 1 / 16 ≤ ρ ^ 2) (ht₁ : ρ ^ 2 ≤ 7 / 10) :
    objective ((cubeBSC 4 ρ hρ).apply f) < 1 - root ρ := by
  let u := (cubeBSC 4 ρ hρ).apply f
  have hu (x : Cube 4) : u x ^ 2 ≤ 1 := by
    have h := UniformChannel.apply_mem_Icc (cubeBSC 4 ρ hρ) f
      (fun y => by rcases hf y with h | h <;> rw [h] <;> constructor <;> norm_num) x
    change u x ∈ Set.Icc (-1 : ℝ) 1 at h
    nlinarith [h.1, h.2]
  have hmean : (∑ x : Cube 4, (1 / 16 : ℝ) * u x) ^ 2 = 1 / 16 := by
    have h := Flatness.noisy_mean_sq hb ρ hρ
    norm_num at h
    simpa [mean, cube_card, Finset.mul_sum] using h
  have hQ₂ : (∑ x : Cube 4, (1 / 16 : ℝ) * u x ^ 2) = (1 + ρ ^ 2) ^ 4 / 16 := by
    have h := Flatness.noise_second_moment hb ρ hρ
    norm_num at h
    simpa [mean, cube_card, Finset.mul_sum, div_eq_mul_inv, mul_comm] using h
  have hQ₄ : (∑ x : Cube 4, (1 / 16 : ℝ) * u x ^ 4) ≤ BentEstimates.bentH (ρ ^ 2) ^ 2 / 256 := by
    have h := bent_fourth_moment_upper f hf hb ρ hρ
    simpa [mean, cube_card, Finset.mul_sum] using h
  have h := BentEstimates.four_dimensional_weighted_hellinger_gap
    (fun _ : Cube 4 => (1 / 16 : ℝ)) u (by intro; norm_num)
    (by simp) hu (ρ ^ 2) ht₀ ht₁ hmean hQ₂ hQ₄
  change root (mean u) - mean (fun x => root (u x)) < 1 - root ρ
  simp only [root, mean, cube_card, Nat.cast_pow, Nat.cast_ofNat] at *
  norm_num only [one_div, inv_pow] at *
  simp only [← Finset.mul_sum] at h
  nlinarith only [h]

/-- The no-flip/single-flip estimate and exact sensitivity distribution cover low noise. -/
theorem bent_four_low_strict (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hlo : 5 / 6 ≤ ρ) :
    objective ((cubeBSC 4 ρ hρ).apply f) < 1 - root ρ := by
  let S := mean (fun x => Real.sqrt (Flatness.sensitivity f x))
  have hs : (3 + 3 * Real.sqrt 2 + 2 * Real.sqrt 3) / 8 ≤ S := by
    exact le_of_eq (bent_four_sensitivity_mean f hf hb).symm
  have hfac := BentEstimates.four_low_noise_ratio_gt_one ((1 - ρ) / 2) S
    (((1 + ρ) / 2) ^ 3 * S) (by linarith only [hlo]) hs (by ring_nf; rfl)
  have hprod := mul_le_mul_of_nonneg_left (le_of_lt hfac) (Real.sqrt_nonneg (1 - ρ ^ 2))
  have hevent := BentLow.posterior_root_mean_lower (show 1 ≤ 4 by omega) hf ρ hρ
  have hR : root ρ ≤ mean (fun x => root ((cubeBSC 4 ρ hρ).apply f x)) := by
    change root ρ * 1 ≤ root ρ * (((1 + ρ) / 2) ^ 3 * S) at hprod
    change root ρ * ((1 + ρ) / 2) ^ 3 * S ≤ _ at hevent
    nlinarith only [hprod, hevent]
  have hroot : root (mean ((cubeBSC 4 ρ hρ).apply f)) < 1 := by
    apply (Real.sqrt_lt' (by norm_num : (0 : ℝ) < 1)).mpr
    have h := Flatness.noisy_mean_sq hb ρ hρ
    norm_num at h
    linarith only [h]
  unfold objective
  linarith only [hR, hroot]

/-- Complete all-noise result for every four-dimensional bent Boolean function. -/
theorem bent_four_hellinger (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 4 ρ hρ).apply f) ≤ 1 - root ρ ∧
      (0 < ρ → objective ((cubeBSC 4 ρ hρ).apply f) < 1 - root ρ) := by
  by_cases hhi : ρ ≤ 3 / 10
  · exact ⟨BentLarge.bent_high_noise_hellinger (by omega) f hb ρ hρ hhi,
      fun hp => BentLarge.bent_high_noise_hellinger_strict (by omega) f hb ρ hρ hhi hp⟩
  · have hm : objective ((cubeBSC 4 ρ hρ).apply f) < 1 - root ρ := by
      by_cases hlo : 5 / 6 ≤ ρ
      · exact bent_four_low_strict f hf hb ρ hρ hlo
      · apply bent_four_middle_strict f hf hb ρ hρ
        · nlinarith [hρ.1]
        · nlinarith [hρ.1]
    exact ⟨le_of_lt hm, fun _ => hm⟩

#print axioms bent_fourth_moment_upper
#print axioms bent_four_hellinger
end Hellinger.BentFourFinal
