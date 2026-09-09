import Hellinger.BentLow
import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! The exact low-noise lemma as stated in the manuscript, including its real exponent. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.BentLowExact
open Fourier

theorem alpha_bounds (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (hmax : α ≤ 1 / (n : ℝ)) : α ≤ 1 / 2 ∧ (n : ℝ) * α ≤ 1 := by
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast hn
  have hp : 0 < (n : ℝ) := by linarith
  have hm := (le_div_iff₀ hp).mp hmax
  have hs := mul_le_mul_of_nonneg_right hnR hα
  constructor <;> nlinarith

/-- The no-flip coefficient proved earlier dominates the precise coefficient
in the manuscript on its full stipulated interval. -/
theorem coefficient_le (n : ℕ) (hn : 2 ≤ n) (α : ℝ) (hα : 0 ≤ α)
    (hmax : α ≤ 1 / (n : ℝ)) :
    (1 - α) ^ (((n : ℝ) - 2) / 2) * Real.sqrt (1 - (n : ℝ) * α) ≤
      (1 - α) ^ (n - 1) := by
  obtain ⟨hhalf, hna⟩ := alpha_bounds n hn α hα hmax
  have hb : 0 ≤ 1 - α := by linarith
  have hq : 0 ≤ 1 - (n : ℝ) * α := by linarith
  have hpow : ((1 - α) ^ (((n : ℝ) - 2) / 2)) ^ 2 = (1 - α) ^ (n - 2) := by
    rw [← Real.rpow_natCast _ 2, ← Real.rpow_mul hb]
    have he : (((n : ℝ) - 2) / 2) * (2 : ℝ) = ((n - 2 : ℕ) : ℝ) := by
      rw [Nat.cast_sub hn]
      norm_num
    norm_num only [Nat.cast_ofNat]
    rw [he, Real.rpow_natCast]
  have hbern := one_add_mul_sub_le_pow (show (-1 : ℝ) ≤ 1 - α by linarith) n
  have hpowbound : 1 - (n : ℝ) * α ≤ (1 - α) ^ n := by nlinarith only [hbern]
  have hmul := mul_le_mul_of_nonneg_left hpowbound (pow_nonneg hb (n - 2))
  have hexp : n - 2 + n = (n - 1) * 2 := by omega
  rw [← pow_add, hexp, pow_mul] at hmul
  have hsq : ((1 - α) ^ (((n : ℝ) - 2) / 2) * Real.sqrt (1 - (n : ℝ) * α)) ^ 2 ≤
      ((1 - α) ^ (n - 1)) ^ 2 := by
    rw [mul_pow, hpow, Real.sq_sqrt hq]
    exact hmul
  have hright : 0 ≤ (1 - α) ^ (n - 1) := pow_nonneg hb _
  nlinarith only [hsq, hright]

/-- Full manuscript low-noise statement: every Boolean function, every `n ≥ 2`,
every `0 < α ≤ 1/n`, and the actual real exponent `(n−2)/2`. -/
theorem manuscript_low_noise {n : ℕ} (hn : 2 ≤ n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (α : ℝ) (hα : 0 < α)
    (hmax : α ≤ 1 / (n : ℝ))
    (hρ : 1 - 2 * α ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => root ((cubeBSC n (1 - 2 * α) hρ).apply f x)) /
        (2 * Real.sqrt (α * (1 - α))) ≥
      (1 - α) ^ (((n : ℝ) - 2) / 2) * Real.sqrt (1 - (n : ℝ) * α) *
        mean (fun x => Real.sqrt (Flatness.sensitivity f x)) := by
  obtain ⟨hhalf, _⟩ := alpha_bounds n hn α hα.le hmax
  have hb : 0 < 1 - α := by linarith
  have hden : 0 < 2 * Real.sqrt (α * (1 - α)) := by positivity
  have hroot : root (1 - 2 * α) = 2 * Real.sqrt (α * (1 - α)) := by
    have hs : Real.sqrt (α * (1 - α)) ^ 2 = α * (1 - α) := Real.sq_sqrt (by positivity)
    have hr : root (1 - 2 * α) ^ 2 = 1 - (1 - 2 * α) ^ 2 :=
      Real.sq_sqrt (by nlinarith [hρ.1, hρ.2])
    have hnroot : 0 ≤ root (1 - 2 * α) := Real.sqrt_nonneg _
    nlinarith only [hs, hr, hnroot, le_of_lt hden]
  have hevent := BentLow.posterior_root_mean_lower (show 1 ≤ n by omega) hf (1 - 2 * α) hρ
  rw [hroot] at hevent
  have hbase : (1 + (1 - 2 * α)) / 2 = 1 - α := by ring
  rw [hbase] at hevent
  have hm : 0 ≤ mean (fun x => Real.sqrt (Flatness.sensitivity f x)) := by
    unfold mean
    positivity
  have hc := mul_le_mul_of_nonneg_right (coefficient_le n hn α hα.le hmax) hm
  apply (le_div_iff₀ hden).mpr
  nlinarith only [hc, hevent, hden]

/-- Noise admissibility is a consequence of the stated alpha range, not an extra
restriction on the manuscript theorem. -/
theorem manuscript_low_noise_full {n : ℕ} (hn : 2 ≤ n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (α : ℝ) (hα : 0 < α)
    (hmax : α ≤ 1 / (n : ℝ)) :
    let hρ : 1 - 2 * α ∈ Set.Icc (0 : ℝ) 1 := by
      obtain ⟨hhalf, _⟩ := alpha_bounds n hn α hα.le hmax
      constructor <;> linarith
    mean (fun x => root ((cubeBSC n (1 - 2 * α) hρ).apply f x)) /
        (2 * Real.sqrt (α * (1 - α))) ≥
      (1 - α) ^ (((n : ℝ) - 2) / 2) * Real.sqrt (1 - (n : ℝ) * α) *
        mean (fun x => Real.sqrt (Flatness.sensitivity f x)) := by
  dsimp only
  exact manuscript_low_noise hn f hf α hα hmax _

#print axioms manuscript_low_noise_full
end Hellinger.BentLowExact
