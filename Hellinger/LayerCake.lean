import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Tactic

/-! The literal integral layer-cake identity for two ordered nonnegative
finite lists. The measure is Lebesgue measure on the nonnegative real axis. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory Set

namespace Hellinger.LayerCake

def threshold (a t : ℝ) : ℝ := if t < a then 1 else 0

theorem threshold_difference_indicator (a b : ℝ) (hab : a ≤ b) :
    (fun t => |threshold a t - threshold b t|) =
      (Ico a b).indicator (fun _ => (1 : ℝ)) := by
  funext t
  by_cases hta : t < a
  · have htb : t < b := hta.trans_le hab
    simp [threshold, hta, htb, Set.indicator_of_notMem, not_le.mpr hta]
  · by_cases htb : t < b
    · simp [threshold, hta, htb, not_lt.mp hta]
    · simp [threshold, hta, htb]

theorem threshold_difference_integrable (a b : ℝ) :
    Integrable (fun t => |threshold a t - threshold b t|) := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [abs_sub_comm] using this b a (le_of_not_ge hab)
  rw [threshold_difference_indicator a b hab]
  exact (integrable_indicator_iff measurableSet_Ico).mpr
    (integrableOn_const (by simp [Real.volume_Ico]))

theorem threshold_difference_integral (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (∫ t in Ici (0 : ℝ), |threshold a t - threshold b t|) = |a - b| := by
  wlog hab : a ≤ b generalizing a b
  · simpa only [abs_sub_comm] using this b a hb ha (le_of_not_ge hab)
  rw [threshold_difference_indicator a b hab, setIntegral_indicator measurableSet_Ico]
  have hsub : Ico a b ⊆ Ici (0 : ℝ) := fun t ht => ha.trans ht.1
  rw [inter_eq_right.mpr hsub, setIntegral_const]
  simp only [measureReal_def, Real.volume_Ico, ENNReal.toReal_ofReal (sub_nonneg.mpr hab),
    smul_eq_mul, mul_one, abs_of_nonpos (sub_nonpos.mpr hab)]
  ring

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

theorem threshold_cuts_nested (a b : ι → ℝ) (ha : Antitone a) (hb : Antitone b) (t : ℝ) :
    (∀ i, threshold (a i) t ≤ threshold (b i) t) ∨
      (∀ i, threshold (b i) t ≤ threshold (a i) t) := by
  by_cases h : ∀ i, t < a i → t < b i
  · left
    intro i
    by_cases hi : t < a i
    · simp [threshold, hi, h i hi]
    · simp [threshold, hi]
      split_ifs <;> norm_num
  · push Not at h
    obtain ⟨i, hai, hbi⟩ := h
    have hreverse : ∀ j, t < b j → t < a j := by
      intro j hj
      rcases le_total j i with hji | hij
      · exact hai.trans_le (ha hji)
      · exact False.elim ((not_lt_of_ge hbi) (hj.trans_le (hb hij)))
    right
    intro j
    by_cases hj : t < b j
    · simp [threshold, hj, hreverse j hj]
    · simp [threshold, hj]
      split_ifs <;> norm_num

theorem sum_abs_threshold_difference (a b : ι → ℝ)
    (ha : Antitone a) (hb : Antitone b) (t : ℝ) :
    (∑ i, |threshold (a i) t - threshold (b i) t|) =
      |(∑ i, threshold (a i) t) - ∑ i, threshold (b i) t| := by
  rw [← Finset.sum_sub_distrib]
  rcases threshold_cuts_nested a b ha hb t with hab | hba
  · have hn : ∀ i, threshold (a i) t - threshold (b i) t ≤ 0 :=
      fun i => sub_nonpos.mpr (hab i)
    rw [abs_of_nonpos (Finset.sum_nonpos (fun i _ => hn i))]
    simp_rw [abs_of_nonpos (hn _), Finset.sum_neg_distrib]
  · have hp : ∀ i, 0 ≤ threshold (a i) t - threshold (b i) t :=
      fun i => sub_nonneg.mpr (hba i)
    rw [abs_of_nonneg (Finset.sum_nonneg (fun i _ => hp i))]
    simp_rw [abs_of_nonneg (hp _)]

def countAbove (a : ι → ℝ) (t : ℝ) : ℝ :=
  ((Finset.univ.filter (fun i => t < a i)).card : ℝ)

omit [LinearOrder ι] in
theorem countAbove_eq_sum (a : ι → ℝ) (t : ℝ) :
    countAbove a t = ∑ i, threshold (a i) t := by
  simp only [countAbove, threshold, Finset.sum_boole]

/-- The exact counting-function integrand is integrable; its integral is not
using a default value for a nonintegrable function. -/
theorem counting_difference_integrable (a b : ι → ℝ)
    (ha : Antitone a) (hb : Antitone b) :
    Integrable (fun t => |countAbove a t - countAbove b t|) := by
  have hi := integrable_finsetSum (Finset.univ : Finset ι)
    (fun i _ => threshold_difference_integrable (a i) (b i))
  simpa only [sum_abs_threshold_difference a b ha hb, ← countAbove_eq_sum] using hi

/-- Original manuscript equation `eq:layercake`, including arbitrary equal
entries and zeros and an empty index type. -/
theorem ordered_layer_cake (a b : ι → ℝ) (ha : Antitone a) (hb : Antitone b)
    (ha₀ : ∀ i, 0 ≤ a i) (hb₀ : ∀ i, 0 ≤ b i) :
    (∑ i, |a i - b i|) = ∫ t in Ici (0 : ℝ), |countAbove a t - countAbove b t| := by
  simp_rw [countAbove_eq_sum, ← sum_abs_threshold_difference a b ha hb]
  rw [integral_finsetSum Finset.univ (fun i _ =>
    (threshold_difference_integrable (a i) (b i)).mono_measure Measure.restrict_le_self)]
  simp_rw [threshold_difference_integral _ _ (ha₀ _) (hb₀ _)]

#print axioms ordered_layer_cake
end Hellinger.LayerCake
