import Hellinger.IndependentChannels
import Hellinger.DiscreteBayes

/-! The discrete Bhattacharyya parameter is the posterior root expectation. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace Hellinger.Bhattacharyya

theorem weighted_root (q p m P M : ℝ) (hq : 0 ≤ q) (hp : 0 ≤ p) (hm : 0 ≤ m)
    (hsum : p + m = 1) (hP : q * p = P / 2) (hM : q * m = M / 2) :
    q * root (p - m) = Real.sqrt (P * M) := by
  have ha : p - m ∈ Set.Icc (-1 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have hr : root (p - m) ^ 2 = 1 - (p - m) ^ 2 :=
    Real.sq_sqrt (by nlinarith [ha.1, ha.2])
  have hprod := congrArg₂ (fun a b : ℝ => a * b) hP hM
  have hpm : 1 - (p - m) ^ 2 = 4 * p * m := by nlinarith [sq_nonneg (p + m - 1)]
  have hsquare : (q * root (p - m)) ^ 2 = P * M := by
    calc
      _ = q ^ 2 * (1 - (p - m) ^ 2) := by rw [mul_pow, hr]
      _ = 4 * (q * p) * (q * m) := by rw [hpm]; ring
      _ = P * M := by nlinarith [hprod]
  rw [← hsquare]
  exact (Real.sqrt_sq (show 0 ≤ q * root (p - m) from mul_nonneg hq (Real.sqrt_nonneg _))).symm

theorem discrete_parameter {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
    [Countable E] [MeasurableSingletonClass E] [Nonempty E]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → Bool) (Y : Ω → E)
    (hB : Measurable B) (hY : Measurable Y)
    (hfair : μ.map B = (PMF.uniformOfFintype Bool).toMeasure) :
    (∫ ω, root (μ[fun ω => boolSign (B ω) | MeasurableSpace.comap Y inferInstance] ω) ∂μ) =
      ∑' y, Real.sqrt ((condDistrib Y B μ false).real {y} *
        (condDistrib Y B μ true).real {y}) := by
  let a := IndependentChannels.bias (condDistrib B Y μ)
  have ha : Measurable a := IndependentChannels.measurable_bias _
  have hr : Measurable (fun y => root (a y)) := by unfold root; fun_prop
  have hν : IsProbabilityMeasure (μ.map Y) := Measure.isProbabilityMeasure_map hY.aemeasurable
  let : IsProbabilityMeasure (μ.map Y) := hν
  have hint := ProductPosterior.integrable_of_abs_le (μ.map Y) _ hr 1
    (fun y => by rw [abs_of_nonneg (ProductPosterior.root_mem _).1]; exact (ProductPosterior.root_mem _).2)
  have hc := IndependentChannels.coordinate_condExp μ (fun _ : Unit => B) (fun _ : Unit => Y)
    (fun _ => hB) (fun _ => hY) ()
  have hpoint (y : E) : (μ.map Y).real {y} * root (a y) =
      Real.sqrt ((condDistrib Y B μ false).real {y} * (condDistrib Y B μ true).real {y}) := by
    apply weighted_root _ _ _ _ _ measureReal_nonneg measureReal_nonneg measureReal_nonneg
      (IndependentChannels.bool_masses (condDistrib B Y μ y))
    · convert DiscreteBayes.bayes_singleton μ B Y hB hY hfair y false using 1
      ring
    · convert DiscreteBayes.bayes_singleton μ B Y hB hY hfair y true using 1
      ring
  calc
    _ = ∫ ω, root (a (Y ω)) ∂μ := integral_congr_ae (hc.fun_comp root)
    _ = ∫ y, root (a y) ∂μ.map Y := (integral_map hY.aemeasurable hr.aestronglyMeasurable).symm
    _ = ∑' y, (μ.map Y).real {y} * root (a y) := by rw [integral_countable hint]; rfl
    _ = _ := tsum_congr hpoint

theorem discrete_channelParameter {ι Ω : Type*} [MeasurableSpace Ω]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : ι → Ω → Bool) (Y : (i : ι) → Ω → E i)
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hfair : ∀ i, μ.map (B i) = (PMF.uniformOfFintype Bool).toMeasure)
    (i : ι) [Countable (E i)] [MeasurableSingletonClass (E i)] [Nonempty (E i)] :
    IndependentChannels.channelParameter μ B Y i =
      ∑' y, Real.sqrt ((condDistrib (Y i) (B i) μ false).real {y} *
        (condDistrib (Y i) (B i) μ true).real {y}) :=
  discrete_parameter μ (B i) (Y i) (hB i) (hY i) (hfair i)

#print axioms weighted_root
#print axioms discrete_parameter

end Hellinger.Bhattacharyya
