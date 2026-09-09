import Hellinger.ProductDisintegration
import Mathlib.Probability.Distributions.Uniform

/-! Bayes' identity for the actual joint law of a fair Boolean input and a
countable discrete channel output. Zero-probability output values are included. -/

set_option autoImplicit false
noncomputable section
open scoped ProbabilityTheory ENNReal
open MeasureTheory ProbabilityTheory Set

namespace Hellinger.DiscreteBayes

variable {Ω E : Type*} [MeasurableSpace Ω] [MeasurableSpace E]
variable [Countable E] [MeasurableSingletonClass E] [Nonempty E]
variable (μ : Measure Ω) [IsProbabilityMeasure μ] (B : Ω → Bool) (Y : Ω → E)

theorem bayes_singleton (hB : Measurable B) (hY : Measurable Y)
    (hfair : μ.map B = (PMF.uniformOfFintype Bool).toMeasure) (y : E) (b : Bool) :
    (μ.map Y).real {y} * (condDistrib B Y μ y).real {b} =
      (1 / 2 : ℝ) * (condDistrib Y B μ b).real {y} := by
  have hforward : μ.map (fun ω => (Y ω, B ω)) ({y} ×ˢ {b}) =
      μ.map Y {y} * condDistrib B Y μ y {b} := by
    rw [← compProd_map_condDistrib hB.aemeasurable,
      Measure.compProd_apply_prod (measurableSet_singleton y) (measurableSet_singleton b),
      lintegral_singleton, mul_comm]
  have hbackward : μ.map (fun ω => (B ω, Y ω)) ({b} ×ˢ {y}) =
      μ.map B {b} * condDistrib Y B μ b {y} := by
    rw [← compProd_map_condDistrib hY.aemeasurable,
      Measure.compProd_apply_prod (measurableSet_singleton b) (measurableSet_singleton y),
      lintegral_singleton, mul_comm]
  have hswap : μ.map (fun ω => (Y ω, B ω)) ({y} ×ˢ {b}) =
      μ.map (fun ω => (B ω, Y ω)) ({b} ×ˢ {y}) := by
    rw [Measure.map_apply (hY.prodMk hB) ((measurableSet_singleton y).prod (measurableSet_singleton b)),
      Measure.map_apply (hB.prodMk hY) ((measurableSet_singleton b).prod (measurableSet_singleton y))]
    congr 1
    ext ω
    exact and_comm
  rw [hforward, hbackward] at hswap
  have hr := congrArg ENNReal.toReal hswap
  simp only [ENNReal.toReal_mul] at hr
  change (μ.map Y).real {y} * (condDistrib B Y μ y).real {b} =
    (μ.map B).real {b} * (condDistrib Y B μ b).real {y} at hr
  rw [hfair] at hr
  have hmass : (PMF.uniformOfFintype Bool).toMeasure.real {b} = (1 / 2 : ℝ) := by
    norm_num [Measure.real, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]
  rw [hmass] at hr
  exact hr

end Hellinger.DiscreteBayes
