import Hellinger.PosteriorSections
import Hellinger.ProductDisintegration
import Mathlib.Probability.Distributions.Uniform
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure

/-! The independent-channel theorem for the original random variables and
conditional expectations, with arbitrary measurable output spaces. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ProbabilityTheory
open MeasureTheory ProbabilityTheory

namespace Hellinger.IndependentChannels

open ProductPosterior ProductDisintegration

def bias {E : Type*} [MeasurableSpace E] (κ : Kernel E Bool) (y : E) : ℝ :=
  (κ y).real {false} - (κ y).real {true}

theorem measurable_bias {E : Type*} [MeasurableSpace E] (κ : Kernel E Bool) :
    Measurable (bias κ) :=
  ((κ.measurable_coe (measurableSet_singleton false)).ennreal_toReal).sub
    ((κ.measurable_coe (measurableSet_singleton true)).ennreal_toReal)

theorem bool_masses (ν : Measure Bool) [IsProbabilityMeasure ν] :
    ν.real {false} + ν.real {true} = 1 := by
  have h := measureReal_add_measureReal_compl (μ := ν) (measurableSet_singleton false)
  have hc : ({false} : Set Bool)ᶜ = {true} := by ext b; cases b <;> simp
  simpa only [hc, measureReal_def, measure_univ, ENNReal.toReal_one] using h

theorem bias_mem {E : Type*} [MeasurableSpace E] (κ : Kernel E Bool) [IsMarkovKernel κ] (y : E) :
    bias κ y ∈ Set.Icc (-1 : ℝ) 1 := by
  have hsum := bool_masses (κ y)
  have hp := measureReal_nonneg (μ := κ y) (s := {false})
  have hn := measureReal_nonneg (μ := κ y) (s := {true})
  dsimp [bias]
  constructor <;> linarith

theorem bias_mass {E : Type*} [MeasurableSpace E] (κ : Kernel E Bool) [IsMarkovKernel κ]
    (y : E) (b : Bool) : (κ y).real {b} = bitProbability (bias κ y) b := by
  have hsum := bool_masses (κ y)
  cases b <;> norm_num [bitProbability, bias, boolSign] <;> linarith

theorem boolSign_integrable (ν : Measure Bool) [IsFiniteMeasure ν] : Integrable boolSign ν := by
  apply integrable_of_abs_le ν boolSign (measurable_of_finite boolSign) 1
  intro b
  cases b <;> norm_num [boolSign]

theorem bias_integral {E : Type*} [MeasurableSpace E] (κ : Kernel E Bool) [IsMarkovKernel κ] (y : E) :
    bias κ y = ∫ b, boolSign b ∂κ y := by
  rw [integral_fintype (boolSign_integrable (κ y))]
  simp [bias, boolSign]
  ring

theorem uniform_mean : ∫ b, boolSign b ∂(PMF.uniformOfFintype Bool).toMeasure = 0 := by
  rw [integral_fintype (boolSign_integrable _)]
  norm_num [boolSign, Measure.real, PMF.toMeasure_apply_singleton, PMF.uniformOfFintype_apply]

theorem productKernel_integral {ι : Type*} [Fintype ι] [DecidableEq ι]
    {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
    (κ : (i : ι) → Kernel (E i) Bool) [∀ i, IsMarkovKernel (κ i)]
    (f : (ι → Bool) → ℝ) (y : (i : ι) → E i) :
    (∫ b, f b ∂productKernel κ y) = PosteriorSections.value (fun i => bias (κ i)) f y := by
  rw [integral_fintype Integrable.of_finite]
  unfold PosteriorSections.value PosteriorSections.probability
  apply Finset.sum_congr rfl
  intro b _
  change (productKernel κ y {b}).toReal * f b = _
  rw [productKernel_singleton, ENNReal.toReal_prod]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact bias_mass (κ i) (y i) (b i)

section RandomVariables

variable {ι Ω : Type*} [Fintype ι] [DecidableEq ι] [MeasurableSpace Ω]
variable {E : ι → Type*} [∀ i, MeasurableSpace (E i)]
variable (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : ι → Ω → Bool) (Y : (i : ι) → Ω → E i)

def coordinateBias (i : ι) : E i → ℝ := bias (condDistrib (B i) (Y i) μ)

def outputLaw (i : ι) : Measure (E i) := μ.map (Y i)

def posterior (f : (ι → Bool) → ℝ) : Ω → ℝ :=
  μ[fun ω => f (fun i => B i ω) | MeasurableSpace.comap (fun ω i => Y i ω) inferInstance]

def channelParameter (i : ι) : ℝ :=
  ∫ ω, root (μ[fun ω => boolSign (B i ω) | MeasurableSpace.comap (Y i) inferInstance] ω) ∂μ

omit [Fintype ι] [DecidableEq ι] in
theorem coordinate_condExp (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i)) (i : ι) :
    μ[fun ω => boolSign (B i ω) | MeasurableSpace.comap (Y i) inferInstance] =ᵐ[μ]
      fun ω => coordinateBias μ B Y i (Y i ω) := by
  have hint : Integrable (fun ω => boolSign (B i ω)) μ := by
    apply integrable_of_abs_le μ _ ((measurable_of_finite boolSign).comp (hB i)) 1
    intro ω
    cases hb : B i ω <;> norm_num [boolSign, hb]
  have h := condExp_ae_eq_integral_condDistrib (hY i) (hB i).aemeasurable
    (measurable_of_finite boolSign).stronglyMeasurable hint
  simpa only [coordinateBias, bias_integral] using h

omit [Fintype ι] [DecidableEq ι] in
theorem coordinate_mean_zero (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hfair : ∀ i, μ.map (B i) = (PMF.uniformOfFintype Bool).toMeasure) (i : ι) :
    ∫ y, coordinateBias μ B Y i y ∂outputLaw μ Y i = 0 := by
  have hm : Measurable (coordinateBias μ B Y i) := measurable_bias _
  rw [outputLaw, integral_map (hY i).aemeasurable hm.aestronglyMeasurable]
  calc
    _ = ∫ ω, μ[fun ω => boolSign (B i ω) | MeasurableSpace.comap (Y i) inferInstance] ω ∂μ :=
      integral_congr_ae (coordinate_condExp μ B Y hB hY i).symm
    _ = ∫ ω, boolSign (B i ω) ∂μ := integral_condExp (hY i).comap_le
    _ = ∫ b, boolSign b ∂μ.map (B i) :=
      (integral_map (hB i).aemeasurable (measurable_of_finite boolSign).aestronglyMeasurable).symm
    _ = 0 := by rw [hfair i]; exact uniform_mean

omit [Fintype ι] [DecidableEq ι] in
theorem channelParameter_eq (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i)) (i : ι) :
    channelParameter μ B Y i =
      PosteriorSections.parameter (outputLaw μ Y) (coordinateBias μ B Y) i := by
  have hm : Measurable (fun y => root (coordinateBias μ B Y i y)) := by
    have hb := measurable_bias (condDistrib (B i) (Y i) μ)
    unfold coordinateBias root
    fun_prop
  rw [PosteriorSections.parameter, outputLaw, integral_map (hY i).aemeasurable hm.aestronglyMeasurable]
  exact integral_congr_ae ((coordinate_condExp μ B Y hB hY i).fun_comp root)

theorem posterior_value (f : (ι → Bool) → ℝ)
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ) :
    posterior μ B Y f =ᵐ[μ]
      fun ω => PosteriorSections.value (coordinateBias μ B Y) f (fun i => Y i ω) := by
  have h := conditional_expectation_productKernel μ B Y f hB hY hpairs
  simp_rw [productKernel_integral] at h
  exact h

theorem posterior_root_integral (f : (ι → Bool) → ℝ)
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ) :
    (∫ ω, root (posterior μ B Y f ω) ∂μ) =
      ∫ y, root (PosteriorSections.value (coordinateBias μ B Y) f y)
        ∂Measure.pi (outputLaw μ Y) := by
  have hm : Measurable (fun y => root (PosteriorSections.value (coordinateBias μ B Y) f y)) := by
    have hv := PosteriorSections.measurable_value (coordinateBias μ B Y)
      (fun i => measurable_bias (condDistrib (B i) (Y i) μ)) f
    unfold root
    fun_prop
  calc
    _ = ∫ ω, root (PosteriorSections.value (coordinateBias μ B Y) f (fun i => Y i ω)) ∂μ :=
      integral_congr_ae ((posterior_value μ B Y f hB hY hpairs).fun_comp root)
    _ = ∫ y, root (PosteriorSections.value (coordinateBias μ B Y) f y)
        ∂μ.map (fun ω i => Y i ω) :=
      (integral_map (by fun_prop : Measurable (fun ω i => Y i ω)).aemeasurable
        hm.aestronglyMeasurable).symm
    _ = _ := by rw [independent_output_law μ B Y hY hpairs]; rfl

theorem independent_channel_bound (p : ι → Prop) [DecidablePred p] [Nonempty {i // p i}]
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ)
    (hfair : ∀ i, μ.map (B i) = (PMF.uniformOfFintype Bool).toMeasure)
    (f : (ι → Bool) → ℝ) (hf : ∀ b, f b = -1 ∨ f b = 1)
    (hflip : ∀ b, f (fun i => if p i then !(b i) else b i) = -f b)
    (i : {i // p i}) (hmin : ∀ j : {j // p j}, channelParameter μ B Y i ≤ channelParameter μ B Y j) :
    channelParameter μ B Y i ≤ ∫ ω, root (posterior μ B Y f ω) ∂μ := by
  let : ∀ j, IsProbabilityMeasure (outputLaw μ Y j) :=
    fun j => Measure.isProbabilityMeasure_map (hY j).aemeasurable
  rw [channelParameter_eq μ B Y hB hY i, posterior_root_integral μ B Y f hB hY hpairs]
  apply PosteriorSections.subset_bound p (outputLaw μ Y) (coordinateBias μ B Y)
    (fun j => measurable_bias _) (fun j => bias_mem _)
    (coordinate_mean_zero μ B Y hB hY hfair) f hf hflip
  · exact PosteriorSections.parameter_mem (outputLaw μ Y) (coordinateBias μ B Y)
      (fun j => measurable_bias (condDistrib (B j) (Y j) μ)) i
  · intro j hj
    simpa only [channelParameter_eq μ B Y hB hY] using hmin ⟨j, hj⟩

theorem coordinate_attains (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ) (i : ι) :
    (∫ ω, root (posterior μ B Y (fun b => boolSign (b i)) ω) ∂μ) = channelParameter μ B Y i := by
  let : ∀ j, IsProbabilityMeasure (outputLaw μ Y j) :=
    fun j => Measure.isProbabilityMeasure_map (hY j).aemeasurable
  rw [posterior_root_integral μ B Y _ hB hY hpairs, channelParameter_eq μ B Y hB hY]
  exact PosteriorSections.coordinate_attains _ _ (fun j => measurable_bias _) i

/-- The minimum of the original conditional-expectation parameters is the
sharp bound over the entire sign-reversing class. -/
theorem independent_channels (p : ι → Prop) [DecidablePred p] [Nonempty {i // p i}]
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ)
    (hfair : ∀ i, μ.map (B i) = (PMF.uniformOfFintype Bool).toMeasure) :
    ∃ i : {i // p i}, (∀ j : {j // p j}, channelParameter μ B Y i ≤ channelParameter μ B Y j) ∧
      (∀ f : (ι → Bool) → ℝ, (∀ b, f b = -1 ∨ f b = 1) →
        (∀ b, f (fun j => if p j then !(b j) else b j) = -f b) →
        channelParameter μ B Y i ≤ ∫ ω, root (posterior μ B Y f ω) ∂μ) ∧
      (∀ b : ι → Bool, boolSign ((fun j => if p j then !(b j) else b j) i) = -boolSign (b i)) ∧
      (∫ ω, root (posterior μ B Y (fun b => boolSign (b i)) ω) ∂μ) = channelParameter μ B Y i := by
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset {i // p i})
    (fun i => channelParameter μ B Y i) Finset.univ_nonempty
  have hmini := fun j => hmin j (Finset.mem_univ j)
  refine ⟨i, hmini, ?_, ?_, coordinate_attains μ B Y hB hY hpairs i⟩
  · intro f hf hflip
    exact independent_channel_bound μ B Y p hB hY hpairs hfair f hf hflip i hmini
  · intro b
    simp only [i.property, if_true]
    cases b i <;> norm_num [boolSign]

end RandomVariables

#print axioms coordinate_mean_zero
#print axioms channelParameter_eq
#print axioms independent_channels

end Hellinger.IndependentChannels
