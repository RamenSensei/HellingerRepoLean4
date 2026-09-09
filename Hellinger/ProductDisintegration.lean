import Mathlib.Probability.Kernel.CondDistrib
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Pi
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-! Independent coordinate pairs have the product of their genuine conditional
Boolean distributions as the conditional law given all outputs. The output
spaces are arbitrary measurable spaces. Only the conditioned Boolean space
uses the standard-Borel hypothesis required by disintegration. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators ENNReal ProbabilityTheory
open MeasureTheory ProbabilityTheory Set

namespace Hellinger.ProductDisintegration

variable {ι : Type*} [Fintype ι]
variable {E : ι → Type*} [∀ i, MeasurableSpace (E i)]

/-- The finite product of coordinate Boolean probability kernels. -/
def productKernel (κ : (i : ι) → Kernel (E i) Bool) [∀ i, IsMarkovKernel (κ i)] :
    Kernel ((i : ι) → E i) (ι → Bool) where
  toFun y := Measure.pi (fun i => κ i (y i))
  measurable' := by
    classical
    refine Measure.measurable_of_measurable_coe _ (fun s _ => ?_)
    have hs : s.Finite := Set.toFinite s
    have hmass (y : (i : ι) → E i) :
        Measure.pi (fun i => κ i (y i)) s =
          ∑ b ∈ hs.toFinset, ∏ i, κ i (y i) {b i} := by
      calc
        _ = Measure.pi (fun i => κ i (y i)) hs.toFinset := by rw [hs.coe_toFinset]
        _ = ∑ b ∈ hs.toFinset, Measure.pi (fun i => κ i (y i)) {b} := sum_measure_singleton.symm
        _ = _ := by simp only [Measure.pi_singleton]
    simp_rw [hmass]
    apply Finset.measurable_fun_sum
    intro b _
    apply Finset.measurable_fun_prod
    intro i _
    exact (Kernel.measurable_coe (κ i) (measurableSet_singleton (b i))).comp (measurable_pi_apply i)

@[simp] theorem productKernel_apply (κ : (i : ι) → Kernel (E i) Bool)
    [∀ i, IsMarkovKernel (κ i)] (y : (i : ι) → E i) :
    productKernel κ y = Measure.pi (fun i => κ i (y i)) := rfl

instance productKernel_isMarkov (κ : (i : ι) → Kernel (E i) Bool)
    [∀ i, IsMarkovKernel (κ i)] : IsMarkovKernel (productKernel κ) := by
  constructor
  intro y
  change IsProbabilityMeasure (Measure.pi (fun i => κ i (y i)))
  infer_instance

@[simp] theorem productKernel_singleton (κ : (i : ι) → Kernel (E i) Bool)
    [∀ i, IsMarkovKernel (κ i)] (y : (i : ι) → E i) (b : ι → Bool) :
    productKernel κ y {b} = ∏ i, κ i (y i) {b i} := by
  rw [productKernel_apply, Measure.pi_singleton]

def groupEquiv : ((i : ι) → E i × Bool) ≃ᵐ (((i : ι) → E i) × (ι → Bool)) where
  toEquiv :=
    { toFun := fun z => ((fun i => (z i).1), (fun i => (z i).2))
      invFun := fun z i => (z.1 i, z.2 i)
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  measurable_toFun := by
    change Measurable (fun z : (i : ι) → E i × Bool => ((fun i => (z i).1), (fun i => (z i).2)))
    fun_prop
  measurable_invFun := by
    change Measurable (fun z : ((i : ι) → E i) × (ι → Bool) => fun i => (z.1 i, z.2 i))
    fun_prop

/- Tonelli factorization for a product of nonnegative measurable coordinate
functions on a finite product space. -/
set_option backward.isDefEq.respectTransparency false in
theorem lintegral_fin_prod {n : ℕ} {X : Fin n → Type*}
    [∀ i, MeasurableSpace (X i)] (ν : (i : Fin n) → Measure (X i)) [∀ i, SigmaFinite (ν i)]
    (f : (i : Fin n) → X i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi ν) = ∏ i, ∫⁻ z, f i z ∂ν i := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      _ = ∫⁻ z : X 0 × ((i : Fin n) → X i.succ),
          f 0 z.1 * ∏ i : Fin n, f i.succ (z.2 i)
          ∂(ν 0).prod (Measure.pi (fun i => ν i.succ)) := by
        rw [← ((measurePreserving_piFinSuccAbove ν 0).symm).lintegral_comp_emb
          (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
        simp_rw [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv,
          Fin.prod_univ_succ, Fin.insertNth_zero, Equiv.coe_fn_mk, Fin.cons_succ,
          Fin.zero_succAbove, cast_eq, Fin.cons_zero]
      _ = (∫⁻ z, f 0 z ∂ν 0) * ∏ i : Fin n, ∫⁻ z, f i.succ z ∂ν i.succ := by
        rw [lintegral_prod_mul (f := f 0)
          (g := fun x : (i : Fin n) → X i.succ => ∏ i, f i.succ (x i)) (hf 0).aemeasurable]
        · rw [ih _ _ (fun i => hf i.succ)]
        · exact (Finset.measurable_fun_prod _ (fun i _ => (hf i.succ).comp
            (measurable_pi_apply i))).aemeasurable
      _ = _ := by rw [Fin.prod_univ_succ]

theorem lintegral_fintype_prod (ν : (i : ι) → Measure (E i)) [∀ i, SigmaFinite (ν i)]
    (f : (i : ι) → E i → ℝ≥0∞) (hf : ∀ i, Measurable (f i)) :
    (∫⁻ x, ∏ i, f i (x i) ∂Measure.pi ν) = ∏ i, ∫⁻ z, f i z ∂ν i := by
  let e := (Fintype.equivFin ι).symm
  rw [← (measurePreserving_piCongrLeft _ e).lintegral_comp_emb
    (MeasurableEquiv.measurableEmbedding _) (fun x => ∏ i, f i (x i))]
  simp_rw [← e.prod_comp, MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
  exact lintegral_fin_prod _ _ (fun i => hf (e i))

/-- Grouping independent coordinate disintegrations is the disintegration by
the product kernel. This identity does not impose any regularity assumption
on the output measurable spaces. -/
theorem pi_compProd (ν : (i : ι) → Measure (E i)) [∀ i, IsProbabilityMeasure (ν i)]
    (κ : (i : ι) → Kernel (E i) Bool) [∀ i, IsMarkovKernel (κ i)] :
    ((Measure.pi ν) ⊗ₘ productKernel κ).map (groupEquiv (E := E)).symm =
      Measure.pi (fun i => ν i ⊗ₘ κ i) := by
  apply (Measure.pi_eq ?_).symm
  intro s hs
  rw [Measure.map_apply (groupEquiv (E := E)).symm.measurable (.univ_pi hs),
    Measure.compProd_apply ((MeasurableSet.univ_pi hs).preimage (groupEquiv (E := E)).symm.measurable)]
  have hsect (y : (i : ι) → E i) :
      Prod.mk y ⁻¹' ((groupEquiv (E := E)).symm ⁻¹' univ.pi s) =
        univ.pi (fun i => Prod.mk (y i) ⁻¹' s i) := by
    rfl
  simp_rw [productKernel_apply, hsect, Measure.pi_pi]
  rw [lintegral_fintype_prod ν (fun i y => κ i y (Prod.mk y ⁻¹' s i))
    (fun i => Kernel.measurable_kernel_prodMk_left (hs i))]
  apply Finset.prod_congr rfl
  intro i _
  exact (Measure.compProd_apply (hs i)).symm

section RandomVariables

variable {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
variable (B : ι → Ω → Bool) (Y : (i : ι) → Ω → E i)

/-- Exact joint-law disintegration derived from independence of the actual
pairs `(Y_i,B_i)` and the actual coordinate conditional distributions. -/
theorem independent_pair_disintegration
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ) :
    μ.map (fun ω => ((fun i => Y i ω), (fun i => B i ω))) =
      (Measure.pi (fun i => μ.map (Y i))) ⊗ₘ
        productKernel (fun i => condDistrib (B i) (Y i) μ) := by
  have hν (i : ι) : IsProbabilityMeasure (μ.map (Y i)) := Measure.isProbabilityMeasure_map (hY i).aemeasurable
  let : ∀ i, IsProbabilityMeasure (μ.map (Y i)) := hν
  have hc := pi_compProd (fun i => μ.map (Y i)) (fun i => condDistrib (B i) (Y i) μ)
  simp_rw [compProd_map_condDistrib (hB _).aemeasurable] at hc
  have hi := hpairs.map_fun_eq_pi_map (fun i => ((hY i).prodMk (hB i)).aemeasurable)
  rw [← hi] at hc
  have hg := congrArg (fun ξ => ξ.map (groupEquiv (E := E))) hc
  rw [Measure.map_map (groupEquiv (E := E)).measurable
    (groupEquiv (E := E)).symm.measurable, Measure.map_map (groupEquiv (E := E)).measurable
    (by fun_prop : Measurable (fun ω i => (Y i ω, B i ω)))] at hg
  have he : (groupEquiv (E := E)) ∘ (groupEquiv (E := E)).symm = id := by
    funext z
    exact (groupEquiv (E := E)).apply_symm_apply z
  rw [he, Measure.map_id] at hg
  exact hg.symm

/- The output vector has the product of the coordinate output marginals. -/
omit [IsProbabilityMeasure μ] in
theorem independent_output_law
    (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ) :
    μ.map (fun ω i => Y i ω) = Measure.pi (fun i => μ.map (Y i)) := by
  have hi := hpairs.comp (fun _ => Prod.fst) (fun _ => measurable_fst)
  exact hi.map_fun_eq_pi_map (fun i => (hY i).aemeasurable)

/-- Uniqueness identifies the constructed product kernel with the actual
conditional distribution of the full Boolean input vector. -/
theorem productKernel_ae_condDistrib
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ) :
    productKernel (fun i => condDistrib (B i) (Y i) μ) =ᵐ[μ.map (fun ω i => Y i ω)]
      condDistrib (fun ω i => B i ω) (fun ω i => Y i ω) μ := by
  symm
  apply condDistrib_ae_eq_of_measure_eq_compProd_of_measurable
    (by fun_prop) (by fun_prop)
  rw [independent_output_law μ B Y hY hpairs]
  exact independent_pair_disintegration μ B Y hB hY hpairs

/-- The actual conditional expectation given all outputs is the integral
against the product of the coordinate conditional Boolean distributions. -/
theorem conditional_expectation_productKernel (f : (ι → Bool) → ℝ)
    (hB : ∀ i, Measurable (B i)) (hY : ∀ i, Measurable (Y i))
    (hpairs : iIndepFun (fun i ω => (Y i ω, B i ω)) μ) :
    μ[fun ω => f (fun i => B i ω) | MeasurableSpace.comap (fun ω i => Y i ω) inferInstance]
      =ᵐ[μ] fun ω => ∫ b, f b ∂productKernel
        (fun i => condDistrib (B i) (Y i) μ) (fun i => Y i ω) := by
  have hYm : Measurable (fun ω i => Y i ω) := by fun_prop
  have hBm : Measurable (fun ω i => B i ω) := by fun_prop
  have hfm : StronglyMeasurable f := (measurable_of_countable f).stronglyMeasurable
  have hint : Integrable (fun ω => f (fun i => B i ω)) μ :=
    (integrable_map_measure hfm.aestronglyMeasurable hBm.aemeasurable).mp Integrable.of_finite
  have hc := condExp_ae_eq_integral_condDistrib hYm hBm.aemeasurable hfm hint
  have hk := ae_of_ae_map hYm.aemeasurable (productKernel_ae_condDistrib μ B Y hB hY hpairs)
  filter_upwards [hc, hk] with ω hω hkω
  rw [hω, hkω]

end RandomVariables

end Hellinger.ProductDisintegration
