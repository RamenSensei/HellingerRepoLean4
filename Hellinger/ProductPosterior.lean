import Hellinger.IntegralLifting

/-! Measurable product posterior ensembles with arbitrary output spaces. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix MeasureTheory

namespace Hellinger.ProductPosterior

open Hellinger.Fourier Hellinger.PosteriorState Hellinger.IntegralLifting Hellinger.MatrixLifting

def bitProbability (a : ℝ) (b : Bool) : ℝ := (1 + boolSign b * a) / 2

theorem bitProbability_mem (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) (b : Bool) :
    bitProbability a b ∈ Set.Icc (0 : ℝ) 1 := by
  cases b <;> norm_num [bitProbability, boolSign] <;> constructor <;> linarith [ha.1, ha.2]

theorem bitProbability_sum (a : ℝ) : ∑ b : Bool, bitProbability a b = 1 := by
  simp [bitProbability, boolSign]
  ring

theorem bitProbability_cross (a : ℝ) (ha : a ∈ Set.Icc (-1 : ℝ) 1) :
    Real.sqrt (bitProbability a false) * Real.sqrt (bitProbability a true) = root a / 2 := by
  rw [← Real.sqrt_mul (bitProbability_mem a ha false).1]
  have heq : bitProbability a false * bitProbability a true = (1 - a ^ 2) / 4 := by
    simp [bitProbability, boolSign]
    ring
  rw [heq, Real.sqrt_div' _ (by norm_num : (0 : ℝ) ≤ 4)]
  norm_num [root]

variable {n : ℕ} {E : Fin n → Type*}

def probability (a : (i : Fin n) → E i → ℝ) (y : (i : Fin n) → E i) (b : Cube n) : ℝ :=
  ∏ i, bitProbability (a i (y i)) (b i)

def vector (a : (i : Fin n) → E i → ℝ) (y : (i : Fin n) → E i) (b : Cube n) : ℝ :=
  ∏ i, Real.sqrt (bitProbability (a i (y i)) (b i))

def posteriorMean (a : (i : Fin n) → E i → ℝ) (f : Cube n → ℝ)
    (y : (i : Fin n) → E i) : ℝ := ∑ b, probability a y b * f b

theorem probability_nonneg (a : (i : Fin n) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (y : (i : Fin n) → E i) (b : Cube n) :
    0 ≤ probability a y b := Finset.prod_nonneg (fun i _ => (bitProbability_mem _ (ha i _) _).1)

theorem probability_sum (a : (i : Fin n) → E i → ℝ) (y : (i : Fin n) → E i) :
    ∑ b, probability a y b = 1 := by
  change (∑ b : Cube n, ∏ i, bitProbability (a i (y i)) (b i)) = 1
  rw [← Fintype.prod_sum (fun i b => bitProbability (a i (y i)) b)]
  simp only [bitProbability_sum, Finset.prod_const_one]

theorem vector_sq (a : (i : Fin n) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (y : (i : Fin n) → E i) (b : Cube n) :
    (vector a y b) ^ 2 = probability a y b := by
  simp only [vector, ← Finset.prod_pow, probability]
  apply Finset.prod_congr rfl
  intro i _
  exact Real.sq_sqrt (bitProbability_mem _ (ha i _) _).1

theorem vector_mem (a : (i : Fin n) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (y : (i : Fin n) → E i) (b : Cube n) :
    vector a y b ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · exact Finset.prod_nonneg (fun _ _ => Real.sqrt_nonneg _)
  · exact Finset.prod_le_one (fun _ _ => Real.sqrt_nonneg _)
      (fun i _ => Real.sqrt_le_one.mpr (bitProbability_mem _ (ha i _) _).2)

theorem vector_unit (a : (i : Fin n) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (y : (i : Fin n) → E i) :
    vector a y ⬝ᵥ vector a y = 1 := by
  change (∑ b, vector a y b * vector a y b) = 1
  simp_rw [← pow_two, vector_sq a ha]
  exact probability_sum a y

theorem reflected_unit (a : (i : Fin n) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (f : Cube n → ℝ)
    (hf : ∀ b, f b = -1 ∨ f b = 1) (y : (i : Fin n) → E i) :
    reflectedVector f (vector a y) ⬝ᵥ reflectedVector f (vector a y) = 1 := by
  calc
    _ = vector a y ⬝ᵥ vector a y := by
      apply Finset.sum_congr rfl
      intro b _
      rcases hf b with hb | hb <;> simp [reflectedVector, hb]
    _ = 1 := vector_unit a ha y

theorem vector_inner (a : (i : Fin n) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (f : Cube n → ℝ) (y : (i : Fin n) → E i) :
    vector a y ⬝ᵥ reflectedVector f (vector a y) = posteriorMean a f y := by
  unfold dotProduct posteriorMean
  apply Finset.sum_congr rfl
  intro b _
  rw [reflectedVector, show vector a y b * (f b * vector a y b) = (vector a y b) ^ 2 * f b by ring,
    vector_sq a ha]

theorem posteriorMean_mem (a : (i : Fin n) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (f : Cube n → ℝ)
    (hf : ∀ b, f b ∈ Set.Icc (-1 : ℝ) 1) (y : (i : Fin n) → E i) :
    posteriorMean a f y ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · calc
      -1 = ∑ b, probability a y b * (-1) := by simp [probability_sum]
      _ ≤ posteriorMean a f y := Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (hf b).1 (probability_nonneg a ha y b))
  · calc
      posteriorMean a f y ≤ ∑ b, probability a y b * 1 := Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (hf b).2 (probability_nonneg a ha y b))
      _ = 1 := by simp [probability_sum]

theorem integrable_of_abs_le {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsFiniteMeasure μ]
    (f : Ω → ℝ) (hf : Measurable f) (C : ℝ) (hC : ∀ y, |f y| ≤ C) : Integrable f μ := by
  exact Integrable.of_bound hf.aestronglyMeasurable C
    (Filter.Eventually.of_forall (fun y => by simpa only [Real.norm_eq_abs] using hC y))

theorem root_mem (t : ℝ) : root t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg t])⟩

variable [∀ i, MeasurableSpace (E i)]

theorem measurable_probability (a : (i : Fin n) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (b : Cube n) : Measurable (fun y => probability a y b) := by
  unfold probability bitProbability
  fun_prop

theorem measurable_vector (a : (i : Fin n) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (b : Cube n) : Measurable (fun y => vector a y b) := by
  unfold vector bitProbability
  fun_prop

theorem measurable_posteriorMean (a : (i : Fin n) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (f : Cube n → ℝ) : Measurable (posteriorMean a f) := by
  unfold posteriorMean
  exact Finset.measurable_sum _ (fun b _ => (measurable_probability a ha b).mul measurable_const)

def parameter (μ : (i : Fin n) → Measure (E i)) (a : (i : Fin n) → E i → ℝ) (i : Fin n) : ℝ :=
  ∫ y, root (a i y) ∂μ i

theorem parameter_mem (μ : (i : Fin n) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : Fin n) → E i → ℝ) (ha : ∀ i, Measurable (a i)) (i : Fin n) :
    parameter μ a i ∈ Set.Icc (0 : ℝ) 1 := by
  have hmeas : Measurable (fun y => root (a i y)) := by unfold root; fun_prop
  have hint := integrable_of_abs_le (μ i) _ hmeas 1
    (fun y => by rw [abs_of_nonneg (root_mem _).1]; exact (root_mem _).2)
  constructor
  · exact integral_nonneg (fun y => (root_mem _).1)
  · have h := integral_mono hint (integrable_const (1 : ℝ)) (fun y => (root_mem (a i y)).2)
    simpa [parameter] using h

theorem bitProbability_integral {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Ω → ℝ) (ha : Measurable a) (hb : ∀ y, a y ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∫ y, a y ∂μ = 0) (b : Bool) : ∫ y, bitProbability (a y) b ∂μ = 1 / 2 := by
  have hint : Integrable a μ := integrable_of_abs_le μ a ha 1 (fun y => abs_le.mpr (hb y))
  unfold bitProbability
  rw [integral_div, integral_add (integrable_const 1) (hint.const_mul _), integral_const_mul, hmean]
  simp

theorem coordinate_average {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (a : Ω → ℝ) (ha : Measurable a) (hb : ∀ y, a y ∈ Set.Icc (-1 : ℝ) 1)
    (hmean : ∫ y, a y ∂μ = 0) (b c : Bool) :
    (∫ y, Real.sqrt (bitProbability (a y) b) * Real.sqrt (bitProbability (a y) c) ∂μ) =
      ProductState.oneQubit (∫ y, root (a y) ∂μ) b c := by
  have hpoint (y : Ω) : Real.sqrt (bitProbability (a y) b) * Real.sqrt (bitProbability (a y) c) =
      if b = c then bitProbability (a y) b else root (a y) / 2 := by
    cases b <;> cases c
    · exact Real.mul_self_sqrt (bitProbability_mem _ (hb _) false).1
    · exact bitProbability_cross _ (hb _)
    · change Real.sqrt (bitProbability (a y) true) * Real.sqrt (bitProbability (a y) false) = root (a y) / 2
      rw [mul_comm]
      exact bitProbability_cross _ (hb _)
    · exact Real.mul_self_sqrt (bitProbability_mem _ (hb _) true).1
  simp_rw [hpoint]
  by_cases hbc : b = c
  · simp only [hbc, if_true, ProductState.oneQubit]
    exact bitProbability_integral μ a ha hb hmean c
  · simp only [hbc, if_false, ProductState.oneQubit, integral_div]

theorem average_projection (μ : (i : Fin n) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : Fin n) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ y, a i y ∂μ i = 0) :
    matrixIntegral (Measure.pi μ) (fun y => Matrix.vecMulVec (vector a y) (vector a y)) =
      HeterogeneousState.state n (parameter μ a) := by
  ext b c
  change (∫ y, vector a y b * vector a y c ∂Measure.pi μ) =
    ∏ i, ProductState.oneQubit (parameter μ a i) (b i) (c i)
  simp only [vector, ← Finset.prod_mul_distrib]
  rw [integral_fintype_prod_eq_prod (fun (i : Fin n) (y : E i) =>
    Real.sqrt (bitProbability (a i y) (b i)) * Real.sqrt (bitProbability (a i y) (c i)))]
  apply Finset.prod_congr rfl
  intro i _
  exact coordinate_average (μ i) (a i) (ha i) (hb i) (hmean i) (b i) (c i)

theorem arbitrary_output_lifting (μ : (i : Fin n) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : Fin n) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ y, a i y ∂μ i = 0)
    (f : Cube n → ℝ) (hf : ∀ b, f b = -1 ∨ f b = 1) :
    TraceNorm.traceNorm (HeterogeneousState.state n (parameter μ a) -
      reflection f * HeterogeneousState.state n (parameter μ a) * reflection f) / 2 ≤
      ∫ y, root (posteriorMean a f y) ∂Measure.pi μ := by
  let V := fun y => Matrix.vecMulVec (vector a y) (vector a y)
  let W := fun y => Matrix.vecMulVec (reflectedVector f (vector a y)) (reflectedVector f (vector a y))
  have hV (b c : Cube n) : Integrable (fun y => V y b c) (Measure.pi μ) := by
    apply integrable_of_abs_le (Measure.pi μ) _
      ((measurable_vector a ha b).mul (measurable_vector a ha c)) 1
    intro y
    change |vector a y b * vector a y c| ≤ 1
    rw [abs_of_nonneg (mul_nonneg (vector_mem a hb y b).1 (vector_mem a hb y c).1)]
    exact mul_le_one₀ (vector_mem a hb y b).2 (vector_mem a hb y c).1 (vector_mem a hb y c).2
  have hW (b c : Cube n) : Integrable (fun y => W y b c) (Measure.pi μ) := by
    have heq : (fun y => W y b c) = fun y => (f b * f c) * V y b c := by
      funext y
      simp only [W, V, Matrix.vecMulVec_apply, reflectedVector]
      ring
    rw [heq]
    exact (hV b c).const_mul _
  have hroot : Integrable (fun y => root (vector a y ⬝ᵥ reflectedVector f (vector a y)))
      (Measure.pi μ) := by
    simp_rw [vector_inner a hb]
    have hm : Measurable (fun y => root (posteriorMean a f y)) := by
      unfold root
      have hmeas := measurable_posteriorMean a ha f
      fun_prop
    exact integrable_of_abs_le (Measure.pi μ) _ hm 1
      (fun y => by rw [abs_of_nonneg (root_mem _).1]; exact (root_mem _).2)
  have h := integral_pure_lifting (Measure.pi μ) (vector a) (fun y => reflectedVector f (vector a y))
    (vector_unit a hb) (reflected_unit a hb f hf) (fun b c => (hV b c).sub (hW b c)) hroot
  simp_rw [vector_inner a hb] at h
  change TraceNorm.traceNorm (matrixIntegral (Measure.pi μ) (fun y => V y - W y)) / 2 ≤ _ at h
  rw [matrixIntegral_sub _ V W hV hW] at h
  have hreflect : W = fun y => reflection f * V y * reflection f := by
    funext y
    exact reflected_projection f (vector a y)
  rw [hreflect, matrixIntegral_reflection] at h
  change TraceNorm.traceNorm (matrixIntegral (Measure.pi μ) V -
    reflection f * matrixIntegral (Measure.pi μ) V * reflection f) / 2 ≤ _ at h
  have hVeq := average_projection μ a ha hb hmean
  change matrixIntegral (Measure.pi μ) V = _ at hVeq
  simpa only [hVeq] using h

theorem antipodal_bound {n : ℕ} {E : Fin (n + 1) → Type*} [∀ i, MeasurableSpace (E i)]
    (μ : (i : Fin (n + 1)) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : Fin (n + 1)) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ y, a i y ∂μ i = 0)
    (f : Cube (n + 1) → ℝ) (hf : ∀ b, f b = -1 ∨ f b = 1)
    (hanti : ∀ b, f (antipode (n + 1) b) = -f b)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (hcz : ∀ i, c ≤ parameter μ a i) :
    c ≤ ∫ y, root (posteriorMean a f y) ∂Measure.pi μ := by
  exact (HeterogeneousState.antipodal_trace_lower_bound n (parameter μ a) (parameter_mem μ a ha)
    c hc hcz f hf hanti).trans (arbitrary_output_lifting μ a ha hb hmean f hf)

#print axioms average_projection
#print axioms arbitrary_output_lifting
#print axioms antipodal_bound

end Hellinger.ProductPosterior
