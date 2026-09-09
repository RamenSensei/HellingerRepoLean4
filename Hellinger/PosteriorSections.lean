import Hellinger.ProductPosterior
import Hellinger.ChannelSections

/-! Arbitrary finite coordinate sets and posterior section comparison. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open MeasureTheory

namespace Hellinger.PosteriorSections

open Hellinger.ProductPosterior Hellinger.ChannelSections

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
variable {E : ι → Type*} [∀ i, MeasurableSpace (E i)]

def probability (a : (i : ι) → E i → ℝ) (y : (i : ι) → E i) (b : ι → Bool) : ℝ :=
  ∏ i, bitProbability (a i (y i)) (b i)

def value (a : (i : ι) → E i → ℝ) (f : (ι → Bool) → ℝ) (y : (i : ι) → E i) : ℝ :=
  ∑ b, probability a y b * f b

def parameter (μ : (i : ι) → Measure (E i)) (a : (i : ι) → E i → ℝ) (i : ι) : ℝ :=
  ∫ y, root (a i y) ∂μ i

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] in
theorem probability_nonneg (a : (i : ι) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (y : (i : ι) → E i) (b : ι → Bool) :
    0 ≤ probability a y b := Finset.prod_nonneg (fun i _ => (bitProbability_mem _ (ha i _) _).1)

omit [∀ i, MeasurableSpace (E i)] in
theorem probability_sum (a : (i : ι) → E i → ℝ) (y : (i : ι) → E i) :
    ∑ b, probability a y b = 1 := by
  change (∑ b : ι → Bool, ∏ i, bitProbability (a i (y i)) (b i)) = 1
  rw [← Fintype.prod_sum (fun i b => bitProbability (a i (y i)) b)]
  simp only [bitProbability_sum, Finset.prod_const_one]

theorem measurable_value (a : (i : ι) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (f : (ι → Bool) → ℝ) : Measurable (value a f) := by
  unfold value probability bitProbability
  fun_prop

omit [∀ i, MeasurableSpace (E i)] in
theorem value_mem (a : (i : ι) → E i → ℝ)
    (ha : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (f : (ι → Bool) → ℝ)
    (hf : ∀ b, f b ∈ Set.Icc (-1 : ℝ) 1) (y : (i : ι) → E i) :
    value a f y ∈ Set.Icc (-1 : ℝ) 1 := by
  constructor
  · calc
      -1 = ∑ b, probability a y b * (-1) := by simp [probability_sum]
      _ ≤ value a f y := Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (hf b).1 (probability_nonneg a ha y b))
  · calc
      value a f y ≤ ∑ b, probability a y b * 1 := Finset.sum_le_sum (fun b _ =>
        mul_le_mul_of_nonneg_left (hf b).2 (probability_nonneg a ha y b))
      _ = 1 := by simp [probability_sum]

theorem value_reindex (e : κ ≃ ι) (a : (i : ι) → E i → ℝ)
    (f : (ι → Bool) → ℝ) (y : (i : κ) → E (e i)) :
    value (fun i => a (e i)) (f ∘ cubeEquiv e) y =
      value a f (MeasurableEquiv.piCongrLeft E e y) := by
  unfold value
  rw [← (cubeEquiv e).sum_comp
    (fun b => probability a (MeasurableEquiv.piCongrLeft E e y) b * f b)]
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  unfold probability
  rw [← e.prod_comp
    (fun i => bitProbability (a i (MeasurableEquiv.piCongrLeft E e y i)) (cubeEquiv e b i))]
  apply Finset.prod_congr rfl
  intro i _
  simp [MeasurableEquiv.piCongrLeft_apply_apply, cubeEquiv]

theorem indexed_antipodal_bound [Nonempty ι]
    (μ : (i : ι) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : ι) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ y, a i y ∂μ i = 0)
    (f : (ι → Bool) → ℝ) (hf : ∀ b, f b = -1 ∨ f b = 1)
    (hanti : ∀ b, f (fun i => !(b i)) = -f b)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (hcz : ∀ i, c ≤ parameter μ a i) :
    c ≤ ∫ y, root (value a f y) ∂Measure.pi μ := by
  let n := Fintype.card ι - 1
  have hn : Fintype.card ι = n + 1 := by
    have := Fintype.card_pos (α := ι)
    omega
  let e : Fin (n + 1) ≃ ι := (finCongr hn).symm.trans (Fintype.equivFin ι).symm
  let g : (Fin (n + 1) → Bool) → ℝ := f ∘ cubeEquiv e
  have hg : ∀ b, g b = -1 ∨ g b = 1 := fun b => hf _
  have hga : ∀ b, g (antipode (n + 1) b) = -g b := fun b => hanti _
  have h := ProductPosterior.antipodal_bound (fun i => μ (e i)) (fun i => a (e i))
    (fun i => ha (e i)) (fun i => hb (e i)) (fun i => hmean (e i)) g hg hga c hc
    (fun i => hcz (e i))
  change c ≤ ∫ y, root (value (fun i => a (e i)) (f ∘ cubeEquiv e) y)
    ∂Measure.pi (fun i => μ (e i)) at h
  simp_rw [value_reindex] at h
  rw [(measurePreserving_piCongrLeft μ e).integral_comp' (fun y => root (value a f y))] at h
  exact h

theorem finite_mixture_bound {Ω β : Type*} [MeasurableSpace Ω] [Fintype β]
    (μ : Measure Ω) [IsProbabilityMeasure μ] (u : β → Ω → ℝ)
    (hu : ∀ b, Measurable (u b)) (hb : ∀ b y, u b y ∈ Set.Icc (-1 : ℝ) 1)
    (q : β → ℝ) (hq : ∀ b, 0 ≤ q b) (hqsum : ∑ b, q b = 1)
    (c : ℝ) (hc : ∀ b, c ≤ ∫ y, root (u b y) ∂μ) :
    c ≤ ∫ y, root (∑ b, q b * u b y) ∂μ := by
  have hmeas (b : β) : Measurable (fun y => root (u b y)) := by unfold root; fun_prop
  have hint (b : β) : Integrable (fun y => root (u b y)) μ :=
    integrable_of_abs_le μ _ (hmeas b) 1
      (fun y => by rw [abs_of_nonneg (root_mem _).1]; exact (root_mem _).2)
  have hsumint : Integrable (fun y => ∑ b, q b * root (u b y)) μ :=
    integrable_finsetSum _ (fun b _ => (hint b).const_mul (q b))
  have hrootmeas : Measurable (fun y => root (∑ b, q b * u b y)) := by unfold root; fun_prop
  have hrootint := integrable_of_abs_le μ _ hrootmeas 1
    (fun y => by rw [abs_of_nonneg (root_mem _).1]; exact (root_mem _).2)
  have hj (y : Ω) : (∑ b, q b * root (u b y)) ≤ root (∑ b, q b * u b y) := by
    simpa only [smul_eq_mul] using root_concave.le_map_sum (t := Finset.univ)
      (w := q) (p := fun b => u b y) (fun b _ => hq b) hqsum (fun b _ => hb b y)
  calc
    c = ∑ b, q b * c := by rw [← Finset.sum_mul, hqsum, one_mul]
    _ ≤ ∑ b, q b * ∫ y, root (u b y) ∂μ :=
      Finset.sum_le_sum (fun b _ => mul_le_mul_of_nonneg_left (hc b) (hq b))
    _ = ∫ y, ∑ b, q b * root (u b y) ∂μ := by
      rw [integral_finsetSum _ (fun b _ => (hint b).const_mul (q b))]
      simp only [integral_const_mul]
    _ ≤ _ := integral_mono hsumint hrootint hj

omit [DecidableEq ι] [∀ i, MeasurableSpace (E i)] in
theorem probability_split_symm (p : ι → Prop) [DecidablePred p]
    (a : (i : ι) → E i → ℝ) (y : (i : ι) → E i)
    (w : {i // p i} → Bool) (z : {i // ¬p i} → Bool) :
    probability a y ((splitCube p).symm (w, z)) =
      probability (fun i : {i // p i} => a i) (fun i => y i) w *
        probability (fun i : {i // ¬p i} => a i) (fun i => y i) z := by
  unfold probability
  rw [← Fintype.prod_subtype_mul_prod_subtype p
    (fun i => bitProbability (a i (y i)) ((splitCube p).symm (w, z) i))]
  congr 1
  · apply Finset.prod_congr rfl
    intro i _
    simp [splitCube, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
  · apply Finset.prod_congr rfl
    intro i _
    simp [splitCube, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]

omit [∀ i, MeasurableSpace (E i)] in
theorem value_split (p : ι → Prop) [DecidablePred p]
    (a : (i : ι) → E i → ℝ) (f : (ι → Bool) → ℝ) (y : (i : ι) → E i) :
    value a f y = ∑ z : {i // ¬p i} → Bool,
      probability (fun i : {i // ¬p i} => a i) (fun i => y i) z *
        value (fun i : {i // p i} => a i)
          (fun w => f ((splitCube p).symm (w, z))) (fun i => y i) := by
  unfold value
  rw [← (splitCube p).symm.sum_comp (fun b => probability a y b * f b),
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro w _
  rw [probability_split_symm]
  ring

omit [Fintype ι] [DecidableEq ι] in
theorem split_flip (p : ι → Prop) [DecidablePred p]
    (w : {i // p i} → Bool) (z : {i // ¬p i} → Bool) :
    (splitCube p).symm ((fun i => !(w i)), z) =
      fun i => if p i then !((splitCube p).symm (w, z) i) else (splitCube p).symm (w, z) i := by
  funext i
  by_cases hi : p i <;> simp [splitCube, Equiv.piEquivPiSubtypeProd_symm_apply, hi]

theorem subset_bound (p : ι → Prop) [DecidablePred p] [Nonempty {i // p i}]
    (μ : (i : ι) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : ι) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ y, a i y ∂μ i = 0)
    (f : (ι → Bool) → ℝ) (hf : ∀ b, f b = -1 ∨ f b = 1)
    (hflip : ∀ b, f (fun i => if p i then !(b i) else b i) = -f b)
    (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) (hcz : ∀ i, p i → c ≤ parameter μ a i) :
    c ≤ ∫ y, root (value a f y) ∂Measure.pi μ := by
  let μin := Measure.pi (fun i : {i // p i} => μ i)
  let μout := Measure.pi (fun i : {i // ¬p i} => μ i)
  let e := MeasurableEquiv.piEquivPiSubtypeProd E p
  let R := fun y => root (value a f (e.symm y))
  have hRmeas : Measurable R := by
    dsimp [R]
    have hv := (measurable_value a ha f).comp e.symm.measurable
    unfold root
    fun_prop
  have hRint : Integrable R (μin.prod μout) :=
    integrable_of_abs_le _ R hRmeas 1
      (fun y => by rw [abs_of_nonneg (root_mem _).1]; exact (root_mem _).2)
  have htransport : (∫ y, root (value a f y) ∂Measure.pi μ) = ∫ y, R y ∂μin.prod μout := by
    have ht := (measurePreserving_piEquivPiSubtypeProd μ p).integral_comp' R
    simpa only [R, e, MeasurableEquiv.symm_apply_apply] using ht
  rw [htransport, integral_prod_symm R hRint]
  have hinner (yo : (i : {i // ¬p i}) → E i) : c ≤ ∫ yi, R (yi, yo) ∂μin := by
    let u := fun (z : {i // ¬p i} → Bool) (yi : (i : {i // p i}) → E i) =>
      value (fun i : {i // p i} => a i) (fun w => f ((splitCube p).symm (w, z))) yi
    let q := fun z : {i // ¬p i} → Bool => probability (fun i : {i // ¬p i} => a i) yo z
    have hu (z) : Measurable (u z) :=
      measurable_value (fun i : {i // p i} => a i) (fun i => ha i) _
    have hub (z) (yi) : u z yi ∈ Set.Icc (-1 : ℝ) 1 := by
      apply value_mem (fun i : {i // p i} => a i) (fun i => hb i)
      intro w
      rcases hf ((splitCube p).symm (w, z)) with hw | hw <;> simp [hw]
    have husec (z) : c ≤ ∫ yi, root (u z yi) ∂μin := by
      apply indexed_antipodal_bound (fun i : {i // p i} => μ i) (fun i : {i // p i} => a i)
        (fun i => ha i) (fun i => hb i) (fun i => hmean i)
        (fun w => f ((splitCube p).symm (w, z))) (fun w => hf _) _ c hc
        (fun i => hcz i i.property)
      intro w
      rw [split_flip]
      exact hflip _
    have hmix := finite_mixture_bound μin u hu hub q
      (probability_nonneg (fun i : {i // ¬p i} => a i) (fun i => hb i) yo)
      (probability_sum _ yo) c husec
    have hv (yi) : value a f (e.symm (yi, yo)) = ∑ z, q z * u z yi := by
      rw [value_split p a f (e.symm (yi, yo))]
      have hleft : (fun i : {i // p i} => e.symm (yi, yo) i) = yi := by
        funext i
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
      have hright : (fun i : {i // ¬p i} => e.symm (yi, yo) i) = yo := by
        funext i
        simp [e, MeasurableEquiv.piEquivPiSubtypeProd, Equiv.piEquivPiSubtypeProd_symm_apply, i.property]
      rw [hleft, hright]
    simp_rw [← hv] at hmix
    exact hmix
  have hbound := integral_mono (integrable_const c) hRint.integral_prod_right hinner
  simpa using hbound

omit [∀ i, MeasurableSpace (E i)] in
theorem value_coordinate (a : (i : ι) → E i → ℝ) (i : ι) (y : (i : ι) → E i) :
    value a (fun b => boolSign (b i)) y = a i (y i) := by
  calc
    _ = ∑ b : ι → Bool, ∏ j, bitProbability (a j (y j)) (b j) *
        (if j = i then boolSign (b j) else 1) := by
      unfold value probability
      apply Finset.sum_congr rfl
      intro b _
      rw [Finset.prod_mul_distrib]
      simp
    _ = ∏ j, ∑ b : Bool, bitProbability (a j (y j)) b *
        (if j = i then boolSign b else 1) :=
      (Fintype.prod_sum (fun (j : ι) (b : Bool) => bitProbability (a j (y j)) b *
        (if j = i then boolSign b else 1))).symm
    _ = a i (y i) := by
      have hfactor (j : ι) :
          (∑ b : Bool, bitProbability (a j (y j)) b * (if j = i then boolSign b else 1)) =
            if j = i then a j (y j) else 1 := by
        by_cases hji : j = i
        · simp [hji, bitProbability, boolSign]
          ring
        · simp only [hji, if_false, mul_one, bitProbability_sum]
      simp_rw [hfactor]
      simp

theorem coordinate_attains (μ : (i : ι) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : ι) → E i → ℝ) (ha : ∀ i, Measurable (a i)) (i : ι) :
    (∫ y, root (value a (fun b => boolSign (b i)) y) ∂Measure.pi μ) = parameter μ a i := by
  simp_rw [value_coordinate]
  have hm : Measurable (fun y => root (a i y)) := by unfold root; fun_prop
  exact integral_comp_eval hm.aestronglyMeasurable

omit [Fintype ι] [DecidableEq ι] in
theorem parameter_mem (μ : (i : ι) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : ι) → E i → ℝ) (ha : ∀ i, Measurable (a i)) (i : ι) :
    parameter μ a i ∈ Set.Icc (0 : ℝ) 1 := by
  have hm : Measurable (fun y => root (a i y)) := by unfold root; fun_prop
  have hi := integrable_of_abs_le (μ i) _ hm 1
    (fun y => by rw [abs_of_nonneg (root_mem _).1]; exact (root_mem _).2)
  refine ⟨integral_nonneg (fun y => (root_mem _).1), ?_⟩
  exact (integral_mono hi (integrable_const (1 : ℝ)) (fun y => (root_mem _).2)).trans_eq
    (by simp)

/-- The best common lower bound is attained by an actual selected coordinate. -/
theorem subset_sharp (p : ι → Prop) [DecidablePred p] [Nonempty {i // p i}]
    (μ : (i : ι) → Measure (E i)) [∀ i, IsProbabilityMeasure (μ i)]
    (a : (i : ι) → E i → ℝ) (ha : ∀ i, Measurable (a i))
    (hb : ∀ i y, a i y ∈ Set.Icc (-1 : ℝ) 1) (hmean : ∀ i, ∫ y, a i y ∂μ i = 0) :
    ∃ i : {i // p i}, (∀ j : {j // p j}, parameter μ a i ≤ parameter μ a j) ∧
      (∀ f : (ι → Bool) → ℝ, (∀ b, f b = -1 ∨ f b = 1) →
        (∀ b, f (fun j => if p j then !(b j) else b j) = -f b) →
        parameter μ a i ≤ ∫ y, root (value a f y) ∂Measure.pi μ) ∧
      (∀ b : ι → Bool, boolSign ((fun j => if p j then !(b j) else b j) i) = -boolSign (b i)) ∧
      (∫ y, root (value a (fun b => boolSign (b i)) y) ∂Measure.pi μ) = parameter μ a i := by
  obtain ⟨i, _, hmin⟩ := Finset.exists_min_image (Finset.univ : Finset {i // p i})
    (fun i => parameter μ a i) Finset.univ_nonempty
  refine ⟨i, fun j => hmin j (Finset.mem_univ j), ?_, ?_, coordinate_attains μ a ha i⟩
  · intro f hf hflip
    exact subset_bound p μ a ha hb hmean f hf hflip (parameter μ a i)
      (parameter_mem μ a ha i)
      (fun j hj => hmin ⟨j, hj⟩ (Finset.mem_univ _))
  · intro b
    simp only [i.property, if_true]
    cases b i <;> norm_num [boolSign]

#print axioms subset_sharp
#print axioms indexed_antipodal_bound
#print axioms subset_bound
#print axioms coordinate_attains

end Hellinger.PosteriorSections
