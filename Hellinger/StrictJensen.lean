import Hellinger.FiniteChannel

/-! Strict root Jensen equality for finite channels. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger

theorem root_strictConcave : StrictConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) root := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hxq : 0 ≤ 1 - x ^ 2 := by nlinarith [hx.1, hx.2]
  have hyq : 0 ≤ 1 - y ^ 2 := by nlinarith [hy.1, hy.2]
  have hrx : (root x) ^ 2 = 1 - x ^ 2 := Real.sq_sqrt hxq
  have hry : (root y) ^ 2 = 1 - y ^ 2 := Real.sq_sqrt hyq
  have hpos : 0 < a * b * (x - y) ^ 2 :=
    mul_pos (mul_pos ha hb) (sq_pos_of_ne_zero (sub_ne_zero.mpr hxy))
  have hnonneg : 0 ≤ a * b * (root x - root y) ^ 2 :=
    mul_nonneg (le_of_lt (mul_pos ha hb)) (sq_nonneg _)
  have hident : (a * root x + b * root y) ^ 2 + (a * x + b * y) ^ 2 +
      a * b * ((x - y) ^ 2 + (root x - root y) ^ 2) = 1 := by
    calc
      _ = a * (a + b) * ((root x) ^ 2 + x ^ 2) +
          b * (a + b) * ((root y) ^ 2 + y ^ 2) := by ring
      _ = 1 := by rw [hab, hrx, hry]; nlinarith
  change a * root x + b * root y < Real.sqrt (1 - (a * x + b * y) ^ 2)
  apply Real.lt_sqrt_of_sq_lt
  nlinarith

theorem root_sum_equality_iff {ι : Type*} [Fintype ι]
    (w p : ι → ℝ) (hw : ∀ i, 0 < w i) (hsum : ∑ i, w i = 1)
    (hp : ∀ i, p i ∈ Set.Icc (-1 : ℝ) 1) :
    root (∑ i, w i * p i) = (∑ i, w i * root (p i)) ↔
      ∀ i j, p i = p j := by
  simpa only [smul_eq_mul, Finset.mem_univ, forall_const] using
    root_strictConcave.map_sum_eq_iff_of_pos (t := Finset.univ) (w := w) (p := p)
      (fun i _ => hw i) hsum (fun i _ => hp i)

theorem eq_of_mean_eq_of_le {ι : Type*} [Fintype ι] [Nonempty ι]
    (f g : ι → ℝ) (hle : ∀ i, f i ≤ g i) (heq : mean f = mean g) :
    ∀ i, f i = g i := by
  have hc : (Fintype.card ι : ℝ)⁻¹ ≠ 0 := by
    exact inv_ne_zero (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)
  have hsum : ∑ i, f i = ∑ i, g i := mul_left_cancel₀ hc heq
  have h := (Finset.sum_eq_sum_iff_of_le (fun i (_ : i ∈ Finset.univ) => hle i)).mp hsum
  exact fun i => h i (Finset.mem_univ i)

namespace UniformChannel

variable {Ω : Type*} [Fintype Ω]

theorem root_apply_equality_iff (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) (y : Ω)
    (hpos : ∀ x, 0 < K.weight y x) :
    root (K.apply f y) = K.apply (fun x => root (f x)) y ↔
      ∀ x z, f x = f z := by
  exact root_sum_equality_iff (K.weight y) f hpos (K.row_sum y) hf

theorem root_mean_equality_iff [Nonempty Ω] (K : UniformChannel Ω) (f : Ω → ℝ)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1)
    (hpos : ∀ y x, 0 < K.weight y x) :
    mean (fun y => root (K.apply f y)) = mean (fun x => root (f x)) ↔
      ∀ x z, f x = f z := by
  constructor
  · intro heq
    have hle (y : Ω) : K.apply (fun x => root (f x)) y ≤ root (K.apply f y) := by
      simpa only [UniformChannel.apply, smul_eq_mul] using
        root_concave.le_map_sum (t := Finset.univ) (w := K.weight y) (p := f)
          (fun x _ => K.nonneg y x) (K.row_sum y) (fun x _ => hf x)
    have hm : mean (K.apply (fun x => root (f x))) =
        mean (fun y => root (K.apply f y)) := by rw [K.mean_apply, heq]
    have hpoint := eq_of_mean_eq_of_le _ _ hle hm
    let y : Ω := Classical.choice inferInstance
    exact (K.root_apply_equality_iff f hf y (hpos y)).mp (hpoint y).symm
  · intro hc
    let x : Ω := Classical.choice inferInstance
    have hconst : f = fun _ => f x := funext (fun y => hc y x)
    have happly (y : Ω) : K.apply f y = f x := by
      rw [hconst]
      simp only [UniformChannel.apply, ← Finset.sum_mul, K.row_sum, one_mul]
    simp only [happly]
    rw [hconst]

end UniformChannel

#print axioms root_strictConcave
#print axioms root_sum_equality_iff
#print axioms UniformChannel.root_mean_equality_iff

end Hellinger
