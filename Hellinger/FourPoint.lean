import Hellinger.OddDual
import Hellinger.EntropyTransfer

/-! Actual four-vertex antipodal completion and its Hellinger comparison. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.FourPoint

open Hellinger.Fourier Hellinger.ChannelSections Hellinger.OddDual

theorem root_pair_antitone (u v w : ℝ) (habs : |v| ≤ |w|)
    (hp : u + w ∈ Set.Icc (-1 : ℝ) 1) (hm : u - w ∈ Set.Icc (-1 : ℝ) 1) :
    root (u + w) + root (u - w) ≤ root (u + v) + root (u - v) := by
  let q : ℝ → ℝ := fun t => root (u + t) + root (u - t)
  have hdom (t : ℝ) (ht : t ∈ Set.Icc (-|w|) |w|) :
      (u + t ∈ Set.Icc (-1 : ℝ) 1) ∧ (u - t ∈ Set.Icc (-1 : ℝ) 1) := by
    rcases le_total 0 w with hw | hw
    · rw [abs_of_nonneg hw] at ht
      constructor <;> constructor <;> linarith [ht.1, ht.2, hp.1, hp.2, hm.1, hm.2]
    · rw [abs_of_nonpos hw] at ht
      constructor <;> constructor <;> linarith [ht.1, ht.2, hp.1, hp.2, hm.1, hm.2]
  have hq : ConcaveOn ℝ (Set.Icc (-|w|) |w|) q := by
    refine ⟨convex_Icc _ _, ?_⟩
    intro x hx y hy a b ha hb hab
    have h1 := root_concave.2 (hdom x hx).1 (hdom y hy).1 ha hb hab
    have h2 := root_concave.2 (hdom x hx).2 (hdom y hy).2 ha hb hab
    change a * q x + b * q y ≤ q (a * x + b * y)
    simp only [smul_eq_mul] at h1 h2
    calc
      a * q x + b * q y = (a * root (u + x) + b * root (u + y)) +
          (a * root (u - x) + b * root (u - y)) := by dsimp [q]; ring
      _ ≤ root (a * (u + x) + b * (u + y)) +
          root (a * (u - x) + b * (u - y)) := add_le_add h1 h2
      _ = q (a * x + b * y) := by
        dsimp [q]
        have habu := congrArg (fun z : ℝ => z * u) hab
        congr 1 <;> congr 1 <;> nlinarith [habu]
  have heven (t : ℝ) : q (-t) = q t := by
    dsimp [q]
    rw [sub_neg_eq_add, show u + -t = u - t by ring, add_comm]
  have hqw : q |w| = q w := by
    rcases le_total 0 w with hw | hw
    · rw [abs_of_nonneg hw]
    · rw [abs_of_nonpos hw, heven]
  have hz : v ∈ segment ℝ (-|w|) |w| := by
    rw [segment_eq_Icc (by linarith [abs_nonneg w])]
    exact abs_le.mp habs
  have h := hq.ge_on_segment (show -|w| ∈ Set.Icc (-|w|) |w| by
    constructor <;> linarith [abs_nonneg w])
    (show |w| ∈ Set.Icc (-|w|) |w| by constructor <;> linarith [abs_nonneg w]) hz
  rw [heven, min_self, hqw] at h
  exact h

theorem apply_add {Ω : Type*} [Fintype Ω] (K : UniformChannel Ω)
    (f g : Ω → ℝ) (y : Ω) :
    K.apply (fun x => f x + g x) y = K.apply f y + K.apply g y := by
  simp only [UniformChannel.apply, mul_add, Finset.sum_add_distrib]

theorem apply_sub {Ω : Type*} [Fintype Ω] (K : UniformChannel Ω)
    (f g : Ω → ℝ) (y : Ω) :
    K.apply (fun x => f x - g x) y = K.apply f y - K.apply g y := by
  simp only [UniformChannel.apply, mul_sub, Finset.sum_sub_distrib]

def delta {n : ℕ} (x : Cube n) (z : Cube n) : ℝ := if z = x then 1 else 0

def exceptionalEven {n : ℕ} (x y : Cube n) (z : Cube n) : ℝ :=
  delta x z + delta (antipode n x) z - delta y z - delta (antipode n y) z

def completionOdd {n : ℕ} (x y : Cube n) (z : Cube n) : ℝ :=
  delta x z - delta (antipode n x) z + delta y z - delta (antipode n y) z

theorem apply_delta {n : ℕ} (K : UniformChannel (Cube n)) (x z : Cube n) :
    K.apply (delta x) z = K.weight z x := by
  classical
  simp [UniformChannel.apply, delta]

theorem apply_exceptionalEven {n : ℕ} (K : UniformChannel (Cube n)) (x y z : Cube n) :
    K.apply (exceptionalEven x y) z =
      K.weight z x + K.weight z (antipode n x) - K.weight z y - K.weight z (antipode n y) := by
  unfold exceptionalEven
  rw [apply_sub, apply_sub, apply_add]
  simp only [apply_delta]

theorem apply_completionOdd {n : ℕ} (K : UniformChannel (Cube n)) (x y z : Cube n) :
    K.apply (completionOdd x y) z =
      K.weight z x - K.weight z (antipode n x) + K.weight z y - K.weight z (antipode n y) := by
  unfold completionOdd
  rw [apply_sub, apply_add, apply_sub]
  simp only [apply_delta]

theorem noise_exceptional_abs_le (n : ℕ) (x y z : Cube n)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    |(cubeBSC n ρ hρ).apply (exceptionalEven x y) z| ≤
      |(cubeBSC n ρ hρ).apply (completionOdd x y) z| := by
  let D := Finset.univ.filter (fun i : Fin n => x i ≠ y i)
  let C := Finset.univ.filter (fun i : Fin n => ¬x i ≠ y i)
  let P : Cube n → ℝ := fun t => ∏ i ∈ D, (bsc ρ hρ).weight (z i) (t i)
  let Q : Cube n → ℝ := fun t => ∏ i ∈ C, (bsc ρ hρ).weight (z i) (t i)
  have hd (i : Fin n) (hi : i ∈ D) : y i = !(x i) := by
    have hn : x i ≠ y i := (Finset.mem_filter.mp hi).2
    cases hx : x i <;> cases hy : y i <;> simp_all
  have hc (i : Fin n) (hi : i ∈ C) : y i = x i :=
    (not_not.mp (Finset.mem_filter.mp hi).2).symm
  have hfac (t : Cube n) : (cubeBSC n ρ hρ).weight z t = P t * Q t := by
    exact (Finset.prod_filter_mul_prod_filter_not Finset.univ
      (fun i => x i ≠ y i) (fun i => (bsc ρ hρ).weight (z i) (t i))).symm
  have hPy : P y = P (antipode n x) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hd i hi]
    rfl
  have hPay : P (antipode n y) = P x := by
    apply Finset.prod_congr rfl
    intro i hi
    change (bsc ρ hρ).weight (z i) (!(y i)) = _
    rw [hd i hi, Bool.not_not]
  have hQy : Q y = Q x := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hc i hi]
  have hQay : Q (antipode n y) = Q (antipode n x) := by
    apply Finset.prod_congr rfl
    intro i hi
    change (bsc ρ hρ).weight (z i) (!(y i)) = _
    rw [hc i hi]
    rfl
  have hP0 (t : Cube n) : 0 ≤ P t := Finset.prod_nonneg (fun i _ => (bsc ρ hρ).nonneg _ _)
  have hsub : |P x - P (antipode n x)| ≤ P x + P (antipode n x) := by
    exact (abs_sub _ _).trans_eq (by rw [abs_of_nonneg (hP0 x), abs_of_nonneg (hP0 _)])
  rw [apply_exceptionalEven, apply_completionOdd]
  simp only [hfac, hPy, hPay, hQy, hQay]
  have he : P x * Q x + P (antipode n x) * Q (antipode n x) -
      P (antipode n x) * Q x - P x * Q (antipode n x) =
      (P x - P (antipode n x)) * (Q x - Q (antipode n x)) := by ring
  have hh : P x * Q x - P (antipode n x) * Q (antipode n x) +
      P (antipode n x) * Q x - P x * Q (antipode n x) =
      (P x + P (antipode n x)) * (Q x - Q (antipode n x)) := by ring
  rw [he, hh, abs_mul, abs_mul, abs_of_nonneg (add_nonneg (hP0 _) (hP0 _))]
  exact mul_le_mul_of_nonneg_right hsub (abs_nonneg _)

theorem antipode_twice (n : ℕ) (x : Cube n) : antipode n (antipode n x) = x := by
  funext i
  simp [antipode]

theorem antipode_ne_self (n : ℕ) (x : Cube (n + 1)) : antipode (n + 1) x ≠ x := by
  intro heq
  have h := congrFun heq 0
  change (!(x 0)) = x 0 at h
  cases hx : x 0 <;> simp [hx] at h

theorem delta_antipode (n : ℕ) (x z : Cube n) : delta x (antipode n z) = delta (antipode n x) z := by
  have hiff : antipode n z = x ↔ z = antipode n x := by
    constructor <;> intro h
    · have h' := congrArg (antipode n) h
      simpa only [antipode_twice] using h'
    · rw [h, antipode_twice]
  simp only [delta, hiff]

theorem exceptionalEven_even (n : ℕ) (x y z : Cube n) :
    exceptionalEven x y (antipode n z) = exceptionalEven x y z := by
  simp only [exceptionalEven, delta_antipode, antipode_twice]
  ring

theorem completionOdd_odd (n : ℕ) (x y z : Cube n) :
    completionOdd x y (antipode n z) = -completionOdd x y z := by
  simp only [completionOdd, delta_antipode, antipode_twice]
  ring

theorem noise_even (n : ℕ) (h : Cube n → ℝ)
    (heven : ∀ x, h (antipode n x) = h x) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (y : Cube n) : (cubeBSC n ρ hρ).apply h (antipode n y) = (cubeBSC n ρ hρ).apply h y := by
  unfold UniformChannel.apply
  rw [← (antipode n).sum_comp (fun x => (cubeBSC n ρ hρ).weight (antipode n y) x * h x)]
  simp only [cube_weight_antipode, heven]

theorem paired_root_mean (n : ℕ) (u v : Cube n → ℝ)
    (hu : ∀ x, u (antipode n x) = -u x) (hv : ∀ x, v (antipode n x) = v x) :
    mean (fun x => root (u x + v x)) = mean (fun x => root (u x - v x)) := by
  have h := mean_comp_equiv (antipode n) (fun x => root (u x + v x))
  change mean (fun x => root (u (antipode n x) + v (antipode n x))) = _ at h
  simp_rw [hu, hv] at h
  have hpoint (x : Cube n) : root (-u x + v x) = root (u x - v x) := by
    rw [show -u x + v x = -(u x - v x) by ring, root_neg]
  simp_rw [hpoint] at h
  exact h.symm

def remainder {n : ℕ} (f : Cube n → ℝ) (x y : Cube n) : Cube n → ℝ :=
  fun z => f z - exceptionalEven x y z

def plusCompletion {n : ℕ} (f : Cube n → ℝ) (x y : Cube n) : Cube n → ℝ :=
  fun z => remainder f x y z + completionOdd x y z

def minusCompletion {n : ℕ} (f : Cube n → ℝ) (x y : Cube n) : Cube n → ℝ :=
  fun z => remainder f x y z - completionOdd x y z

theorem exceptional_data (n : ℕ) (f : Cube (n + 1) → ℝ) (x y : Cube (n + 1))
    (hyx : y ≠ x) (hyax : y ≠ antipode (n + 1) x)
    (hfx : f x = 1) (hfax : f (antipode (n + 1) x) = 1)
    (hfy : f y = -1) (hfay : f (antipode (n + 1) y) = -1)
    (hother : ∀ z, z ≠ x → z ≠ antipode (n + 1) x → z ≠ y → z ≠ antipode (n + 1) y →
      f (antipode (n + 1) z) = -f z) :
    (∀ z, f z + f (antipode (n + 1) z) = 2 * exceptionalEven x y z) ∧
      ∀ z, (exceptionalEven x y z = f z ∧
          (completionOdd x y z = 1 ∨ completionOdd x y z = -1)) ∨
        (exceptionalEven x y z = 0 ∧ completionOdd x y z = 0) := by
  have hxax := antipode_ne_self n x
  have hyay := antipode_ne_self n y
  have hxy := hyx.symm
  have haxy := hyax.symm
  have hxay : x ≠ antipode (n + 1) y := by
    intro h
    apply hyax
    rw [h, antipode_twice]
  have haxay : antipode (n + 1) x ≠ antipode (n + 1) y :=
    (antipode (n + 1)).injective.ne hxy
  have hex : exceptionalEven x y x = 1 := by
    simp [exceptionalEven, delta, Ne.symm hxax, hxy, hxay]
  have heax : exceptionalEven x y (antipode (n + 1) x) = 1 := by
    simp [exceptionalEven, delta, hxax, haxy, haxay]
  have hey : exceptionalEven x y y = -1 := by
    simp [exceptionalEven, delta, hyx, hyax, Ne.symm hyay]
  have heay : exceptionalEven x y (antipode (n + 1) y) = -1 := by
    simp [exceptionalEven, delta, Ne.symm hxay, Ne.symm haxay, hyay]
  have hhx : completionOdd x y x = 1 := by
    simp [completionOdd, delta, Ne.symm hxax, hxy, hxay]
  have hhax : completionOdd x y (antipode (n + 1) x) = -1 := by
    simp [completionOdd, delta, hxax, haxy, haxay]
  have hhy : completionOdd x y y = 1 := by
    simp [completionOdd, delta, hyx, hyax, Ne.symm hyay]
  have hhay : completionOdd x y (antipode (n + 1) y) = -1 := by
    simp [completionOdd, delta, Ne.symm hxay, Ne.symm haxay, hyay]
  constructor
  · intro z
    by_cases hz : z = x
    · rw [hz, hfx, hfax, hex]; norm_num
    by_cases hza : z = antipode (n + 1) x
    · rw [hza, antipode_twice, hfax, hfx, heax]; norm_num
    by_cases hzy : z = y
    · rw [hzy, hfy, hfay, hey]; norm_num
    by_cases hzya : z = antipode (n + 1) y
    · rw [hzya, antipode_twice, hfay, hfy, heay]; norm_num
    rw [hother z hz hza hzy hzya]
    simp [exceptionalEven, delta, hz, hza, hzy, hzya]
  · intro z
    by_cases hz : z = x
    · exact Or.inl ⟨by rw [hz, hex, hfx], Or.inl (by rw [hz, hhx])⟩
    by_cases hza : z = antipode (n + 1) x
    · exact Or.inl ⟨by rw [hza, heax, hfax], Or.inr (by rw [hza, hhax])⟩
    by_cases hzy : z = y
    · exact Or.inl ⟨by rw [hzy, hey, hfy], Or.inl (by rw [hzy, hhy])⟩
    by_cases hzya : z = antipode (n + 1) y
    · exact Or.inl ⟨by rw [hzya, heay, hfay], Or.inr (by rw [hzya, hhay])⟩
    exact Or.inr (by simp [exceptionalEven, completionOdd, delta, hz, hza, hzy, hzya])

theorem remainder_odd {n : ℕ} (f : Cube n → ℝ) (x y : Cube n)
    (hpair : ∀ z, f z + f (antipode n z) = 2 * exceptionalEven x y z) (z : Cube n) :
    remainder f x y (antipode n z) = -remainder f x y z := by
  unfold remainder
  rw [exceptionalEven_even]
  linarith [hpair z]

theorem completion_boolean {n : ℕ} (f : Cube n → ℝ) (x y : Cube n)
    (hf : ∀ z, f z = -1 ∨ f z = 1)
    (hdata : ∀ z, (exceptionalEven x y z = f z ∧
          (completionOdd x y z = 1 ∨ completionOdd x y z = -1)) ∨
        (exceptionalEven x y z = 0 ∧ completionOdd x y z = 0)) :
    (∀ z, plusCompletion f x y z = -1 ∨ plusCompletion f x y z = 1) ∧
      (∀ z, minusCompletion f x y z = -1 ∨ minusCompletion f x y z = 1) := by
  constructor <;> intro z
  all_goals
    rcases hdata z with ⟨he, hh | hh⟩ | ⟨he, hh⟩
    all_goals simp only [plusCompletion, minusCompletion, remainder, he, hh, sub_self,
      zero_add, zero_sub, neg_neg, sub_zero, add_zero]
    all_goals first | exact Or.inl True.intro | exact Or.inr True.intro | exact hf z

theorem plusCompletion_odd {n : ℕ} (f : Cube n → ℝ) (x y : Cube n)
    (hpair : ∀ z, f z + f (antipode n z) = 2 * exceptionalEven x y z) (z : Cube n) :
    plusCompletion f x y (antipode n z) = -plusCompletion f x y z := by
  unfold plusCompletion
  rw [remainder_odd f x y hpair, completionOdd_odd]
  ring

theorem minusCompletion_odd {n : ℕ} (f : Cube n → ℝ) (x y : Cube n)
    (hpair : ∀ z, f z + f (antipode n z) = 2 * exceptionalEven x y z) (z : Cube n) :
    minusCompletion f x y (antipode n z) = -minusCompletion f x y z := by
  unfold minusCompletion
  rw [remainder_odd f x y hpair, completionOdd_odd]
  ring

theorem average_completion_improvement (n : ℕ) (f : Cube n → ℝ) (x y : Cube n)
    (hmean : mean f = 0)
    (hpair : ∀ z, f z + f (antipode n z) = 2 * exceptionalEven x y z)
    (hp : ∀ z, plusCompletion f x y z = -1 ∨ plusCompletion f x y z = 1)
    (hm : ∀ z, minusCompletion f x y z = -1 ∨ minusCompletion f x y z = 1)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC n ρ hρ).apply f) ≤
      (objective ((cubeBSC n ρ hρ).apply (plusCompletion f x y)) +
        objective ((cubeBSC n ρ hρ).apply (minusCompletion f x y))) / 2 := by
  let K := cubeBSC n ρ hρ
  let u := K.apply (remainder f x y)
  let v := K.apply (exceptionalEven x y)
  let w := K.apply (completionOdd x y)
  have hpc (z) : plusCompletion f x y z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases hp z with hz | hz <;> simp [hz]
  have hmc (z) : minusCompletion f x y z ∈ Set.Icc (-1 : ℝ) 1 := by
    rcases hm z with hz | hz <;> simp [hz]
  have hKp (z) : K.apply (plusCompletion f x y) z = u z + w z := by
    exact apply_add K _ _ z
  have hKm (z) : K.apply (minusCompletion f x y) z = u z - w z := by
    exact apply_sub K _ _ z
  have hKf (z) : K.apply f z = u z + v z := by
    have hdecomp : f = fun t => remainder f x y t + exceptionalEven x y t := by
      funext t
      dsimp [remainder]
      ring
    conv_lhs => rw [hdecomp]
    exact apply_add K _ _ z
  have hineq := mean_mono
    (fun z => root (u z + w z) + root (u z - w z))
    (fun z => root (u z + v z) + root (u z - v z))
    (fun z => root_pair_antitone (u z) (v z) (w z) (noise_exceptional_abs_le n x y z ρ hρ)
      (by rw [← hKp]; exact K.apply_mem_Icc _ hpc z)
      (by rw [← hKm]; exact K.apply_mem_Icc _ hmc z))
  have hsym := paired_root_mean n u v
    (noise_odd n _ (remainder_odd f x y hpair) ρ hρ)
    (noise_even n _ (exceptionalEven_even n x y) ρ hρ)
  rw [Fourier.mean_add, Fourier.mean_add, ← hsym] at hineq
  simp_rw [← hKp, ← hKm, ← hKf] at hineq
  have hmp : mean (plusCompletion f x y) = 0 :=
    antipodal_mean_zero n _ (plusCompletion_odd f x y hpair)
  have hmm : mean (minusCompletion f x y) = 0 :=
    antipodal_mean_zero n _ (minusCompletion_odd f x y hpair)
  unfold objective
  rw [UniformChannel.mean_apply, UniformChannel.mean_apply, UniformChannel.mean_apply,
    hmean, hmp, hmm]
  have hr0 : root (0 : ℝ) = 1 := by norm_num [root]
  rw [hr0]
  linarith

theorem completion_agrees_outside {n : ℕ} (f : Cube n → ℝ) (x y z : Cube n)
    (hzx : z ≠ x) (hzax : z ≠ antipode n x) (hzy : z ≠ y) (hzay : z ≠ antipode n y) :
    plusCompletion f x y z = f z ∧ minusCompletion f x y z = f z := by
  simp [plusCompletion, minusCompletion, remainder, exceptionalEven, completionOdd, delta,
    hzx, hzax, hzy, hzay]

theorem four_point_completion (n : ℕ) (f : Cube n → ℝ)
    (hf : ∀ z, f z = -1 ∨ f z = 1) (hmean : mean f = 0) (x y : Cube n)
    (hyx : y ≠ x) (hyax : y ≠ antipode n x)
    (hfx : f x = 1) (hfax : f (antipode n x) = 1)
    (hfy : f y = -1) (hfay : f (antipode n y) = -1)
    (hother : ∀ z, z ≠ x → z ≠ antipode n x → z ≠ y → z ≠ antipode n y →
      f (antipode n z) = -f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    ∃ g : Cube n → ℝ,
      (g = plusCompletion f x y ∨ g = minusCompletion f x y) ∧
      (∀ z, g z = -1 ∨ g z = 1) ∧
      (∀ z, g (antipode n z) = -g z) ∧
      (∀ z, z ≠ x → z ≠ antipode n x → z ≠ y → z ≠ antipode n y → g z = f z) ∧
      objective ((cubeBSC n ρ hρ).apply f) ≤ objective ((cubeBSC n ρ hρ).apply g) := by
  cases n with
  | zero => exact False.elim (hyx (Subsingleton.elim _ _))
  | succ n =>
    obtain ⟨hpair, hdata⟩ := exceptional_data n f x y hyx hyax hfx hfax hfy hfay hother
    obtain ⟨hp, hm⟩ := completion_boolean f x y hf hdata
    have havg := average_completion_improvement (n + 1) f x y hmean hpair hp hm ρ hρ
    rcases le_total (objective ((cubeBSC (n + 1) ρ hρ).apply (plusCompletion f x y)))
      (objective ((cubeBSC (n + 1) ρ hρ).apply (minusCompletion f x y))) with hle | hle
    · refine ⟨minusCompletion f x y, Or.inr rfl, hm, minusCompletion_odd f x y hpair, ?_, ?_⟩
      · intro z hzx hzax hzy hzay
        exact (completion_agrees_outside f x y z hzx hzax hzy hzay).2
      · linarith
    · refine ⟨plusCompletion f x y, Or.inl rfl, hp, plusCompletion_odd f x y hpair, ?_, ?_⟩
      · intro z hzx hzax hzy hzay
        exact (completion_agrees_outside f x y z hzx hzax hzy hzay).1
      · linarith

theorem four_point_bounds (n : ℕ) (f : Cube n → ℝ)
    (hf : ∀ z, f z = -1 ∨ f z = 1) (hmean : mean f = 0) (x y : Cube n)
    (hyx : y ≠ x) (hyax : y ≠ antipode n x)
    (hfx : f x = 1) (hfax : f (antipode n x) = 1)
    (hfy : f y = -1) (hfay : f (antipode n y) = -1)
    (hother : ∀ z, z ≠ x → z ≠ antipode n x → z ≠ y → z ≠ antipode n y →
      f (antipode n z) = -f z)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    PaperSpecs.HellingerBound f ρ hρ ∧ PaperSpecs.CKBound f ρ hρ := by
  cases n with
  | zero => exact False.elim (hyx (Subsingleton.elim _ _))
  | succ n =>
    obtain ⟨g, _, hg, hga, _, hbetter⟩ :=
      four_point_completion (n + 1) f hf hmean x y hyx hyax hfx hfax hfy hfay hother ρ hρ
    have hroot := ParityBlocks.antipodal_hellinger n g hg hga ρ hρ
    have hmg := antipodal_mean_zero (n + 1) g hga
    have hgH : objective ((cubeBSC (n + 1) ρ hρ).apply g) ≤ 1 - root ρ := by
      unfold objective
      rw [UniformChannel.mean_apply, hmg]
      have hr0 : root (0 : ℝ) = 1 := by norm_num [root]
      rw [hr0]
      exact sub_le_sub_left hroot _
    have hfH : PaperSpecs.HellingerBound f ρ hρ := hbetter.trans hgH
    exact ⟨hfH, EntropyTransfer.hellinger_implies_ck f hf ρ hρ hfH⟩

#print axioms noise_exceptional_abs_le
#print axioms average_completion_improvement
#print axioms four_point_completion
#print axioms four_point_bounds

end Hellinger.FourPoint
