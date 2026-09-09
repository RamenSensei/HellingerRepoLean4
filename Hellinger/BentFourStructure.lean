import Hellinger.BentFour
import Hellinger.FourierProducts

/-! Structural consequences of the four-dimensional quadratic representation. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.BentFourStructure
open Fourier BentFour

theorem coefficient_squares (f : Cube 4 → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) :
    constantTerm f ^ 2 = 1 ∧ (∀ i, linearTerms f i ^ 2 = 1) ∧
      (∀ i, mixedTerms f i ^ 2 = 1) := by
  have hs (x : Cube 4) : f x ^ 2 = 1 := by rcases hf x with h | h <;> norm_num [h]
  refine ⟨hs _, ?_, ?_⟩
  · intro i
    fin_cases i <;> dsimp [linearTerms, constantTerm] <;>
      simp only [mul_pow, hs, mul_one]
  · intro i
    fin_cases i <;> dsimp [mixedTerms, constantTerm] <;>
      simp only [mul_pow, hs, mul_one]

def dual (f : Cube 4 → ℝ) : Cube 4 → ℝ := fun s => 4 * walsh f s

theorem dual_boolean (f : Cube 4 → ℝ) (hb : Flatness.IsBent f) :
    ∀ s, dual f s = -1 ∨ dual f s = 1 := by
  intro s
  rcases flat_four_coefficient f hb s with h | h <;> norm_num [dual, h]

theorem dual_walsh (f : Cube 4 → ℝ) (x : Cube 4) : walsh (dual f) x = f x / 4 := by
  change mean (fun s => (4 * walsh f s) * phase x s) = _
  have hmul : (fun s => 4 * walsh f s * phase x s) =
      (fun s => 4 * (walsh f s * phase x s)) := by funext; ring
  rw [hmul, mean_const_mul]
  change 4 * walsh (walsh f) x = _
  rw [FourierProducts.walsh_involution]
  norm_num
  ring

theorem dual_bent (f : Cube 4 → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1) :
    Flatness.IsBent (dual f) := by
  intro x
  rw [dual_walsh]
  rcases hf x with h | h <;> norm_num [h]

theorem edgeAction_sq (e : Fin 6 → ℝ) (he : ∀ i, e i ^ 2 = 1)
    (x : Cube 4) (i : Fin 4) : edgeAction e x i ^ 2 = 1 := by
  fin_cases i <;> dsimp [edgeAction] <;>
    simp only [mul_pow, ite_pow, he, one_pow, ite_self, mul_one]

private theorem signFactor_xor (a : ℝ) (ha : a ^ 2 = 1) (b c : Bool) :
    (if Bool.xor b c then a else 1) = (if b then a else 1) * (if c then a else 1) := by
  cases b <;> cases c <;> norm_num [← pow_two, ha]

theorem edgeAction_translate (e : Fin 6 → ℝ) (he : ∀ i, e i ^ 2 = 1)
    (s x : Cube 4) (i : Fin 4) :
    edgeAction e (translate s x) i = edgeAction e x i * edgeAction e s i := by
  fin_cases i
  · change (if Bool.xor (x 1) (s 1) then e 0 else 1) * (if Bool.xor (x 2) (s 2) then e 1 else 1) * (if Bool.xor (x 3) (s 3) then e 2 else 1) = ((if x 1 then e 0 else 1) * (if x 2 then e 1 else 1) * (if x 3 then e 2 else 1)) * ((if s 1 then e 0 else 1) * (if s 2 then e 1 else 1) * (if s 3 then e 2 else 1))
    simp_rw [signFactor_xor _ (he _)]
    ring
  · change (if Bool.xor (x 0) (s 0) then e 0 else 1) * (if Bool.xor (x 2) (s 2) then e 3 else 1) * (if Bool.xor (x 3) (s 3) then e 4 else 1) = ((if x 0 then e 0 else 1) * (if x 2 then e 3 else 1) * (if x 3 then e 4 else 1)) * ((if s 0 then e 0 else 1) * (if s 2 then e 3 else 1) * (if s 3 then e 4 else 1))
    simp_rw [signFactor_xor _ (he _)]
    ring
  · change (if Bool.xor (x 0) (s 0) then e 1 else 1) * (if Bool.xor (x 1) (s 1) then e 3 else 1) * (if Bool.xor (x 3) (s 3) then e 5 else 1) = ((if x 0 then e 1 else 1) * (if x 1 then e 3 else 1) * (if x 3 then e 5 else 1)) * ((if s 0 then e 1 else 1) * (if s 1 then e 3 else 1) * (if s 3 then e 5 else 1))
    simp_rw [signFactor_xor _ (he _)]
    ring
  · change (if Bool.xor (x 0) (s 0) then e 2 else 1) * (if Bool.xor (x 1) (s 1) then e 4 else 1) * (if Bool.xor (x 2) (s 2) then e 5 else 1) = ((if x 0 then e 2 else 1) * (if x 1 then e 4 else 1) * (if x 2 then e 5 else 1)) * ((if s 0 then e 2 else 1) * (if s 1 then e 4 else 1) * (if s 2 then e 5 else 1))
    simp_rw [signFactor_xor _ (he _)]
    ring

def edgeBits (e : Fin 6 → ℝ) (x : Cube 4) : Cube 4 :=
  fun i => decide (edgeAction e x i = -1)

theorem edgeBits_sign (e : Fin 6 → ℝ) (he : ∀ i, e i ^ 2 = 1)
    (x : Cube 4) (i : Fin 4) : boolSign (edgeBits e x i) = edgeAction e x i := by
  rcases sq_eq_one_iff.mp (edgeAction_sq e he x i) with h | h <;>
    norm_num [edgeBits, boolSign, h]

theorem edgeBits_injective (e : Fin 6 → ℝ) (he : ∀ i, e i ^ 2 = 1)
    (hnd : EdgeNondegenerate e) : Function.Injective (edgeBits e) := by
  intro x y hxy
  have heq (i : Fin 4) : edgeAction e x i = edgeAction e y i := by
    have h := congrArg (fun z : Cube 4 => boolSign (z i)) hxy
    simpa only [edgeBits_sign e he] using h
  have hall (i : Fin 4) : edgeAction e (translate y x) i = 1 := by
    rw [edgeAction_translate e he, heq, ← pow_two, edgeAction_sq e he]
  have hzero : translate y x = (fun _ => false) := by
    by_contra hz
    have h := hnd (translate y x) hz
    simp only [hall] at h
    norm_num at h
  funext i
  have h := congrFun hzero i
  cases hx : x i <;> cases hy : y i <;> simp [translate, hx, hy] at h ⊢

def edgeEquiv (e : Fin 6 → ℝ) (he : ∀ i, e i ^ 2 = 1)
    (hnd : EdgeNondegenerate e) : Cube 4 ≃ Cube 4 :=
  Equiv.ofBijective (edgeBits e) ⟨edgeBits_injective e he hnd, Finite.surjective_of_injective (edgeBits_injective e he hnd)⟩

theorem edge_mean_invariant (e : Fin 6 → ℝ) (he : ∀ i, e i ^ 2 = 1)
    (hnd : EdgeNondegenerate e) (F : Cube 4 → ℝ) :
    mean (fun x => F (edgeBits e x)) = mean F := by
  unfold mean
  rw [show (∑ x, F (edgeBits e x)) = ∑ x, F x from (edgeEquiv e he hnd).sum_comp F]

theorem edgeAction_unit_character (e : Fin 6 → ℝ) (x : Cube 4) (i : Fin 4) :
    signCharacter (edgeAction e (unit i)) x = edgeAction e x i := by
  simp only [signCharacter, Fin.prod_univ_succ]
  fin_cases i <;> dsimp [edgeAction, unit] <;> simp only [ite_self, one_mul, mul_one] <;> ring

theorem quadratic_unit (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ) (i : Fin 4) :
    quadraticPhase c l e (unit i) = c * l i := by
  fin_cases i <;> dsimp [quadraticPhase, unit] <;> ring

theorem quadratic_coordinate_derivative (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1)
    (x : Cube 4) (i : Fin 4) :
    quadraticPhase c l e x * quadraticPhase c l e (translate (unit i) x) =
      l i * edgeAction e x i := by
  rw [quadratic_polar c l e hc hl he, edgeAction_unit_character, quadratic_unit]
  calc
    c * (c * l i) * edgeAction e x i = c ^ 2 * (l i * edgeAction e x i) := by ring
    _ = _ := by rw [hc, one_mul]

def linearBits (l : Fin 4 → ℝ) : Cube 4 := fun i => decide (l i = -1)

theorem linearBits_sign (l : Fin 4 → ℝ) (hl : ∀ i, l i ^ 2 = 1) (i : Fin 4) :
    boolSign (linearBits l i) = l i := by
  rcases sq_eq_one_iff.mp (hl i) with h | h <;> norm_num [linearBits, boolSign, h]

private theorem sign_disagreement (a b : Bool) :
    (1 - boolSign a * boolSign b) / 2 = if Bool.xor b a then (1 : ℝ) else 0 := by
  cases a <;> cases b <;> norm_num [boolSign]

theorem degree_eq_sum (x : Cube 4) : (degree x : ℝ) = ∑ i, if x i then (1 : ℝ) else 0 := by
  simp [degree, support, Finset.sum_boole]

theorem quadratic_sensitivity (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1)
    (x : Cube 4) :
    Flatness.sensitivity (quadraticPhase c l e) x =
      (degree (translate (linearBits l) (edgeBits e x)) : ℝ) := by
  unfold Flatness.sensitivity Flatness.sensitivityIndicator
  simp_rw [quadratic_coordinate_derivative c l e hc hl he]
  rw [degree_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [← linearBits_sign l hl i, ← edgeBits_sign e he x i, sign_disagreement]
  rfl

theorem quadratic_sensitivity_distribution (c : ℝ) (l : Fin 4 → ℝ) (e : Fin 6 → ℝ)
    (hc : c ^ 2 = 1) (hl : ∀ i, l i ^ 2 = 1) (he : ∀ i, e i ^ 2 = 1)
    (hnd : EdgeNondegenerate e) (Φ : ℝ → ℝ) :
    mean (fun x => Φ (Flatness.sensitivity (quadraticPhase c l e) x)) =
      mean (fun x : Cube 4 => Φ (degree x)) := by
  simp_rw [quadratic_sensitivity c l e hc hl he]
  rw [edge_mean_invariant e he hnd (fun x => Φ (degree (translate (linearBits l) x)))]
  exact mean_translate (fun x : Cube 4 => Φ (degree x)) (linearBits l)

theorem sqrt_degree_mean :
    mean (fun x : Cube 4 => Real.sqrt (degree x)) =
      (3 + 3 * Real.sqrt 2 + 2 * Real.sqrt 3) / 8 := by
  simp_rw [degree_eq_sum]
  simp only [mean, cube_card, sum_four_bits, Fintype.sum_bool, Fin.sum_univ_succ]
  dsimp
  norm_num
  have h4 : Real.sqrt (4 : ℝ) = 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  ring

/-- Exact binomial sensitivity distribution, derived from actual four-dimensional flatness. -/
theorem bent_four_sensitivity_mean (f : Cube 4 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f) :
    mean (fun x => Real.sqrt (Flatness.sensitivity f x)) =
      (3 + 3 * Real.sqrt 2 + 2 * Real.sqrt 3) / 8 := by
  obtain ⟨hc, hl, he⟩ := coefficient_squares f hf
  have hrep := bent_quadratic_representation f hf hb
  have hnd := quadratic_bent_nondegenerate (constantTerm f) (linearTerms f) (mixedTerms f)
    hc hl he (by rw [← hrep]; exact hb)
  conv_lhs => rw [hrep]
  rw [quadratic_sensitivity_distribution (constantTerm f) (linearTerms f) (mixedTerms f)
    hc hl he hnd Real.sqrt, sqrt_degree_mean]

#print axioms bent_four_sensitivity_mean
end Hellinger.BentFourStructure
