import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.ByContra
import Mathlib.Tactic.SplitIfs

set_option autoImplicit false

/-!
# Finite algebra and Boolean linear rigidity for the Hellinger equality argument

This file does not formalize trace norms, posterior square-root states, or the
derivation of the normalized Gram equality. It starts at an explicitly stated
normalized or squared Gram identity. The Boolean linear theorem starts from the
full assertion that the linear form is Boolean on every sign vector.
-/

namespace Hellinger.Rigidity

open scoped BigOperators

/-- The exact factorization used after clearing and squaring the Gram equality. -/
theorem gram_factorization (p q : ℝ) :
    (1 + (p + q) / 2) ^ 2 * (1 - p) * (1 - q) -
      (1 - (p + q) / 2) ^ 2 * (1 + p) * (1 + q) =
      -(1 / 2 : ℝ) * (p + q) * (p - q) ^ 2 := by
  ring

/-- The squared Gram identity forces equality up to sign.
No positivity or full-support hypotheses are needed at this algebraic stage. -/
theorem eq_or_eq_neg_of_squared_gram (p q : ℝ)
    (h : (1 + (p + q) / 2) ^ 2 * (1 - p) * (1 - q) =
      (1 - (p + q) / 2) ^ 2 * (1 + p) * (1 + q)) :
    p = q ∨ p = -q := by
  have hprod : (p + q) * (p - q) ^ 2 = 0 := by
    nlinarith [gram_factorization p q]
  rcases mul_eq_zero.mp hprod with hsum | hsq
  · right
    linarith
  · left
    exact sub_eq_zero.mp (eq_zero_of_pow_eq_zero hsq)

/-- The local conclusion of the paper's Gram calculation. -/
theorem abs_eq_of_squared_gram (p q : ℝ)
    (h : (1 + (p + q) / 2) ^ 2 * (1 - p) * (1 - q) =
      (1 - (p + q) / 2) ^ 2 * (1 + p) * (1 + q)) :
    |p| = |q| := by
  rcases eq_or_eq_neg_of_squared_gram p q h with heq | hneg
  · rw [heq]
  · rw [hneg, abs_neg]

/-- Clearing denominators and squaring the normalized Gram equality from the
paper. The open-interval assumptions supply the required positive denominators. -/
theorem squared_gram_of_normalized_gram (p q : ℝ)
    (hp_lower : -1 < p) (hp_upper : p < 1)
    (hq_lower : -1 < q) (hq_upper : q < 1)
    (hgram :
      (1 + (p + q) / 2) / Real.sqrt ((1 + p) * (1 + q)) =
        (1 - (p + q) / 2) / Real.sqrt ((1 - p) * (1 - q))) :
    (1 + (p + q) / 2) ^ 2 * (1 - p) * (1 - q) =
      (1 - (p + q) / 2) ^ 2 * (1 + p) * (1 + q) := by
  have hplus : 0 < (1 + p) * (1 + q) :=
    mul_pos (by linarith) (by linarith)
  have hminus : 0 < (1 - p) * (1 - q) :=
    mul_pos (by linarith) (by linarith)
  have hcross := (div_eq_div_iff
    (ne_of_gt (Real.sqrt_pos.2 hplus))
    (ne_of_gt (Real.sqrt_pos.2 hminus))).mp hgram
  have hsquare := congrArg (fun r : ℝ => r ^ 2) hcross
  simpa only [mul_pow, Real.sq_sqrt hplus.le, Real.sq_sqrt hminus.le,
    mul_assoc] using hsquare

/-- The complete local scalar implication from the normalized Gram equation. -/
theorem abs_eq_of_normalized_gram (p q : ℝ)
    (hp_lower : -1 < p) (hp_upper : p < 1)
    (hq_lower : -1 < q) (hq_upper : q < 1)
    (hgram :
      (1 + (p + q) / 2) / Real.sqrt ((1 + p) * (1 + q)) =
        (1 - (p + q) / 2) / Real.sqrt ((1 - p) * (1 - q))) :
    |p| = |q| :=
  abs_eq_of_squared_gram p q
    (squared_gram_of_normalized_gram p q hp_lower hp_upper hq_lower hq_upper hgram)

section FiniteCoordinates

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A function on a finite product which is invariant under replacing one
coordinate is constant. This is the finite-cube connectivity step, proved by
induction on the coordinates that may differ. -/
theorem constant_of_update_invariant {β γ : Type*} (g : (ι → β) → γ)
    (hupdate : ∀ x i b, g (Function.update x i b) = g x) :
    ∀ x y, g x = g y := by
  have hfinite : ∀ s : Finset ι, ∀ x y : ι → β,
      (∀ i, i ∉ s → x i = y i) → g x = g y := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        intro x y h
        have hxy : x = y := by
          funext i
          exact h i (by simp)
        rw [hxy]
    | @insert i s hi ih =>
        intro x y h
        let z := Function.update x i (y i)
        have hzy : ∀ j, j ∉ s → z j = y j := by
          intro j hj
          by_cases hji : j = i
          · subst j
            simp [z]
          · simpa [z, Function.update_of_ne hji] using
              h j (by simp [hj, hji])
        calc
          g x = g z := (hupdate x i (y i)).symm
          _ = g y := ih z y hzy
  intro x y
  exact hfinite Finset.univ x y (by simp)

/-- All values have the same absolute value if each one-coordinate replacement
satisfies the squared Gram identity. The upstream analytic Gram identity is an
explicit hypothesis, not an axiom or a formalized trace-norm equality claim. -/
theorem abs_constant_of_update_squared_gram (g : (ι → Bool) → ℝ)
    (hgram : ∀ x i b,
      (1 + (g (Function.update x i b) + g x) / 2) ^ 2 *
          (1 - g (Function.update x i b)) * (1 - g x) =
        (1 - (g (Function.update x i b) + g x) / 2) ^ 2 *
          (1 + g (Function.update x i b)) * (1 + g x)) :
    ∀ x y, |g x| = |g y| := by
  apply constant_of_update_invariant (fun x => |g x|)
  intro x i b
  exact abs_eq_of_squared_gram _ _ (hgram x i b)

/-- A version whose hypothesis is required only on actual cube edges: replacing
one bit by its negation. The proof supplies unchanged-coordinate updates itself. -/
theorem abs_constant_of_flip_squared_gram (g : (ι → Bool) → ℝ)
    (hgram : ∀ x i,
      (1 + (g (Function.update x i (!(x i))) + g x) / 2) ^ 2 *
          (1 - g (Function.update x i (!(x i)))) * (1 - g x) =
        (1 - (g (Function.update x i (!(x i))) + g x) / 2) ^ 2 *
          (1 + g (Function.update x i (!(x i)))) * (1 + g x)) :
    ∀ x y, |g x| = |g y| := by
  apply constant_of_update_invariant (fun x => |g x|)
  intro x i b
  by_cases hb : b = x i
  · subst b
    rw [Function.update_eq_self]
  · have hflip : b = !(x i) := by
      cases hxi : x i <;> cases b <;> simp_all
    rw [hflip]
    exact abs_eq_of_squared_gram _ _ (hgram x i)

/-- The finite scalar and connectivity portion of Lemma 7, starting with the
normalized Gram equality on edges and the open-interval bounds. No trace-norm
statement or posterior model is hidden in this theorem. -/
theorem abs_constant_of_normalized_edge_gram (g : (ι → Bool) → ℝ)
    (hbound : ∀ x, -1 < g x ∧ g x < 1)
    (hgram : ∀ x i,
      (1 + (g (Function.update x i (!(x i))) + g x) / 2) /
          Real.sqrt ((1 + g (Function.update x i (!(x i)))) * (1 + g x)) =
        (1 - (g (Function.update x i (!(x i))) + g x) / 2) /
          Real.sqrt ((1 - g (Function.update x i (!(x i)))) * (1 - g x))) :
    ∀ x y, |g x| = |g y| := by
  apply abs_constant_of_flip_squared_gram g
  intro x i
  exact squared_gram_of_normalized_gram _ _
    (hbound _).1 (hbound _).2 (hbound x).1 (hbound x).2 (hgram x i)

/-- A real vector representing a vertex of the sign cube. -/
def IsSignVector (x : ι → ℝ) : Prop := ∀ i, (x i) ^ 2 = 1

omit [DecidableEq ι] in
/-- The coefficient sum for the all-positive input. -/
lemma all_positive_square (a : ι → ℝ)
    (hbool : ∀ x : ι → ℝ, IsSignVector x → (∑ i, a i * x i) ^ 2 = 1) :
    (∑ i, a i) ^ 2 = 1 := by
  simpa using hbool (fun _ => 1) (by intro i; norm_num)

/-- Evaluation of a linear form at a sign vector with one negative coordinate. -/
lemma sum_single_flip (a : ι → ℝ) (i : ι) :
    (∑ k, a k * (if k = i then (-1 : ℝ) else 1)) =
      (∑ k, a k) - 2 * a i := by
  have hterm : ∀ k, a k * (if k = i then (-1 : ℝ) else 1) =
      a k - (if k = i then 2 * a k else 0) := by
    intro k
    split_ifs <;> ring
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib]

/-- Evaluation at a sign vector with two distinct negative coordinates. -/
lemma sum_double_flip (a : ι → ℝ) (i j : ι) (hij : i ≠ j) :
    (∑ k, a k * (if k = i ∨ k = j then (-1 : ℝ) else 1)) =
      (∑ k, a k) - 2 * a i - 2 * a j := by
  have hterm : ∀ k, a k * (if k = i ∨ k = j then (-1 : ℝ) else 1) =
      a k - (if k = i then 2 * a k else 0) -
        (if k = j then 2 * a k else 0) := by
    intro k
    by_cases hki : k = i
    · subst k
      simp [hij]
      ring
    · by_cases hkj : k = j
      · subst k
        simp [hki]
        ring
      · simp [hki, hkj]
  simp_rw [hterm]
  simp [Finset.sum_sub_distrib]

/-- Pairwise coefficient products vanish as a consequence of the full Boolean
linear-form hypothesis. They are not assumed. -/
theorem coefficient_mul_eq_zero_of_boolean_linear (a : ι → ℝ)
    (hbool : ∀ x : ι → ℝ, IsSignVector x → (∑ i, a i * x i) ^ 2 = 1)
    (i j : ι) (hij : i ≠ j) :
    a i * a j = 0 := by
  have hbase := all_positive_square a hbool
  have hi : ((∑ k, a k) - 2 * a i) ^ 2 = 1 := by
    have h := hbool (fun k => if k = i then -1 else 1)
      (by intro k; dsimp; split_ifs <;> norm_num)
    rwa [sum_single_flip] at h
  have hj : ((∑ k, a k) - 2 * a j) ^ 2 = 1 := by
    have h := hbool (fun k => if k = j then -1 else 1)
      (by intro k; dsimp; split_ifs <;> norm_num)
    rwa [sum_single_flip] at h
  have hboth : ((∑ k, a k) - 2 * a i - 2 * a j) ^ 2 = 1 := by
    have h := hbool (fun k => if k = i ∨ k = j then -1 else 1)
      (by intro k; dsimp; split_ifs <;> norm_num)
    rwa [sum_double_flip a i j hij] at h
  nlinarith

/-- Full finite-dimensional Boolean linear rigidity: a real linear form that
is Boolean on every sign vector has one signed-unit coefficient and all other
coefficients zero. This theorem does not assume a Fourier expansion theorem,
Parseval, or pairwise vanishing of coefficient products. -/
theorem boolean_linear_coefficients (a : ι → ℝ)
    (hbool : ∀ x : ι → ℝ, IsSignVector x → (∑ i, a i * x i) ^ 2 = 1) :
    ∃ i, (a i = 1 ∨ a i = -1) ∧ ∀ j, j ≠ i → a j = 0 := by
  have hbase := all_positive_square a hbool
  have hexists : ∃ i, a i ≠ 0 := by
    by_contra! hzero
    have hsum : ∑ i, a i = 0 := Finset.sum_eq_zero (by intro i hi; exact hzero i)
    rw [hsum] at hbase
    norm_num at hbase
  obtain ⟨i, hi⟩ := hexists
  have hothers : ∀ j, j ≠ i → a j = 0 := by
    intro j hji
    exact (mul_eq_zero.mp
      (coefficient_mul_eq_zero_of_boolean_linear a hbool i j hji.symm)).resolve_left hi
  have hsum : ∑ j, a j = a i := by
    apply Finset.sum_eq_single i
    · intro j hj hji
      exact hothers j hji
    · simp
  have hai : (a i) ^ 2 = 1 := by simpa [hsum] using hbase
  have hsign : a i = 1 ∨ a i = -1 := by
    have hprod : (a i - 1) * (a i + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hprod with h | h
    · left
      linarith
    · right
      linarith
  exact ⟨i, hsign, hothers⟩

/-- The preceding coefficient classification also identifies the entire linear
form with a single signed coordinate, on all real inputs. -/
theorem boolean_linear_is_signed_coordinate (a : ι → ℝ)
    (hbool : ∀ x : ι → ℝ, IsSignVector x → (∑ i, a i * x i) ^ 2 = 1) :
    ∃ i, (a i = 1 ∨ a i = -1) ∧
      (∀ j, j ≠ i → a j = 0) ∧
      ∀ x : ι → ℝ, (∑ j, a j * x j) = a i * x i := by
  obtain ⟨i, hsign, hothers⟩ := boolean_linear_coefficients a hbool
  refine ⟨i, hsign, hothers, ?_⟩
  intro x
  apply Finset.sum_eq_single i
  · intro j hj hji
    rw [hothers j hji, zero_mul]
  · simp

/-- The unique-coordinate conclusion stated as an explicit uniqueness theorem. -/
theorem boolean_linear_unique_nonzero (a : ι → ℝ)
    (hbool : ∀ x : ι → ℝ, IsSignVector x → (∑ i, a i * x i) ^ 2 = 1) :
    ∃! i, a i ≠ 0 := by
  obtain ⟨i, hsign, hothers⟩ := boolean_linear_coefficients a hbool
  refine ⟨i, ?_, ?_⟩
  · rcases hsign with h | h <;> simp [h]
  · intro j hj
    by_contra hji
    exact hj (hothers j hji)

omit [Fintype ι] [DecidableEq ι] in
/-- A finite weighted-sum equality has no positive weight at a strictly smaller
multiplier. This isolates the finite-sum rigidity used after Parseval. -/
theorem weight_eq_zero_of_strict_multiplier {s : Finset ι}
    (a w : ι → ℝ) (c : ℝ)
    (hw : ∀ i ∈ s, 0 ≤ w i)
    (ha : ∀ i ∈ s, a i ≤ c)
    (heq : (∑ i ∈ s, a i * w i) = c * ∑ i ∈ s, w i)
    {j : ι} (hj : j ∈ s) (hstrict : a j < c) :
    w j = 0 := by
  have hsum : (∑ i ∈ s, (c - a i) * w i) = 0 := by
    simp_rw [sub_mul]
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, heq]
    ring
  have hnonneg : ∀ i ∈ s, 0 ≤ (c - a i) * w i := by
    intro i hi
    exact mul_nonneg (sub_nonneg.mpr (ha i hi)) (hw i hi)
  have hz : (c - a j) * w j = 0 :=
    (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j hj
  exact (mul_eq_zero.mp hz).resolve_left (ne_of_gt (sub_pos.mpr hstrict))

omit [Fintype ι] [DecidableEq ι] in
/-- The exact finite-sum consequence of the two Parseval identities used in the
paper: once the nonconstant spectral coefficients have squared mass one and
their noise-weighted squared mass is rho squared, every degree above one
vanishes. The Fourier expansion and Parseval identities themselves remain
explicit hypotheses of this theorem. -/
theorem coefficient_eq_zero_of_noise_parseval_equality {s : Finset ι}
    (degree : ι → ℕ) (coeff : ι → ℝ) (rho : ℝ)
    (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (hdegree : ∀ i ∈ s, 1 ≤ degree i)
    (hnorm : (∑ i ∈ s, (coeff i) ^ 2) = 1)
    (hnoise : (∑ i ∈ s, rho ^ (2 * degree i) * (coeff i) ^ 2) = rho ^ 2)
    {j : ι} (hj : j ∈ s) (hhigh : 1 < degree j) :
    coeff j = 0 := by
  have hle : ∀ i ∈ s, rho ^ (2 * degree i) ≤ rho ^ 2 := by
    intro i hi
    apply pow_le_pow_of_le_one hrho_pos.le hrho_lt_one.le
    simpa using Nat.mul_le_mul_left 2 (hdegree i hi)
  have hstrict : rho ^ (2 * degree j) < rho ^ 2 := by
    apply pow_lt_pow_right_of_lt_one₀ hrho_pos hrho_lt_one
    simpa using Nat.mul_lt_mul_of_pos_left hhigh (by norm_num : 0 < (2 : ℕ))
  have heq : (∑ i ∈ s, rho ^ (2 * degree i) * (coeff i) ^ 2) =
      rho ^ 2 * ∑ i ∈ s, (coeff i) ^ 2 := by
    rw [hnorm, mul_one]
    exact hnoise
  have hz : (coeff j) ^ 2 = 0 :=
    weight_eq_zero_of_strict_multiplier
      (fun i => rho ^ (2 * degree i)) (fun i => (coeff i) ^ 2) (rho ^ 2)
      (by intro i hi; exact sq_nonneg _) hle heq hj hstrict
  exact eq_zero_of_pow_eq_zero hz

end FiniteCoordinates

#print axioms gram_factorization
#print axioms eq_or_eq_neg_of_squared_gram
#print axioms abs_eq_of_normalized_gram
#print axioms abs_constant_of_update_squared_gram
#print axioms abs_constant_of_flip_squared_gram
#print axioms abs_constant_of_normalized_edge_gram
#print axioms coefficient_mul_eq_zero_of_boolean_linear
#print axioms boolean_linear_coefficients
#print axioms boolean_linear_is_signed_coordinate
#print axioms boolean_linear_unique_nonzero
#print axioms weight_eq_zero_of_strict_multiplier
#print axioms coefficient_eq_zero_of_noise_parseval_equality

end Hellinger.Rigidity
