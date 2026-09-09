import Hellinger.QuadraticDual
import Mathlib.Algebra.MvPolynomial.NoZeroDivisors

/-! The explicit Maiorana–McFarland family in the unbounded-degree remark.
Its Walsh transform is the actual normalized transform on a 2k-dimensional
Boolean cube, and its phase is a multilinear polynomial over F₂. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.MaioranaMcFarland

open Fourier F2Model ChannelSections

def halves (k : ℕ) : Fourier.Cube (k + k) ≃ Fourier.Cube k × Fourier.Cube k :=
  (Equiv.arrowCongr finSumFinEquiv.symm (Equiv.refl Bool)).trans
    (Equiv.sumArrowEquivProdArrow (Fin k) (Fin k) Bool)

def highSign {k : ℕ} (y : Fourier.Cube k) : ℝ := sign (∏ i, bitEquiv (y i))

def pairFunction {k : ℕ} (p : Fourier.Cube k × Fourier.Cube k) : ℝ :=
  Fourier.phase p.1 p.2 * highSign p.2

def family (k : ℕ) : Fourier.Cube (k + k) → ℝ := pairFunction ∘ halves k

theorem phase_halves {k : ℕ} (s x : Fourier.Cube (k + k)) :
    Fourier.phase s x = Fourier.phase (halves k s).1 (halves k x).1 *
      Fourier.phase (halves k s).2 (halves k x).2 := by
  unfold Fourier.phase
  rw [← finSumFinEquiv.prod_comp (fun i : Fin (k + k) => boolSign (s i && x i))]
  rw [Fintype.prod_sum_type]
  rfl

theorem pair_walsh {k : ℕ} (s t : Fourier.Cube k) :
    mean (fun p : Fourier.Cube k × Fourier.Cube k =>
      pairFunction p * Fourier.phase s p.1 * Fourier.phase t p.2) =
        ((2 : ℝ) ^ k)⁻¹ * highSign s * Fourier.phase t s := by
  rw [mean_prod_swap]
  have hinner (y : Fourier.Cube k) :
      mean (fun x => pairFunction (x, y) * Fourier.phase s x * Fourier.phase t y) =
        (if y = s then 1 else 0) * (highSign y * Fourier.phase t y) := by
    have heq (x : Fourier.Cube k) :
        pairFunction (x, y) * Fourier.phase s x * Fourier.phase t y =
          (Fourier.phase y x * Fourier.phase s x) * (highSign y * Fourier.phase t y) := by
      rw [pairFunction, Fourier.phase_symm x y]
      ring
    simp_rw [heq]
    rw [Fourier.mean_mul_const, Fourier.orthogonality]
  simp_rw [hinner]
  simp [mean, mul_assoc]

theorem walsh_family (k : ℕ) (v : Fourier.Cube (k + k)) :
    Fourier.walsh (family k) v = ((2 : ℝ) ^ k)⁻¹ *
      highSign (halves k v).1 * Fourier.phase (halves k v).2 (halves k v).1 := by
  unfold Fourier.walsh
  rw [← mean_comp_equiv (halves k).symm]
  change mean (fun p => family k ((halves k).symm p) *
    Fourier.phase v ((halves k).symm p)) = _
  have heq (p : Fourier.Cube k × Fourier.Cube k) :
      family k ((halves k).symm p) * Fourier.phase v ((halves k).symm p) =
        pairFunction p * Fourier.phase (halves k v).1 p.1 * Fourier.phase (halves k v).2 p.2 := by
    rw [phase_halves]
    simp only [family, Function.comp_apply, Equiv.apply_symm_apply]
    ring
  simp_rw [heq]
  exact pair_walsh _ _

theorem family_boolean (k : ℕ) (x : Fourier.Cube (k + k)) :
    family k x = -1 ∨ family k x = 1 := by
  have hp := Fourier.phase_sq (halves k x).1 (halves k x).2
  have hs := QuadraticRadical.sign_sq (∏ i, bitEquiv ((halves k x).2 i))
  have h : family k x ^ 2 = 1 := by
    simp only [family, Function.comp_apply, pairFunction, highSign, mul_pow, hp, hs, one_mul]
  rcases sq_eq_one_iff.mp h with hx | hx
  · exact Or.inr hx
  · exact Or.inl hx

theorem family_bent (k : ℕ) : Flatness.IsBent (family k) := by
  intro v
  rw [walsh_family, mul_pow, mul_pow, Fourier.phase_sq,
    show highSign (halves k v).1 ^ 2 = 1 from QuadraticRadical.sign_sq _]
  simp [pow_add, pow_two, mul_inv_rev]

theorem family_mean (k : ℕ) (hk : 0 < k) : mean (family k) = ((2 : ℝ) ^ k)⁻¹ := by
  rw [← Fourier.walsh_zero, walsh_family]
  have hh : halves k (fun _ => false) = ((fun _ => false), (fun _ => false)) := rfl
  rw [hh]
  simp [highSign, Fourier.phase, boolSign, sign, Nat.ne_of_gt hk]

abbrev Variables (k : ℕ) := Fin k ⊕ Fin k

def quadraticPart (k : ℕ) : MvPolynomial (Variables k) F2 :=
  ∑ i, MvPolynomial.X (Sum.inl i) * MvPolynomial.X (Sum.inr i)

def highPart (k : ℕ) : MvPolynomial (Variables k) F2 :=
  ∏ i, MvPolynomial.X (Sum.inr i)

def anf (k : ℕ) : MvPolynomial (Variables k) F2 := quadraticPart k + highPart k

theorem anf_eval (k : ℕ) (x y : Fourier.Cube k) :
    sign (MvPolynomial.eval (Sum.elim (fun i => bitEquiv (x i)) (fun i => bitEquiv (y i)))
      (anf k)) = pairFunction (x, y) := by
  simp only [anf, quadraticPart, highPart, map_add, map_sum, map_mul, map_prod,
    MvPolynomial.eval_X, Sum.elim_inl, Sum.elim_inr, sign_add]
  rw [QuadraticDual.sign_sum]
  have hprod : (∏ i, sign (bitEquiv (x i) * bitEquiv (y i))) = Fourier.phase x y := by
    apply Finset.prod_congr rfl
    intro i _
    cases x i <;> cases y i <;> norm_num [sign, boolSign]
  exact congrArg (· * highSign y) hprod

theorem quadraticPart_totalDegree (k : ℕ) : (quadraticPart k).totalDegree ≤ 2 := by
  apply MvPolynomial.totalDegree_finsetSum_le
  intro i _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

theorem prod_X_totalDegree {σ β : Type*} (s : Finset β) (j : β → σ) :
    (∏ i ∈ s, (MvPolynomial.X (j i) : MvPolynomial σ F2)).totalDegree = s.card := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.card_insert_of_notMem hi,
      MvPolynomial.totalDegree_mul_of_isDomain (MvPolynomial.X_ne_zero _)
        (Finset.prod_ne_zero_iff.mpr (fun _ _ => MvPolynomial.X_ne_zero _)),
      MvPolynomial.totalDegree_X, ih]
    omega

theorem highPart_totalDegree (k : ℕ) : (highPart k).totalDegree = k := by
  simpa [highPart] using prod_X_totalDegree (Finset.univ : Finset (Fin k)) Sum.inr

theorem anf_totalDegree (k : ℕ) (hk : 3 ≤ k) : (anf k).totalDegree = k := by
  rw [anf, MvPolynomial.totalDegree_add_eq_right_of_totalDegree_lt, highPart_totalDegree]
  rw [highPart_totalDegree]
  exact lt_of_le_of_lt (quadraticPart_totalDegree k) (by omega)

/-- Every exponent is at most one, so this is the multilinear algebraic normal form. -/
theorem anf_multilinear (k : ℕ) (v : Variables k) : (anf k).degreeOf v ≤ 1 := by
  apply (MvPolynomial.degreeOf_add_le v _ _).trans
  apply max_le
  · apply (MvPolynomial.degreeOf_sum_le v Finset.univ _).trans
    apply Finset.sup_le
    intro i _
    apply (MvPolynomial.degreeOf_mul_le v _ _).trans
    cases v with
    | inl j => simp [MvPolynomial.degreeOf_X]; split_ifs <;> omega
    | inr j => simp [MvPolynomial.degreeOf_X]; split_ifs <;> omega
  · apply (MvPolynomial.degreeOf_prod_le v Finset.univ _).trans
    cases v with
    | inl j => simp [MvPolynomial.degreeOf_X]
    | inr j => simp [MvPolynomial.degreeOf_X]

#print axioms walsh_family
#print axioms family_bent
#print axioms family_mean
#print axioms anf_eval
#print axioms anf_totalDegree
#print axioms anf_multilinear

end Hellinger.MaioranaMcFarland
