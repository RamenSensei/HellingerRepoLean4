import Hellinger.ParityBlocks
import Mathlib.Analysis.Normed.Algebra.MatrixExponential
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Artanh
import Mathlib.Analysis.SpecialFunctions.Exponential

/-! Coordinate Pauli X operators, the ordered product formula, and the
actual matrix-exponential Gibbs representation of the posterior state. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace Hellinger.SpinState
open ProductState

def spin (n : ℕ) (i : Fin n) : Matrix (Cube n) (Cube n) ℝ :=
  Equiv.Perm.permMatrix ℝ (Fourier.translationEquiv (Fourier.unit i))

theorem spin_action (n : ℕ) (i : Fin n) (v : Cube n → ℝ) (x : Cube n) :
    (spin n i *ᵥ v) x = v (Function.update x i (!(x i))) := by
  simp only [spin, Matrix.permMatrix_mulVec]
  change v (Fourier.translationEquiv (Fourier.unit i) x) = _
  rw [show Fourier.translationEquiv (Fourier.unit i) x =
    Fourier.translate (Fourier.unit i) x from rfl, Fourier.translate_unit]

theorem phase_unit (n : ℕ) (s : Cube n) (i : Fin n) :
    Fourier.phase s (Fourier.unit i) = boolSign (s i) := by
  unfold Fourier.phase
  rw [Finset.prod_eq_single i]
  · simp [Fourier.unit]
  · intro j _ hji
    simp [Fourier.unit, hji, boolSign]
  · simp

theorem spin_phase (n : ℕ) (i : Fin n) (s : Cube n) (x : Cube n) :
    (spin n i *ᵥ Fourier.phase s) x = boolSign (s i) * Fourier.phase s x := by
  simp only [spin, Matrix.permMatrix_mulVec]
  change Fourier.phase s (Fourier.translate (Fourier.unit i) x) = _
  rw [Fourier.phase_translate, phase_unit, mul_comm]

theorem spin_mul_hadamard (n : ℕ) (i : Fin n) :
    spin n i * hadamard n = hadamard n * Matrix.diagonal (fun s => boolSign (s i)) := by
  ext x s
  rw [Matrix.mul_diagonal]
  simp only [Matrix.mul_apply, ProductState.hadamard]
  calc
    (∑ z, spin n i x z * (normalization n * Fourier.phase s z)) =
        normalization n * (spin n i *ᵥ Fourier.phase s) x := by
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = _ := by rw [spin_phase]; ring

theorem transformed_spin (n : ℕ) (i : Fin n) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (spin n i) =
      Matrix.diagonal (fun s => boolSign (s i)) := by
  simp only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose]
  rw [Matrix.mul_assoc, spin_mul_hadamard, ← Matrix.mul_assoc, hadamard_squared, Matrix.one_mul]

def orderedProduct (n : ℕ) (c : ℝ) : Matrix (Cube n) (Cube n) ℝ :=
  (List.ofFn (fun i : Fin n => 1 + c • spin n i)).prod

theorem transformed_orderedProduct (n : ℕ) (c : ℝ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (orderedProduct n c) =
      Matrix.diagonal (fun s => ∏ i : Fin n, (1 + c * boolSign (s i))) := by
  have hfactor (i : Fin n) :
      Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (1 + c • spin n i) =
        Matrix.diagonal (fun s => 1 + c * boolSign (s i)) := by
    rw [map_add, map_one, map_smul, transformed_spin]
    rw [← Matrix.diagonal_one, ← Matrix.diagonal_smul, ← Matrix.diagonal_add]
    rfl
  rw [orderedProduct, map_list_prod, List.map_ofFn]
  simp only [Function.comp_def, hfactor]
  have hmap := map_list_prod (Matrix.diagonalRingHom (Cube n) ℝ)
    (List.ofFn (fun i : Fin n => (fun s : Cube n => 1 + c * boolSign (s i))))
  rw [List.map_ofFn] at hmap
  simp only [Function.comp_def, Matrix.diagonalRingHom_apply] at hmap
  rw [← hmap, List.prod_ofFn]
  congr 1
  funext s
  exact Finset.prod_apply _ _ _

theorem state_eigenvalue_product (n : ℕ) (c : ℝ) (s : Cube n) :
    eigenvalue n c s = ∏ i : Fin n, (1 + c * boolSign (s i)) / 2 := by
  have hfactor (i : Fin n) :
      (1 + c * boolSign (s i)) / 2 =
        if i ∈ Fourier.support s then (1 - c) / 2 else (1 + c) / 2 := by
    cases hi : s i <;> simp [Fourier.support, boolSign, hi, sub_eq_add_neg]
  simp_rw [hfactor]
  rw [ProductState.product_two_levels]
  rfl

theorem state_ordered_product (n : ℕ) (c : ℝ) :
    state n c = ((2 : ℝ) ^ n)⁻¹ • orderedProduct n c := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (state n c) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (((2 : ℝ) ^ n)⁻¹ • orderedProduct n c)
  rw [ParityBlocks.transformed_state, map_smul, transformed_orderedProduct,
    ← Matrix.diagonal_smul]
  congr 1
  funext s
  rw [state_eigenvalue_product, Finset.prod_div_distrib]
  simp [div_eq_mul_inv, mul_comm]

def totalSpin (n : ℕ) : Matrix (Cube n) (Cube n) ℝ := ∑ i : Fin n, spin n i

theorem transformed_totalSpin (n : ℕ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (totalSpin n) =
      Matrix.diagonal (fun s => ∑ i : Fin n, boolSign (s i)) := by
  rw [totalSpin, map_sum]
  simp only [transformed_spin]
  ext s t
  by_cases hst : s = t
  · subst t
    simp [Matrix.sum_apply]
  · simp [Matrix.sum_apply, Matrix.diagonal, hst]

theorem one_gibbs_factor (β : ℝ) (b : Bool) :
    Real.exp (β * boolSign b) / (2 * Real.cosh β) = (1 + Real.tanh β * boolSign b) / 2 := by
  have hc : Real.cosh β ≠ 0 := ne_of_gt (Real.cosh_pos β)
  cases b
  · simp only [boolSign, Bool.false_eq_true, if_false, mul_one]
    rw [← Real.cosh_add_sinh, Real.tanh_eq_sinh_div_cosh]
    field_simp
  · simp only [boolSign, if_true, mul_neg_one]
    rw [← Real.cosh_sub_sinh, Real.tanh_eq_sinh_div_cosh]
    field_simp
    ring

theorem eigenvalue_gibbs (n : ℕ) (β : ℝ) (s : Cube n) :
    eigenvalue n (Real.tanh β) s =
      ((2 * Real.cosh β) ^ n)⁻¹ * Real.exp (β * ∑ i : Fin n, boolSign (s i)) := by
  rw [state_eigenvalue_product]
  simp_rw [← one_gibbs_factor]
  rw [Finset.prod_div_distrib, ← Real.exp_sum]
  simp [← Finset.mul_sum, div_eq_mul_inv, mul_comm]

theorem hadamard_conjugate_exp (n : ℕ) (A : Matrix (Cube n) (Cube n) ℝ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (NormedSpace.exp A) =
      NormedSpace.exp (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) A) := by
  let U : (Matrix (Cube n) (Cube n) ℝ)ˣ :=
    ⟨hadamard n, hadamard n, hadamard_squared n, hadamard_squared n⟩
  have h := Matrix.exp_units_conj U A
  have hU : (U : Matrix (Cube n) (Cube n) ℝ) = hadamard n := rfl
  have hUi : ((U⁻¹ : (Matrix (Cube n) (Cube n) ℝ)ˣ) : Matrix (Cube n) (Cube n) ℝ) =
      hadamard n := rfl
  rw [hU, hUi] at h
  simpa only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose] using h.symm

def gibbsState (n : ℕ) (β : ℝ) : Matrix (Cube n) (Cube n) ℝ :=
  ((2 * Real.cosh β) ^ n)⁻¹ • NormedSpace.exp (β • totalSpin n)

theorem state_gibbs (n : ℕ) (β : ℝ) : state n (Real.tanh β) = gibbsState n β := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (state n (Real.tanh β)) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (gibbsState n β)
  rw [ParityBlocks.transformed_state, gibbsState, map_smul, hadamard_conjugate_exp,
    map_smul, transformed_totalSpin, ← Matrix.diagonal_smul, Matrix.exp_diagonal,
    ← Matrix.diagonal_smul]
  congr 1
  funext s
  simpa only [Pi.smul_apply, smul_eq_mul, Pi.coe_exp, ← Real.exp_eq_exp_ℝ] using eigenvalue_gibbs n β s

theorem exists_positive_gibbs_parameter (n : ℕ) (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ β : ℝ, 0 < β ∧ c = Real.tanh β ∧ state n c = gibbsState n β := by
  have hc' : c ∈ Set.Ioo (-1 : ℝ) 1 := ⟨by linarith [hc.1], hc.2⟩
  refine ⟨Real.artanh c, Real.artanh_pos hc, (Real.tanh_artanh hc').symm, ?_⟩
  simpa only [Real.tanh_artanh hc'] using state_gibbs n (Real.artanh c)

end Hellinger.SpinState
