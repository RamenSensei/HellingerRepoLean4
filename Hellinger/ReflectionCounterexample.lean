import Hellinger.SpinState
import Hellinger.FourierProducts
import Mathlib.Tactic.FinCases

/-! The explicit three-qubit reflection from the manuscript. Its trace
distance is computed from the concrete product state, and its failure of
Boolean multiplication structure is certified by two equal-XOR entries. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix

namespace Hellinger.ReflectionCounterexample
open ProductState TraceNorm

theorem abs_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    CFC.abs (Matrix.diagonal d) = Matrix.diagonal (fun i => |d i|) := by
  apply CFC.sqrt_unique
  · simp only [Matrix.diagonal_mul_diagonal, Matrix.star_eq_conjTranspose,
      Matrix.diagonal_conjTranspose, star_trivial]
    congr 1
    funext i
    exact abs_mul_abs_self (d i)
  · exact (Matrix.posSemidef_diagonal_iff.mpr (fun i => abs_nonneg (d i))).nonneg

theorem traceNorm_diagonal {ι : Type*} [Fintype ι] [DecidableEq ι] (d : ι → ℝ) :
    traceNorm (Matrix.diagonal d) = ∑ i, |d i| := by
  rw [traceNorm, abs_diagonal, Matrix.trace_diagonal]

theorem multiplication_xor (n : ℕ) (f : Cube n → ℝ) (s t : Cube n) :
    ParityBlocks.transformedReflection n f s t = Fourier.walsh f (Fourier.translate s t) := by
  simp only [ParityBlocks.transformedReflection, Unitary.conjStarAlgAut_apply,
    hadamardUnitary_coe, Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, hadamard_transpose]
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, ProductState.hadamard]
  calc
    (∑ x, (normalization n * Fourier.phase x s * f x) *
        (normalization n * Fourier.phase t x)) =
      normalization n ^ 2 * ∑ x, f x * Fourier.phase (Fourier.translate s t) x := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro x _
        rw [Fourier.phase_symm x s, ← FourierProducts.phase_product]
        ring
    _ = _ := by
      unfold Fourier.walsh mean
      rw [Fourier.cube_card]
      push_cast
      have hnorm := normalization_square n
      have hne : (2 : ℝ) ^ n ≠ 0 := by positivity
      have hn : normalization n ^ 2 = ((2 : ℝ) ^ n)⁻¹ := by
        rw [← one_div]
        apply (eq_div_iff hne).mpr
        exact hnorm
      rw [hn]

def threeBitsEquiv : Cube 3 ≃ Bool × Bool × Bool where
  toFun x := ⟨x 0, x 1, x 2⟩
  invFun p := ![p.1, p.2.1, p.2.2]
  left_inv x := by funext i; fin_cases i <;> rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

theorem sum_three_bits {R : Type*} [AddCommMonoid R] (F : Cube 3 → R) :
    (∑ x, F x) = ∑ a : Bool, ∑ b : Bool, ∑ c : Bool, F ![a, b, c] := by
  rw [← threeBitsEquiv.symm.sum_comp F]
  simp [Fintype.sum_prod_type, threeBitsEquiv]

def pairSwap (x : Cube 3) : Cube 3 :=
  match x 0, x 1, x 2 with
  | false, false, false => ![false, false, true]
  | false, false, true => ![false, false, false]
  | false, true, false => ![true, false, false]
  | true, false, false => ![false, true, false]
  | false, true, true => ![true, true, true]
  | true, true, true => ![false, true, true]
  | true, false, true => ![true, true, false]
  | true, true, false => ![true, false, true]

@[simp] theorem vec3_last (a b c : Bool) : (![a, b, c] : Cube 3) 2 = c := rfl

theorem pairSwap_involutive : Function.Involutive pairSwap := by
  unfold Function.Involutive
  decide

def pairing : Equiv.Perm (Cube 3) :=
  ⟨pairSwap, pairSwap, pairSwap_involutive, pairSwap_involutive⟩

@[simp] theorem pairing_apply (x : Cube 3) : pairing x = pairSwap x := rfl

theorem degree_three (a b c : Bool) :
    Fourier.degree ![a, b, c] =
      (if a then 1 else 0) + (if b then 1 else 0) + (if c then 1 else 0) := by
  cases a <;> cases b <;> cases c <;> decide

theorem pairing_nofixed (x : Cube 3) : pairing x ≠ x := by
  have h : ∀ x : Cube 3, pairSwap x ≠ x := by decide
  exact h x

def fourierReflection : Matrix (Cube 3) (Cube 3) ℝ := pairing.permMatrix ℝ

theorem pairing_inv : pairing⁻¹ = pairing := rfl

theorem fourierReflection_isHermitian : fourierReflection.IsHermitian := by
  simp [Matrix.IsHermitian, fourierReflection, pairing_inv]

theorem fourierReflection_squared : fourierReflection * fourierReflection = 1 := by
  rw [fourierReflection, ← Matrix.permMatrix_mul]
  have h : pairing * pairing = 1 := by
    apply Equiv.ext
    intro x
    exact pairSwap_involutive x
  rw [h, Matrix.permMatrix_one]

theorem fourierReflection_entry (x y : Cube 3) :
    fourierReflection x y = if pairing x = y then 1 else 0 := by
  simp [fourierReflection, Equiv.toPEquiv_apply]
  rfl

theorem fourierReflection_diagonal (x : Cube 3) : fourierReflection x x = 0 := by
  rw [fourierReflection_entry, if_neg (pairing_nofixed x)]

theorem conjugate_diagonal (d : Cube 3 → ℝ) :
    fourierReflection * Matrix.diagonal d * fourierReflection =
      Matrix.diagonal (fun x => d (pairing x)) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext x
  simp only [← Matrix.mulVec_mulVec, fourierReflection, Matrix.permMatrix_mulVec,
    Function.comp_apply, Matrix.mulVec_diagonal]
  change d (pairSwap x) * v (pairSwap (pairSwap x)) = d (pairSwap x) * v x
  rw [pairSwap_involutive]

theorem fourier_trace_distance (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    traceNorm (Matrix.diagonal (eigenvalue 3 c) -
      fourierReflection * Matrix.diagonal (eigenvalue 3 c) * fourierReflection) / 2 =
        c * (1 + c ^ 2) / 2 := by
  rw [conjugate_diagonal, Matrix.diagonal_sub, traceNorm_diagonal, sum_three_bits]
  norm_num [Fintype.sum_bool, eigenvalue, degree_three, pairSwap, Matrix.cons_val]
  have h₁ : 0 ≤ ((1 + c) / 2) ^ 3 - ((1 + c) / 2) ^ 2 * ((1 - c) / 2) := by
    nlinarith [mul_nonneg hc.1 (sq_nonneg ((1 + c) / 2))]
  have h₂ : 0 ≤ (1 + c) / 2 * ((1 - c) / 2) ^ 2 - ((1 - c) / 2) ^ 3 := by
    nlinarith [mul_nonneg hc.1 (sq_nonneg ((1 - c) / 2))]
  rw [abs_sub_comm (((1 - c) / 2) ^ 3),
    abs_sub_comm (((1 + c) / 2) ^ 2 * ((1 - c) / 2)),
    abs_of_nonneg h₁, abs_of_nonneg h₂]
  ring

def reflection : Matrix (Cube 3) (Cube 3) ℝ :=
  Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3) fourierReflection

theorem hadamard_conjugate_involution (n : ℕ) (A : Matrix (Cube n) (Cube n) ℝ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)
      (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) A) = A := by
  simp only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose]
  simp only [← Matrix.mul_assoc, hadamard_squared, Matrix.one_mul]
  rw [Matrix.mul_assoc, hadamard_squared, Matrix.mul_one]

theorem reflection_isHermitian : reflection.IsHermitian := by
  change star reflection = reflection
  rw [reflection, ← map_star]
  congr 1
  exact fourierReflection_isHermitian

theorem reflection_squared : reflection * reflection = 1 := by
  rw [reflection, ← map_mul, fourierReflection_squared, map_one]

theorem reflection_fourier_diagonal (x : Cube 3) :
    (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3) reflection) x x = 0 := by
  rw [reflection, hadamard_conjugate_involution, fourierReflection_diagonal]

theorem reflection_trace_distance (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    traceNorm (state 3 c - reflection * state 3 c * reflection) / 2 =
      c * (1 + c ^ 2) / 2 := by
  rw [← traceNorm_conjugate (hadamardUnitary 3)]
  rw [map_sub, map_mul, map_mul, ParityBlocks.transformed_state,
    reflection, hadamard_conjugate_involution]
  exact fourier_trace_distance c hc

theorem fourierReflection_not_multiplication (f : Cube 3 → ℝ) :
    fourierReflection ≠ ParityBlocks.transformedReflection 3 f := by
  intro h
  have h₁ := congrArg (fun M : Matrix (Cube 3) (Cube 3) ℝ =>
    M ![false, false, false] ![false, false, true]) h
  have h₂ := congrArg (fun M : Matrix (Cube 3) (Cube 3) ℝ =>
    M ![false, true, false] ![false, true, true]) h
  rw [fourierReflection_entry, multiplication_xor] at h₁ h₂
  have hs : Fourier.translate ![false, false, false] ![false, false, true] =
      Fourier.translate ![false, true, false] ![false, true, true] := by decide
  rw [hs] at h₁
  norm_num [pairSwap, Matrix.cons_val, show
    (![true, false, false] : Cube 3) ≠ ![false, true, true] from by decide] at h₁ h₂
  linarith

theorem reflection_not_multiplication (f : Cube 3 → ℝ) :
    reflection ≠ Matrix.diagonal f := by
  intro h
  have hh := congrArg (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3)) h
  rw [reflection, hadamard_conjugate_involution] at hh
  exact fourierReflection_not_multiplication f hh

theorem reflection_counterexample (c : ℝ) (hc : c ∈ Set.Ioo (0 : ℝ) 1) :
    ∃ P : Matrix (Cube 3) (Cube 3) ℝ,
      P.IsHermitian ∧ P * P = 1 ∧
      (∀ x, (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary 3) P) x x = 0) ∧
      traceNorm (state 3 c - P * state 3 c * P) / 2 = c * (1 + c ^ 2) / 2 ∧
      c * (1 + c ^ 2) / 2 < c ∧ (∀ f : Cube 3 → ℝ, P ≠ Matrix.diagonal f) := by
  refine ⟨reflection, reflection_isHermitian, reflection_squared,
    reflection_fourier_diagonal, reflection_trace_distance c ⟨hc.1.le, hc.2.le⟩,
    ?_, reflection_not_multiplication⟩
  have hs : c ^ 2 < 1 := by nlinarith [mul_lt_mul_of_pos_left hc.2 hc.1, hc.2]
  nlinarith [mul_pos hc.1 (sub_pos.mpr hs)]

end Hellinger.ReflectionCounterexample
