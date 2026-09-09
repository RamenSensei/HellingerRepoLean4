import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.InnerProductSpace.SingularValues

/-! The unnormalized Schatten 1 norm of real matrices.  The definition below
is exactly the trace of the positive square root of `Aᵀ * A`.  No matrix
operator, entrywise, or Frobenius norm is used in its place. -/

set_option autoImplicit false
open scoped BigOperators MatrixOrder
open Matrix Unitary

namespace Hellinger.TraceNorm

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The trace is not normalized by the dimension. -/
noncomputable def traceNorm (A : Matrix ι ι ℝ) : ℝ := (CFC.abs A).trace

theorem traceNorm_eq_trace_sqrt (A : Matrix ι ι ℝ) :
    traceNorm A = (CFC.sqrt (A.transpose * A)).trace := by
  simp only [traceNorm, CFC.abs, Matrix.star_eq_conjTranspose, conjTranspose_eq_transpose_of_trivial]

theorem traceNorm_nonneg (A : Matrix ι ι ℝ) : 0 ≤ traceNorm A :=
  (CFC.abs_nonneg A).posSemidef.trace_nonneg

@[simp] theorem traceNorm_zero : traceNorm (0 : Matrix ι ι ℝ) = 0 := by
  simp [traceNorm]

@[simp] theorem traceNorm_neg (A : Matrix ι ι ℝ) : traceNorm (-A) = traceNorm A := by
  simp [traceNorm]

theorem traceNorm_smul (r : ℝ) (A : Matrix ι ι ℝ) :
    traceNorm (r • A) = |r| * traceNorm A := by
  simp [traceNorm, CFC.abs_smul, Real.norm_eq_abs]

theorem traceNorm_of_posSemidef (A : Matrix ι ι ℝ) (hA : A.PosSemidef) :
    traceNorm A = A.trace := by
  rw [traceNorm, CFC.abs_of_nonneg A hA.nonneg]

theorem trace_conjugate (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    (conjStarAlgAut ℝ _ U A).trace = A.trace := by
  simp only [conjStarAlgAut_apply, trace_mul_cycle, coe_star_mul_self, one_mul]

theorem trace_cfc {A : Matrix ι ι ℝ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    (cfc f A).trace = ∑ i, f (hA.eigenvalues i) := by
  rw [hA.cfc_eq, Matrix.IsHermitian.cfc, trace_conjugate, trace_diagonal]
  rfl

theorem traceNorm_eq_sum_abs_eigenvalues {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    traceNorm A = ∑ i, |hA.eigenvalues i| := by
  rw [traceNorm, CFC.abs_eq_cfc_norm A hA, trace_cfc hA]
  simp [Real.norm_eq_abs]

theorem posSemidef_conjugate (U : Matrix.unitaryGroup ι ℝ)
    {A : Matrix ι ι ℝ} (hA : A.PosSemidef) :
    (conjStarAlgAut ℝ _ U A).PosSemidef := by
  simpa only [conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
    hA.mul_mul_conjTranspose_same (U : Matrix ι ι ℝ)

theorem abs_conjugate (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    CFC.abs (conjStarAlgAut ℝ _ U A) = conjStarAlgAut ℝ _ U (CFC.abs A) := by
  change CFC.sqrt (star (conjStarAlgAut ℝ _ U A) * conjStarAlgAut ℝ _ U A) = _
  apply CFC.sqrt_unique
  · rw [← map_mul, CFC.abs_mul_abs, map_mul, map_star]
  · exact (posSemidef_conjugate U (CFC.abs_nonneg A).posSemidef).nonneg

theorem traceNorm_conjugate (U : Matrix.unitaryGroup ι ℝ) (A : Matrix ι ι ℝ) :
    traceNorm (conjStarAlgAut ℝ _ U A) = traceNorm A := by
  rw [traceNorm, abs_conjugate, trace_conjugate]
  rfl

theorem traceNorm_eq_zero_iff (A : Matrix ι ι ℝ) : traceNorm A = 0 ↔ A = 0 := by
  rw [traceNorm, (CFC.abs_nonneg A).posSemidef.trace_eq_zero_iff]
  constructor
  · intro h
    apply Matrix.conjTranspose_mul_self_eq_zero.mp
    have hs := CFC.abs_mul_abs A
    simpa only [h, zero_mul, Matrix.star_eq_conjTranspose] using hs.symm
  · rintro rfl
    exact CFC.abs_zero

/-- The order interval `[-I,I]`, expressed without a norm convention. -/
def OrderContraction (Q : Matrix ι ι ℝ) : Prop :=
  (1 - Q).PosSemidef ∧ (1 + Q).PosSemidef

theorem OrderContraction.conjugate {Q : Matrix ι ι ℝ} (hQ : OrderContraction Q)
    (U : Matrix.unitaryGroup ι ℝ) : OrderContraction (conjStarAlgAut ℝ _ U Q) := by
  constructor
  · simpa only [map_sub, map_one] using posSemidef_conjugate U hQ.1
  · simpa only [map_add, map_one] using posSemidef_conjugate U hQ.2

omit [Fintype ι] in
theorem OrderContraction.diagonal_abs_le {Q : Matrix ι ι ℝ}
    (hQ : OrderContraction Q) (i : ι) : |Q i i| ≤ 1 := by
  have h₁ := hQ.1.diag_nonneg (i := i)
  have h₂ := hQ.2.diag_nonneg (i := i)
  simp only [Matrix.sub_apply, Matrix.add_apply, one_apply_eq] at h₁ h₂
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem trace_mul_le_traceNorm {A Q : Matrix ι ι ℝ}
    (hA : A.IsHermitian) (hQ : OrderContraction Q) :
    (Q * A).trace ≤ traceNorm A := by
  rw [← trace_conjugate (star hA.eigenvectorUnitary) (Q * A), map_mul,
    hA.conjStarAlgAut_star_eigenvectorUnitary, traceNorm_eq_sum_abs_eigenvalues hA]
  simp only [trace, diag_apply, mul_diagonal, Function.comp_apply, RCLike.ofReal_real_eq_id, id_eq]
  apply Finset.sum_le_sum
  intro i _
  calc
    _ ≤ |(conjStarAlgAut ℝ _ (star hA.eigenvectorUnitary) Q) i i * hA.eigenvalues i| :=
      le_abs_self _
    _ = |(conjStarAlgAut ℝ _ (star hA.eigenvectorUnitary) Q) i i| * |hA.eigenvalues i| :=
      abs_mul _ _
    _ ≤ 1 * |hA.eigenvalues i| :=
      mul_le_mul_of_nonneg_right ((hQ.conjugate _).diagonal_abs_le i) (abs_nonneg _)
    _ = _ := one_mul _

/-- A real sign function with value zero at zero. -/
noncomputable def scalarSign (x : ℝ) : ℝ :=
  if x < 0 then -1 else if x = 0 then 0 else 1

theorem scalarSign_bounds (x : ℝ) : -1 ≤ scalarSign x ∧ scalarSign x ≤ 1 := by
  unfold scalarSign
  split_ifs <;> norm_num

theorem scalarSign_mul (x : ℝ) : scalarSign x * x = |x| := by
  by_cases hx : x < 0
  · simp [scalarSign, hx, abs_of_neg hx]
  · by_cases hz : x = 0
    · simp [scalarSign, hz]
    · simp [scalarSign, hx, hz, abs_of_nonneg (le_of_not_gt hx)]

/-- The genuine spectral sign matrix, with zero on the zero eigenspace. -/
noncomputable def signWitness {A : Matrix ι ι ℝ} (hA : A.IsHermitian) : Matrix ι ι ℝ :=
  conjStarAlgAut ℝ _ hA.eigenvectorUnitary (diagonal (fun i => scalarSign (hA.eigenvalues i)))

theorem signWitness_orderContraction {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    OrderContraction (signWitness hA) := by
  apply OrderContraction.conjugate
  constructor
  · rw [← diagonal_one, diagonal_sub]
    exact .diagonal fun i => sub_nonneg.mpr (scalarSign_bounds _).2
  · rw [← diagonal_one, diagonal_add]
    exact .diagonal fun i => by dsimp; linarith [(scalarSign_bounds (hA.eigenvalues i)).1]

theorem signWitness_attains {A : Matrix ι ι ℝ} (hA : A.IsHermitian) :
    (signWitness hA * A).trace = traceNorm A := by
  calc
    _ = (signWitness hA * conjStarAlgAut ℝ _ hA.eigenvectorUnitary
        (diagonal (RCLike.ofReal ∘ hA.eigenvalues))).trace :=
      congrArg (fun X => (signWitness hA * X).trace) hA.spectral_theorem
    _ = _ := by
      rw [signWitness, ← map_mul, trace_conjugate, diagonal_mul_diagonal, trace_diagonal,
        traceNorm_eq_sum_abs_eigenvalues hA]
      simp [scalarSign_mul]

/-- The trace-norm triangle inequality for arbitrary real symmetric matrices. -/
theorem traceNorm_add_le {A B : Matrix ι ι ℝ} (hA : A.IsHermitian) (hB : B.IsHermitian) :
    traceNorm (A + B) ≤ traceNorm A + traceNorm B := by
  rw [← signWitness_attains (hA.add hB), mul_add, trace_add]
  exact add_le_add (trace_mul_le_traceNorm hA (signWitness_orderContraction _))
    (trace_mul_le_traceNorm hB (signWitness_orderContraction _))

theorem traceNorm_sum_le {α : Type*} (s : Finset α) (A : α → Matrix ι ι ℝ)
    (hA : ∀ i ∈ s, (A i).IsHermitian) :
    traceNorm (∑ i ∈ s, A i) ≤ ∑ i ∈ s, traceNorm (A i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi]
    have hs : (∑ j ∈ s, A j).IsHermitian :=
      isSelfAdjoint_sum s (fun j hj => hA j (Finset.mem_insert_of_mem hj))
    exact (traceNorm_add_le (A := A i) (B := ∑ j ∈ s, A j)
      (hA i (Finset.mem_insert_self _ _)) hs).trans
      (add_le_add (le_refl _) (ih (fun j hj => hA j (Finset.mem_insert_of_mem hj))))

section Blocks

variable {κ : Type*} [Fintype κ] [DecidableEq κ]

omit [DecidableEq ι] [DecidableEq κ] in
theorem posSemidef_blockDiagonal {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    (Matrix.fromBlocks A 0 0 B).PosSemidef := by
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    (hA.isHermitian.fromBlocks (by simp) hB.isHermitian)
  intro x
  have h₁ := hA.dotProduct_mulVec_nonneg (x ∘ Sum.inl)
  have h₂ := hB.dotProduct_mulVec_nonneg (x ∘ Sum.inr)
  simpa [Matrix.fromBlocks_mulVec, dotProduct, Fintype.sum_sum_type] using add_nonneg h₁ h₂

omit [DecidableEq ι] [DecidableEq κ] in
theorem trace_blockDiagonal (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    (Matrix.fromBlocks A 0 0 B).trace = A.trace + B.trace := by
  simp [Matrix.trace, Matrix.diag, Fintype.sum_sum_type]

theorem sqrt_blockDiagonal {A : Matrix ι ι ℝ} {B : Matrix κ κ ℝ}
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    CFC.sqrt (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (CFC.sqrt A) 0 0 (CFC.sqrt B) := by
  apply CFC.sqrt_unique
  · simp only [fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
    rw [CFC.sqrt_mul_sqrt_self A hA.nonneg, CFC.sqrt_mul_sqrt_self B hB.nonneg]
  · exact (posSemidef_blockDiagonal (CFC.sqrt_nonneg A).posSemidef
      (CFC.sqrt_nonneg B).posSemidef).nonneg

theorem abs_blockDiagonal (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    CFC.abs (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (CFC.abs A) 0 0 (CFC.abs B) := by
  simp only [CFC.abs, Matrix.star_eq_conjTranspose, fromBlocks_conjTranspose,
    conjTranspose_zero, fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  exact sqrt_blockDiagonal (Matrix.posSemidef_conjTranspose_mul_self A)
    (Matrix.posSemidef_conjTranspose_mul_self B)

theorem traceNorm_blockDiagonal (A : Matrix ι ι ℝ) (B : Matrix κ κ ℝ) :
    traceNorm (Matrix.fromBlocks A 0 0 B) = traceNorm A + traceNorm B := by
  rw [traceNorm, abs_blockDiagonal, trace_blockDiagonal]
  rfl

end Blocks

/-- The paired diagonal blocks occurring after an anticommuting reflection
have twice the trace norm of either difference block. -/
theorem traceNorm_paired_difference (U : Matrix.unitaryGroup ι ℝ)
    (A B : Matrix ι ι ℝ) :
    traceNorm (Matrix.fromBlocks (A - conjStarAlgAut ℝ _ U B) 0 0
      (B - conjStarAlgAut ℝ _ (star U) A)) =
      2 * traceNorm (A - conjStarAlgAut ℝ _ U B) := by
  have hsecond : B - conjStarAlgAut ℝ _ (star U) A =
      -conjStarAlgAut ℝ _ (star U) (A - conjStarAlgAut ℝ _ U B) := by
    rw [map_sub, ← conjStarAlgAut_mul_apply]
    simp
  rw [traceNorm_blockDiagonal, hsecond, traceNorm_neg, traceNorm_conjugate]
  ring


end Hellinger.TraceNorm
