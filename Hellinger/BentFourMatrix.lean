import Hellinger.BentFour
import Hellinger.BentFourEdgeCount
import Hellinger.InterlaceMoment

/-! The four-dimensional moment parameter is the actual edge count of the inverse polar matrix. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.BentFourMatrix
open F2Model QuadraticRadical QuadraticDual BentFour

/-- The six upper-triangular entries in the fixed order 01, 02, 03, 12, 13, 23. -/
def edgeSigns (B : Matrix (Fin 4) (Fin 4) F2) : Fin 6 → ℝ :=
  ![sign (B 0 1), sign (B 0 2), sign (B 0 3), sign (B 1 2), sign (B 1 3), sign (B 2 3)]

/-- Number of nonzero entries strictly above the diagonal. -/
def upperEdgeCount (B : Matrix (Fin 4) (Fin 4) F2) : ℕ :=
  ∑ i : Fin 4, ∑ j : Fin 4, if i < j ∧ B i j ≠ 0 then 1 else 0

theorem edgeSigns_sq (B : Matrix (Fin 4) (Fin 4) F2) (i : Fin 6) :
    edgeSigns B i ^ 2 = 1 := by
  fin_cases i <;> dsimp [edgeSigns] <;> exact sign_sq _

theorem sign_mul_bit (z : F2) (b : Bool) :
    sign (z * bitEquiv b) = if b then sign z else 1 := by
  cases b <;> simp

theorem edgeAction_matrix (B : Matrix (Fin 4) (Fin 4) F2)
    (hB : B.IsSymm) (hd : ∀ i, B i i = 0) (s : Fourier.Cube 4) (i : Fin 4) :
    edgeAction (edgeSigns B) s i = sign ((B *ᵥ bitsEquiv (Fin 4) s) i) := by
  have hs (j k : Fin 4) : B j k = B k j := congrArg (fun A => A k j) hB.eq
  simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ, bitsEquiv_apply]
  simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, sign_add, sign_mul_bit]
  fin_cases i <;> dsimp [edgeAction, edgeSigns] <;>
    simp only [hd, sign_zero, ite_self, mul_one, one_mul, mul_assoc]
  · rw [hs 1 0]
  · rw [hs 2 0, hs 2 1]
  · rw [hs 3 0, hs 3 1, hs 3 2]

theorem sign_dot_character (x : Fourier.Cube 4) (v : Cube 4) :
    sign (bitsEquiv (Fin 4) x ⬝ᵥ v) = signCharacter (fun i => sign (v i)) x := by
  rw [dotProduct_comm]
  unfold dotProduct signCharacter
  rw [sign_sum]
  apply Finset.prod_congr rfl
  intro i _
  exact sign_mul_bit (v i) (x i)

theorem matrix_character_sum (B : Matrix (Fin 4) (Fin 4) F2)
    (hB : B.IsSymm) (hd : ∀ i, B i i = 0) (ρ : ℝ) (s : Fourier.Cube 4) :
    (∑ x : Cube 4, noiseWeight ρ x * noiseWeight ρ (x + bitsEquiv (Fin 4) s) *
      sign (x ⬝ᵥ B *ᵥ bitsEquiv (Fin 4) s)) = noiseDerivativeSum (edgeSigns B) ρ s := by
  rw [← (bitsEquiv (Fin 4)).sum_comp]
  have he : (fun i => sign ((B *ᵥ bitsEquiv (Fin 4) s) i)) =
      edgeAction (edgeSigns B) s := by funext i; exact (edgeAction_matrix B hB hd s i).symm
  simp only [← bitsEquiv_translate, noiseWeight_bits, sign_dot_character, he, ← pow_add]
  have ht (x : Fourier.Cube 4) : Fourier.translate x s = Fourier.translate s x := by
    funext i; exact Bool.xor_comm _ _
  simp_rw [ht]
  exact weighted_character_sum _ ρ s

theorem edgeSigns_nondegenerate (B : Matrix (Fin 4) (Fin 4) F2)
    (hB : B.IsSymm) (hd : ∀ i, B i i = 0) (hdet : IsUnit B.det) :
    EdgeNondegenerate (edgeSigns B) := by
  intro s hs
  have hb : bitsEquiv (Fin 4) s ≠ 0 := by
    intro h
    apply hs
    apply (bitsEquiv (Fin 4)).injective
    simpa using h
  have hBs : B *ᵥ bitsEquiv (Fin 4) s ≠ 0 := by
    intro h
    have hh := congrArg (fun v => B⁻¹ *ᵥ v) h
    simp only [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hdet,
      Matrix.one_mulVec, Matrix.mulVec_zero] at hh
    exact hb hh
  obtain ⟨i, hi⟩ : ∃ i, (B *ᵥ bitsEquiv (Fin 4) s) i ≠ 0 := by
    by_contra h
    apply hBs
    push Not at h
    exact funext h
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  rw [edgeAction_matrix B hB hd, eq_one_of_ne_zero _ hi]
  norm_num

theorem negativeEdges_eq_upperEdgeCount (B : Matrix (Fin 4) (Fin 4) F2) :
    BentFourEdgeCount.negativeEdges (edgeSigns B) = upperEdgeCount B := by
  have hz (z : F2) : sign z = -1 ↔ z ≠ 0 := by
    by_cases h : z = 0
    · rw [h]
      norm_num
    · rw [eq_one_of_ne_zero _ h]
      norm_num
  have hn (e : Fin 6 → ℝ) : BentFourEdgeCount.negativeEdges e =
      (if e 0 = -1 then 1 else 0) + (if e 1 = -1 then 1 else 0) +
      (if e 2 = -1 then 1 else 0) + (if e 3 = -1 then 1 else 0) +
      (if e 4 = -1 then 1 else 0) + (if e 5 = -1 then 1 else 0) := by
    simp only [BentFourEdgeCount.negativeEdges, Fin.sum_univ_succ]
    simp only [Finset.univ_eq_empty, Finset.sum_empty, add_zero, add_assoc]
    rfl
  rw [hn]
  change (if sign (B 0 1) = -1 then 1 else 0) +
      (if sign (B 0 2) = -1 then 1 else 0) +
      (if sign (B 0 3) = -1 then 1 else 0) +
      (if sign (B 1 2) = -1 then 1 else 0) +
      (if sign (B 1 3) = -1 then 1 else 0) +
      (if sign (B 2 3) = -1 then 1 else 0) = _
  simp_rw [hz]
  simp only [upperEdgeCount, Fin.sum_univ_succ]
  simp only [Fin.lt_def, Fin.val_zero, Fin.val_succ]
  norm_num
  rw [show (Fin.succ (2 : Fin 3)) = (3 : Fin 4) from rfl]
  omega

set_option maxHeartbeats 200000 in

/-- Exact dimension-four fourth moment, with the parameter equal to the number
of nonzero entries above the diagonal of the actual inverse polar matrix. -/
theorem fourth_moment_actual_edges (a : F2) (Q : Form 4)
    (hQ : IsUnit (polarMatrix Q).det) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    2 ≤ upperEdgeCount ((polarMatrix Q)⁻¹) ∧
    mean (fun x => ((cubeBSC 4 ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin 4)) x) ^ 4) =
      BentEstimates.fourthMomentExpression (upperEdgeCount ((polarMatrix Q)⁻¹)) (ρ ^ 2) := by
  let B := (polarMatrix Q)⁻¹
  have hB : B.IsSymm := (polarMatrix_symmetric Q).inv
  have hd : ∀ i, B i i = 0 := (InterlaceMoment.inverse_polar_isAdjMatrix Q hQ).apply_diag
  have hdet : IsUnit B.det := by
    dsimp [B]
    rw [Matrix.det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using hQ.inv
  obtain ⟨hc, hm⟩ := BentFourEdgeCount.derivative_moment_edge_count (edgeSigns B)
    (edgeSigns_sq B) (edgeSigns_nondegenerate B hB hd hdet) ρ
  rw [negativeEdges_eq_upperEdgeCount] at hc hm
  refine ⟨hc, ?_⟩
  rw [phase_fourth_moment a Q hQ]
  rw [← (bitsEquiv (Fin 4)).sum_comp]
  change ((2 : ℝ) ^ 4)⁻¹ ^ 2 *
    (∑ s : Fourier.Cube 4, (∑ x : Cube 4, noiseWeight ρ x *
      noiseWeight ρ (x + bitsEquiv (Fin 4) s) *
        sign (x ⬝ᵥ B *ᵥ bitsEquiv (Fin 4) s)) ^ 2) = _
  simp_rw [matrix_character_sum B hB hd]
  rw [hm]
  change ((2 : ℝ) ^ 4)⁻¹ ^ 2 *
    (256 * BentEstimates.fourthMomentExpression (upperEdgeCount B) (ρ ^ 2)) =
      BentEstimates.fourthMomentExpression (upperEdgeCount B) (ρ ^ 2)
  rw [← mul_assoc, show ((2 : ℝ) ^ 4)⁻¹ ^ 2 * 256 = 1 by norm_num, one_mul]

#print axioms edgeAction_matrix
#print axioms matrix_character_sum
#print axioms edgeSigns_nondegenerate
#print axioms fourth_moment_actual_edges
end Hellinger.BentFourMatrix
