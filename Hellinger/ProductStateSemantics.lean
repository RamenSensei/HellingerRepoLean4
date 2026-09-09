import Hellinger.ProductStateProperties
import Hellinger.CutNorm

/-! Direct manuscript-facing structural equivalences and trace-zero observations. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.ProductStateSemantics
open ProductState SpinState ProductStateProperties ParityBlocks ReflectionCounterexample TraceNorm

theorem antipodal_iff_anticommutes (n : ℕ) (f : Cube n → ℝ) :
    (∀ x, f (antipode n x) = -f x) ↔
      Matrix.diagonal f * antipodalMatrix n = -(antipodalMatrix n * Matrix.diagonal f) := by
  constructor
  · exact reflection_anticommutes n f
  · intro h x
    have hm := congrArg (fun A : Matrix (Cube n) (Cube n) ℝ => (A *ᵥ (fun _ => 1)) x) h
    simp only [← Matrix.mulVec_mulVec, Matrix.neg_mulVec, Pi.neg_apply,
      Matrix.mulVec_diagonal, antipodalMatrix_apply, mul_one] at hm
    linarith

theorem state_commutes_spin (n : ℕ) (c : ℝ) (i : Fin n) :
    Commute (state n c) (spin n i) := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (state n c * spin n i) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (spin n i * state n c)
  rw [map_mul, map_mul, transformed_state, transformed_spin]
  simp [Matrix.diagonal_mul_diagonal, mul_comm]

theorem state_commutes_antipode (n : ℕ) (c : ℝ) :
    Commute (state n c) (antipodalMatrix n) := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (state n c * antipodalMatrix n) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (antipodalMatrix n * state n c)
  rw [map_mul, map_mul, transformed_state, transformed_antipodalMatrix]
  simp [parityDiagonal, Matrix.diagonal_mul_diagonal, mul_comm]

theorem spin_isHermitian (n : ℕ) (i : Fin n) : (spin n i).IsHermitian := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (star (spin n i)) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (spin n i)
  rw [map_star, transformed_spin]
  exact Matrix.isHermitian_diagonal_iff.mpr (fun _ => IsSelfAdjoint.all _)

theorem spin_trace_zero (n : ℕ) (i : Fin n) : (spin n i).trace = 0 := by
  have hn (x : Cube n) : Fourier.translationEquiv (Fourier.unit i) x ≠ x := by
    intro h
    have hi := congrFun h i
    change (Fourier.translate (Fourier.unit i) x) i = x i at hi
    rw [Fourier.translate_unit, Function.update_self] at hi
    cases hx : x i <;> simp [hx] at hi
  unfold Matrix.trace Matrix.diag
  apply Finset.sum_eq_zero
  intro x _
  simp [spin, Equiv.toPEquiv_apply, hn x]

/-- The trace-zero obstruction in the discussion is a concrete coordinate spin. -/
theorem coordinate_spin_zero_distance (n : ℕ) (c : ℝ) (i : Fin n) :
    (spin n i).IsHermitian ∧ spin n i * spin n i = 1 ∧ (spin n i).trace = 0 ∧
      traceNorm (state n c - spin n i * state n c * spin n i) / 2 = 0 := by
  refine ⟨spin_isHermitian n i, spin_squared n i, spin_trace_zero n i, ?_⟩
  rw [← (state_commutes_spin n c i).eq, Matrix.mul_assoc, spin_squared,
    Matrix.mul_one, sub_self, traceNorm_zero, zero_div]

theorem multiplication_fourier_diagonal (n : ℕ) (f : Cube n → ℝ) (s : Cube n) :
    transformedReflection n f s s = mean f := by
  rw [multiplication_xor]
  have ht : Fourier.translate s s = (fun _ => false) := by
    funext i
    exact Bool.xor_self _
  rw [ht, Fourier.walsh_zero]

theorem multiplication_trace_zero_of_balanced (n : ℕ) (f : Cube n → ℝ) (hf : mean f = 0) :
    (Matrix.diagonal f).trace = 0 := by
  rw [Matrix.trace_diagonal]
  have hp : (Fintype.card (Cube n) : ℝ)⁻¹ ≠ 0 := by simp [Cube]
  exact (mul_eq_zero.mp hf).resolve_left hp

#print axioms antipodal_iff_anticommutes
#print axioms coordinate_spin_zero_distance
end Hellinger.ProductStateSemantics
