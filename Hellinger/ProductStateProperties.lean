import Hellinger.ReflectionCounterexample

/-! Density-matrix normalization and the commuting coordinate-spin algebra
used in the product-state argument. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators MatrixOrder
open Matrix

namespace Hellinger.ProductStateProperties
open ProductState SpinState TraceNorm

theorem state_posSemidef (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (-1 : ℝ) 1) :
    (state n c).PosSemidef := by
  have he : (Matrix.diagonal (eigenvalue n c)).PosSemidef := by
    apply Matrix.posSemidef_diagonal_iff.mpr
    intro s
    exact mul_nonneg (pow_nonneg (by linarith [hc.1]) _)
      (pow_nonneg (by linarith [hc.2]) _)
  have h := posSemidef_conjugate (hadamardUnitary n) he
  rw [← ParityBlocks.transformed_state, ReflectionCounterexample.hadamard_conjugate_involution] at h
  exact h

theorem state_trace_one (n : ℕ) (c : ℝ) : (state n c).trace = 1 := by
  simp [Matrix.trace, Matrix.diag, state_entry, hammingDistance]

theorem spin_squared (n : ℕ) (i : Fin n) : spin n i * spin n i = 1 := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (spin n i * spin n i) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) 1
  rw [map_mul, transformed_spin, map_one, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext s
  cases s i <;> norm_num [boolSign]

theorem spin_commute (n : ℕ) (i j : Fin n) : Commute (spin n i) (spin n j) := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (spin n i * spin n j) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (spin n j * spin n i)
  rw [map_mul, map_mul, transformed_spin, transformed_spin]
  simp [Matrix.diagonal_mul_diagonal, mul_comm]

theorem sign_product_degree (n : ℕ) (s : Cube n) :
    (∏ i : Fin n, boolSign (s i)) = (-1 : ℝ) ^ Fourier.degree s := by
  simp [boolSign, Finset.prod_ite, Fourier.degree, Fourier.support]

theorem spin_product_antipode (n : ℕ) :
    (List.ofFn (spin n)).prod = antipodalMatrix n := by
  apply (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n)).injective
  change Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) ((List.ofFn (spin n)).prod) =
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (antipodalMatrix n)
  rw [map_list_prod, List.map_ofFn, ParityBlocks.transformed_antipodalMatrix]
  simp only [Function.comp_def, transformed_spin]
  have hm := map_list_prod (Matrix.diagonalRingHom (Cube n) ℝ)
    (List.ofFn (fun i : Fin n => (fun s : Cube n => boolSign (s i))))
  rw [List.map_ofFn] at hm
  change Matrix.diagonal ((List.ofFn (fun i : Fin n =>
    (fun s : Cube n => boolSign (s i)))).prod) =
      (List.ofFn (fun i : Fin n => Matrix.diagonal (fun s : Cube n => boolSign (s i)))).prod at hm
  change _ = Matrix.diagonal (fun s => (-1 : ℝ) ^ Fourier.degree s)
  rw [← hm, List.prod_ofFn]
  congr 1
  funext s
  simp [sign_product_degree]

end Hellinger.ProductStateProperties
