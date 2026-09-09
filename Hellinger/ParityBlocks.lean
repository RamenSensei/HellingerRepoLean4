import Hellinger.ProductState
import Hellinger.FourierCounting
import Hellinger.SortedEnumeration
import Hellinger.EigenvalueOrder
import Hellinger.MatrixReindex
import Hellinger.PosteriorState

/-! Actual even and odd Walsh-frequency blocks, with sorted enumerations.
Their dimensions, multiplicities, ordering and spectral distance are proved
from the concrete product state. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Matrix

namespace Hellinger.ParityBlocks
open Fourier ProductState

abbrev EvenIndex (n : ℕ) := {s : Fourier.Cube (n + 1) // Even (degree s)}
abbrev OddIndex (n : ℕ) := {s : Fourier.Cube (n + 1) // Odd (degree s)}

theorem even_card (n : ℕ) : Fintype.card (EvenIndex n) = 2 ^ n := by
  simpa only [Fintype.subtype_card] using card_even_degree n

theorem odd_card (n : ℕ) : Fintype.card (OddIndex n) = 2 ^ n := by
  simpa only [Fintype.subtype_card] using card_odd_degree n

def evenEquiv (n : ℕ) : Fin (2 ^ n) ≃ EvenIndex n :=
  (finCongr (even_card n).symm).trans (SortedEnumeration.sortedEquiv (fun s => degree s.val))

def oddEquiv (n : ℕ) : Fin (2 ^ n) ≃ OddIndex n :=
  (finCongr (odd_card n).symm).trans (SortedEnumeration.sortedEquiv (fun s => degree s.val))

def evenLevel (n : ℕ) (i : Fin (2 ^ n)) : ℕ := degree (evenEquiv n i).val
def oddLevel (n : ℕ) (i : Fin (2 ^ n)) : ℕ := degree (oddEquiv n i).val

theorem evenLevel_monotone (n : ℕ) : Monotone (evenLevel n) := by
  intro i j hij
  apply SortedEnumeration.sortedEquiv_monotone (fun s : EvenIndex n => degree s.val)
  exact hij

theorem oddLevel_monotone (n : ℕ) : Monotone (oddLevel n) := by
  intro i j hij
  apply SortedEnumeration.sortedEquiv_monotone (fun s : OddIndex n => degree s.val)
  exact hij

theorem evenLevel_le (n : ℕ) (i : Fin (2 ^ n)) : evenLevel n i ≤ n + 1 :=
  degree_le _

theorem oddLevel_le (n : ℕ) (i : Fin (2 ^ n)) : oddLevel n i ≤ n + 1 :=
  degree_le _

theorem subtype_degree_count (d k : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    (∑ s : {s : Fourier.Cube d // p (degree s)}, if degree s.val = k then (1 : ℝ) else 0) =
      if p k then (d.choose k : ℝ) else 0 := by
  rw [← Finset.sum_subtype (Finset.univ.filter (fun s : Fourier.Cube d => p (degree s)))
    (by simp) (fun s : Fourier.Cube d => if degree s = k then (1 : ℝ) else 0)]
  rw [Finset.sum_filter]
  have hterm (s : Fourier.Cube d) :
      (if p (degree s) then (if degree s = k then (1 : ℝ) else 0) else 0) =
        if p k then (if degree s = k then 1 else 0) else 0 := by
    by_cases h : degree s = k
    · simp [h]
    · simp [h]
  simp_rw [hterm]
  split_ifs with hk
  · simp only [Finset.sum_boole]
    rw [card_degree]
  · simp

theorem even_multiplicities (n k : ℕ) :
    (∑ i, if evenLevel n i = k then (1 : ℝ) else 0) =
      ParitySpectrum.evenMultiplicity (n + 1) k := by
  unfold evenLevel
  rw [(evenEquiv n).sum_comp (fun s => if degree s.val = k then (1 : ℝ) else 0)]
  exact subtype_degree_count (n + 1) k Even

theorem odd_multiplicities (n k : ℕ) :
    (∑ i, if oddLevel n i = k then (1 : ℝ) else 0) =
      ParitySpectrum.oddMultiplicity (n + 1) k := by
  unfold oddLevel
  rw [(oddEquiv n).sum_comp (fun s => if degree s.val = k then (1 : ℝ) else 0)]
  exact subtype_degree_count (n + 1) k Odd

def evenEigenvalue (n : ℕ) (c : ℝ) (i : Fin (2 ^ n)) : ℝ :=
  eigenvalue (n + 1) c (evenEquiv n i).val

def oddEigenvalue (n : ℕ) (c : ℝ) (i : Fin (2 ^ n)) : ℝ :=
  eigenvalue (n + 1) c (oddEquiv n i).val

theorem evenEigenvalue_antitone (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (evenEigenvalue n c) := by
  intro i j hij
  exact ParitySpectrum.spectralLevel_antitone (n + 1) _ _
    (by linarith [hc.1]) (by linarith [hc.2]) (by linarith [hc.1])
    _ _ (evenLevel_monotone n hij) (evenLevel_le n j)

theorem oddEigenvalue_antitone (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    Antitone (oddEigenvalue n c) := by
  intro i j hij
  exact ParitySpectrum.spectralLevel_antitone (n + 1) _ _
    (by linarith [hc.1]) (by linarith [hc.2]) (by linarith [hc.1])
    _ _ (oddLevel_monotone n hij) (oddLevel_le n j)

theorem actual_parity_spectra_l1 (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    (∑ i, |evenEigenvalue n c i - oddEigenvalue n c i|) = c := by
  exact ParitySpectrum.parity_spectra_l1 n c hc.1 hc.2
    (evenLevel n) (oddLevel n) (evenLevel_monotone n) (oddLevel_monotone n)
    (evenLevel_le n) (oddLevel_le n)
    (fun k _ => even_multiplicities n k) (fun k _ => odd_multiplicities n k)

def parityEquiv (n : ℕ) : EvenIndex n ⊕ OddIndex n ≃ Fourier.Cube (n + 1) :=
  (Equiv.sumCongr (Equiv.refl _) (Equiv.subtypeEquivRight (fun _ =>
    Nat.not_even_iff_odd.symm))).trans (Equiv.sumCompl (fun s => Even (degree s)))

def blockEquiv (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fourier.Cube (n + 1) :=
  (Equiv.sumCongr (evenEquiv n) (oddEquiv n)).trans (parityEquiv n)

@[simp] theorem blockEquiv_inl (n : ℕ) (i : Fin (2 ^ n)) :
    blockEquiv n (Sum.inl i) = (evenEquiv n i).val := rfl

@[simp] theorem blockEquiv_inr (n : ℕ) (i : Fin (2 ^ n)) :
    blockEquiv n (Sum.inr i) = (oddEquiv n i).val := rfl

theorem state_diagonal_blocks (n : ℕ) (c : ℝ) :
    (Matrix.diagonal (eigenvalue (n + 1) c)).submatrix (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks (Matrix.diagonal (evenEigenvalue n c)) 0 0
        (Matrix.diagonal (oddEigenvalue n c)) := by
  rw [Matrix.submatrix_diagonal_equiv]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.diagonal, Matrix.fromBlocks, evenEigenvalue, oddEigenvalue]

def parityDiagonal (n : ℕ) : Matrix (Fourier.Cube n) (Fourier.Cube n) ℝ :=
  Matrix.diagonal (fun s => (-1 : ℝ) ^ degree s)

theorem parity_diagonal_blocks (n : ℕ) :
    (parityDiagonal (n + 1)).submatrix (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks 1 0 0 (-1) := by
  unfold parityDiagonal
  rw [Matrix.submatrix_diagonal_equiv]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · simp [Matrix.diagonal, Matrix.fromBlocks, (evenEquiv n i).property.neg_one_pow,
      Matrix.one_apply]
  · simp
  · simp
  · simp [Matrix.diagonal, Matrix.fromBlocks, (oddEquiv n i).property.neg_one_pow,
      Matrix.one_apply]
    split_ifs <;> norm_num

def transformedReflection (n : ℕ) (f : Fourier.Cube n → ℝ) :
    Matrix (Fourier.Cube n) (Fourier.Cube n) ℝ :=
  Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (Matrix.diagonal f)

theorem reflection_squared (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) : Matrix.diagonal f * Matrix.diagonal f = 1 := by
  rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext x
  rcases hf x with hx | hx <;> simp [hx]

theorem transformedReflection_squared (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) :
    transformedReflection n f * transformedReflection n f = 1 := by
  rw [transformedReflection, ← map_mul, reflection_squared n f hf, map_one]

theorem transformedReflection_isHermitian (n : ℕ) (f : Fourier.Cube n → ℝ) :
    (transformedReflection n f).IsHermitian := by
  change star (transformedReflection n f) = transformedReflection n f
  rw [transformedReflection, ← map_star]
  congr 1
  exact Matrix.isHermitian_diagonal_iff.mpr (fun _ => IsSelfAdjoint.all _)

theorem reflection_anticommutes (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hanti : ∀ x, f (antipode n x) = -f x) :
    Matrix.diagonal f * antipodalMatrix n = -(antipodalMatrix n * Matrix.diagonal f) := by
  apply Matrix.ext_iff_mulVec.mpr
  intro v
  ext x
  simp only [← Matrix.mulVec_mulVec, Matrix.neg_mulVec, Matrix.mulVec_diagonal,
    Pi.neg_apply, antipodalMatrix_apply, hanti, neg_mul, neg_neg]

theorem transformed_antipodalMatrix (n : ℕ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (antipodalMatrix n) =
      parityDiagonal n := by
  simpa only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose, parityDiagonal] using antipodalMatrix_diagonalization n

theorem transformedReflection_anticommutes (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hanti : ∀ x, f (antipode n x) = -f x) :
    transformedReflection n f * parityDiagonal n =
      -(parityDiagonal n * transformedReflection n f) := by
  rw [transformedReflection, ← transformed_antipodalMatrix, ← map_mul,
    reflection_anticommutes n f hanti, map_neg, map_mul]

theorem transformedReflection_same_parity_zero (n : ℕ) (f : Fourier.Cube n → ℝ)
    (hanti : ∀ x, f (antipode n x) = -f x) (s t : Fourier.Cube n)
    (heq : (-1 : ℝ) ^ degree s = (-1 : ℝ) ^ degree t) :
    transformedReflection n f s t = 0 := by
  have h := congrFun (congrFun (transformedReflection_anticommutes n f hanti) s) t
  simp only [parityDiagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.neg_apply] at h
  rw [heq] at h
  have hn : (-1 : ℝ) ^ degree t ≠ 0 := pow_ne_zero _ (by norm_num)
  have hz : transformedReflection n f s t * (-1 : ℝ) ^ degree t = 0 := by nlinarith [h]
  exact (mul_eq_zero.mp hz).resolve_right hn

def offBlock (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ) :
    Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℝ :=
  fun i j => transformedReflection (n + 1) f (evenEquiv n i).val (oddEquiv n j).val

theorem reflection_blocks (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    (transformedReflection (n + 1) f).submatrix (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks 0 (offBlock n f) (offBlock n f).transpose 0 := by
  ext i j
  rcases i with i | i <;> rcases j with j | j
  · exact transformedReflection_same_parity_zero (n + 1) f hanti _ _ (by
      simp only [blockEquiv_inl, (evenEquiv n i).property.neg_one_pow,
        (evenEquiv n j).property.neg_one_pow])
  · rfl
  · have h := congrFun (congrFun (transformedReflection_isHermitian (n + 1) f) 
      (evenEquiv n j).val) (oddEquiv n i).val
    exact h
  · exact transformedReflection_same_parity_zero (n + 1) f hanti _ _ (by
      simp only [blockEquiv_inr, (oddEquiv n i).property.neg_one_pow,
        (oddEquiv n j).property.neg_one_pow])

theorem offBlock_mul_transpose (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    offBlock n f * (offBlock n f).transpose = 1 := by
  have h := congrArg (fun M => M.submatrix (blockEquiv n) (blockEquiv n))
    (transformedReflection_squared (n + 1) f hf)
  rw [← Matrix.submatrix_mul_equiv _ _ (blockEquiv n) (blockEquiv n) (blockEquiv n),
    reflection_blocks n f hanti,
    Matrix.fromBlocks_multiply, Matrix.submatrix_one_equiv] at h
  have h₁ := congrArg Matrix.toBlocks₁₁ h
  ext i j
  have hij := congrFun (congrFun h₁ i) j
  simpa [Matrix.toBlocks₁₁, Matrix.one_apply] using hij

def blockUnitary (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    Matrix.unitaryGroup (Fin (2 ^ n)) ℝ :=
  ⟨offBlock n f, Matrix.mem_unitaryGroup_iff.mpr (by
    simpa only [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial]
      using offBlock_mul_transpose n f hf hanti)⟩

theorem transformed_state (n : ℕ) (c : ℝ) :
    Unitary.conjStarAlgAut ℝ _ (hadamardUnitary n) (state n c) =
      Matrix.diagonal (eigenvalue n c) := by
  simpa only [Unitary.conjStarAlgAut_apply, hadamardUnitary_coe,
    Matrix.star_eq_conjTranspose, Matrix.conjTranspose_eq_transpose_of_trivial,
    hadamard_transpose] using state_diagonalization n c

theorem difference_blocks (n : ℕ) (c : ℝ) (f : Fourier.Cube (n + 1) → ℝ)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    (Unitary.conjStarAlgAut ℝ _ (hadamardUnitary (n + 1))
      (state (n + 1) c - Matrix.diagonal f * state (n + 1) c * Matrix.diagonal f)).submatrix
        (blockEquiv n) (blockEquiv n) =
      Matrix.fromBlocks
        (Matrix.diagonal (evenEigenvalue n c) -
          offBlock n f * Matrix.diagonal (oddEigenvalue n c) * (offBlock n f).transpose) 0 0
        (Matrix.diagonal (oddEigenvalue n c) -
          (offBlock n f).transpose * Matrix.diagonal (evenEigenvalue n c) * offBlock n f) := by
  simp only [map_sub, map_mul, transformed_state]
  change (Matrix.diagonal (eigenvalue (n + 1) c)).submatrix (blockEquiv n) (blockEquiv n) -
    (transformedReflection (n + 1) f * Matrix.diagonal (eigenvalue (n + 1) c) *
      transformedReflection (n + 1) f).submatrix (blockEquiv n) (blockEquiv n) = _
  rw [← Matrix.submatrix_mul_equiv _ _ (blockEquiv n) (blockEquiv n) (blockEquiv n),
    ← Matrix.submatrix_mul_equiv _ _ (blockEquiv n) (blockEquiv n) (blockEquiv n),
    state_diagonal_blocks, reflection_blocks n f hanti]
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add]
  ext i j
  rcases i with i | i <;> rcases j with j | j <;> simp [Matrix.diagonal]

theorem actual_block_trace (n : ℕ) (c : ℝ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    TraceNorm.traceNorm (state (n + 1) c -
      Matrix.diagonal f * state (n + 1) c * Matrix.diagonal f) =
      2 * TraceNorm.traceNorm (Matrix.diagonal (evenEigenvalue n c) -
        Unitary.conjStarAlgAut ℝ _ (blockUnitary n f hf hanti)
          (Matrix.diagonal (oddEigenvalue n c))) := by
  rw [← TraceNorm.traceNorm_conjugate (hadamardUnitary (n + 1)),
    ← TraceNorm.traceNorm_submatrix_equiv _ (blockEquiv n), difference_blocks n c f hanti]
  have h := TraceNorm.traceNorm_paired_difference (blockUnitary n f hf hanti)
    (Matrix.diagonal (evenEigenvalue n c)) (Matrix.diagonal (oddEigenvalue n c))
  simpa only [Unitary.conjStarAlgAut_apply, blockUnitary, Unitary.coe_star,
    Matrix.star_eq_conjTranspose,
    Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.transpose_transpose] using h

theorem antipodal_trace_lower_bound (n : ℕ) (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1)
    (f : Fourier.Cube (n + 1) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x) :
    c ≤ TraceNorm.traceNorm (state (n + 1) c -
      Matrix.diagonal f * state (n + 1) c * Matrix.diagonal f) / 2 := by
  rw [actual_block_trace n c f hf hanti]
  have h := TraceNorm.sorted_diagonal_distance_le_traceNorm
    (evenEigenvalue n c) (oddEigenvalue n c)
    (evenEigenvalue_antitone n c hc) (oddEigenvalue_antitone n c hc)
    (blockUnitary n f hf hanti)
  rw [actual_parity_spectra_l1 n c hc] at h
  linarith

theorem antipodal_hellinger (n : ℕ) (f : Fourier.Cube (n + 1) → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (antipode (n + 1) x) = -f x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    root ρ ≤ mean (fun y => root ((cubeBSC (n + 1) ρ hρ).apply f y)) := by
  have hc : root ρ ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Real.sqrt_nonneg _, Real.sqrt_le_one.mpr (by nlinarith [sq_nonneg ρ])⟩
  exact (antipodal_trace_lower_bound n (root ρ) hc
    f hf hanti).trans (PosteriorState.bsc_lifting (n + 1) f hf ρ hρ)

end Hellinger.ParityBlocks
