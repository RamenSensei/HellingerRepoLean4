import Hellinger.BentFour

/-! Kernel-checked finite classification of the six quadratic cross terms.
The noise parameter remains an arbitrary real throughout every polynomial identity. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators
namespace Hellinger.BentFourGraphs
open Hellinger.Fourier Hellinger.BentFour

set_option maxHeartbeats 20000000 in
/-- Each nondegenerate four-coordinate sign matrix has one of the exact
fourth-moment polynomials, with at least two nonzero cross terms. -/
theorem derivative_moment_classification (e : Fin 6 → ℝ)
    (he : ∀ i, e i ^ 2 = 1) (hnd : EdgeNondegenerate e) (ρ : ℝ) :
    ∃ d : ℝ, 2 ≤ d ∧ (∑ s : Cube 4, noiseDerivativeSum e ρ s ^ 2) =
      256 * BentEstimates.fourthMomentExpression d (ρ ^ 2) := by
  have hevec : e = ![e 0, e 1, e 2, e 3, e 4, e 5] := by funext i; fin_cases i <;> rfl
  rw [hevec] at hnd ⊢
  have h0 : e 0 = 1 ∨ e 0 = -1 := sq_eq_one_iff.mp (he 0)
  have h1 : e 1 = 1 ∨ e 1 = -1 := sq_eq_one_iff.mp (he 1)
  have h2 : e 2 = 1 ∨ e 2 = -1 := sq_eq_one_iff.mp (he 2)
  have h3 : e 3 = 1 ∨ e 3 = -1 := sq_eq_one_iff.mp (he 3)
  have h4 : e 4 = 1 ∨ e 4 = -1 := sq_eq_one_iff.mp (he 4)
  have h5 : e 5 = 1 ∨ e 5 = -1 := sq_eq_one_iff.mp (he 5)
  rcases h0 with h0 | h0 <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
    rcases h3 with h3 | h3 <;> rcases h4 with h4 | h4 <;> rcases h5 with h5 | h5 <;>
    rw [h0, h1, h2, h3, h4, h5] at hnd ⊢
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, false, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, true, false] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, true, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, false, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, true, true] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, true, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, true, false] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, false, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, true, false] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, true, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨2, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, false, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨2, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, false, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, true, true] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, false, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, true, true] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, true, true, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨2, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, true, false] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, true, true] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, true, false] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, false, true, false] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, true, false, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, true, true, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨3, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, true, true, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, false, true] (by
      intro hz
      have hi := congrFun hz 3
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, true, true, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, true, true] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, true, true, false] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨4, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring
  · exfalso
    have hz := hnd ![false, true, false, true] (by
      intro hz
      have hi := congrFun hz 1
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · exfalso
    have hz := hnd ![false, false, true, true] (by
      intro hz
      have hi := congrFun hz 2
      change true = false at hi
      contradiction)
    simp only [Fin.prod_univ_succ] at hz
    dsimp [edgeAction] at hz
    norm_num at hz
  · refine ⟨6, by norm_num, ?_⟩
    simp only [sum_four_bits, Fintype.sum_bool, noiseDerivativeSum, Fin.prod_univ_succ]
    dsimp [edgeAction, BentEstimates.fourthMomentExpression]
    ring

theorem derivative_moment_upper (e : Fin 6 → ℝ)
    (he : ∀ i, e i ^ 2 = 1) (hnd : EdgeNondegenerate e) (ρ : ℝ) :
    (∑ s : Cube 4, noiseDerivativeSum e ρ s ^ 2) / 256 ≤
      BentEstimates.bentH (ρ ^ 2) ^ 2 / 256 := by
  obtain ⟨d, hd, heq⟩ := derivative_moment_classification e he hnd ρ
  rw [heq]
  have h := BentEstimates.fourthMomentExpression_le d (ρ ^ 2) hd
  nlinarith only [h]

#print axioms derivative_moment_classification
#print axioms derivative_moment_upper
end Hellinger.BentFourGraphs
