import Hellinger.PrincipalRankMoment
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix

/-! The exact two-variable interlace-polynomial specialization of the BSC fourth moment. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.InterlaceMoment
open F2Model QuadraticRadical QuadraticDual PrincipalSubspaces PrincipalRankMoment

/-- The usual two-variable interlace polynomial evaluated at two real arguments,
using the true ranks of principal submatrices over F₂. -/
def interlace {n : ℕ} (B : Matrix (Fin n) (Fin n) F2) (ξ η : ℝ) : ℝ :=
  ∑ S : Finset (Fin n), (ξ - 1) ^ (principalMatrix B S).rank *
    (η - 1) ^ (S.card - (principalMatrix B S).rank)

theorem scalar_substitution (n s r : ℕ) (hs : s ≤ n) (hr : r ≤ s)
    (t : ℝ) (ht : t ≠ 1) :
    (1 - t) ^ (2 * n) *
      ((4 * t) / (1 - t) ^ 2) ^ r * ((8 * t) / (1 - t) ^ 2) ^ (s - r) =
      (1 - t) ^ (2 * (n - s)) * (2 * t) ^ s * (2 : ℝ) ^ (2 * s - r) := by
  have hd : 1 - t ≠ 0 := sub_ne_zero.mpr (Ne.symm ht)
  have he : 2 * n = 2 * (n - s) + 2 * s := by omega
  have he₂ : r + (s - r) = s := by omega
  have hcoef : (4 * t) ^ r * (8 * t) ^ (s - r) =
      (2 * t) ^ s * (2 : ℝ) ^ (2 * s - r) := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, show (8 : ℝ) = 2 ^ 3 by norm_num]
    simp only [mul_pow, ← pow_mul]
    calc
      _ = (2 : ℝ) ^ (2 * r + 3 * (s - r)) * t ^ (r + (s - r)) := by
        rw [pow_add, pow_add]
        ring
      _ = (2 : ℝ) ^ (s + (2 * s - r)) * t ^ s := by
        congr 2; omega
      _ = _ := by rw [pow_add]; ring
  rw [he, pow_add]
  calc
    _ = (1 - t) ^ (2 * (n - s)) *
        (((1 - t) ^ 2) ^ s *
          (((4 * t) / (1 - t) ^ 2) ^ r * ((8 * t) / (1 - t) ^ 2) ^ (s - r))) := by
      rw [← pow_mul]
      ring
    _ = (1 - t) ^ (2 * (n - s)) * ((4 * t) ^ r * (8 * t) ^ (s - r)) := by
      congr 1
      rw [div_pow, div_pow, div_mul_div_comm, ← pow_add, he₂]
      exact mul_div_cancel₀ _ (pow_ne_zero _ (pow_ne_zero _ hd))
    _ = _ := by rw [hcoef]; ring

/-- The graph-polynomial specialization is a term-by-term algebraic identity. -/
theorem interlace_substitution {n : ℕ} (B : Matrix (Fin n) (Fin n) F2)
    (t : ℝ) (ht : t ≠ 1) :
    (1 - t) ^ (2 * n) * interlace B (1 + 4 * t / (1 - t) ^ 2)
      (1 + 8 * t / (1 - t) ^ 2) =
      ∑ S : Finset (Fin n), rankWeight t S *
        (2 : ℝ) ^ (2 * S.card - (principalMatrix B S).rank) := by
  simp only [interlace, add_sub_cancel_left, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro S _
  have hs : S.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ S)
  have hr : (principalMatrix B S).rank ≤ S.card := by
    simpa using (principalMatrix B S).rank_le_card_width
  simpa only [rankWeight, mul_assoc] using scalar_substitution n S.card
    (principalMatrix B S).rank hs hr t ht

/-- The true BSC noise fourth moment is the claimed interlace specialization. -/
theorem fourth_moment_interlace {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρlt : ρ < 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ((2 : ℝ) ^ (2 * n))⁻¹ * (1 - ρ ^ 2) ^ (2 * n) *
        interlace (polarMatrix Q)⁻¹ (1 + 4 * ρ ^ 2 / (1 - ρ ^ 2) ^ 2)
          (1 + 8 * ρ ^ 2 / (1 - ρ ^ 2) ^ 2) := by
  have ht : ρ ^ 2 ≠ 1 := by nlinarith [hρ.1]
  rw [fourth_moment_principal_ranks a Q hQ, mul_assoc, interlace_substitution _ _ ht]
  rfl

theorem inverse_polar_alternating {n : ℕ} (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (x : Cube n) :
    x ⬝ᵥ (polarMatrix Q)⁻¹ *ᵥ x = 0 := by
  rw [← dualForm_polar Q hQ]
  change QuadraticMap.polar (dualForm Q) x x = 0
  rw [QuadraticMap.polar_self, two_nsmul]
  exact (F2Model.add_eq_zero_iff _ _).mpr rfl

theorem inverse_polar_isAdjMatrix {n : ℕ} (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) : ((polarMatrix Q)⁻¹).IsAdjMatrix where
  zero_or_one i j := by
    by_cases h : (polarMatrix Q)⁻¹ i j = 0
    · exact Or.inl h
    · exact Or.inr (eq_one_of_ne_zero _ h)
  symm := (polarMatrix_symmetric Q).inv
  apply_diag i := by
    have h := inverse_polar_alternating Q hQ (Pi.single i 1)
    simpa using h

/-- The actual loopless simple graph with adjacency matrix the inverse polar matrix. -/
def inversePolarGraph {n : ℕ} (Q : Form n) (hQ : IsUnit (polarMatrix Q).det) :
    SimpleGraph (Fin n) := (inverse_polar_isAdjMatrix Q hQ).toGraph

noncomputable instance inversePolarGraph_decidable {n : ℕ} (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) : DecidableRel (inversePolarGraph Q hQ).Adj :=
  Classical.decRel _

theorem inversePolarGraph_adjacency {n : ℕ} (Q : Form n) (hQ : IsUnit (polarMatrix Q).det) :
    (inversePolarGraph Q hQ).adjMatrix F2 = (polarMatrix Q)⁻¹ := by
  ext i j
  rw [SimpleGraph.adjMatrix_apply]
  simp only [inversePolarGraph, Matrix.IsAdjMatrix.toGraph_adj]
  rcases (inverse_polar_isAdjMatrix Q hQ).zero_or_one i j with h | h <;> simp [h]

/-- Graph-native version of the same interlace evaluation. -/
def graphInterlace {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (ξ η : ℝ) : ℝ :=
  interlace (G.adjMatrix F2) ξ η

theorem fourth_moment_graph_interlace {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρlt : ρ < 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ((2 : ℝ) ^ (2 * n))⁻¹ * (1 - ρ ^ 2) ^ (2 * n) *
        graphInterlace (inversePolarGraph Q hQ) (1 + 4 * ρ ^ 2 / (1 - ρ ^ 2) ^ 2)
          (1 + 8 * ρ ^ 2 / (1 - ρ ^ 2) ^ 2) := by
  rw [graphInterlace, inversePolarGraph_adjacency]
  exact fourth_moment_interlace a Q hQ ρ hρ hρlt

theorem noise_one {n : ℕ} (f : Fourier.Cube n → ℝ)
    (h₁ : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) : (cubeBSC n 1 h₁).apply f = f := by
  funext x
  rw [Fourier.inversion ((cubeBSC n 1 h₁).apply f) x]
  simp only [Fourier.walsh_noise, one_pow, one_mul]
  exact (Fourier.inversion f x).symm

/-- The endpoint omitted by the rational substitution is included by the rank formula
and has exactly the expected fourth moment one. -/
theorem phase_fourth_moment_one {n : ℕ} (a : F2) (Q : Form n)
    (h₁ : (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n 1 h₁).apply (phase a Q ∘ bitsEquiv (Fin n)) x) ^ 4) = 1 := by
  rw [noise_one]
  have h (x : Fourier.Cube n) : (phase a Q ∘ bitsEquiv (Fin n)) x ^ 4 = 1 := by
    rcases phase_boolean a Q (bitsEquiv (Fin n) x) with h | h <;>
      simp only [Function.comp_apply, h] <;> norm_num
  simp only [h, mean_const]

#print axioms fourth_moment_interlace
#print axioms fourth_moment_graph_interlace
#print axioms phase_fourth_moment_one
end Hellinger.InterlaceMoment
