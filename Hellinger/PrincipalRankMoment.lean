import Hellinger.RankMomentExpansion
import Hellinger.PrincipalSubspaces

/-! Exact fourth moments from true principal matrix ranks in every dimension. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.PrincipalRankMoment
open F2Model QuadraticRadical QuadraticDual RankMomentExpansion PrincipalSubspaces

def rankWeight {n : ℕ} (t : ℝ) (S : Finset (Fin n)) : ℝ :=
  (1 - t) ^ (2 * (n - S.card)) * (2 * t) ^ S.card

theorem outside_indicator {n : ℕ} (S : Finset (Fin n)) (s d : Cube n) :
    (∏ i ∈ Sᶜ, if s i = 0 ∧ d i = 0 then (1 : ℝ) else 0) =
      if Supported S s ∧ Supported S d then 1 else 0 := by
  rw [Finset.prod_boole]
  congr 1
  apply propext
  constructor
  · intro h
    exact ⟨fun i hi => (h i (by simp [hi])).1, fun i hi => (h i (by simp [hi])).2⟩
  · rintro ⟨hs, hd⟩ i hi
    have hiS : i ∉ S := by simpa using hi
    exact ⟨hs i hiS, hd i hiS⟩

theorem coordinate_product_expansion {n : ℕ} (t : ℝ) (s d : Cube n) :
    (∏ i, (2 * t + (1 - t) ^ 2 * (if s i = 0 ∧ d i = 0 then 1 else 0))) =
      ∑ S : Finset (Fin n), rankWeight t S *
        (if Supported S s ∧ Supported S d then 1 else 0) := by
  rw [Fintype.prod_add (fun _ : Fin n => 2 * t)
    (fun i => (1 - t) ^ 2 * (if s i = 0 ∧ d i = 0 then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro S _
  simp only [Finset.prod_const, Finset.prod_mul_distrib, outside_indicator,
    Finset.card_compl, Fintype.card_fin, ← pow_mul, rankWeight]
  ring

/-- Character orthogonality converts the full coordinate expansion to true principal ranks. -/
theorem rank_sum_expansion {n : ℕ} (B : Matrix (Fin n) (Fin n) F2) (t : ℝ) :
    (∑ s : Cube n, ∑ d : Cube n, sign (d ⬝ᵥ B *ᵥ s) *
      ∏ i, (2 * t + (1 - t) ^ 2 * (if s i = 0 ∧ d i = 0 then 1 else 0))) =
      ∑ S : Finset (Fin n), rankWeight t S *
        (2 : ℝ) ^ (2 * S.card - (principalMatrix B S).rank) := by
  simp_rw [coordinate_product_expansion, Finset.mul_sum]
  have hswap (s : Cube n) :
      (∑ d : Cube n, ∑ S : Finset (Fin n), sign (d ⬝ᵥ B *ᵥ s) *
        (rankWeight t S * (if Supported S s ∧ Supported S d then 1 else 0))) =
      ∑ S : Finset (Fin n), ∑ d : Cube n, sign (d ⬝ᵥ B *ᵥ s) *
        (rankWeight t S * (if Supported S s ∧ Supported S d then 1 else 0)) :=
    Finset.sum_comm
  simp_rw [hswap]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S _
  have hi (s d : Cube n) : sign (d ⬝ᵥ B *ᵥ s) *
      (rankWeight t S * (if Supported S s ∧ Supported S d then 1 else 0)) =
      rankWeight t S * (if Supported S s ∧ Supported S d then sign (d ⬝ᵥ B *ᵥ s) else 0) := by
    split_ifs <;> ring
  simp_rw [hi, ← Finset.mul_sum]
  rw [principal_character_sum]

/-- The manuscript's principal-rank fourth-moment formula, for actual BSC posteriors,
actual inverse polar matrix, and actual matrix ranks over `ZMod 2`. -/
theorem fourth_moment_principal_ranks {n : ℕ} (a : F2) (Q : Form n)
    (hQ : IsUnit (polarMatrix Q).det) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply (phase a Q ∘ bitsEquiv (Fin n)) x) ^ 4) =
      ((2 : ℝ) ^ (2 * n))⁻¹ * ∑ S : Finset (Fin n),
        (1 - ρ ^ 2) ^ (2 * (n - S.card)) * (2 * ρ ^ 2) ^ S.card *
          (2 : ℝ) ^ (2 * S.card - (principalMatrix (polarMatrix Q)⁻¹ S).rank) := by
  rw [phase_fourth_coordinate_expansion a Q hQ, rank_sum_expansion]
  simp only [rankWeight, ← inv_pow, ← pow_mul]
  rw [Nat.mul_comm n 2]

/-- Explicit coefficient-level version matching `PaperSpecs.quadraticValue`. -/
theorem fourth_moment_quadratic_value {n : ℕ} (a : F2) (b : Fin n → F2)
    (q : Fin n → Fin n → F2) (f : PaperSpecs.Cube n → ℝ)
    (hf : ∀ x, f x = if PaperSpecs.quadraticValue a b q x = 0 then 1 else -1)
    (hQ : (polarMatrix (polynomial b q)).det ≠ 0)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    mean (fun x => ((cubeBSC n ρ hρ).apply f x) ^ 4) =
      ((2 : ℝ) ^ (2 * n))⁻¹ * ∑ S : Finset (Fin n),
        (1 - ρ ^ 2) ^ (2 * (n - S.card)) * (2 * ρ ^ 2) ^ S.card *
          (2 : ℝ) ^ (2 * S.card -
            (principalMatrix (polarMatrix (polynomial b q))⁻¹ S).rank) := by
  have hform : f = phase a (polynomial b q) ∘ bitsEquiv (Fin n) := by
    funext x
    exact (hf x).trans (polynomial_phase_bits a b q x).symm
  rw [hform]
  exact fourth_moment_principal_ranks a (polynomial b q) (isUnit_iff_ne_zero.mpr hQ) ρ hρ

#print axioms fourth_moment_principal_ranks
#print axioms fourth_moment_quadratic_value
end Hellinger.PrincipalRankMoment
