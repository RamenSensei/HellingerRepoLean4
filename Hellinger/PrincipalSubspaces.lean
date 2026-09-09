import Hellinger.QuadraticDual
import Hellinger.RankCharacterSum

/-! Restriction to genuine principal coordinate subspaces over F₂. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.PrincipalSubspaces
open F2Model QuadraticDual RankCharacterSum

def Supported {n : ℕ} (S : Finset (Fin n)) (v : Cube n) : Prop :=
  ∀ i, i ∉ S → v i = 0

instance supportedDecidable {n : ℕ} (S : Finset (Fin n)) (v : Cube n) : Decidable (Supported S v) :=
  Classical.propDecidable _

def embed {n : ℕ} (S : Finset (Fin n)) (x : S → F2) : Cube n :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else 0

theorem embed_supported {n : ℕ} (S : Finset (Fin n)) (x : S → F2) : Supported S (embed S x) := by
  intro i hi
  simp [embed, hi]

def supportedEquiv {n : ℕ} (S : Finset (Fin n)) : (S → F2) ≃ {v : Cube n // Supported S v} where
  toFun x := ⟨embed S x, embed_supported S x⟩
  invFun v i := v.1 i
  left_inv x := by
    funext i
    simp [embed]
  right_inv v := by
    apply Subtype.ext
    funext i
    by_cases hi : i ∈ S
    · simp [embed, hi]
    · simp [embed, hi, v.2 i hi]

theorem sum_supported {n : ℕ} (S : Finset (Fin n)) (F : Cube n → ℝ) :
    (∑ v : Cube n, if Supported S v then F v else 0) = ∑ x : S → F2, F (embed S x) := by
  rw [← Finset.sum_filter]
  rw [Finset.sum_subtype _ (by simp : ∀ x : Cube n,
    x ∈ Finset.univ.filter (Supported S) ↔ Supported S x)]
  rw [← (supportedEquiv S).sum_comp]
  rfl

def principalMatrix {n : ℕ} (B : Matrix (Fin n) (Fin n) F2) (S : Finset (Fin n)) :
    Matrix S S F2 := B.submatrix Subtype.val Subtype.val

theorem embed_dot {n : ℕ} (S : Finset (Fin n)) (x : S → F2) (v : Cube n) :
    embed S x ⬝ᵥ v = ∑ i : S, x i * v i := by
  have hs : (∑ i ∈ S, embed S x i * v i) = ∑ i : Fin n, embed S x i * v i := by
    apply Finset.sum_subset (Finset.subset_univ S)
    intro i _ hi
    simp [embed, hi]
  rw [dotProduct, ← hs, Finset.sum_subtype S (p := fun i => i ∈ S) (F := inferInstance) (by intro i; rfl)]
  simp [embed]

theorem mulVec_embed {n : ℕ} (B : Matrix (Fin n) (Fin n) F2)
    (S : Finset (Fin n)) (y : S → F2) (i : Fin n) :
    (B *ᵥ embed S y) i = ∑ j : S, B i j * y j := by
  change B i ⬝ᵥ embed S y = _
  rw [dotProduct_comm, embed_dot]
  apply Finset.sum_congr rfl
  intro j _
  ring

theorem embed_bilin {n : ℕ} (B : Matrix (Fin n) (Fin n) F2)
    (S : Finset (Fin n)) (x y : S → F2) :
    embed S x ⬝ᵥ B *ᵥ embed S y = x ⬝ᵥ principalMatrix B S *ᵥ y := by
  rw [embed_dot]
  simp_rw [mulVec_embed]
  rfl

theorem principal_character_sum {n : ℕ} (B : Matrix (Fin n) (Fin n) F2)
    (S : Finset (Fin n)) :
    (∑ s : Cube n, ∑ d : Cube n,
      if Supported S s ∧ Supported S d then sign (d ⬝ᵥ B *ᵥ s) else 0) =
      (2 : ℝ) ^ (2 * S.card - (principalMatrix B S).rank) := by
  have hi (s d : Cube n) :
      (if Supported S s ∧ Supported S d then sign (d ⬝ᵥ B *ᵥ s) else 0) =
      if Supported S s then (if Supported S d then sign (d ⬝ᵥ B *ᵥ s) else 0) else 0 := by
    split_ifs <;> simp_all
  simp_rw [hi, Finset.sum_ite_irrel, Finset.sum_const_zero, sum_supported]
  simp_rw [embed_bilin]
  simpa using double_character_sum (principalMatrix B S)

#print axioms principal_character_sum
end Hellinger.PrincipalSubspaces
