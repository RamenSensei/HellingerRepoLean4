import Hellinger.BentFourMatrix
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Actual ranks of the small principal submatrices in the four-dimensional argument. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators Matrix
namespace Hellinger.SmallPrincipalRanks
open F2Model QuadraticRadical QuadraticDual PrincipalSubspaces

/-- A nonzero symmetric zero-diagonal matrix over F₂ has rank at least two. -/
theorem alternating_rank_ge_two {ι : Type*} [Fintype ι] [DecidableEq ι]
    (C : Matrix ι ι F2) (hs : C.IsSymm) (hd : ∀ i, C i i = 0) (hC : C ≠ 0) :
    2 ≤ C.rank := by
  obtain ⟨i, j, hij⟩ : ∃ i j, C i j ≠ 0 := by
    by_contra! h
    exact hC (Matrix.ext h)
  have hji : C j i = C i j := congrArg (fun A => A i j) hs.eq
  let e : Fin 2 → ι := ![i, j]
  have hdet : (C.submatrix e e).det ≠ 0 := by
    simp only [Matrix.det_fin_two, Matrix.submatrix_apply]
    change C i i * C j j - C i j * C j i ≠ 0
    rw [hd, hd, hji, zero_mul, zero_sub]
    exact neg_ne_zero.mpr (mul_ne_zero hij hij)
  have hr := Matrix.rank_of_det_ne_zero hdet
  have hle := C.rank_submatrix_le e e
  simpa only [hr, Fintype.card_fin] using hle

/-- In size three, a nonzero alternating matrix over F₂ has rank exactly two. -/
theorem alternating_three_rank (C : Matrix (Fin 3) (Fin 3) F2)
    (hs : C.IsSymm) (hd : ∀ i, C i i = 0) (hC : C ≠ 0) : C.rank = 2 := by
  have hs10 : C 1 0 = C 0 1 := congrArg (fun A => A 0 1) hs.eq
  have hs20 : C 2 0 = C 0 2 := congrArg (fun A => A 0 2) hs.eq
  have hs21 : C 2 1 = C 1 2 := congrArg (fun A => A 1 2) hs.eq
  let v : Fin 3 → F2 := ![C 1 2, C 0 2, C 0 1]
  have hv : v ≠ 0 := by
    intro h
    have h12 : C 1 2 = 0 := congrFun h 0
    have h02 : C 0 2 = 0 := congrFun h 1
    have h01 : C 0 1 = 0 := congrFun h 2
    apply hC
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hd, hs10, hs20, hs21, h12, h02, h01]
  have hker : C.mulVecLin v = 0 := by
    change C *ᵥ v = 0
    funext i
    fin_cases i <;> simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_succ] <;>
      dsimp [v] <;> simp only [hd, hs10, hs20, hs21] <;>
      ring_nf <;> simp only [show (2 : F2) = 0 from rfl, mul_zero]
  have hkpos : 0 < Module.finrank F2 C.mulVecLin.ker := by
    apply Module.finrank_pos_iff_exists_ne_zero.mpr
    refine ⟨⟨v, hker⟩, ?_⟩
    intro h
    exact hv (congrArg Subtype.val h)
  have hdim := C.mulVecLin.finrank_range_add_finrank_ker
  have htotal : Module.finrank F2 (Fin 3 → F2) = 3 := by simp
  rw [htotal] at hdim
  have hlow := alternating_rank_ge_two C hs hd hC
  change C.rank + Module.finrank F2 C.mulVecLin.ker = 3 at hdim
  omega

/-- If a three-coordinate principal block vanished, the full matrix would factor
through a two-dimensional space. Thus nonsingularity rules this out. -/
theorem principal_three_nonzero (B : Matrix (Fin 4) (Fin 4) F2)
    (hs : B.IsSymm) (hd : ∀ i, B i i = 0) (hdet : B.det ≠ 0)
    (S : Finset (Fin 4)) (hS : S.card = 3) : principalMatrix B S ≠ 0 := by
  intro hzero
  have hSc : Sᶜ.card = 1 := by simp [Finset.card_compl, hS]
  obtain ⟨k, hk⟩ := Finset.card_eq_one.mp hSc
  have hmem (i : Fin 4) (hi : i ≠ k) : i ∈ S := by
    by_contra hiS
    have hiC : i ∈ Sᶜ := by simpa using hiS
    rw [hk] at hiC
    exact hi (Finset.mem_singleton.mp hiC)
  have hz (i j : Fin 4) (hi : i ≠ k) (hj : j ≠ k) : B i j = 0 :=
    congrArg (fun C : Matrix S S F2 => C ⟨i, hmem i hi⟩ ⟨j, hmem j hj⟩) hzero
  let U : Matrix (Fin 4) (Fin 2) F2 := fun i j =>
    if j = 0 then B k i else if i = k then 1 else 0
  let V : Matrix (Fin 2) (Fin 4) F2 := fun i j =>
    if i = 0 then (if j = k then 1 else 0) else B k j
  have hfactor : B = U * V := by
    ext i j
    rw [Matrix.mul_apply]
    simp only [Fin.sum_univ_succ]
    by_cases hi : i = k
    · subst i
      by_cases hj : j = k
      · subst j
        simp [U, V, hd]
      · simp [U, V, hd, hj]
    · by_cases hj : j = k
      · subst j
        have hsym : B i k = B k i := congrArg (fun C => C k i) hs.eq
        simp [U, V, hi, hd, hsym]
      · simp [U, V, hi, hj, hz i j hi hj]
  have hr : B.rank = 4 := by simpa using Matrix.rank_of_det_ne_zero hdet
  have hU : U.rank ≤ 2 := by simpa using U.rank_le_card_width
  have hle := Matrix.rank_mul_le_left U V
  rw [← hfactor, hr] at hle
  omega

/-- Every three-by-three principal submatrix of an invertible alternating
four-by-four matrix has its actual F₂ rank equal to two. -/
theorem principal_three_rank (B : Matrix (Fin 4) (Fin 4) F2)
    (hs : B.IsSymm) (hd : ∀ i, B i i = 0) (hdet : B.det ≠ 0)
    (S : Finset (Fin 4)) (hS : S.card = 3) : (principalMatrix B S).rank = 2 := by
  let e : Fin 3 ≃ S := (Finset.equivFinOfCardEq hS).symm
  let C := (principalMatrix B S).submatrix e e
  have hCs : C.IsSymm := by
    ext i j
    exact congrArg (fun A => A (e i).val (e j).val) hs.eq
  have hCd : ∀ i, C i i = 0 := fun i => hd (e i).val
  have hCn : C ≠ 0 := by
    intro h
    apply principal_three_nonzero B hs hd hdet S hS
    ext i j
    have hh := congrArg (fun A : Matrix (Fin 3) (Fin 3) F2 => A (e.symm i) (e.symm j)) h
    change C (e.symm i) (e.symm j) = (0 : F2) at hh
    change principalMatrix B S i j = (0 : F2)
    simpa only [C, Matrix.submatrix_apply, e.apply_symm_apply] using hh
  have hr := alternating_three_rank C hCs hCd hCn
  simpa only [C, Matrix.rank_submatrix] using hr

/-- Exact two-coordinate rank: it is two for a nonzero edge, and zero otherwise. -/
theorem alternating_two_rank (C : Matrix (Fin 2) (Fin 2) F2)
    (hs : C.IsSymm) (hd : ∀ i, C i i = 0) :
    C.rank = if C 0 1 = 0 then 0 else 2 := by
  have hs10 : C 1 0 = C 0 1 := congrArg (fun A => A 0 1) hs.eq
  by_cases h : C 0 1 = 0
  · rw [if_pos h]
    have hz : C = 0 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [hd, hs10, h]
    rw [hz, Matrix.rank_zero]
  · rw [if_neg h]
    have hdet : C.det ≠ 0 := by
      rw [Matrix.det_fin_two, hd, hd, zero_mul, zero_sub, hs10]
      exact neg_ne_zero.mpr (mul_ne_zero h h)
    simpa using Matrix.rank_of_det_ne_zero hdet

/-- The statement applies to every two-element principal set and either ordering
of its two distinct vertices. -/
theorem principal_two_rank {n : ℕ} (B : Matrix (Fin n) (Fin n) F2)
    (hs : B.IsSymm) (hd : ∀ i, B i i = 0) (S : Finset (Fin n)) (hS : S.card = 2)
    (i j : S) (hij : i ≠ j) :
    (principalMatrix B S).rank = if B i j = 0 then 0 else 2 := by
  let e₀ : Fin 2 → S := ![i, j]
  have heinj : Function.Injective e₀ := by
    intro x y h
    fin_cases x <;> fin_cases y
    · rfl
    · exact False.elim (hij h)
    · exact False.elim (hij h.symm)
    · rfl
  have hecard : Fintype.card (Fin 2) = Fintype.card S := by simpa using hS.symm
  let e : Fin 2 ≃ S := Equiv.ofBijective e₀
    ((Fintype.bijective_iff_injective_and_card e₀).mpr ⟨heinj, hecard⟩)
  let C := (principalMatrix B S).submatrix e e
  have hCs : C.IsSymm := by
    ext x y
    exact congrArg (fun A => A (e x).val (e y).val) hs.eq
  have hCd : ∀ x, C x x = 0 := fun x => hd (e x).val
  have h := alternating_two_rank C hCs hCd
  have hval : C 0 1 = B i j := rfl
  rw [hval] at h
  simpa only [C, Matrix.rank_submatrix] using h

theorem principal_two_rank_iff {n : ℕ} (B : Matrix (Fin n) (Fin n) F2)
    (hs : B.IsSymm) (hd : ∀ i, B i i = 0) (S : Finset (Fin n)) (hS : S.card = 2)
    (i j : S) (hij : i ≠ j) :
    ((principalMatrix B S).rank = 2 ↔ B i j ≠ 0) ∧
      ((principalMatrix B S).rank = 0 ↔ B i j = 0) := by
  rw [principal_two_rank B hs hd S hS i j hij]
  by_cases h : B i j = 0 <;> simp [h]

theorem principal_empty_rank {n : ℕ} (B : Matrix (Fin n) (Fin n) F2) :
    (principalMatrix B ∅).rank = 0 := by
  have hle := (principalMatrix B ∅).rank_le_card_width
  simpa using hle

/-- Manuscript specialization to the actual inverse polar matrix. -/
theorem inverse_polar_principal_three (Q : Form 4) (hQ : IsUnit (polarMatrix Q).det)
    (S : Finset (Fin 4)) (hS : S.card = 3) :
    (principalMatrix (polarMatrix Q)⁻¹ S).rank = 2 := by
  have hB := InterlaceMoment.inverse_polar_isAdjMatrix Q hQ
  apply principal_three_rank _ hB.symm hB.apply_diag _ S hS
  rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv]
  exact inv_ne_zero (isUnit_iff_ne_zero.mp hQ)

theorem inverse_polar_principal_two (Q : Form 4) (hQ : IsUnit (polarMatrix Q).det)
    (S : Finset (Fin 4)) (hS : S.card = 2) (i j : S) (hij : i ≠ j) :
    (principalMatrix (polarMatrix Q)⁻¹ S).rank =
      if (polarMatrix Q)⁻¹ i j = 0 then 0 else 2 := by
  have hB := InterlaceMoment.inverse_polar_isAdjMatrix Q hQ
  exact principal_two_rank _ hB.symm hB.apply_diag S hS i j hij

#print axioms alternating_rank_ge_two
#print axioms alternating_three_rank
#print axioms principal_three_rank
#print axioms principal_two_rank_iff
#print axioms inverse_polar_principal_three
#print axioms inverse_polar_principal_two
end Hellinger.SmallPrincipalRanks
