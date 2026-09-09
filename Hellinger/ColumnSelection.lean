import Hellinger.F2Model
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.StdBasis

/-! A genuine choice of independent input columns of a surjective map.
The coordinate basis is extracted from surjectivity, not assumed. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.ColumnSelection
open F2Model

theorem span_columns_eq_top (n k : ℕ) (L : Cube n →ₗ[F2] Cube k)
    (hL : Function.Surjective L) :
    Submodule.span F2 (Set.range (fun i : Fin n => L (Pi.single i 1))) = ⊤ := by
  have h := congrArg (Submodule.map L) (Pi.basisFun F2 (Fin n)).span_eq
  rw [Submodule.map_span, Submodule.map_top, LinearMap.range_eq_top.mpr hL] at h
  simpa only [← Set.range_comp, Function.comp_def, Pi.basisFun_apply] using h

theorem exists_column_basis (n k : ℕ) (L : Cube n →ₗ[F2] Cube k)
    (hL : Function.Surjective L) :
    ∃ (a : Fin k ↪ Fin n) (b : Module.Basis (Fin k) F2 (Cube k)),
      ∀ i, b i = L (Pi.single (a i) 1) := by
  classical
  obtain ⟨κ, a, ha, hs, hi⟩ :=
    exists_linearIndependent' F2 (fun i : Fin n => L (Pi.single i 1))
  let : Finite κ := Finite.of_injective a ha
  let : Fintype κ := Fintype.ofFinite κ
  let b : Module.Basis κ F2 (Cube k) := Module.Basis.mk hi (by
    rw [hs, span_columns_eq_top n k L hL])
  have hcard : Fintype.card κ = k := by
    rw [← Module.finrank_eq_card_basis b]
    simp [Cube, Module.finrank_fintype_fun_eq_card]
  let e : κ ≃ Fin k := (Fintype.equivFin κ).trans (finCongr hcard)
  refine ⟨⟨a ∘ e.symm, ha.comp e.symm.injective⟩, b.reindex e, ?_⟩
  intro i
  simp only [Module.Basis.reindex_apply, b, Module.Basis.mk_apply, Function.comp_apply]
  rfl

end Hellinger.ColumnSelection
