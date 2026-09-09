import Hellinger.ColumnSelection
import Hellinger.ShearNoise

/-! The selected input coordinates and remaining coordinates form an actual
equivalence of cubes. This equivalence preserves the product BSC exactly. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.PivotCoordinates
open F2Model ChannelSections

variable {n k : ℕ}

abbrev Remaining (a : Fin k ↪ Fin n) := {j : Fin n // j ∉ Set.range a}

noncomputable instance remainingFintype (a : Fin k ↪ Fin n) : Fintype (Remaining a) :=
  Fintype.ofFinite _

def indexEquiv (a : Fin k ↪ Fin n) : Fin k ⊕ Remaining a ≃ Fin n := by
  classical
  exact (Equiv.sumCongr (Equiv.ofInjective a a.injective) (Equiv.refl _)).trans
    (Equiv.sumCompl (fun j => j ∈ Set.range a))

@[simp] theorem indexEquiv_inl (a : Fin k ↪ Fin n) (i : Fin k) :
    indexEquiv a (Sum.inl i) = a i := rfl

@[simp] theorem indexEquiv_inr (a : Fin k ↪ Fin n) (i : Remaining a) :
    indexEquiv a (Sum.inr i) = i.val := rfl

def coordinates (a : Fin k ↪ Fin n) : Cube n ≃ (Cube k × (Remaining a → F2)) :=
  (Equiv.arrowCongr (indexEquiv a).symm (Equiv.refl F2)).trans
    (Equiv.sumArrowEquivProdArrow (Fin k) (Remaining a) F2)

@[simp] theorem coordinates_fst (a : Fin k ↪ Fin n) (x : Cube n) (i : Fin k) :
    (coordinates a x).1 i = x (a i) := rfl

@[simp] theorem coordinates_snd (a : Fin k ↪ Fin n) (x : Cube n) (i : Remaining a) :
    (coordinates a x).2 i = x i.val := rfl

def coordinatesLinear (a : Fin k ↪ Fin n) : Cube n ≃ₗ[F2] (Cube k × (Remaining a → F2)) :=
  { coordinates a with
    map_add' := fun _ _ => rfl
    map_smul' := fun _ _ => rfl }

@[simp] theorem coordinatesLinear_apply (a : Fin k ↪ Fin n) (x : Cube n) :
    coordinatesLinear a x = coordinates a x := rfl

theorem noise_weight_coordinates (a : Fin k ↪ Fin n) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (x y : Cube n) :
    (productChannel (noise (Fin k) ρ hρ) (noise (Remaining a) ρ hρ)).weight
      (coordinates a x) (coordinates a y) = (noise (Fin n) ρ hρ).weight x y := by
  have h := (indexEquiv a).prod_comp (fun i => (oneStep ρ hρ).weight (x i) (y i))
  rw [Fintype.prod_sum_type] at h
  exact h

theorem noise_apply_coordinates (a : Fin k ↪ Fin n) (ρ : ℝ)
    (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (g : (Cube k × (Remaining a → F2)) → ℝ) (x : Cube n) :
    (noise (Fin n) ρ hρ).apply (g ∘ coordinates a) x =
      (productChannel (noise (Fin k) ρ hρ) (noise (Remaining a) ρ hρ)).apply g (coordinates a x) := by
  unfold UniformChannel.apply
  rw [← (coordinates a).sum_comp
    (fun y => (productChannel (noise (Fin k) ρ hρ) (noise (Remaining a) ρ hρ)).weight
      (coordinates a x) y * g y)]
  simp only [noise_weight_coordinates, Function.comp_apply]

theorem selected_single (a : Fin k ↪ Fin n) (i : Fin k) :
    coordinatesLinear a (Pi.single (a i) 1) = (Pi.single i 1, 0) := by
  apply Prod.ext
  · funext j
    simp [coordinatesLinear, coordinates, indexEquiv, Pi.single_apply, a.injective.eq_iff]
  · funext j
    have hne : j.val ≠ a i := by
      intro h
      exact j.property ⟨i, h.symm⟩
    simp [coordinatesLinear, coordinates, indexEquiv, hne]

theorem selected_assembly (a : Fin k ↪ Fin n) (x : Cube k) :
    (coordinatesLinear a).symm (x, 0) = ∑ i, x i • Pi.single (a i) 1 := by
  apply (coordinatesLinear a).injective
  simp only [LinearEquiv.apply_symm_apply, map_sum, map_smul, selected_single,
    Prod.smul_mk, smul_zero]
  apply Prod.ext
  · simp [Prod.fst_sum, ← Pi.single_smul, Finset.univ_sum_single]
  · simp [Prod.snd_sum]

theorem quotient_assembly (a : Fin k ↪ Fin n) (b : Module.Basis (Fin k) F2 (Cube k))
    (L : Cube n →ₗ[F2] Cube k) (hb : ∀ i, b i = L (Pi.single (a i) 1)) (x : Cube k) :
    L ((coordinatesLinear a).symm (x, 0)) = b.equivFun.symm x := by
  rw [selected_assembly, map_sum, Module.Basis.equivFun_symm_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [map_smul, hb]

def outsideLinear (a : Fin k ↪ Fin n) : (Remaining a → F2) →ₗ[F2] Cube n :=
  (coordinatesLinear a).symm.toLinearMap.comp (LinearMap.inr F2 (Cube k) (Remaining a → F2))

def quotientShear (a : Fin k ↪ Fin n) (b : Module.Basis (Fin k) F2 (Cube k))
    (L : Cube n →ₗ[F2] Cube k) : (Remaining a → F2) →ₗ[F2] Cube k :=
  b.equivFun.toLinearMap.comp (L.comp (outsideLinear a))

theorem quotient_coordinate_formula (a : Fin k ↪ Fin n) (b : Module.Basis (Fin k) F2 (Cube k))
    (L : Cube n →ₗ[F2] Cube k) (hb : ∀ i, b i = L (Pi.single (a i) 1))
    (x : Cube k) (z : Remaining a → F2) :
    L ((coordinates a).symm (x, z)) = b.equivFun.symm (x + quotientShear a b L z) := by
  have hsplit : (x, z) = (x, 0) + (0, z) := by simp
  change L ((coordinatesLinear a).symm (x, z)) = _
  rw [hsplit, map_add, map_add, quotient_assembly a b L hb x, map_add]
  congr 1
  exact (b.equivFun.symm_apply_apply (L (outsideLinear a z))).symm

end Hellinger.PivotCoordinates
