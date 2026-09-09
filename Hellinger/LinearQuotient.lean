import Hellinger.PivotCoordinates

/-! Full finite linear-quotient comparison for the actual additive BSC.
One invertible output coordinate map works for every noise parameter and
every convex function. No posterior formula or pivot basis is assumed. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.LinearQuotient
open F2Model ChannelSections PivotCoordinates ShearNoise

theorem linear_quotient_comparison (n k : ℕ) (L : Cube n →ₗ[F2] Cube k)
    (hL : Function.Surjective L) (g : Cube k → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ M : Cube k ≃ₗ[F2] Cube k,
      mean (g ∘ M) = mean (g ∘ L) ∧
      ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
        (Ψ : ℝ → ℝ), ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) Ψ →
        mean (fun y => Ψ ((noise (Fin n) ρ hρ).apply (g ∘ L) y)) ≤
          mean (fun y => Ψ ((noise (Fin k) ρ hρ).apply (g ∘ M) y)) := by
  obtain ⟨a, b, hb⟩ := ColumnSelection.exists_column_basis n k L hL
  let M := b.equivFun.symm
  let D := quotientShear a b L
  let F := shearFunction (g ∘ M) D
  have hfun : F ∘ coordinates a = g ∘ L := by
    funext x
    have h := quotient_coordinate_formula a b L hb (coordinates a x).1 (coordinates a x).2
    simp only [Prod.mk.eta, Equiv.symm_apply_apply] at h
    exact congrArg g h.symm
  refine ⟨M, ?_, ?_⟩
  · have h := mean_comp_equiv (coordinates a) F
    rw [hfun, mean_shear] at h
    exact h.symm
  · intro ρ hρ Ψ hΨ
    calc
      _ = mean ((fun p => Ψ ((productChannel (noise (Fin k) ρ hρ)
          (noise (Remaining a) ρ hρ)).apply F p)) ∘ coordinates a) := by
        congr 1
        funext y
        rw [← hfun, noise_apply_coordinates]
        rfl
      _ = mean (fun p => Ψ ((productChannel (noise (Fin k) ρ hρ)
          (noise (Remaining a) ρ hρ)).apply F p)) := mean_comp_equiv _ _
      _ ≤ _ := shear_convex_comparison ρ hρ (g ∘ M) (fun x => hg _) D Ψ hΨ

theorem linear_quotient_objective_comparison (n k : ℕ) (L : Cube n →ₗ[F2] Cube k)
    (hL : Function.Surjective L) (g : Cube k → ℝ)
    (hg : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1) :
    ∃ M : Cube k ≃ₗ[F2] Cube k,
      mean (g ∘ M) = mean (g ∘ L) ∧
      ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1),
        objective ((noise (Fin n) ρ hρ).apply (g ∘ L)) ≤
          objective ((noise (Fin k) ρ hρ).apply (g ∘ M)) := by
  obtain ⟨M, hm, h⟩ := linear_quotient_comparison n k L hL g hg
  refine ⟨M, hm, ?_⟩
  intro ρ hρ
  have hc := h ρ hρ (fun t => -root t) root_concave.neg
  rw [mean_neg, mean_neg] at hc
  simp only [objective, UniformChannel.mean_apply]
  rw [hm]
  linarith

theorem linear_quotient_boolean (n k : ℕ) (L : Cube n →ₗ[F2] Cube k)
    (hL : Function.Surjective L) (g : Cube k → ℝ)
    (hg : ∀ x, g x = -1 ∨ g x = 1) :
    ∃ g₀ : Cube k → ℝ, (∀ x, g₀ x = -1 ∨ g₀ x = 1) ∧
      mean g₀ = mean (g ∘ L) ∧
      ∀ (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
        (Ψ : ℝ → ℝ), ConvexOn ℝ (Set.Icc (-1 : ℝ) 1) Ψ →
        mean (fun y => Ψ ((noise (Fin n) ρ hρ).apply (g ∘ L) y)) ≤
          mean (fun y => Ψ ((noise (Fin k) ρ hρ).apply g₀ y)) := by
  have hgc : ∀ x, g x ∈ Set.Icc (-1 : ℝ) 1 := by
    intro x
    rcases hg x with hx | hx <;> simp [hx]
  obtain ⟨M, hm, h⟩ := linear_quotient_comparison n k L hL g hgc
  exact ⟨g ∘ M, (fun x => hg _), hm, h⟩

#print axioms linear_quotient_comparison
#print axioms linear_quotient_objective_comparison

end Hellinger.LinearQuotient
