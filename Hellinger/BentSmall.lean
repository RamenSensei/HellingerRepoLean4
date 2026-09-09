import Hellinger.Flatness
import Hellinger.TwoBitCase

/-! Definition bridges for the actual normalized Walsh conventions. -/
set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.BentSmall

theorem normalizedWalsh_eq (f : Fourier.Cube 2 → ℝ) (s : Bool × Bool) :
    TwoBitCase.normalizedWalsh f s = Fourier.walsh f ![s.1, s.2] := by
  unfold TwoBitCase.normalizedWalsh Fourier.walsh
  congr 1
  funext x
  congr 1
  rcases s with ⟨s₀, s₁⟩
  cases s₀ <;> cases s₁ <;> cases hx₀ : x 0 <;> cases hx₁ : x 1 <;>
    norm_num [Fourier.phase, Fin.prod_univ_two, boolSign, hx₀, hx₁]

theorem flatness_implies_isBent2 (f : Fourier.Cube 2 → ℝ) (hb : Flatness.IsBent f) :
    TwoBitCase.IsBent2 f := by
  intro s
  rw [normalizedWalsh_eq, hb]
  norm_num

theorem bent_two_hellinger (f : Fourier.Cube 2 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC 2 ρ hρ).apply f) ≤ 1 - root ρ :=
  TwoBitCase.bent2_hellinger f hf (flatness_implies_isBent2 f hb) ρ hρ

theorem bent_two_hellinger_strict (f : Fourier.Cube 2 → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) :
    objective ((cubeBSC 2 ρ hρ).apply f) < 1 - root ρ :=
  TwoBitCase.bent2_hellinger_strict f hf (flatness_implies_isBent2 f hb) ρ hρ hρpos

#print axioms bent_two_hellinger
#print axioms bent_two_hellinger_strict
end Hellinger.BentSmall
