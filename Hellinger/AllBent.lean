import Hellinger.BentSmall
import Hellinger.BentFourFinal
import Hellinger.FlatnessConsequences
import Hellinger.PaperSpecs

/-! The complete manuscript bent-function Hellinger theorem. -/
set_option autoImplicit false
noncomputable section
namespace Hellinger.AllBent
open Fourier

/-- Every positive-dimensional bent Boolean function satisfies the all-noise
Hellinger inequality, with strictness for every positive correlation. -/
theorem bent_hellinger (n : ℕ) (hn : 0 < n) (f : Cube n → ℝ)
    (hf : ∀ x, f x = -1 ∨ f x = 1) (hb : Flatness.IsBent f)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) :
    objective ((cubeBSC n ρ hρ).apply f) ≤ 1 - root ρ ∧
      (0 < ρ → objective ((cubeBSC n ρ hρ).apply f) < 1 - root ρ) := by
  have heven := Flatness.dimension_even hf hb
  by_cases hn2 : n = 2
  · subst n
    exact ⟨BentSmall.bent_two_hellinger f hf hb ρ hρ,
      fun hp => BentSmall.bent_two_hellinger_strict f hf hb ρ hρ hp⟩
  · by_cases hn4 : n = 4
    · subst n
      exact BentFourFinal.bent_four_hellinger f hf hb ρ hρ
    · obtain ⟨k, hk⟩ := heven
      have hn6 : 6 ≤ n := by omega
      exact BentLow.bent_large_hellinger hn6 hf hb ρ hρ

/-- Direct inhabitant of the independently declared full manuscript target. -/
theorem paper_bent_hellinger : PaperSpecs.BentHellinger := by
  intro n hn f hf hb ρ hρ
  exact bent_hellinger n hn f hf hb ρ hρ

#print axioms bent_hellinger
#print axioms paper_bent_hellinger
end Hellinger.AllBent
