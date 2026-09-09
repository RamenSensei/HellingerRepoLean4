import Hellinger.FiniteChannel
import Mathlib.Algebra.Group.Units.Equiv

/-! Additional convolution noise as a uniform-measure-preserving channel.
This supplies the Jensen step in the linear-quotient argument; the identification
of a quotient posterior with this convolution is a separate remaining step. -/

set_option autoImplicit false
open scoped BigOperators

namespace Hellinger

variable {G : Type*} [Fintype G] [AddCommGroup G]

noncomputable def convolution (p f : G → ℝ) (x : G) : ℝ :=
  ∑ e, p e * f (x + e)

noncomputable def translationChannel (p : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1) : UniformChannel G where
  weight x y := p (y - x)
  nonneg x y := hp (y - x)
  row_sum x := by
    calc
      (∑ y, p (y - x)) = ∑ e, p e := (Equiv.subRight x).sum_comp p
      _ = 1 := hs
  column_sum y := by
    calc
      (∑ x, p (y - x)) = ∑ e, p e := (Equiv.subLeft y).sum_comp p
      _ = 1 := hs

theorem translationChannel_apply (p f : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1) (x : G) :
    (translationChannel p hp hs).apply f x = convolution p f x := by
  unfold UniformChannel.apply translationChannel convolution
  symm
  apply Fintype.sum_equiv (Equiv.addLeft x)
  intro e
  simp

theorem convolution_preserves_mean (p f : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1) :
    mean (convolution p f) = mean f := by
  have hfun : (translationChannel p hp hs).apply f = convolution p f := by
    funext x
    exact translationChannel_apply p f hp hs x
  rw [← hfun]
  exact UniformChannel.mean_apply _ _

theorem convolution_objective_le (p f : G → ℝ)
    (hp : ∀ e, 0 ≤ p e) (hs : ∑ e, p e = 1)
    (hf : ∀ x, f x ∈ Set.Icc (-1 : ℝ) 1) :
    objective (convolution p f) ≤ objective f := by
  have hfun : (translationChannel p hp hs).apply f = convolution p f := by
    funext x
    exact translationChannel_apply p f hp hs x
  rw [← hfun]
  exact objective_channel_le _ _ hf

#print axioms convolution_preserves_mean
#print axioms convolution_objective_le

end Hellinger
