import Hellinger.AntipodalEquality
import Hellinger.ChannelSections
import Hellinger.StrictJensen

/-! Equality classification for every nonempty set of flipped coordinates. -/

set_option autoImplicit false
noncomputable section
open scoped BigOperators

namespace Hellinger.TranslationEquality

open Hellinger.ChannelSections

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem indexed_antipodal_root_equality [Nonempty ι]
    (f : (ι → Bool) → ℝ) (hf : ∀ x, f x = -1 ∨ f x = 1)
    (hanti : ∀ x, f (fun i => !(x i)) = -f x)
    (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) (hρlt : ρ < 1)
    (heq : mean (fun y => root ((indexedBSC ι ρ hρ).apply f y)) = root ρ) :
    ∃ i : ι, ∃ negative : Bool,
      f = fun x => if negative then -boolSign (x i) else boolSign (x i) := by
  let n := Fintype.card ι - 1
  have hn : Fintype.card ι = n + 1 := by
    have := Fintype.card_pos (α := ι)
    omega
  let e : ι ≃ Fin (n + 1) := (Fintype.equivFin ι).trans (finCongr hn)
  let g : (Fin (n + 1) → Bool) → ℝ := f ∘ cubeEquiv e.symm
  have hg : ∀ x, g x = -1 ∨ g x = 1 := fun x => hf _
  have hga : ∀ x, g (antipode (n + 1) x) = -g x := fun x => hanti _
  have hcomp : g ∘ cubeEquiv e = f := by
    funext x
    exact congrArg f ((cubeEquiv e).symm_apply_apply x)
  have hpoint (x : ι → Bool) :
      (indexedBSC ι ρ hρ).apply f x =
        (cubeBSC (n + 1) ρ hρ).apply g (cubeEquiv e x) := by
    rw [← hcomp]
    exact indexedBSC_apply_reindex e ρ hρ g x
  have hgeq : mean (fun y => root ((cubeBSC (n + 1) ρ hρ).apply g y)) = root ρ := by
    rw [← mean_comp_equiv (cubeEquiv e)]
    change mean (fun x : ι → Bool =>
      root ((cubeBSC (n + 1) ρ hρ).apply g (cubeEquiv e x))) = root ρ
    simp_rw [← hpoint]
    exact heq
  obtain ⟨i, negative, hform⟩ :=
    (AntipodalEquality.root_mean_equality_iff_signed_dictator
      n g hg hga ρ hρ hρpos hρlt).mp hgeq
  refine ⟨e.symm i, negative, ?_⟩
  funext x
  have h := congrFun hform (cubeEquiv e x)
  change (g ∘ cubeEquiv e) x = _ at h
  rw [hcomp] at h
  exact h

theorem indexedBSC_weight_pos (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρlt : ρ < 1)
    (x y : ι → Bool) : 0 < (indexedBSC ι ρ hρ).weight x y := by
  apply Finset.prod_pos
  intro i _
  exact PosteriorGram.bsc_weight_pos ρ hρ hρlt (x i) (y i)

theorem cubeBSC_injective (n : ℕ) (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1)
    (hρpos : 0 < ρ) : Function.Injective (cubeBSC n ρ hρ).apply := by
  intro f g heq
  have hw (s : Fourier.Cube n) : Fourier.walsh f s = Fourier.walsh g s := by
    have h := congrArg (fun h => Fourier.walsh h s) heq
    simp only [Fourier.walsh_noise] at h
    exact mul_left_cancel₀ (pow_ne_zero _ (ne_of_gt hρpos)) h
  funext x
  rw [Fourier.inversion f x, Fourier.inversion g x]
  simp only [hw]

theorem indexedBSC_injective (ρ : ℝ) (hρ : ρ ∈ Set.Icc (0 : ℝ) 1) (hρpos : 0 < ρ) :
    Function.Injective (indexedBSC ι ρ hρ).apply := by
  intro f g heq
  let e : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  have hpre : (cubeBSC (Fintype.card ι) ρ hρ).apply (f ∘ cubeEquiv e.symm) =
      (cubeBSC (Fintype.card ι) ρ hρ).apply (g ∘ cubeEquiv e.symm) := by
    funext x
    change (indexedBSC (Fin (Fintype.card ι)) ρ hρ).apply (f ∘ cubeEquiv e.symm) x =
      (indexedBSC (Fin (Fintype.card ι)) ρ hρ).apply (g ∘ cubeEquiv e.symm) x
    rw [indexedBSC_apply_reindex, indexedBSC_apply_reindex]
    exact congrFun heq _
  have hfg := cubeBSC_injective (Fintype.card ι) ρ hρ hρpos hpre
  funext x
  have h := congrFun hfg (cubeEquiv e x)
  change f ((cubeEquiv e).symm (cubeEquiv e x)) =
    g ((cubeEquiv e).symm (cubeEquiv e x)) at h
  simpa only [Equiv.symm_apply_apply] using h

variable {Ω Λ : Type*} [Fintype Ω] [Fintype Λ] [Nonempty Ω] [Nonempty Λ]

theorem sections_equal_of_root_mean_equality
    (K : UniformChannel Ω) (L : UniformChannel Λ)
    (f : Ω × Λ → ℝ) (hf : ∀ p, f p ∈ Set.Icc (-1 : ℝ) 1)
    (hpos : ∀ y x, 0 < L.weight y x)
    (heq : mean (fun p => root ((productChannel K L).apply f p)) =
      mean (fun z => mean (fun y => root (K.apply (fun x => f (x, z)) y)))) :
    ∀ y z w, K.apply (fun x => f (x, z)) y = K.apply (fun x => f (x, w)) y := by
  let u : Ω → Λ → ℝ := fun y z => K.apply (fun x => f (x, z)) y
  have hu (y : Ω) (z : Λ) : u y z ∈ Set.Icc (-1 : ℝ) 1 :=
    K.apply_mem_Icc _ (fun x => hf (x, z)) y
  have hle (y : Ω) : mean (fun z => root (u y z)) ≤
      mean (fun z => root (L.apply (u y) z)) :=
    L.concave_mean_expands (u y) root root_concave (hu y)
  have hswap := mean_prod_swap (fun p : Ω × Λ => root (u p.1 p.2))
  rw [mean_prod] at hswap
  have hmeans : mean (fun y => mean (fun z => root (u y z))) =
      mean (fun y => mean (fun z => root (L.apply (u y) z))) := by
    rw [hswap]
    rw [mean_prod] at heq
    simpa only [productChannel_apply] using heq.symm
  have hpoint := eq_of_mean_eq_of_le _ _ hle hmeans
  intro y z w
  exact (L.root_mean_equality_iff (u y) (hu y) hpos).mp (hpoint y).symm z w

theorem sections_of_bound_equality (K : UniformChannel Ω) (L : UniformChannel Λ)
    (f : Ω × Λ → ℝ) (hf : ∀ p, f p ∈ Set.Icc (-1 : ℝ) 1)
    (hpos : ∀ y x, 0 < L.weight y x) (c : ℝ)
    (hsec : ∀ z, c ≤ mean (fun y => root (K.apply (fun x => f (x, z)) y)))
    (heq : mean (fun p => root ((productChannel K L).apply f p)) = c) :
    (∀ z, mean (fun y => root (K.apply (fun x => f (x, z)) y)) = c) ∧
      ∀ y z w, K.apply (fun x => f (x, z)) y = K.apply (fun x => f (x, w)) y := by
  have hl := mean_mono (fun _ : Λ => c) _ hsec
  rw [mean_const] at hl
  have hu := sections_root_mean_le K L f hf
  have hm : mean (fun z => mean (fun y => root (K.apply (fun x => f (x, z)) y))) = c := by
    rw [heq] at hu
    exact le_antisymm hu hl
  constructor
  · have h := eq_of_mean_eq_of_le (fun _ : Λ => c) _ hsec (by rw [mean_const, hm])
    exact fun z => (h z).symm
  · exact sections_equal_of_root_mean_equality K L f hf hpos (heq.trans hm.symm)

theorem translation_equality : PaperSpecs.TranslationEquality := by
  intro n f hf S hS hanti ρ hρ hρpos hρlt
  constructor
  · intro heq
    let : Fintype {i : Fin n // i ∈ S} := Subtype.fintype (fun i : Fin n => i ∈ S)
    have : Nonempty {i : Fin n // i ∈ S} := by
      obtain ⟨i, hi⟩ := hS
      exact ⟨⟨i, hi⟩⟩
    let e := splitCube (fun i : Fin n => i ∈ S)
    let g : (({i : Fin n // i ∈ S} → Bool) × ({i : Fin n // i ∉ S} → Bool)) → ℝ :=
      f ∘ e.symm
    let K := indexedBSC {i : Fin n // i ∈ S} ρ hρ
    let L := indexedBSC {i : Fin n // i ∉ S} ρ hρ
    have hgf (x) : g x = -1 ∨ g x = 1 := hf _
    have hgc (x) : g x ∈ Set.Icc (-1 : ℝ) 1 := by
      rcases hgf x with hx | hx <;> simp [hx]
    have hga (z : {i : Fin n // i ∉ S} → Bool)
        (w : {i : Fin n // i ∈ S} → Bool) : g ((fun i => !(w i)), z) = -g (w, z) := by
      change f ((splitCube (fun i => i ∈ S)).symm ((fun i => !(w i)), z)) = _
      rw [split_flip_section]
      exact hanti _
    have hsec (z : {i : Fin n // i ∉ S} → Bool) :
        root ρ ≤ mean (fun y => root (K.apply (fun w => g (w, z)) y)) :=
      indexed_antipodal_hellinger _ (fun w => hgf (w, z)) (hga z) ρ hρ
    have hcomp : g ∘ e = f := by
      funext x
      exact congrArg f (e.symm_apply_apply x)
    have hpoint (x : Fin n → Bool) :
        (cubeBSC n ρ hρ).apply f x = (productChannel K L).apply g (e x) := by
      rw [← hcomp]
      exact indexedBSC_apply_split (fun i => i ∈ S) ρ hρ g x
    have hgeq : mean (fun y => root ((productChannel K L).apply g y)) = root ρ := by
      rw [← mean_comp_equiv e]
      change mean (fun x : Fin n → Bool => root ((productChannel K L).apply g (e x))) = _
      simp_rw [← hpoint]
      exact heq
    obtain ⟨hseceq, hsmoothed⟩ := sections_of_bound_equality K L g hgc
      (indexedBSC_weight_pos ρ hρ hρlt) (root ρ) hsec hgeq
    let z0 : {i : Fin n // i ∉ S} → Bool := fun _ => false
    obtain ⟨i, negative, hform⟩ := indexed_antipodal_root_equality
      (fun w => g (w, z0)) (fun w => hgf (w, z0)) (hga z0) ρ hρ hρpos hρlt (hseceq z0)
    have hsections (z : {i : Fin n // i ∉ S} → Bool) :
        (fun w => g (w, z)) = fun w => g (w, z0) := by
      apply indexedBSC_injective ρ hρ hρpos
      funext y
      exact hsmoothed y z z0
    refine ⟨i.1, i.2, negative, ?_⟩
    funext x
    have h := (congrFun (hsections (e x).2) (e x).1).trans (congrFun hform (e x).1)
    change g (e x) = _ at h
    change (g ∘ e) x = _ at h
    rw [hcomp] at h
    exact h
  · rintro ⟨i, hi, negative, hform⟩
    have hm : mean f = 0 := mean_eq_zero_of_sign_reversing (flipEquiv n S) f hanti
    have hobj : objective ((cubeBSC n ρ hρ).apply f) = 1 - root ρ := by
      rw [hform]
      exact bsc_signed_dictator_equality n i negative ρ hρ
    unfold objective at hobj
    rw [UniformChannel.mean_apply, hm] at hobj
    have hz : root (0 : ℝ) = 1 := by norm_num [root]
    rw [hz] at hobj
    change mean (fun y => root ((cubeBSC n ρ hρ).apply f y)) = root ρ
    linarith

#print axioms cubeBSC_injective
#print axioms sections_of_bound_equality
#print axioms translation_equality

end Hellinger.TranslationEquality
