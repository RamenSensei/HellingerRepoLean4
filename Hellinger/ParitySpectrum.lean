import Mathlib.Data.Nat.Choose.Sum
import Mathlib.Data.Real.Basic
import Mathlib.Tactic

set_option autoImplicit false

/-!
# Parity-spectrum layer calculation

This file formalizes the dimension-independent alternating-binomial and
weighted-layer calculations, a finite layer-cake identity for sorted lists,
and the resulting scalar parity-spectrum distance from explicit multiplicity
hypotheses. The identification with restrictions of concrete product-state
matrices is outside this file; the precise scope is recorded in
`formal/notes/parity.md`.
-/

namespace Hellinger.ParitySpectrum

open Finset

/-- The alternating partial sum, with dimension written as `n + 1`.
It remains valid even when the cut index is beyond the dimension. -/
theorem alternating_partial_choose (n k : ℕ) :
    (∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ)) =
      (-1 : ℝ) ^ k * (n.choose k : ℝ) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [sum_range_succ, ih, Nat.choose_succ_succ]
      push_cast
      rw [pow_succ]
      ring

/-- Absolute cumulative parity imbalance is a binomial coefficient. -/
theorem abs_alternating_partial_choose (n k : ℕ) :
    |∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * ((n + 1).choose j : ℝ)| =
      (n.choose k : ℝ) := by
  rw [alternating_partial_choose, abs_mul, abs_pow]
  simp

/-- The product-state spectral level of Hamming weight `k`. -/
def spectralLevel (n k : ℕ) (a b : ℝ) : ℝ := a ^ (n - k) * b ^ k

/-- Factoring the gap between successive levels uses the restriction `k ≤ n`. -/
theorem spectralLevel_gap (n k : ℕ) (a b : ℝ) (hk : k ≤ n) :
    spectralLevel (n + 1) k a b - spectralLevel (n + 1) (k + 1) a b =
      (a - b) * a ^ (n - k) * b ^ k := by
  unfold spectralLevel
  have h₁ : n + 1 - k = n - k + 1 := by omega
  have h₂ : n + 1 - (k + 1) = n - k := by omega
  rw [h₁, h₂, pow_succ, pow_succ]
  ring

/-- Exact weighted layer-gap sum in every positive dimension. -/
theorem weighted_layer_gaps (n : ℕ) (a b : ℝ) :
    (∑ k ∈ range (n + 1), (n.choose k : ℝ) *
      (spectralLevel (n + 1) k a b - spectralLevel (n + 1) (k + 1) a b)) =
      (a - b) * (a + b) ^ n := by
  calc
    _ = ∑ k ∈ range (n + 1),
        (a - b) * (b ^ k * a ^ (n - k) * (n.choose k : ℝ)) := by
      apply sum_congr rfl
      intro k hk
      rw [spectralLevel_gap n k a b (by simpa using mem_range.mp hk)]
      ring
    _ = (a - b) * ∑ k ∈ range (n + 1),
        b ^ k * a ^ (n - k) * (n.choose k : ℝ) := by rw [mul_sum]
    _ = (a - b) * (b + a) ^ n := by rw [← add_pow]
    _ = (a - b) * (a + b) ^ n := by rw [add_comm b a]

/-- The discrete layer-cake expression before identifying it with a distance
between sorted eigenvalue lists. -/
def parityLayerDistance (n : ℕ) (a b : ℝ) : ℝ :=
  ∑ k ∈ range n,
    |∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ)| *
      (spectralLevel n k a b - spectralLevel n (k + 1) a b)

/-- Evaluation of the layer-cake side; this is not yet the sorting bridge. -/
theorem parityLayerDistance_succ (n : ℕ) (a b : ℝ) :
    parityLayerDistance (n + 1) a b = (a - b) * (a + b) ^ n := by
  unfold parityLayerDistance
  simp_rw [abs_alternating_partial_choose]
  exact weighted_layer_gaps n a b

/-- Algebraic normalization of the layer expression. This identity holds for
all real `c`; its interpretation as an ℓ¹-distance uses `0 ≤ c ≤ 1` below. -/
theorem parityLayerDistance_normalized (n : ℕ) (c : ℝ) :
    parityLayerDistance (n + 1) ((1 + c) / 2) ((1 - c) / 2) = c := by
  rw [parityLayerDistance_succ]
  have hadd : (1 + c) / 2 + (1 - c) / 2 = (1 : ℝ) := by ring
  have hsub : (1 + c) / 2 - (1 - c) / 2 = c := by ring
  rw [hadd, hsub, one_pow, mul_one]

/-! ## Finite layer-cake bridge -/

/-- The real-valued indicator of a level being at or before a cut. -/
def cutIndicator (s k : ℕ) : ℝ := if s ≤ k then 1 else 0

theorem cutIndicator_antitone (s t k : ℕ) (hst : s ≤ t) :
    cutIndicator t k ≤ cutIndicator s k := by
  by_cases htk : t ≤ k
  · have hsk : s ≤ k := hst.trans htk
    simp [cutIndicator, htk, hsk]
  · simp only [cutIndicator, if_neg htk]
    split_ifs <;> norm_num

/-- Telescoping a list of gaps starting at an arbitrary level. -/
theorem sum_gaps_cutIndicator (level : ℕ → ℝ) (d s : ℕ) (hs : s ≤ d) :
    (∑ k ∈ range d, (level k - level (k + 1)) * cutIndicator s k) =
      level s - level d := by
  induction d generalizing s with
  | zero =>
      have : s = 0 := by omega
      subst s
      simp
  | succ d ih =>
      by_cases hsd : s ≤ d
      · rw [sum_range_succ, ih s hsd]
        simp only [cutIndicator, if_pos hsd, mul_one]
        ring
      · have hse : s = d + 1 := by omega
        subst s
        have hz : (∑ k ∈ range (d + 1),
            (level k - level (k + 1)) * cutIndicator (d + 1) k) = 0 := by
          apply sum_eq_zero
          intro k hk
          have hnot : ¬d + 1 ≤ k := by simpa using mem_range.mp hk
          simp [cutIndicator, hnot]
        simpa using hz

/-- Scalar discrete layer cake. Only finite monotonicity of the levels is needed. -/
theorem abs_level_sub_eq_sum_gaps (level : ℕ → ℝ) (d s t : ℕ)
    (hlevel : ∀ i j, i ≤ j → j ≤ d → level j ≤ level i)
    (hs : s ≤ d) (ht : t ≤ d) :
    |level s - level t| =
      ∑ k ∈ range d, (level k - level (k + 1)) *
        |cutIndicator s k - cutIndicator t k| := by
  have hsum :
      (∑ k ∈ range d, (level k - level (k + 1)) *
        (cutIndicator s k - cutIndicator t k)) = level s - level t := by
    simp_rw [mul_sub]
    rw [sum_sub_distrib, sum_gaps_cutIndicator level d s hs,
      sum_gaps_cutIndicator level d t ht]
    ring
  rcases le_total s t with hst | hts
  · rw [abs_of_nonneg (sub_nonneg.mpr (hlevel s t hst ht))]
    calc
      level s - level t = ∑ k ∈ range d, (level k - level (k + 1)) *
          (cutIndicator s k - cutIndicator t k) := hsum.symm
      _ = _ := by
        apply sum_congr rfl
        intro k _
        rw [abs_of_nonneg (sub_nonneg.mpr (cutIndicator_antitone s t k hst))]
  · rw [abs_of_nonpos (sub_nonpos.mpr (hlevel t s hts hs))]
    calc
      -(level s - level t) = -∑ k ∈ range d, (level k - level (k + 1)) *
          (cutIndicator s k - cutIndicator t k) := congrArg Neg.neg hsum.symm
      _ = ∑ k ∈ range d, (level k - level (k + 1)) *
          |cutIndicator s k - cutIndicator t k| := by
        rw [← sum_neg_distrib]
        apply sum_congr rfl
        intro k _
        rw [abs_of_nonpos (sub_nonpos.mpr (cutIndicator_antitone t s k hts))]
        ring

/-- Two initial segments of a linear order are nested. Consequently all
indicator differences at a fixed cut have the same sign. -/
theorem monotone_cuts_nested {ι : Type*} [LinearOrder ι]
    (p q : ι → ℕ) (hp : Monotone p) (hq : Monotone q) (k : ℕ) :
    (∀ i, cutIndicator (p i) k ≤ cutIndicator (q i) k) ∨
      (∀ i, cutIndicator (q i) k ≤ cutIndicator (p i) k) := by
  by_cases h : ∀ i, p i ≤ k → q i ≤ k
  · left
    intro i
    by_cases hpi : p i ≤ k
    · simp [cutIndicator, hpi, h i hpi]
    · simp only [cutIndicator, if_neg hpi]
      split_ifs <;> norm_num
  · push Not at h
    obtain ⟨i, hpi, hqi⟩ := h
    have hrev : ∀ j, q j ≤ k → p j ≤ k := by
      intro j hqj
      by_cases hji : j ≤ i
      · exact (hp hji).trans hpi
      · have hij : i ≤ j := le_of_not_ge hji
        exact False.elim ((not_le_of_gt hqi) ((hq hij).trans hqj))
    right
    intro j
    by_cases hqj : q j ≤ k
    · simp [cutIndicator, hqj, hrev j hqj]
    · simp only [cutIndicator, if_neg hqj]
      split_ifs <;> norm_num

/-- For two ordered lists, the sum of absolute indicator differences equals
the absolute difference of the cumulative counts. -/
theorem sum_abs_cutIndicator_sub {ι : Type*} [Fintype ι] [LinearOrder ι]
    (p q : ι → ℕ) (hp : Monotone p) (hq : Monotone q) (k : ℕ) :
    (∑ i, |cutIndicator (p i) k - cutIndicator (q i) k|) =
      |(∑ i, cutIndicator (p i) k) - ∑ i, cutIndicator (q i) k| := by
  rw [← sum_sub_distrib]
  rcases monotone_cuts_nested p q hp hq k with hpq | hqp
  · have hnonpos : ∀ i, cutIndicator (p i) k - cutIndicator (q i) k ≤ 0 :=
      fun i => sub_nonpos.mpr (hpq i)
    have habs : ∀ i, |cutIndicator (p i) k - cutIndicator (q i) k| =
        -(cutIndicator (p i) k - cutIndicator (q i) k) :=
      fun i => abs_of_nonpos (hnonpos i)
    rw [abs_of_nonpos (sum_nonpos (fun i _ => hnonpos i))]
    simp_rw [habs]
    rw [sum_neg_distrib]
  · have hnonneg : ∀ i, 0 ≤ cutIndicator (p i) k - cutIndicator (q i) k :=
      fun i => sub_nonneg.mpr (hqp i)
    have habs : ∀ i, |cutIndicator (p i) k - cutIndicator (q i) k| =
        cutIndicator (p i) k - cutIndicator (q i) k :=
      fun i => abs_of_nonneg (hnonneg i)
    rw [abs_of_nonneg (sum_nonneg (fun i _ => hnonneg i))]
    simp_rw [habs]

/-- A fully finite layer-cake identity for two sorted lists whose entries lie
on the same finite decreasing set of levels. The lists are represented by
monotone level-index functions on a finite linear order. -/
theorem ordered_layer_distance {ι : Type*} [Fintype ι] [LinearOrder ι]
    (level : ℕ → ℝ) (d : ℕ) (p q : ι → ℕ)
    (hp : Monotone p) (hq : Monotone q)
    (hp_bound : ∀ i, p i ≤ d) (hq_bound : ∀ i, q i ≤ d)
    (hlevel : ∀ i j, i ≤ j → j ≤ d → level j ≤ level i) :
    (∑ i, |level (p i) - level (q i)|) =
      ∑ k ∈ range d, (level k - level (k + 1)) *
        |(∑ i, cutIndicator (p i) k) - ∑ i, cutIndicator (q i) k| := by
  calc
    _ = ∑ i, ∑ k ∈ range d, (level k - level (k + 1)) *
          |cutIndicator (p i) k - cutIndicator (q i) k| := by
      apply sum_congr rfl
      intro i _
      exact abs_level_sub_eq_sum_gaps level d (p i) (q i)
        hlevel (hp_bound i) (hq_bound i)
    _ = ∑ k ∈ range d, ∑ i, (level k - level (k + 1)) *
          |cutIndicator (p i) k - cutIndicator (q i) k| := by rw [sum_comm]
    _ = _ := by
      apply sum_congr rfl
      intro k _
      rw [← mul_sum, sum_abs_cutIndicator_sub p q hp hq k]

/-- Nonnegative ordered one-coordinate eigenvalues give ordered finite
product-state spectral levels, including degenerate endpoints. -/
theorem spectralLevel_step (n k : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a) (hk : k < n) :
    spectralLevel n (k + 1) a b ≤ spectralLevel n k a b := by
  cases n with
  | zero => omega
  | succ n =>
    have hgap := spectralLevel_gap n k a b (by omega)
    have hnonneg : 0 ≤ (a - b) * a ^ (n - k) * b ^ k :=
      mul_nonneg (mul_nonneg (sub_nonneg.mpr hab) (pow_nonneg ha _))
        (pow_nonneg hb _)
    linarith

theorem spectralLevel_antitone (n : ℕ) (a b : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : b ≤ a)
    (i j : ℕ) (hij : i ≤ j) (hj : j ≤ n) :
    spectralLevel n j a b ≤ spectralLevel n i a b := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_add_of_le hij
  clear hij
  revert hj
  induction r with
  | zero => intro _; simp
  | succ r ih =>
    intro hj
    have hstep := spectralLevel_step n (i + r) a b ha hb hab (by omega)
    have hprev := ih (by omega)
    simpa [Nat.add_assoc] using hstep.trans hprev

/-- The cumulative count is the sum of the multiplicities up to its cut. -/
theorem cutIndicator_eq_sum_multiplicities (s k : ℕ) :
    cutIndicator s k = ∑ j ∈ range (k + 1), (if s = j then (1 : ℝ) else 0) := by
  simp [cutIndicator]

/-- Summing a signed multiplicity formula gives the corresponding cumulative
count formula. This isolates the meaning of the parity multiplicity input. -/
theorem cumulative_from_multiplicities {ι : Type*} [Fintype ι]
    (n k : ℕ) (p q : ι → ℕ)
    (hmult : ∀ j ≤ k,
      (∑ i, if p i = j then (1 : ℝ) else 0) -
        (∑ i, if q i = j then (1 : ℝ) else 0) =
          (-1 : ℝ) ^ j * (n.choose j : ℝ)) :
    (∑ i, cutIndicator (p i) k) - (∑ i, cutIndicator (q i) k) =
      ∑ j ∈ range (k + 1), (-1 : ℝ) ^ j * (n.choose j : ℝ) := by
  simp_rw [cutIndicator_eq_sum_multiplicities]
  rw [sum_comm, sum_comm (f := fun i j => if q i = j then (1 : ℝ) else 0),
    ← sum_sub_distrib]
  apply sum_congr rfl
  intro j hj
  exact hmult j (by simpa using mem_range.mp hj)

/-- Exact distance between the sorted even- and odd-parity spectra,
expressed through sorted level-index lists and their signed multiplicities.

The multiplicity hypothesis says: the even list contains `choose (n+1) k`
copies of level `k` for even `k`, the odd list contains that many for odd
`k`, and common copies cancel. It is sufficient to state their difference.
The theorem includes `c = 0` and `c = 1` without a continuity argument. -/
theorem sorted_parity_spectrum_distance {ι : Type*} [Fintype ι] [LinearOrder ι]
    (n : ℕ) (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (p q : ι → ℕ) (hp : Monotone p) (hq : Monotone q)
    (hp_bound : ∀ i, p i ≤ n + 1) (hq_bound : ∀ i, q i ≤ n + 1)
    (hmult : ∀ k ≤ n + 1,
      (∑ i, if p i = k then (1 : ℝ) else 0) -
        (∑ i, if q i = k then (1 : ℝ) else 0) =
          (-1 : ℝ) ^ k * ((n + 1).choose k : ℝ)) :
    (∑ i, |spectralLevel (n + 1) (p i) ((1 + c) / 2) ((1 - c) / 2) -
      spectralLevel (n + 1) (q i) ((1 + c) / 2) ((1 - c) / 2)|) = c := by
  have ha : 0 ≤ (1 + c) / 2 := by linarith
  have hb : 0 ≤ (1 - c) / 2 := by linarith
  have hab : (1 - c) / 2 ≤ (1 + c) / 2 := by linarith
  calc
    _ = parityLayerDistance (n + 1) ((1 + c) / 2) ((1 - c) / 2) := by
      rw [ordered_layer_distance
        (fun k => spectralLevel (n + 1) k ((1 + c) / 2) ((1 - c) / 2))
        (n + 1) p q hp hq hp_bound hq_bound
        (spectralLevel_antitone (n + 1) _ _ ha hb hab)]
      unfold parityLayerDistance
      apply sum_congr rfl
      intro k hk
      rw [cumulative_from_multiplicities (n + 1) k p q
        (fun j hj => hmult j (by have := mem_range.mp hk; omega))]
      ring
    _ = c := parityLayerDistance_normalized n c

/-- Multiplicity of level `k` in the even-parity spectrum in dimension `d`. -/
def evenMultiplicity (d k : ℕ) : ℝ := if Even k then (d.choose k : ℝ) else 0

/-- Multiplicity of level `k` in the odd-parity spectrum in dimension `d`. -/
def oddMultiplicity (d k : ℕ) : ℝ := if Odd k then (d.choose k : ℝ) else 0

theorem evenMultiplicity_sub_oddMultiplicity (d k : ℕ) :
    evenMultiplicity d k - oddMultiplicity d k =
      (-1 : ℝ) ^ k * (d.choose k : ℝ) := by
  unfold evenMultiplicity oddMultiplicity
  rcases Nat.even_or_odd k with heven | hodd
  · have hnotodd : ¬Odd k := Nat.not_odd_iff_even.mpr heven
    simp [heven, hnotodd, heven.neg_one_pow]
  · have hnoteven : ¬Even k := Nat.not_even_iff_odd.mpr hodd
    simp [hodd, hnoteven, hodd.neg_one_pow]

/-- Scalar form of the parity-spectrum lemma: any two sorted lists of length
`2^n`, with exactly the even and odd binomial spectral multiplicities in
dimension `n+1`, have normalized spectral ℓ¹-distance `c`.

The hypotheses state the spectral multiplicities explicitly. This theorem
does not identify the eigenvalues of concrete operators or their restrictions;
that separate linear-algebra bridge is not part of this file. -/
theorem parity_spectra_l1 (n : ℕ) (c : ℝ) (hc₀ : 0 ≤ c) (hc₁ : c ≤ 1)
    (p q : Fin (2 ^ n) → ℕ) (hp : Monotone p) (hq : Monotone q)
    (hp_bound : ∀ i, p i ≤ n + 1) (hq_bound : ∀ i, q i ≤ n + 1)
    (heven : ∀ k ≤ n + 1,
      (∑ i, if p i = k then (1 : ℝ) else 0) = evenMultiplicity (n + 1) k)
    (hodd : ∀ k ≤ n + 1,
      (∑ i, if q i = k then (1 : ℝ) else 0) = oddMultiplicity (n + 1) k) :
    (∑ i, |spectralLevel (n + 1) (p i) ((1 + c) / 2) ((1 - c) / 2) -
      spectralLevel (n + 1) (q i) ((1 + c) / 2) ((1 - c) / 2)|) = c := by
  apply sorted_parity_spectrum_distance n c hc₀ hc₁ p q hp hq hp_bound hq_bound
  intro k hk
  rw [heven k hk, hodd k hk, evenMultiplicity_sub_oddMultiplicity]

end Hellinger.ParitySpectrum

#print axioms Hellinger.ParitySpectrum.alternating_partial_choose
#print axioms Hellinger.ParitySpectrum.weighted_layer_gaps
#print axioms Hellinger.ParitySpectrum.parityLayerDistance_normalized
#print axioms Hellinger.ParitySpectrum.ordered_layer_distance
#print axioms Hellinger.ParitySpectrum.sorted_parity_spectrum_distance
#print axioms Hellinger.ParitySpectrum.parity_spectra_l1
