import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.IntervalCases

/-!
# Machine-Certified Degree-45 Bivariate (3, 4) Fewnomial System with 8 Positive Roots

We formally certify in Lean 4.36.0 (with zero `sorry` and only standard axioms) that the
symmetric integer system
* `f1(x, y) = x^8 + y^8 - 1 = 0` (trinomial, 3 terms, degree 8)
* `f2(x, y) = 8*x^45 + 8*y^45 + 35*x^3*y^3 - 25*x*y = 0` (tetranomial, 4 terms, degree 45)
has at least 8 distinct strictly positive real solutions `(x, y) ∈ (0, ∞)²`.
-/

namespace Fewnomial.Deg45

def f1 (x y : ℝ) : ℝ := x ^ 8 + y ^ 8 - 1

def f2 (x y : ℝ) : ℝ :=
  8 * x ^ 45 + 8 * y ^ 45 + 35 * x ^ 3 * y ^ 3 - 25 * x * y

noncomputable def yOf (x : ℝ) : ℝ := (1 - x ^ 8) ^ ((1 : ℝ) / 8)

noncomputable def g (x : ℝ) : ℝ := f2 x (yOf x)

lemma yOf_pos {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) : 0 < yOf x := by
  unfold yOf
  apply Real.rpow_pos_of_pos
  have h1 : x ^ 8 < 1 ^ 8 := pow_lt_pow_left₀ hx1 hx0.le (by norm_num)
  linarith

lemma yOf_pow_eight {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : (yOf x) ^ 8 = 1 - x ^ 8 := by
  unfold yOf
  have hnonneg : 0 ≤ 1 - x ^ 8 := by
    have : x ^ 8 ≤ 1 ^ 8 := pow_le_pow_left₀ hx0 hx1 8
    linarith
  rw [← Real.rpow_natCast, ← Real.rpow_mul hnonneg]
  norm_num

lemma f1_yOf {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) : f1 x (yOf x) = 0 := by
  unfold f1
  rw [yOf_pow_eight hx0 hx1]
  ring

lemma yOf_gt_of_pow_lt {x ylo : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1)
    (hlt : ylo ^ 8 < 1 - x ^ 8) : ylo < yOf x := by
  have hy0 : 0 ≤ yOf x := Real.rpow_nonneg (by
    have : x ^ 8 ≤ 1 ^ 8 := pow_le_pow_left₀ hx0 hx1 8; linarith) _
  by_contra h
  push Not at h
  have hpow : (yOf x) ^ 8 ≤ ylo ^ 8 := pow_le_pow_left₀ hy0 h 8
  rw [yOf_pow_eight hx0 hx1] at hpow
  linarith

lemma yOf_lt_of_pow_gt {x yhi : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) (hyhi : 0 ≤ yhi)
    (hgt : 1 - x ^ 8 < yhi ^ 8) : yOf x < yhi := by
  by_contra h
  push Not at h
  have hpow : yhi ^ 8 ≤ (yOf x) ^ 8 := pow_le_pow_left₀ hyhi h 8
  rw [yOf_pow_eight hx0 hx1] at hpow
  linarith

lemma g_pos_of_bracket {x ylo yhi : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (hylo : 0 ≤ ylo) (hyhi : 0 ≤ yhi)
    (hlo : ylo ^ 8 < 1 - x ^ 8) (hhi : 1 - x ^ 8 < yhi ^ 8)
    (hpos : 0 < 8 * x ^ 45 + 8 * ylo ^ 45 + 35 * x ^ 3 * ylo ^ 3 - 25 * x * yhi) :
    0 < g x := by
  have h1 : ylo < yOf x := yOf_gt_of_pow_lt hx0.le hx1.le hlo
  have h2 : yOf x < yhi := yOf_lt_of_pow_gt hx0.le hx1.le hyhi hhi
  have hp45 : ylo ^ 45 ≤ (yOf x) ^ 45 := pow_le_pow_left₀ hylo h1.le 45
  have hp3 : ylo ^ 3 ≤ (yOf x) ^ 3 := pow_le_pow_left₀ hylo h1.le 3
  have hx3 : 0 ≤ 35 * x ^ 3 := by positivity
  have hm3 : 35 * x ^ 3 * ylo ^ 3 ≤ 35 * x ^ 3 * (yOf x) ^ 3 :=
    mul_le_mul_of_nonneg_left hp3 hx3
  have hm1 : 25 * x * yOf x ≤ 25 * x * yhi :=
    mul_le_mul_of_nonneg_left h2.le (by positivity)
  unfold g f2
  linarith

lemma g_neg_of_bracket {x ylo yhi : ℝ}
    (hx0 : 0 < x) (hx1 : x < 1) (_hylo : 0 ≤ ylo) (hyhi : 0 ≤ yhi)
    (hlo : ylo ^ 8 < 1 - x ^ 8) (hhi : 1 - x ^ 8 < yhi ^ 8)
    (hneg : 8 * x ^ 45 + 8 * yhi ^ 45 + 35 * x ^ 3 * yhi ^ 3 - 25 * x * ylo < 0) :
    g x < 0 := by
  have h1 : ylo < yOf x := yOf_gt_of_pow_lt hx0.le hx1.le hlo
  have h2 : yOf x < yhi := yOf_lt_of_pow_gt hx0.le hx1.le hyhi hhi
  have hy0 : 0 ≤ yOf x := (yOf_pos hx0 hx1).le
  have hp45 : (yOf x) ^ 45 ≤ yhi ^ 45 := pow_le_pow_left₀ hy0 h2.le 45
  have hp3 : (yOf x) ^ 3 ≤ yhi ^ 3 := pow_le_pow_left₀ hy0 h2.le 3
  have hx3 : 0 ≤ 35 * x ^ 3 := by positivity
  have hm3 : 35 * x ^ 3 * (yOf x) ^ 3 ≤ 35 * x ^ 3 * yhi ^ 3 :=
    mul_le_mul_of_nonneg_left hp3 hx3
  have hm1 : 25 * x * ylo ≤ 25 * x * yOf x :=
    mul_le_mul_of_nonneg_left h1.le (by positivity)
  unfold g f2
  linarith

lemma continuousOn_g : ContinuousOn g (Set.Icc (3 / 10 : ℝ) (917 / 1000)) := by
  have hy : ContinuousOn yOf (Set.Icc (3 / 10 : ℝ) (917 / 1000)) := by
    unfold yOf
    refine ContinuousOn.rpow_const (Continuous.continuousOn (by continuity)) ?_
    intro x _
    right
    norm_num
  unfold g f2
  have hx : ContinuousOn (fun x : ℝ => x) (Set.Icc (3 / 10 : ℝ) (917 / 1000)) := continuousOn_id
  exact ((((hx.pow 45).const_smul (8 : ℝ)).add ((hy.pow 45).const_smul (8 : ℝ))).add
    (((hx.pow 3).const_smul (35 : ℝ)).mul (hy.pow 3))).sub
    ((hx.const_smul (25 : ℝ)).mul hy)

-- Exact sign certificates on the 5 rational test points in (0, 2^{-1/8})!
lemma g_at_x0 : 0 < g (3 / 10) :=
  g_pos_of_bracket (ylo := 999 / 1000) (yhi := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma g_at_x1 : g (1 / 2) < 0 :=
  g_neg_of_bracket (ylo := 999 / 1000) (yhi := 1)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma g_at_x2 : 0 < g (3 / 4) :=
  g_pos_of_bracket (ylo := 9869 / 10000) (yhi := 987 / 1000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma g_at_x3 : g (21 / 25) < 0 :=
  g_neg_of_bracket (ylo := 96501 / 100000) (yhi := 48251 / 50000)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

lemma g_at_x4 : 0 < g (917 / 1000) :=
  g_pos_of_bracket (ylo := 917 / 1000) (yhi := 459 / 500)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)

private lemma root_in_open_pos_neg {a b : ℝ} (hab : a < b)
    (ha_lo : (3 / 10 : ℝ) ≤ a) (hb_hi : b ≤ 917 / 1000)
    (hga : 0 < g a) (hgb : g b < 0) :
    ∃ r, a < r ∧ r < b ∧ g r = 0 := by
  have hcont : ContinuousOn g (Set.Icc a b) :=
    continuousOn_g.mono (Set.Icc_subset_Icc ha_lo hb_hi)
  have hmem : (0 : ℝ) ∈ Set.Icc (g b) (g a) := ⟨hgb.le, hga.le⟩
  obtain ⟨r, ⟨hr1, hr2⟩, hgr⟩ := intermediate_value_Icc' hab.le hcont hmem
  refine ⟨r, ?_, ?_, hgr⟩
  · exact lt_of_le_of_ne hr1 (fun h => by subst h; linarith)
  · exact lt_of_le_of_ne hr2 (fun h => by subst h; linarith)

private lemma root_in_open_neg_pos {a b : ℝ} (hab : a < b)
    (ha_lo : (3 / 10 : ℝ) ≤ a) (hb_hi : b ≤ 917 / 1000)
    (hga : g a < 0) (hgb : 0 < g b) :
    ∃ r, a < r ∧ r < b ∧ g r = 0 := by
  have hcont : ContinuousOn g (Set.Icc a b) :=
    continuousOn_g.mono (Set.Icc_subset_Icc ha_lo hb_hi)
  have hmem : (0 : ℝ) ∈ Set.Icc (g a) (g b) := ⟨hga.le, hgb.le⟩
  obtain ⟨r, ⟨hr1, hr2⟩, hgr⟩ := intermediate_value_Icc hab.le hcont hmem
  refine ⟨r, ?_, ?_, hgr⟩
  · exact lt_of_le_of_ne hr1 (fun h => by subst h; linarith)
  · exact lt_of_le_of_ne hr2 (fun h => by subst h; linarith)

/-- For any `x ∈ (0, 917/1000)`, we have `x < 917/1000 < yOf x`. -/
lemma lt_yOf_of_lt_mid {x : ℝ} (hx0 : 0 < x) (hx : x < 917 / 1000) :
    (917 / 1000 : ℝ) < yOf x := by
  apply yOf_gt_of_pow_lt hx0.le (by linarith)
  have hpow : x ^ 8 < (917 / 1000 : ℝ) ^ 8 := pow_lt_pow_left₀ hx hx0.le (by norm_num)
  have hmid : (917 / 1000 : ℝ) ^ 8 < 1 - (917 / 1000 : ℝ) ^ 8 := by norm_num
  linarith

/-- **Theorem 2 (Formally Certified in Lean 4.36.0):**
    The explicit bivariate integer system of type `(3, 4)`
      `x^8 + y^8 - 1 = 0`,
      `8*x^45 + 8*y^45 + 35*x^3*y^3 - 25*x*y = 0`
    has at least 8 distinct strictly positive real solutions in `(0, ∞)²`. -/
theorem explicit_deg45_eight_positive_roots :
    ∃ roots : Fin 8 → ℝ × ℝ,
      Function.Injective roots ∧
      ∀ k : Fin 8,
        0 < (roots k).1 ∧ 0 < (roots k).2 ∧
        f1 (roots k).1 (roots k).2 = 0 ∧
        f2 (roots k).1 (roots k).2 = 0 := by
  obtain ⟨r0, hr0a, hr0b, hgr0⟩ :=
    root_in_open_pos_neg (by norm_num) (by norm_num) (by norm_num) g_at_x0 g_at_x1
  obtain ⟨r1, hr1a, hr1b, hgr1⟩ :=
    root_in_open_neg_pos (by norm_num) (by norm_num) (by norm_num) g_at_x1 g_at_x2
  obtain ⟨r2, hr2a, hr2b, hgr2⟩ :=
    root_in_open_pos_neg (by norm_num) (by norm_num) (by norm_num) g_at_x2 g_at_x3
  obtain ⟨r3, hr3a, hr3b, hgr3⟩ :=
    root_in_open_neg_pos (by norm_num) (by norm_num) (by norm_num) g_at_x3 g_at_x4
  let rs : Fin 4 → ℝ
    | ⟨0, _⟩ => r0
    | ⟨1, _⟩ => r1
    | ⟨2, _⟩ => r2
    | ⟨3, _⟩ => r3
  have hrs_lt : ∀ i : Fin 4, 0 < rs i ∧ rs i < 917 / 1000 := by
    rintro ⟨i, hi⟩
    match i, hi with
    | 0, _ => exact ⟨by linarith [hr0a], by linarith [hr0b]⟩
    | 1, _ => exact ⟨by linarith [hr1a], by linarith [hr1b]⟩
    | 2, _ => exact ⟨by linarith [hr2a], by linarith [hr2b]⟩
    | 3, _ => exact ⟨by linarith [hr3a], by linarith [hr3b]⟩
  have hrs_mono : StrictMono rs := by
    rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
    change i < j at hij
    match i, hi, j, hj with
    | 0, _, 1, _ => dsimp [rs]; linarith [hr0b, hr1a]
    | 0, _, 2, _ => dsimp [rs]; linarith [hr0b, hr1a, hr1b, hr2a]
    | 0, _, 3, _ => dsimp [rs]; linarith [hr0b, hr1a, hr1b, hr2a, hr2b, hr3a]
    | 1, _, 2, _ => dsimp [rs]; linarith [hr1b, hr2a]
    | 1, _, 3, _ => dsimp [rs]; linarith [hr1b, hr2a, hr2b, hr3a]
    | 2, _, 3, _ => dsimp [rs]; linarith [hr2b, hr3a]
    | 0, _, 0, _ | 1, _, 0, _ | 1, _, 1, _ | 2, _, 0, _ | 2, _, 1, _ | 2, _, 2, _
    | 3, _, 0, _ | 3, _, 1, _ | 3, _, 2, _ | 3, _, 3, _ => omega
  have hrs_g : ∀ i : Fin 4, g (rs i) = 0 := by
    rintro ⟨i, hi⟩
    match i, hi with
    | 0, _ => exact hgr0
    | 1, _ => exact hgr1
    | 2, _ => exact hgr2
    | 3, _ => exact hgr3
  let roots : Fin 8 → ℝ × ℝ := fun k =>
    if h : k.1 < 4 then (rs ⟨k.1, h⟩, yOf (rs ⟨k.1, h⟩))
    else (yOf (rs ⟨k.1 - 4, by omega⟩), rs ⟨k.1 - 4, by omega⟩)
  refine ⟨roots, ?_, ?_⟩
  · -- Injectivity: first 4 have x < 917/1000 < y, last 4 have y < 917/1000 < x!
    intro i j hij
    by_cases hi : i.1 < 4 <;> by_cases hj : j.1 < 4
    · simp only [roots, hi, hj, dite_true, Prod.mk.injEq] at hij
      have := hrs_mono.injective hij.1
      exact Fin.ext (by simpa using congrArg Fin.val this)
    · simp only [roots, hi, hj, dite_true, dite_false, Prod.mk.injEq] at hij
      have h1 := (hrs_lt ⟨i.1, hi⟩).2
      have h2 := lt_yOf_of_lt_mid (hrs_lt ⟨j.1 - 4, by omega⟩).1 (hrs_lt ⟨j.1 - 4, by omega⟩).2
      linarith
    · simp only [roots, hi, hj, dite_true, dite_false, Prod.mk.injEq] at hij
      have h1 := (hrs_lt ⟨j.1, hj⟩).2
      have h2 := lt_yOf_of_lt_mid (hrs_lt ⟨i.1 - 4, by omega⟩).1 (hrs_lt ⟨i.1 - 4, by omega⟩).2
      linarith
    · simp only [roots, hi, hj, dite_false, Prod.mk.injEq] at hij
      have := hrs_mono.injective hij.2
      have hval : i.1 - 4 = j.1 - 4 := congrArg Fin.val this
      exact Fin.ext (by omega)
  · -- Every root is strictly positive and satisfies f1 = 0, f2 = 0 (by symmetry of f1, f2!)
    intro k
    by_cases hk : k.1 < 4
    · simp only [roots, hk, dite_true]
      have ⟨h0, hmid⟩ := hrs_lt ⟨k.1, hk⟩
      have h1 : rs ⟨k.1, hk⟩ < 1 := by linarith
      exact ⟨h0, yOf_pos h0 h1, f1_yOf h0.le h1.le, hrs_g ⟨k.1, hk⟩⟩
    · simp only [roots, hk, dite_false]
      have ⟨h0, hmid⟩ := hrs_lt ⟨k.1 - 4, by omega⟩
      have h1 : rs ⟨k.1 - 4, by omega⟩ < 1 := by linarith
      refine ⟨yOf_pos h0 h1, h0, ?_, ?_⟩
      · have hf1 := f1_yOf h0.le h1.le
        unfold f1 at hf1 ⊢; linarith
      · have hf2 := hrs_g ⟨k.1 - 4, by omega⟩
        unfold g f2 at hf2; unfold f2; linarith

end Fewnomial.Deg45
