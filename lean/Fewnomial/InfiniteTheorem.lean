import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.IntervalCases

/-!
# Formal Proof in Lean 4.36.0: `S(3, t) >= 3t - 4` for Every `t >= 3`

We formally prove Theorem 1 with zero `sorry` and only standard axioms:
For every integer `t >= 3`, there exist explicit bivariate integer polynomials
`f, g` where `f` has exactly 3 distinct monomials (trinomial) and `g` has exactly `t`
distinct monomials (`t`-nomial) with nonzero integer coefficients, such that `f = g = 0`
has at least `3 * t - 4` distinct, nondegenerate (`det J ≠ 0`) strictly positive real
solutions in `(0, ∞)²`.

Our proof uses an elementary constructive induction with explicit monotonicity on three
disjoint subintervals (avoiding Sard's theorem and measure theory altogether).
-/

open Filter Topology

namespace Fewnomial.InfiniteTheorem

/-! ## Section 1: Bivariate Integer Fewnomials and Their Jacobians -/

/-- A bivariate integer polynomial represented explicitly as a list of `(coeff, deg_x, deg_y)`. -/
def evalPoly (terms : List (ℤ × ℕ × ℕ)) (x y : ℝ) : ℝ :=
  (terms.map fun t => (t.1 : ℝ) * x ^ t.2.1 * y ^ t.2.2).sum

def evalPolyDx (terms : List (ℤ × ℕ × ℕ)) (x y : ℝ) : ℝ :=
  (terms.map fun t => (t.1 : ℝ) * (t.2.1 : ℝ) * x ^ (t.2.1 - 1) * y ^ t.2.2).sum

def evalPolyDy (terms : List (ℤ × ℕ × ℕ)) (x y : ℝ) : ℝ :=
  (terms.map fun t => (t.1 : ℝ) * (t.2.2 : ℝ) * x ^ t.2.1 * y ^ (t.2.2 - 1)).sum

/-- Exact validity predicate for a bivariate `t`-nomial over `ℤ`:
    exact length `t`, all coefficients nonzero, and pairwise distinct monomial exponents. -/
def ValidFewnomial (t : ℕ) (terms : List (ℤ × ℕ × ℕ)) : Prop :=
  terms.length = t ∧
  (∀ term ∈ terms, term.1 ≠ 0) ∧
  (terms.map Prod.snd).Nodup

lemma hasDerivAt_evalPoly_curve (terms : List (ℤ × ℕ × ℕ)) {x y y' : ℝ}
    {yf : ℝ → ℝ} (hy0 : yf x = y) (hy' : HasDerivAt yf y' x) :
    HasDerivAt (fun s => evalPoly terms s (yf s))
      (evalPolyDx terms x y + evalPolyDy terms x y * y') x := by
  induction terms with
  | nil =>
    simp [evalPoly, evalPolyDx, evalPolyDy]
    exact hasDerivAt_const x (0 : ℝ)
  | cons hd tl ih =>
    rcases hd with ⟨c, p, q⟩
    have hfun : (fun s => evalPoly ((c, p, q) :: tl) s (yf s)) =
        fun s => (c : ℝ) * s ^ p * (yf s) ^ q + evalPoly tl s (yf s) := by
      ext s; simp [evalPoly]
    rw [hfun]
    have hx : HasDerivAt (fun s : ℝ => s ^ p) ((p : ℝ) * x ^ (p - 1)) x :=
      hasDerivAt_pow p x
    have hy : HasDerivAt (fun s : ℝ => (yf s) ^ q) ((q : ℝ) * y ^ (q - 1) * y') x := by
      have h1 := hy'.pow q
      rw [hy0] at h1
      exact h1
    have hterm : HasDerivAt (fun s : ℝ => (c : ℝ) * s ^ p * (yf s) ^ q)
        ((c : ℝ) * (p : ℝ) * x ^ (p - 1) * y ^ q +
          (c : ℝ) * (q : ℝ) * x ^ p * y ^ (q - 1) * y') x := by
      have hmul := (hx.const_mul (c : ℝ)).mul hy
      rw [hy0] at hmul
      exact hmul.congr_deriv (by ring)
    have hsum := hterm.add ih
    refine hsum.congr_deriv ?_
    simp only [evalPolyDx, evalPolyDy, List.map_cons, List.sum_cons]
    ring

/-! ## Section 2: Generalized Rational-Exponent Polynomials on `(0, 1)` -/

/-- Generalized polynomial `F(u) = ∑ (c, a, b) ∈ L, c * u^a * (1 - u)^b`. -/
noncomputable def evalGen (L : List (ℚ × ℚ × ℚ)) (u : ℝ) : ℝ :=
  (L.map fun t => (t.1 : ℝ) * u ^ (t.2.1 : ℝ) * (1 - u) ^ (t.2.2 : ℝ)).sum

/-- Formal derivative `F'(u)` on `(0, 1)`. -/
noncomputable def derivGen (L : List (ℚ × ℚ × ℚ)) (u : ℝ) : ℝ :=
  (L.map fun t => (t.1 : ℝ) *
    ((t.2.1 : ℝ) * u ^ ((t.2.1 : ℝ) - 1) * (1 - u) ^ (t.2.2 : ℝ) -
     (t.2.2 : ℝ) * u ^ (t.2.1 : ℝ) * (1 - u) ^ ((t.2.2 : ℝ) - 1))).sum

lemma hasDerivAt_genTerm (c a b : ℝ) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (fun s => c * s ^ a * (1 - s) ^ b)
      (c * (a * u ^ (a - 1) * (1 - u) ^ b - b * u ^ a * (1 - u) ^ (b - 1))) u := by
  have h1 : HasDerivAt (fun s : ℝ => s ^ a) (a * u ^ (a - 1)) u := by
    have := Real.hasDerivAt_rpow_const (p := a) (x := u) (Or.inl hu0.ne')
    simpa [mul_one] using this
  have h2sub : HasDerivAt (fun s : ℝ => 1 - s) (-1) u := by
    simpa using (hasDerivAt_id u).const_sub (1 : ℝ)
  have h2 := h2sub.rpow_const (p := b) (Or.inl (by linarith : 1 - u ≠ 0))
  have hmul := (h1.const_mul c).mul h2
  exact hmul.congr_deriv (by ring)

lemma hasDerivAt_evalGen (L : List (ℚ × ℚ × ℚ)) {u : ℝ} (hu0 : 0 < u) (hu1 : u < 1) :
    HasDerivAt (evalGen L) (derivGen L u) u := by
  induction L with
  | nil =>
    simp [evalGen, derivGen]
    exact hasDerivAt_const u (0 : ℝ)
  | cons hd tl ih =>
    rcases hd with ⟨c, a, b⟩
    simp only [evalGen, derivGen, List.map_cons, List.sum_cons]
    exact (hasDerivAt_genTerm c a b hu0 hu1).add ih

lemma continuousOn_evalGen (L : List (ℚ × ℚ × ℚ)) :
    ContinuousOn (evalGen L) (Set.Ioo 0 1) := by
  intro u hu
  exact (hasDerivAt_evalGen L hu.1 hu.2).continuousAt.continuousWithinAt

lemma continuousOn_derivGen (L : List (ℚ × ℚ × ℚ)) :
    ContinuousOn (derivGen L) (Set.Ioo 0 1) := by
  induction L with
  | nil =>
    have : derivGen [] = fun _ => (0 : ℝ) := by ext; simp [derivGen]
    rw [this]; exact continuousOn_const
  | cons hd tl ih =>
    rcases hd with ⟨c, a, b⟩
    have hfun : derivGen ((c, a, b) :: tl) = fun u =>
        (c : ℝ) * ((a : ℝ) * u ^ ((a : ℝ) - 1) * (1 - u) ^ (b : ℝ) -
         (b : ℝ) * u ^ (a : ℝ) * (1 - u) ^ ((b : ℝ) - 1)) + derivGen tl u := by
      ext u; simp [derivGen]
    rw [hfun]
    have h1 : ContinuousOn (fun u : ℝ => (a : ℝ) * u ^ ((a : ℝ) - 1) * (1 - u) ^ (b : ℝ)) (Set.Ioo 0 1) := by
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
      · refine ContinuousOn.rpow_const continuousOn_id ?_
        intro u hu; left; exact hu.1.ne'
      · refine ContinuousOn.rpow_const (Continuous.continuousOn (by continuity)) ?_
        intro u hu; left; linarith [hu.2]
    have h2 : ContinuousOn (fun u : ℝ => (b : ℝ) * u ^ (a : ℝ) * (1 - u) ^ ((b : ℝ) - 1)) (Set.Ioo 0 1) := by
      refine ContinuousOn.mul (ContinuousOn.mul continuousOn_const ?_) ?_
      · refine ContinuousOn.rpow_const continuousOn_id ?_
        intro u hu; left; exact hu.1.ne'
      · refine ContinuousOn.rpow_const (Continuous.continuousOn (by continuity)) ?_
        intro u hu; left; linarith [hu.2]
    exact (ContinuousOn.mul continuousOn_const (h1.sub h2)).add ih

/-- Shift all `u`-exponents by `-a0` and scale all coefficients by `s` (`s = ±1`). -/
def shiftScale (s a0 : ℚ) (L : List (ℚ × ℚ × ℚ)) : List (ℚ × ℚ × ℚ) :=
  L.map fun t => (s * t.1, t.2.1 - a0, t.2.2)

lemma evalGen_shiftScale (s a0 : ℚ) (L : List (ℚ × ℚ × ℚ)) {u : ℝ} (hu0 : 0 < u) :
    evalGen (shiftScale s a0 L) u = (s : ℝ) * u ^ (-(a0 : ℝ)) * evalGen L u := by
  induction L with
  | nil => simp [shiftScale, evalGen]
  | cons hd tl ih =>
    rcases hd with ⟨c, a, b⟩
    have hcons : shiftScale s a0 ((c, a, b) :: tl) = (s * c, a - a0, b) :: shiftScale s a0 tl := rfl
    rw [hcons]
    simp only [evalGen, List.map_cons, List.sum_cons, Rat.cast_mul, Rat.cast_sub]
    rw [show (List.map (fun t : ℚ × ℚ × ℚ => (t.1 : ℝ) * u ^ (t.2.1 : ℝ) * (1 - u) ^ (t.2.2 : ℝ))
      (shiftScale s a0 tl)).sum = evalGen (shiftScale s a0 tl) u from rfl, ih, mul_add]
    congr 1
    rw [sub_eq_add_neg, Real.rpow_add hu0]
    ring

/-! ## Section 3: Elementary Limit & Asymptotic Lemmas as `u → 0⁺`, `M → ∞`, `δ → 0⁺` -/

lemma tendsto_rpow_pos_nhdsGT_zero {p : ℝ} (hp : 0 < p) :
    Tendsto (fun u : ℝ => u ^ p) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have h : Tendsto (fun u : ℝ => u ^ p) (nhds 0) (nhds ((0 : ℝ) ^ p)) :=
    (Real.continuous_rpow_const hp.le).tendsto 0
  rw [Real.zero_rpow hp.ne'] at h
  exact h.mono_left nhdsWithin_le_nhds

lemma tendsto_one_sub_rpow_nhdsGT_zero (b : ℝ) :
    Tendsto (fun u : ℝ => (1 - u) ^ b) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have h : ContinuousAt (fun u : ℝ => (1 - u) ^ b) 0 := by
    have hsub : ContinuousAt (fun u : ℝ => 1 - u) 0 := by fun_prop
    exact ContinuousAt.rpow_const hsub (Or.inl (by norm_num))
  simpa using h.tendsto.mono_left nhdsWithin_le_nhds

lemma tendsto_rest_div_rpow (rest : List (ℚ × ℚ × ℚ)) {γ : ℝ}
    (hrest : ∀ term ∈ rest, γ < (term.2.1 : ℝ)) :
    Tendsto (fun u : ℝ => evalGen rest u / u ^ γ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  induction rest with
  | nil =>
    simp [evalGen]
  | cons hd tl ih =>
    rcases hd with ⟨c, a, b⟩
    have ha : γ < (a : ℝ) := hrest (c, a, b) (by simp)
    have htl : ∀ term ∈ tl, γ < (term.2.1 : ℝ) := fun t ht => hrest t (by simp [ht])
    have hhd : Tendsto (fun u : ℝ => ((c : ℝ) * u ^ (a : ℝ) * (1 - u) ^ (b : ℝ)) / u ^ γ)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have heq : (fun u : ℝ => ((c : ℝ) * u ^ (a : ℝ) * (1 - u) ^ (b : ℝ)) / u ^ γ) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun u : ℝ => (c : ℝ) * u ^ ((a : ℝ) - γ) * (1 - u) ^ (b : ℝ)) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu0 : 0 < u := hu
        rw [Real.rpow_sub hu0]
        ring
      rw [tendsto_congr' heq]
      have h0 : Tendsto (fun u : ℝ => (c : ℝ) * u ^ ((a : ℝ) - γ) * (1 - u) ^ (b : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((c : ℝ) * 0 * 1)) :=
        ((tendsto_rpow_pos_nhdsGT_zero (by linarith)).const_mul _).mul
          (tendsto_one_sub_rpow_nhdsGT_zero b)
      simpa using h0
    have hsum := hhd.add (ih htl)
    simpa [evalGen, add_div] using hsum

lemma tendsto_derivRest_div_rpow (rest : List (ℚ × ℚ × ℚ)) {γ : ℝ}
    (hrest : ∀ term ∈ rest, γ < (term.2.1 : ℝ)) :
    Tendsto (fun u : ℝ => derivGen rest u / u ^ (γ - 1)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  induction rest with
  | nil =>
    simp [derivGen]
  | cons hd tl ih =>
    rcases hd with ⟨c, a, b⟩
    have ha : γ < (a : ℝ) := hrest (c, a, b) (by simp)
    have htl : ∀ term ∈ tl, γ < (term.2.1 : ℝ) := fun t ht => hrest t (by simp [ht])
    have hhd : Tendsto (fun u : ℝ =>
        ((c : ℝ) * ((a : ℝ) * u ^ ((a : ℝ) - 1) * (1 - u) ^ (b : ℝ) -
         (b : ℝ) * u ^ (a : ℝ) * (1 - u) ^ ((b : ℝ) - 1))) / u ^ (γ - 1))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have heq : (fun u : ℝ =>
          ((c : ℝ) * ((a : ℝ) * u ^ ((a : ℝ) - 1) * (1 - u) ^ (b : ℝ) -
           (b : ℝ) * u ^ (a : ℝ) * (1 - u) ^ ((b : ℝ) - 1))) / u ^ (γ - 1))
          =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun u : ℝ => (c : ℝ) * ((a : ℝ) * u ^ ((a : ℝ) - γ) * (1 - u) ^ (b : ℝ) -
            (b : ℝ) * u ^ ((a : ℝ) - γ + 1) * (1 - u) ^ ((b : ℝ) - 1))) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        have hu0 : 0 < u := hu
        have hsub1 : u ^ ((a : ℝ) - 1) / u ^ (γ - 1) = u ^ ((a : ℝ) - γ) := by
          rw [← Real.rpow_sub hu0]; congr 1; ring
        have hsub2 : u ^ (a : ℝ) / u ^ (γ - 1) = u ^ ((a : ℝ) - γ + 1) := by
          rw [← Real.rpow_sub hu0]; congr 1; ring
        calc ((c : ℝ) * ((a : ℝ) * u ^ ((a : ℝ) - 1) * (1 - u) ^ (b : ℝ) -
                (b : ℝ) * u ^ (a : ℝ) * (1 - u) ^ ((b : ℝ) - 1))) / u ^ (γ - 1)
            = (c : ℝ) * ((a : ℝ) * (u ^ ((a : ℝ) - 1) / u ^ (γ - 1)) * (1 - u) ^ (b : ℝ) -
                (b : ℝ) * (u ^ (a : ℝ) / u ^ (γ - 1)) * (1 - u) ^ ((b : ℝ) - 1)) := by ring
          _ = _ := by rw [hsub1, hsub2]
      rw [tendsto_congr' heq]
      have ht1 : Tendsto (fun u : ℝ => (a : ℝ) * u ^ ((a : ℝ) - γ) * (1 - u) ^ (b : ℝ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((a : ℝ) * 0 * 1)) :=
        ((tendsto_rpow_pos_nhdsGT_zero (by linarith)).const_mul _).mul
          (tendsto_one_sub_rpow_nhdsGT_zero b)
      have ht2 : Tendsto (fun u : ℝ => (b : ℝ) * u ^ ((a : ℝ) - γ + 1) * (1 - u) ^ ((b : ℝ) - 1))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds ((b : ℝ) * 0 * 1)) :=
        ((tendsto_rpow_pos_nhdsGT_zero (by linarith)).const_mul _).mul
          (tendsto_one_sub_rpow_nhdsGT_zero ((b : ℝ) - 1))
      simpa using (ht1.sub ht2).const_mul (c : ℝ)
    have hsum := hhd.add (ih htl)
    simpa [derivGen, add_div] using hsum

/-- `((1 - u)^b - 1) / u^γ → 0` as `u → 0⁺` for any `γ ∈ (0, 1)`. -/
lemma tendsto_one_sub_rpow_sub_one_div_rpow (b : ℝ) {γ : ℝ} (hγ1 : γ < 1) :
    Tendsto (fun u : ℝ => ((1 - u) ^ b - 1) / u ^ γ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
  have hd : HasDerivAt (fun u : ℝ => (1 - u) ^ b) (-b) 0 := by
    have hsub : HasDerivAt (fun u : ℝ => 1 - u) (-1) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).const_sub (1 : ℝ)
    have hpow := hsub.rpow_const (p := b) (Or.inl (by norm_num : (1 : ℝ) - 0 ≠ 0))
    exact hpow.congr_deriv (by norm_num)
  have hsl : Tendsto (fun u : ℝ => ((1 - u) ^ b - 1) / u) (nhdsWithin 0 (Set.Ioi 0)) (nhds (-b)) := by
    have h := hd.tendsto_slope_zero_right
    simpa [smul_eq_mul, div_eq_inv_mul] using h
  have heq : (fun u : ℝ => ((1 - u) ^ b - 1) / u ^ γ) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun u : ℝ => (((1 - u) ^ b - 1) / u) * u ^ (1 - γ)) := by
    filter_upwards [self_mem_nhdsWithin] with u hu
    have hu0 : 0 < u := hu
    rw [Real.rpow_sub hu0, Real.rpow_one]
    field_simp [hu0.ne']
  rw [tendsto_congr' heq]
  simpa using hsl.mul (tendsto_rpow_pos_nhdsGT_zero (by linarith : 0 < 1 - γ))

/-- Elementary Bernoulli upper bound: if `0 ≤ u`, `M * u ≤ 1/2`, then `(1 - u)^(-M) ≤ 1 + 2 * M * u`. -/
lemma inv_one_sub_pow_le {u : ℝ} (hu0 : 0 ≤ u) (hu1 : u < 1) {M : ℕ}
    (hMu : (M : ℝ) * u ≤ 1 / 2) :
    ((1 - u) ^ M)⁻¹ ≤ 1 + 2 * (M : ℝ) * u := by
  have hbern : 1 - (M : ℝ) * u ≤ (1 - u) ^ M := by
    have := one_add_mul_le_pow (a := -u) (by linarith : (-2 : ℝ) ≤ -u) M
    simpa [sub_eq_add_neg, mul_neg] using this
  have hpos1 : 0 < 1 - (M : ℝ) * u := by linarith
  have hinv : ((1 - u) ^ M)⁻¹ ≤ (1 - (M : ℝ) * u)⁻¹ :=
    inv_anti₀ hpos1 hbern
  have hlin : (1 - (M : ℝ) * u)⁻¹ ≤ 1 + 2 * (M : ℝ) * u := by
    rw [inv_le_iff_one_le_mul₀' hpos1]
    have hMu0 : 0 ≤ (M : ℝ) * u := mul_nonneg (Nat.cast_nonneg M) hu0
    nlinarith
  exact hinv.trans hlin

/-- `(k * δ) ^ (δ / γ) → 1` as `δ → 0⁺` for any `k > 0, γ > 0`. -/
lemma tendsto_const_mul_rpow_div_nhdsGT_zero {k γ : ℝ} (hk : 0 < k) (hγ : 0 < γ) :
    Tendsto (fun δ : ℝ => (k * δ) ^ (δ / γ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have hlog : Tendsto (fun δ : ℝ => δ * Real.log δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have htop : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
      simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
    have hinv : Tendsto (fun δ : ℝ => δ⁻¹) (nhdsWithin 0 (Set.Ioi 0)) atTop :=
      tendsto_inv_nhdsGT_zero
    have hcomp := (htop.comp hinv).neg
    rw [neg_zero] at hcomp
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    simp only [Function.comp_apply, Real.log_inv, div_inv_eq_mul]
    ring
  have hexp_arg : Tendsto (fun δ : ℝ => (δ / γ) * Real.log (k * δ))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    have heq : (fun δ : ℝ => (δ / γ) * Real.log (k * δ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun δ : ℝ => (Real.log k / γ) * δ + (1 / γ) * (δ * Real.log δ)) := by
      filter_upwards [self_mem_nhdsWithin] with δ hδ
      have hδ0 : 0 < δ := hδ
      rw [Real.log_mul hk.ne' hδ0.ne']
      ring
    rw [tendsto_congr' heq]
    have hid : Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h1 : Tendsto (fun δ : ℝ => (Real.log k / γ) * δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hid.const_mul (Real.log k / γ)
    have h2 : Tendsto (fun δ : ℝ => (1 / γ) * (δ * Real.log δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      simpa using hlog.const_mul (1 / γ)
    simpa using h1.add h2
  have heq2 : (fun δ : ℝ => (k * δ) ^ (δ / γ)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
      (fun δ : ℝ => Real.exp ((δ / γ) * Real.log (k * δ))) := by
    filter_upwards [self_mem_nhdsWithin] with δ hδ
    have hpos : 0 < k * δ := mul_pos hk hδ
    rw [Real.rpow_def_of_pos hpos, mul_comm]
  rw [tendsto_congr' heq2]
  have hcomp : Tendsto (fun δ : ℝ => Real.exp ((δ / γ) * Real.log (k * δ)))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (Real.exp 0)) :=
    (Real.continuous_exp.tendsto 0).comp hexp_arg
  simpa using hcomp

/-! ## Section 4: The Inductive Invariant and the `+3` Boundary-Pole Insertion Lemma -/

/-- Inductive invariant `GenInv t L`:
    `L` is a `t`-term rational-exponent generalized polynomial with `3 * t - 4` strictly
    increasing simple roots in `(0, 1)` and leading two `u`-exponents `a1 < a2` separated
    by `0 < a2 - a1 < 1/16` with opposite-sign coefficients. -/
structure GenInv (t : ℕ) where
  c1 : ℚ
  c2 : ℚ
  a1 : ℚ
  a2 : ℚ
  b1 : ℚ
  b2 : ℚ
  rest : List (ℚ × ℚ × ℚ)
  len_eq : rest.length + 2 = t
  hc1 : c1 ≠ 0
  hc2 : c2 ≠ 0
  hrest_c : ∀ term ∈ rest, term.1 ≠ 0
  hopp : (c1 : ℝ) * (c2 : ℝ) < 0
  ha_lt : a1 < a2
  ha_gap : a2 - a1 < 1 / 16
  hrest_a : ∀ term ∈ rest, a2 < term.2.1
  hrest_nodup : (rest.map Prod.snd).Nodup
  roots : Fin (3 * t - 4) → ℝ
  roots_mono : StrictMono roots
  roots_pos : ∀ k, 0 < roots k
  roots_lt1 : ∀ k, roots k < 1
  roots_zero : ∀ k, evalGen ((c1, a1, b1) :: (c2, a2, b2) :: rest) (roots k) = 0
  roots_simple : ∀ k, derivGen ((c1, a1, b1) :: (c2, a2, b2) :: rest) (roots k) ≠ 0

def GenInv.terms {t : ℕ} (G : GenInv t) : List (ℚ × ℚ × ℚ) :=
  (G.c1, G.a1, G.b1) :: (G.c2, G.a2, G.b2) :: G.rest

lemma GenInv.terms_zero {t : ℕ} (G : GenInv t) (k : Fin (3 * t - 4)) :
    evalGen G.terms (G.roots k) = 0 := G.roots_zero k

lemma GenInv.terms_simple {t : ℕ} (G : GenInv t) (k : Fin (3 * t - 4)) :
    derivGen G.terms (G.roots k) ≠ 0 := G.roots_simple k

lemma GenInv.terms_nodup {t : ℕ} (G : GenInv t) : (G.terms.map Prod.snd).Nodup := by
  simp only [GenInv.terms, List.map_cons, List.nodup_cons, List.mem_cons, List.mem_map]
  refine ⟨?_, ?_, G.hrest_nodup⟩
  · rintro (h | ⟨term, ht, hterm⟩)
    · have := congrArg Prod.fst h; linarith [G.ha_lt]
    · have := congrArg Prod.fst hterm; linarith [G.ha_lt, G.hrest_a term ht]
  · rintro ⟨term, ht, hterm⟩
    have := congrArg Prod.fst hterm; linarith [G.hrest_a term ht]

/-- Base case `t = 2`: `F_2(u) = -1 + 2 * u^(1/32) * (1 - u)^(1/32)` has 2 simple roots in `(0, 1)`. -/
noncomputable def baseCase : GenInv 2 := by
  -- Evaluate F_2(u) = -1 + 2 * u^(1/32) * (1 - u)^(1/32)
  let L : List (ℚ × ℚ × ℚ) := [(-1, 0, 0), (2, 1 / 32, 1 / 32)]
  have hF : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      evalGen L u = -1 + 2 * u ^ ((1 : ℝ) / 32) * (1 - u) ^ ((1 : ℝ) / 32) := by
    intro u hu
    simp [L, evalGen, Real.rpow_zero]
  have hD : ∀ u ∈ Set.Ioo (0 : ℝ) 1,
      derivGen L u = 2 * ((1 : ℝ) / 32) * (1 - 2 * u) *
        u ^ (((1 : ℝ) / 32) - 1) * (1 - u) ^ (((1 : ℝ) / 32) - 1) := by
    intro u hu
    simp only [L, derivGen, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Rat.cast_neg, Rat.cast_one, Rat.cast_zero, Rat.cast_ofNat, Rat.cast_div]
    have h1 : u ^ ((1 : ℝ) / 32) = u * u ^ (((1 : ℝ) / 32) - 1) := by
      conv_lhs => rw [show ((1 : ℝ) / 32) = 1 + (((1 : ℝ) / 32) - 1) by ring]
      rw [Real.rpow_add hu.1, Real.rpow_one]
    have h2 : (1 - u) ^ ((1 : ℝ) / 32) = (1 - u) * (1 - u) ^ (((1 : ℝ) / 32) - 1) := by
      conv_lhs => rw [show ((1 : ℝ) / 32) = 1 + (((1 : ℝ) / 32) - 1) by ring]
      rw [Real.rpow_add (by linarith [hu.2]), Real.rpow_one]
    rw [h1, h2]
    ring
  -- Check F_2(1/2) > 0: 2 * (1/4)^(1/32) > 1 since 2^32 * (1/4) = 2^30 > 1!
  have hmid_pos : 0 < evalGen L (1 / 2) := by
    rw [hF (1 / 2) (by constructor <;> norm_num)]
    have h1 : ((1 : ℝ) / 2) ^ ((1 : ℝ) / 32) * (1 - (1 : ℝ) / 2) ^ ((1 : ℝ) / 32) =
        ((1 : ℝ) / 4) ^ ((1 : ℝ) / 32) := by
      rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, ← Real.mul_rpow (by norm_num) (by norm_num)]
      norm_num
    rw [mul_assoc, h1]
    have hlt : (1 : ℝ) < (2 * ((1 : ℝ) / 4) ^ ((1 : ℝ) / 32)) ^ (32 : ℕ) := by
      rw [mul_pow, ← Real.rpow_natCast (((1 : ℝ) / 4) ^ ((1 : ℝ) / 32)),
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
    have h2 : (1 : ℝ) < 2 * ((1 : ℝ) / 4) ^ ((1 : ℝ) / 32) := by
      by_contra h
      push Not at h
      have hpos : 0 ≤ 2 * ((1 : ℝ) / 4) ^ ((1 : ℝ) / 32) := by positivity
      have := pow_le_pow_left₀ hpos h 32
      norm_num at this
      linarith
    linarith
  -- Check F_2(eps) < 0 where eps = (1/4)^32: 2 * eps^(1/32) * (1-eps)^(1/32) <= 2*(1/4) = 1/2 < 1!
  have heps_ex : ∃ eps : ℝ, 0 < eps ∧ eps < 1 / 4 ∧ eps ^ ((1 : ℝ) / 32) = 1 / 4 := by
    refine ⟨((1 : ℝ) / 4) ^ (32 : ℕ), by positivity, ?_, ?_⟩
    · have h1 : ((1 : ℝ) / 4) ^ (32 : ℕ) < ((1 : ℝ) / 4) ^ (1 : ℕ) :=
        pow_lt_pow_right_of_lt_one₀ (by norm_num) (by norm_num) (by norm_num)
      simpa using h1
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 4)]
      norm_num
  let eps := Classical.choose heps_ex
  have ⟨heps0, heps_lt, heps_pow⟩ := Classical.choose_spec heps_ex
  have hlo_neg : evalGen L eps < 0 := by
    have hmem : eps ∈ Set.Ioo (0 : ℝ) 1 := ⟨heps0, by linarith⟩
    rw [hF eps hmem, heps_pow]
    have h2 : (1 - eps) ^ ((1 : ℝ) / 32) ≤ 1 :=
      Real.rpow_le_one (by linarith) (by linarith) (by norm_num)
    linarith
  -- By symmetry F_2(1 - u) = F_2(u), also F_2(1 - eps) < 0!
  have hhi_neg : evalGen L (1 - eps) < 0 := by
    have hmem1 : (1 - eps) ∈ Set.Ioo (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
    have hmem2 : eps ∈ Set.Ioo (0 : ℝ) 1 := ⟨heps0, by linarith⟩
    rw [hF _ hmem1, show 1 - (1 - eps) = eps by ring]
    rw [hF _ hmem2] at hlo_neg
    linarith
  -- Apply IVT on [eps, 1/2] and [1/2, 1 - eps]
  have hcont1 : ContinuousOn (evalGen L) (Set.Icc eps (1 / 2)) :=
    (continuousOn_evalGen L).mono (fun u hu => ⟨by linarith [hu.1, heps0], by linarith [hu.2]⟩)
  have hcont2 : ContinuousOn (evalGen L) (Set.Icc (1 / 2) (1 - eps)) :=
    (continuousOn_evalGen L).mono (fun u hu => ⟨by linarith [hu.1], by linarith [hu.2, heps0]⟩)
  have hex1 : ∃ r, eps < r ∧ r < 1 / 2 ∧ evalGen L r = 0 := by
    obtain ⟨r, ⟨h1, h2⟩, hr⟩ := intermediate_value_Icc (by linarith) hcont1 ⟨hlo_neg.le, hmid_pos.le⟩
    exact ⟨r, lt_of_le_of_ne h1 (fun h => by subst h; linarith),
      lt_of_le_of_ne h2 (fun h => by subst h; linarith), hr⟩
  have hex2 : ∃ r, (1 / 2 : ℝ) < r ∧ r < 1 - eps ∧ evalGen L r = 0 := by
    obtain ⟨r, ⟨h1, h2⟩, hr⟩ := intermediate_value_Icc' (by linarith) hcont2 ⟨hhi_neg.le, hmid_pos.le⟩
    exact ⟨r, lt_of_le_of_ne h1 (fun h => by subst h; linarith),
      lt_of_le_of_ne h2 (fun h => by subst h; linarith), hr⟩
  let r0 := Classical.choose hex1
  have hr0 := Classical.choose_spec hex1
  let r1 := Classical.choose hex2
  have hr1 := Classical.choose_spec hex2
  let rs2 : Fin 2 → ℝ
    | ⟨0, _⟩ => r0
    | ⟨1, _⟩ => r1
  exact {
    c1 := -1
    c2 := 2
    a1 := 0
    a2 := 1 / 32
    b1 := 0
    b2 := 1 / 32
    rest := []
    len_eq := rfl
    hc1 := by norm_num
    hc2 := by norm_num
    hrest_c := by simp
    hopp := by norm_num
    ha_lt := by norm_num
    ha_gap := by norm_num
    hrest_a := by simp
    hrest_nodup := by simp
    roots := rs2
    roots_mono := by
      rintro ⟨i, hi⟩ ⟨j, hj⟩ hij
      change i < j at hij
      match i, hi, j, hj with
      | 0, _, 1, _ => dsimp [rs2]; linarith [hr0.2.1, hr1.1]
      | 0, _, 0, _ | 1, _, 0, _ | 1, _, 1, _ => omega
    roots_pos := by
      rintro ⟨k, hk⟩
      match k, hk with
      | 0, _ => dsimp [rs2]; linarith [heps0, hr0.1]
      | 1, _ => dsimp [rs2]; linarith [hr1.1]
    roots_lt1 := by
      rintro ⟨k, hk⟩
      match k, hk with
      | 0, _ => dsimp [rs2]; linarith [hr0.2.1]
      | 1, _ => dsimp [rs2]; linarith [heps0, hr1.2.1]
    roots_zero := by
      rintro ⟨k, hk⟩
      match k, hk with
      | 0, _ => exact hr0.2.2
      | 1, _ => exact hr1.2.2
    roots_simple := by
      rintro ⟨k, hk⟩
      match k, hk with
      | 0, _ =>
        dsimp [rs2]
        rw [hD r0 ⟨by linarith [heps0, hr0.1], by linarith [hr0.2.1]⟩]
        have h1 : (0 : ℝ) < 1 - 2 * r0 := by linarith [hr0.2.1]
        have h2 : (0 : ℝ) < r0 ^ (((1 : ℝ) / 32) - 1) := Real.rpow_pos_of_pos (by linarith [heps0, hr0.1]) _
        have h3 : (0 : ℝ) < (1 - r0) ^ (((1 : ℝ) / 32) - 1) := Real.rpow_pos_of_pos (by linarith [hr0.2.1]) _
        positivity
      | 1, _ =>
        dsimp [rs2]
        rw [hD r1 ⟨by linarith [hr1.1], by linarith [heps0, hr1.2.1]⟩]
        have h1 : 1 - 2 * r1 < 0 := by linarith [hr1.1]
        have h2 : (0 : ℝ) < r1 ^ (((1 : ℝ) / 32) - 1) := Real.rpow_pos_of_pos (by linarith [hr1.1]) _
        have h3 : (0 : ℝ) < (1 - r1) ^ (((1 : ℝ) / 32) - 1) := Real.rpow_pos_of_pos (by linarith [heps0, hr1.2.1]) _
        have hneg : 2 * ((1 : ℝ) / 32) * (1 - 2 * r1) * r1 ^ (((1 : ℝ) / 32) - 1) *
            (1 - r1) ^ (((1 : ℝ) / 32) - 1) < 0 := by nlinarith [mul_pos h2 h3]
        exact hneg.ne
  }

/-- Helper: persistence of `R` isolated simple roots of `G` under small `C¹` perturbation on `[uC, 1)`. -/
lemma persist_simple_roots {R : ℕ} {G G' : ℝ → ℝ} {uC : ℝ} (huC0 : 0 < uC)
    (roots : Fin R → ℝ) (hmono : StrictMono roots)
    (hgt : ∀ k, uC < roots k) (hlt : ∀ k, roots k < 1)
    (hzero : ∀ k, G (roots k) = 0) (hsimple : ∀ k, G' (roots k) ≠ 0)
    (hderivG : ∀ u ∈ Set.Ioo 0 1, HasDerivAt G (G' u) u)
    (hcontG' : ContinuousOn G' (Set.Ioo 0 1)) :
    ∃ (a b : Fin R → ℝ) (ε : ℝ),
      0 < ε ∧
      (∀ k, uC < a k ∧ a k < roots k ∧ roots k < b k ∧ b k < 1) ∧
      (∀ i j : Fin R, i < j → b i < a j) ∧
      (∀ (F F' : ℝ → ℝ),
        (∀ u ∈ Set.Ioo 0 1, HasDerivAt F (F' u) u) →
        (∀ u ∈ Set.Ico uC 1, |F u - G u| < ε ∧ |F' u - G' u| < ε) →
        ∃ new_roots : Fin R → ℝ,
          (∀ k, a k < new_roots k ∧ new_roots k < b k ∧ F (new_roots k) = 0 ∧ F' (new_roots k) ≠ 0)) := by
  -- Around each simple root r_k, pick small radius η_k so [r_k - η_k, r_k + η_k] are pairwise disjoint
  -- inside (uC, 1), |G'| >= m_k > 0 on [r_k - η_k, r_k + η_k], and G(r_k - η_k), G(r_k + η_k) have opposite signs!
  have hsingle : ∀ k : Fin R, ∃ η : ℝ, 0 < η ∧
      uC < roots k - η ∧ roots k + η < 1 ∧
      (∀ j : Fin R, j ≠ k → η < |roots j - roots k| / 3) ∧
      (0 < |G (roots k - η)| ∧ 0 < |G (roots k + η)| ∧
       G (roots k - η) * G (roots k + η) < 0) ∧
      (∃ m : ℝ, 0 < m ∧ ∀ u ∈ Set.Icc (roots k - η) (roots k + η), m ≤ |G' u|) := by
    intro k
    set rk := roots k
    have hrk : rk ∈ Set.Ioo 0 1 := ⟨lt_trans huC0 (hgt k), hlt k⟩
    have hne : 0 < |G' rk| := abs_pos.mpr (hsimple k)
    -- By continuity of G' at rk, |G' u| >= |G' rk|/2 on (rk - δ1, rk + δ1)
    have hcont_at : ContinuousAt G' rk := hcontG'.continuousAt (isOpen_Ioo.mem_nhds hrk)
    have hnear := (Metric.continuousAt_iff.mp hcont_at) (|G' rk| / 2) (by linarith)
    obtain ⟨δ1, hδ1_pos, hδ1⟩ := hnear
    -- Separation from other roots
    let sep : ℝ := if h : (Finset.univ.erase k).Nonempty then
      ((Finset.univ.erase k).image (fun j => |roots j - rk| / 3)).min' (h.image _)
      else 1
    have hsep_pos : 0 < sep := by
      dsimp [sep]
      split_ifs with h
      · rw [Finset.lt_min'_iff]
        intro y hy
        rcases Finset.mem_image.mp hy with ⟨j, hj, rfl⟩
        have hjk : j ≠ k := (Finset.mem_erase.mp hj).1
        have hne' : roots j - rk ≠ 0 := sub_ne_zero.mpr (hmono.injective.ne hjk)
        positivity
      · norm_num
    let η : ℝ := min (min ((rk - uC) / 2) ((1 - rk) / 2)) (min (δ1 / 2) (sep / 2))
    have hη_pos : 0 < η := by
      have : 0 < rk - uC := sub_pos.mpr (hgt k)
      have : 0 < 1 - rk := sub_pos.mpr (hlt k)
      positivity
    have hη_uC : uC < rk - η := by
      have : η ≤ (rk - uC) / 2 := (min_le_left _ _).trans (min_le_left _ _)
      linarith [hgt k]
    have hη_1 : rk + η < 1 := by
      have : η ≤ (1 - rk) / 2 := (min_le_left _ _).trans (min_le_right _ _)
      linarith [hlt k]
    have hη_δ1 : η < δ1 := by
      have : η ≤ δ1 / 2 := (min_le_right _ _).trans (min_le_left _ _)
      linarith
    have hη_sep : ∀ j : Fin R, j ≠ k → η < |roots j - rk| / 3 := by
      intro j hjk
      have hne_s : (Finset.univ.erase k).Nonempty := ⟨j, Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩⟩
      have hle : sep ≤ |roots j - rk| / 3 := by
        dsimp [sep]; rw [dif_pos hne_s]
        exact Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩))
      have hηs : η ≤ sep / 2 := (min_le_right _ _).trans (min_le_right _ _)
      linarith
    -- On [rk - η, rk + η], G' keeps the same sign as G' rk and |G' u| >= |G' rk|/2!
    have hG'_bound : ∀ u ∈ Set.Icc (rk - η) (rk + η), |G' rk| / 2 ≤ |G' u| ∧
        (0 < G' rk → 0 < G' u) ∧ (G' rk < 0 → G' u < 0) := by
      intro u hu
      have hdist : dist u rk < δ1 := by
        rw [Real.dist_eq, abs_lt]
        constructor <;> linarith [hu.1, hu.2]
      have hd := hδ1 hdist
      rw [Real.dist_eq] at hd
      refine ⟨?_, ?_, ?_⟩
      · have := abs_sub_abs_le_abs_sub (G' rk) (G' u)
        rw [abs_sub_comm] at hd
        linarith
      · intro hp
        rw [abs_of_pos hp] at hd
        linarith [(abs_lt.mp hd).1]
      · intro hn
        rw [abs_of_neg hn] at hd
        linarith [(abs_lt.mp hd).2]
    -- By MVT on [rk - η, rk] and [rk, rk + η], G(rk - η) and G(rk + η) have strictly opposite signs!
    have hG_signs : 0 < |G (rk - η)| ∧ 0 < |G (rk + η)| ∧ G (rk - η) * G (rk + η) < 0 := by
      have hcontL : ContinuousOn G (Set.Icc (rk - η) rk) := fun u hu =>
        (hderivG u ⟨by linarith [hu.1, hη_uC, huC0], by linarith [hu.2, hlt k]⟩).continuousAt.continuousWithinAt
      have hdiffL : DifferentiableOn ℝ G (Set.Ioo (rk - η) rk) := fun u hu =>
        (hderivG u ⟨by linarith [hu.1, hη_uC, huC0], by linarith [hu.2, hlt k]⟩).differentiableAt.differentiableWithinAt
      obtain ⟨cL, hcL, hEqL⟩ := exists_deriv_eq_slope G (by linarith : rk - η < rk) hcontL hdiffL
      have hderivL : deriv G cL = G' cL :=
        (hderivG cL ⟨by linarith [hcL.1, hη_uC, huC0], by linarith [hcL.2, hlt k]⟩).deriv
      rw [hderivL, hzero k] at hEqL
      have hGL : G (rk - η) = -η * G' cL := by
        have hne_η : rk - (rk - η) ≠ 0 := by linarith
        have := (eq_div_iff hne_η).mp hEqL
        linarith
      have hcontR : ContinuousOn G (Set.Icc rk (rk + η)) := fun u hu =>
        (hderivG u ⟨by linarith [hu.1, hgt k, huC0], by linarith [hu.2, hη_1]⟩).continuousAt.continuousWithinAt
      have hdiffR : DifferentiableOn ℝ G (Set.Ioo rk (rk + η)) := fun u hu =>
        (hderivG u ⟨by linarith [hu.1, hgt k, huC0], by linarith [hu.2, hη_1]⟩).differentiableAt.differentiableWithinAt
      obtain ⟨cR, hcR, hEqR⟩ := exists_deriv_eq_slope G (by linarith : rk < rk + η) hcontR hdiffR
      have hderivR : deriv G cR = G' cR :=
        (hderivG cR ⟨by linarith [hcR.1, hgt k, huC0], by linarith [hcR.2, hη_1]⟩).deriv
      rw [hderivR, hzero k] at hEqR
      have hGR : G (rk + η) = η * G' cR := by
        have hne_η : rk + η - rk ≠ 0 := by linarith
        have := (eq_div_iff hne_η).mp hEqR
        linarith
      have hL_in : cL ∈ Set.Icc (rk - η) (rk + η) := ⟨hcL.1.le, by linarith [hcL.2]⟩
      have hR_in : cR ∈ Set.Icc (rk - η) (rk + η) := ⟨by linarith [hcR.1], hcR.2.le⟩
      rcases lt_or_gt_of_ne (hsimple k) with hneg | hpos
      · have h1 := (hG'_bound cL hL_in).2.2 hneg
        have h2 := (hG'_bound cR hR_in).2.2 hneg
        rw [hGL, hGR]
        refine ⟨abs_pos.mpr (mul_ne_zero (neg_ne_zero.mpr hη_pos.ne') h1.ne),
          abs_pos.mpr (mul_ne_zero hη_pos.ne' h2.ne), ?_⟩
        have hmul_pos : 0 < G' cL * G' cR := mul_pos_of_neg_of_neg h1 h2
        have hsq_pos : 0 < η * η := mul_pos hη_pos hη_pos
        nlinarith [mul_pos hsq_pos hmul_pos]
      · have h1 := (hG'_bound cL hL_in).2.1 hpos
        have h2 := (hG'_bound cR hR_in).2.1 hpos
        rw [hGL, hGR]
        refine ⟨abs_pos.mpr (mul_ne_zero (neg_ne_zero.mpr hη_pos.ne') h1.ne'),
          abs_pos.mpr (mul_ne_zero hη_pos.ne' h2.ne'), ?_⟩
        have hmul_pos : 0 < G' cL * G' cR := mul_pos h1 h2
        have hsq_pos : 0 < η * η := mul_pos hη_pos hη_pos
        nlinarith [mul_pos hsq_pos hmul_pos]
    exact ⟨η, hη_pos, hη_uC, hη_1, hη_sep, hG_signs, |G' rk| / 2, by linarith,
      fun u hu => (hG'_bound u hu).1⟩
  choose η hη_pos hη_uC hη_1 hη_sep hG_signs m hm_pos hm_bound using hsingle
  let a : Fin R → ℝ := fun k => roots k - η k
  let b : Fin R → ℝ := fun k => roots k + η k
  let ε : ℝ := if h : (Finset.univ : Finset (Fin R)).Nonempty then
    (Finset.univ.image (fun k => min (min (|G (a k)|) (|G (b k)|)) (m k))).min' (h.image _) / 2
    else 1
  have hε_pos : 0 < ε := by
    dsimp [ε]
    split_ifs with h
    · apply half_pos
      rw [Finset.lt_min'_iff]
      intro y hy
      rcases Finset.mem_image.mp hy with ⟨k, _, rfl⟩
      exact lt_min (lt_min (hG_signs k).1 (hG_signs k).2.1) (hm_pos k)
    · norm_num
  refine ⟨a, b, ε, hε_pos, ?_, ?_, ?_⟩
  · intro k; exact ⟨hη_uC k, by linarith [hη_pos k], by linarith [hη_pos k], hη_1 k⟩
  · intro i j hij
    have hlt_r : roots i < roots j := hmono hij
    have h1 := hη_sep i j hij.ne'
    have h2 := hη_sep j i hij.ne
    rw [abs_of_pos (sub_pos.mpr hlt_r)] at h1
    rw [abs_sub_comm, abs_of_pos (sub_pos.mpr hlt_r)] at h2
    dsimp [a, b]
    linarith
  · intro F F' hderivF hclose
    have hex_k : ∀ k : Fin R, ∃ r, a k < r ∧ r < b k ∧ F r = 0 ∧ F' r ≠ 0 := by
      intro k
      have hne_u : (Finset.univ : Finset (Fin R)).Nonempty := ⟨k, Finset.mem_univ k⟩
      have hε_le : ε < min (min (|G (a k)|) (|G (b k)|)) (m k) := by
        have hle : (Finset.univ.image (fun j => min (min (|G (a j)|) (|G (b j)|)) (m j))).min' (hne_u.image _) ≤
            min (min (|G (a k)|) (|G (b k)|)) (m k) :=
          Finset.min'_le _ _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
        have hpos_m : 0 < min (min (|G (a k)|) (|G (b k)|)) (m k) :=
          lt_min (lt_min (hG_signs k).1 (hG_signs k).2.1) (hm_pos k)
        dsimp [ε]; rw [dif_pos hne_u]
        linarith
      have hε_Ga : ε < |G (a k)| := lt_of_lt_of_le hε_le ((min_le_left _ _).trans (min_le_left _ _))
      have hε_Gb : ε < |G (b k)| := lt_of_lt_of_le hε_le ((min_le_left _ _).trans (min_le_right _ _))
      have hε_mk : ε < m k := lt_of_lt_of_le hε_le (min_le_right _ _)
      have hFa := (hclose (a k) ⟨(hη_uC k).le, by linarith [hη_pos k, hη_1 k]⟩).1
      have hFb := (hclose (b k) ⟨by linarith [hη_uC k, hη_pos k], hη_1 k⟩).1
      have hcontF : ContinuousOn F (Set.Icc (a k) (b k)) := fun u hu =>
        (hderivF u ⟨by linarith [hu.1, hη_uC k, huC0], by linarith [hu.2, hη_1 k]⟩).continuousAt.continuousWithinAt
      have hroot : ∃ r, a k < r ∧ r < b k ∧ F r = 0 := by
        have hab : a k < b k := by dsimp [a, b]; linarith [hη_pos k]
        rcases lt_or_gt_of_ne (abs_pos.mp (hG_signs k).1) with hGa_n | hGa_p
        · have hGb_p : 0 < G (b k) := by
            by_contra h; push Not at h
            have hle : 0 ≤ G (a k) * G (b k) := mul_nonneg_of_nonpos_of_nonpos hGa_n.le h
            linarith [(hG_signs k).2.2]
          have hFa_n : F (a k) < 0 := by
            rw [abs_of_neg hGa_n] at hε_Ga
            linarith [(abs_lt.mp hFa).2]
          have hFb_p : 0 < F (b k) := by
            rw [abs_of_pos hGb_p] at hε_Gb
            linarith [(abs_lt.mp hFb).1]
          obtain ⟨r, ⟨hr1, hr2⟩, hFr⟩ := intermediate_value_Icc hab.le hcontF ⟨hFa_n.le, hFb_p.le⟩
          exact ⟨r, lt_of_le_of_ne hr1 (fun h => by subst h; linarith),
            lt_of_le_of_ne hr2 (fun h => by subst h; linarith), hFr⟩
        · have hGb_n : G (b k) < 0 := by
            by_contra h; push Not at h
            have hle : 0 ≤ G (a k) * G (b k) := mul_nonneg hGa_p.le h
            linarith [(hG_signs k).2.2]
          have hFa_p : 0 < F (a k) := by
            rw [abs_of_pos hGa_p] at hε_Ga
            linarith [(abs_lt.mp hFa).1]
          have hFb_n : F (b k) < 0 := by
            rw [abs_of_neg hGb_n] at hε_Gb
            linarith [(abs_lt.mp hFb).2]
          obtain ⟨r, ⟨hr1, hr2⟩, hFr⟩ := intermediate_value_Icc' hab.le hcontF ⟨hFb_n.le, hFa_p.le⟩
          exact ⟨r, lt_of_le_of_ne hr1 (fun h => by subst h; linarith),
            lt_of_le_of_ne hr2 (fun h => by subst h; linarith), hFr⟩
      obtain ⟨r, hr1, hr2, hFr⟩ := hroot
      have hr_in : r ∈ Set.Icc (a k) (b k) := ⟨hr1.le, hr2.le⟩
      have hG'_r : m k ≤ |G' r| := hm_bound k r hr_in
      have hF'_close := (hclose r ⟨by linarith [hη_uC k, hr1], by linarith [hr2, hη_1 k]⟩).2
      have hF'_ne : F' r ≠ 0 := by
        intro h0
        rw [h0, zero_sub, abs_neg] at hF'_close
        linarith
      exact ⟨r, hr1, hr2, hFr, hF'_ne⟩
    choose nr hnr using hex_k
    exact ⟨nr, hnr⟩

set_option maxHeartbeats 6000000 in
/-- **The Inductive `+3` Boundary-Pole Insertion Step:**
    Given `I : GenInv t` (`t ≥ 2`), proves existence of `I' : GenInv (t + 1)` with `3` additional
    simple roots in `(0, 1)`, using direct strict monotonicity on three disjoint subintervals! -/
theorem stepInsert_exists {t : ℕ} (ht : 2 ≤ t) (I : GenInv t) : Nonempty (GenInv (t + 1)) := by
  -- 1. Normalize sign and shift u-exponents by -I.a1 so leading two terms are:
  --      c1' * (1 - u)^b1 - c2' * u^γ * (1 - u)^b2 + rest'
  --    with c1' = |I.c1| > 0, c2' = |I.c2| > 0, γ = I.a2 - I.a1 ∈ (0, 1/16).
  let sgn : ℚ := if 0 < I.c1 then 1 else -1
  have hsgn_ne : sgn ≠ 0 := by dsimp [sgn]; split_ifs <;> norm_num
  have hsgn_c1_pos : (0 : ℝ) < (sgn * I.c1 : ℚ) := by
    dsimp [sgn]; split_ifs with h
    · simp; exact_mod_cast h
    · push Not at h
      have hlt : I.c1 < 0 := lt_of_le_of_ne h I.hc1
      have hlt_r : (I.c1 : ℝ) < 0 := by exact_mod_cast hlt
      simp only [neg_one_mul, Rat.cast_neg]
      linarith
  have hsgn_c2_neg : ((sgn * I.c2 : ℚ) : ℝ) < 0 := by
    have hmul : ((sgn * I.c1 : ℚ) : ℝ) * ((sgn * I.c2 : ℚ) : ℝ) = (I.c1 : ℝ) * (I.c2 : ℝ) := by
      dsimp [sgn]; split_ifs <;> push_cast <;> ring
    nlinarith [I.hopp]
  let c1' : ℚ := sgn * I.c1
  let c2' : ℚ := sgn * I.c2
  let γq : ℚ := I.a2 - I.a1
  let rest' : List (ℚ × ℚ × ℚ) := shiftScale sgn I.a1 I.rest
  let L0 : List (ℚ × ℚ × ℚ) := (c1', 0, I.b1) :: (c2', γq, I.b2) :: rest'
  have hL0_eq : L0 = shiftScale sgn I.a1 I.terms := by
    simp [L0, GenInv.terms, shiftScale, c1', c2', γq, rest']
  -- Set shorthand positive real constants C1 = c1', C2 = -c2', γ = γq, A = γ * C2 / C1!
  let C1 : ℝ := (c1' : ℝ)
  let C2 : ℝ := -(c2' : ℝ)
  let γ : ℝ := (γq : ℝ)
  have hC1 : 0 < C1 := hsgn_c1_pos
  have hC2 : 0 < C2 := neg_pos.mpr hsgn_c2_neg
  have hγ0 : 0 < γ := by
    dsimp [γ, γq]; exact_mod_cast sub_pos.mpr I.ha_lt
  have hγ16 : γ < 1 / 16 := by
    have hq : γq < (1 / 16 : ℚ) := I.ha_gap
    have hr : (γq : ℝ) < ((1 / 16 : ℚ) : ℝ) := by exact_mod_cast hq
    simpa [γ] using hr
  let A : ℝ := γ * C2 / C1
  have hA : 0 < A := by positivity
  -- Verify G(u) = evalGen L0 u inherits all R = 3*t - 4 simple roots of I!
  let R := 3 * t - 4
  have hR_pos : 0 < R := by omega
  have hG_zero : ∀ k : Fin R, evalGen L0 (I.roots k) = 0 := by
    intro k
    rw [hL0_eq, evalGen_shiftScale sgn I.a1 I.terms (I.roots_pos k), I.terms_zero k, mul_zero]
  have hG_simple : ∀ k : Fin R, derivGen L0 (I.roots k) ≠ 0 := by
    intro k
    have hu0 := I.roots_pos k
    have hu1 := I.roots_lt1 k
    have hd1 := hasDerivAt_evalGen L0 hu0 hu1
    have hfun : evalGen L0 =ᶠ[nhds (I.roots k)]
        (fun u => (sgn : ℝ) * u ^ (-(I.a1 : ℝ)) * evalGen I.terms u) := by
      filter_upwards [Ioi_mem_nhds hu0] with u hu
      rw [hL0_eq, evalGen_shiftScale sgn I.a1 I.terms hu]
    have hd2 : HasDerivAt (fun u => (sgn : ℝ) * u ^ (-(I.a1 : ℝ)) * evalGen I.terms u)
        ((sgn : ℝ) * (I.roots k) ^ (-(I.a1 : ℝ)) * derivGen I.terms (I.roots k)) (I.roots k) := by
      have hp : HasDerivAt (fun u : ℝ => (sgn : ℝ) * u ^ (-(I.a1 : ℝ)))
          ((sgn : ℝ) * (-(I.a1 : ℝ) * (I.roots k) ^ (-(I.a1 : ℝ) - 1))) (I.roots k) :=
        (Real.hasDerivAt_rpow_const (Or.inl hu0.ne')).const_mul _
      have hm := hp.mul (hasDerivAt_evalGen I.terms hu0 hu1)
      rw [I.terms_zero k, mul_zero, zero_add] at hm
      exact hm
    have heq_d := (hd1.congr_of_eventuallyEq hfun.symm).unique hd2
    rw [heq_d]
    have hsgn_r : (sgn : ℝ) ≠ 0 := by exact_mod_cast hsgn_ne
    have hpow_ne : (I.roots k) ^ (-(I.a1 : ℝ)) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
    exact mul_ne_zero (mul_ne_zero hsgn_r hpow_ne) (I.terms_simple k)
  -- Check rest' u-exponents > γ
  have hrest'_a : ∀ term ∈ rest', γ < (term.2.1 : ℝ) := by
    intro term ht
    rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
    have := I.hrest_a orig horig
    dsimp [γ, γq]
    push_cast
    exact_mod_cast (by linarith : I.a2 - I.a1 < orig.2.1 - I.a1)
  -- 2. Asymptotics of G = evalGen L0 and G' = derivGen L0 as u → 0⁺!
  have hG_asymp : Tendsto (fun u : ℝ => (evalGen L0 u - C1) / u ^ γ)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-C2)) := by
    have heq : (fun u : ℝ => (evalGen L0 u - C1) / u ^ γ) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun u : ℝ => C1 * (((1 - u) ^ (I.b1 : ℝ) - 1) / u ^ γ) +
          (-C2) * (1 - u) ^ (I.b2 : ℝ) + evalGen rest' u / u ^ γ) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : 0 < u := hu
      have hp0 : u ^ (0 : ℝ) = 1 := Real.rpow_zero u
      have hupos : (u ^ γ) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
      simp only [L0, evalGen, List.map_cons, List.sum_cons, Rat.cast_zero, hp0, mul_one]
      have hc2e : (c2' : ℝ) = -C2 := by dsimp [C2]; ring
      rw [hc2e]
      field_simp [hupos]
      dsimp [C1, γ]
      ring
    rw [tendsto_congr' heq]
    have h1 := (tendsto_one_sub_rpow_sub_one_div_rpow (I.b1 : ℝ) (by linarith : γ < 1)).const_mul C1
    have h2 := (tendsto_one_sub_rpow_nhdsGT_zero (I.b2 : ℝ)).const_mul (-C2)
    have h3 := tendsto_rest_div_rpow rest' hrest'_a
    simpa using (h1.add h2).add h3
  have hG'_asymp : Tendsto (fun u : ℝ => derivGen L0 u / u ^ (γ - 1))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (-γ * C2)) := by
    have heq : (fun u : ℝ => derivGen L0 u / u ^ (γ - 1)) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
        (fun u : ℝ => (-C1 * (I.b1 : ℝ)) * (1 - u) ^ ((I.b1 : ℝ) - 1) * u ^ (1 - γ) +
          (-C2) * (γ * (1 - u) ^ (I.b2 : ℝ) - (I.b2 : ℝ) * u * (1 - u) ^ ((I.b2 : ℝ) - 1)) +
          derivGen rest' u / u ^ (γ - 1)) := by
      filter_upwards [self_mem_nhdsWithin] with u hu
      have hu0 : 0 < u := hu
      have hp0 : u ^ (0 : ℝ) = 1 := Real.rpow_zero u
      have hupos : (u ^ (γ - 1)) ≠ 0 := (Real.rpow_pos_of_pos hu0 _).ne'
      have h1div : (1 : ℝ) / u ^ (γ - 1) = u ^ (1 - γ) := by
        rw [one_div, ← Real.rpow_neg hu0.le]; congr 1; ring
      have hug : u ^ γ / u ^ (γ - 1) = u := by
        rw [← Real.rpow_sub hu0]; simp
      have hL0d : derivGen L0 u = (c1' : ℝ) * -((I.b1 : ℝ) * (1 - u) ^ ((I.b1 : ℝ) - 1)) +
          ((c2' : ℝ) * ((γq : ℝ) * u ^ ((γq : ℝ) - 1) * (1 - u) ^ (I.b2 : ℝ) -
            (I.b2 : ℝ) * u ^ (γq : ℝ) * (1 - u) ^ ((I.b2 : ℝ) - 1)) +
           derivGen rest' u) := by
        simp only [L0, derivGen, List.map_cons, List.sum_cons, Rat.cast_zero, zero_mul, zero_sub, hp0, mul_one]
      rw [hL0d]
      have hc2e : (c2' : ℝ) = -C2 := by dsimp [C2]; ring
      rw [hc2e]
      dsimp only [C1, γ] at hupos h1div hug ⊢
      calc ((c1' : ℝ) * -((I.b1 : ℝ) * (1 - u) ^ ((I.b1 : ℝ) - 1)) +
              (-C2 * ((γq : ℝ) * u ^ ((γq : ℝ) - 1) * (1 - u) ^ (I.b2 : ℝ) -
                (I.b2 : ℝ) * u ^ (γq : ℝ) * (1 - u) ^ ((I.b2 : ℝ) - 1)) +
               derivGen rest' u)) / u ^ ((γq : ℝ) - 1)
          = (-(c1' : ℝ) * (I.b1 : ℝ)) * (1 - u) ^ ((I.b1 : ℝ) - 1) * (1 / u ^ ((γq : ℝ) - 1)) +
            (-C2) * ((γq : ℝ) * (u ^ ((γq : ℝ) - 1) / u ^ ((γq : ℝ) - 1)) * (1 - u) ^ (I.b2 : ℝ) -
              (I.b2 : ℝ) * (u ^ (γq : ℝ) / u ^ ((γq : ℝ) - 1)) * (1 - u) ^ ((I.b2 : ℝ) - 1)) +
            derivGen rest' u / u ^ ((γq : ℝ) - 1) := by ring
        _ = _ := by rw [h1div, div_self hupos, hug]; ring
    rw [tendsto_congr' heq]
    have h1 : Tendsto (fun u : ℝ => (-C1 * (I.b1 : ℝ)) * (1 - u) ^ ((I.b1 : ℝ) - 1) * u ^ (1 - γ))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have ha := (tendsto_one_sub_rpow_nhdsGT_zero ((I.b1 : ℝ) - 1)).const_mul (-C1 * (I.b1 : ℝ))
      have hb := tendsto_rpow_pos_nhdsGT_zero (by linarith : 0 < 1 - γ)
      simpa using ha.mul hb
    have h2 : Tendsto (fun u : ℝ =>
        (-C2) * (γ * (1 - u) ^ (I.b2 : ℝ) - (I.b2 : ℝ) * u * (1 - u) ^ ((I.b2 : ℝ) - 1)))
        (nhdsWithin 0 (Set.Ioi 0)) (nhds (-γ * C2)) := by
      have ha := (tendsto_one_sub_rpow_nhdsGT_zero (I.b2 : ℝ)).const_mul γ
      have hid : Tendsto (fun u : ℝ => u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
        tendsto_id.mono_left nhdsWithin_le_nhds
      have hb : Tendsto (fun u : ℝ => (I.b2 : ℝ) * u * (1 - u) ^ ((I.b2 : ℝ) - 1))
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        simpa using (hid.const_mul (I.b2 : ℝ)).mul (tendsto_one_sub_rpow_nhdsGT_zero ((I.b2 : ℝ) - 1))
      have hsub := (ha.sub hb).const_mul (-C2)
      convert hsub using 1; ring
    have h3 := tendsto_derivRest_div_rpow rest' hrest'_a
    simpa using (h1.add h2).add h3
  -- 3. Pick uC ∈ (0, min(1/2, r_0)) where G and G' obey clean two-sided asymptotic bounds!
  have huC_ex : ∃ uC : ℝ, 0 < uC ∧ uC < 1 / 2 ∧
      (∀ k : Fin R, uC < I.roots k) ∧
      (∀ u ∈ Set.Ioc 0 uC,
        C1 / 2 ≤ evalGen L0 u ∧
        C1 - (3 / 2) * C2 * u ^ γ ≤ evalGen L0 u ∧
        evalGen L0 u ≤ C1 - (1 / 2) * C2 * u ^ γ ∧
        -(3 / 2) * γ * C2 * u ^ (γ - 1) ≤ derivGen L0 u ∧
        derivGen L0 u ≤ -(1 / 2) * γ * C2 * u ^ (γ - 1)) := by
    have h1 := (Metric.tendsto_nhds.mp hG_asymp) (C2 / 2) (by linarith)
    have h2 := (Metric.tendsto_nhds.mp hG'_asymp) (γ * C2 / 2) (by positivity)
    have h3 : ∀ᶠ u in nhdsWithin 0 (Set.Ioi 0), (3 / 2) * C2 * u ^ γ ≤ C1 / 2 := by
      have ht := (tendsto_rpow_pos_nhdsGT_zero hγ0).const_mul ((3 / 2) * C2)
      rw [mul_zero] at ht
      exact (tendsto_order.mp ht).2 (C1 / 2) (by linarith) |>.mono (fun _ hu => hu.le)
    have hall := (h1.and (h2.and h3))
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hall
    obtain ⟨ρ, hρ_pos, hρ⟩ := hall
    let r0 := I.roots ⟨0, hR_pos⟩
    let uC : ℝ := min (min (1 / 4) (r0 / 2)) (ρ / 2)
    have huC0 : 0 < uC := by
      have : 0 < r0 := I.roots_pos ⟨0, hR_pos⟩
      positivity
    refine ⟨uC, huC0, ?_, ?_, ?_⟩
    · exact lt_of_le_of_lt ((min_le_left _ _).trans (min_le_left _ _)) (by norm_num)
    · intro k
      have hk : r0 ≤ I.roots k := I.roots_mono.monotone (show (⟨0, hR_pos⟩ : Fin R) ≤ k from Nat.zero_le _)
      have hu : uC ≤ r0 / 2 := (min_le_left _ _).trans (min_le_right _ _)
      linarith [I.roots_pos ⟨0, hR_pos⟩]
    · intro u hu
      have hu_pos : 0 < u := hu.1
      have hu_ρ : u ∈ Metric.ball (0 : ℝ) ρ := by
        rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hu_pos]
        have : uC ≤ ρ / 2 := min_le_right _ _
        linarith [hu.2]
      obtain ⟨hA1, hA2, hA3⟩ := hρ ⟨hu_ρ, hu_pos⟩
      rw [Real.dist_eq] at hA1 hA2
      have hup_γ : 0 < u ^ γ := Real.rpow_pos_of_pos hu_pos _
      have hup_γ1 : 0 < u ^ (γ - 1) := Real.rpow_pos_of_pos hu_pos _
      have hG_lo : C1 - (3 / 2) * C2 * u ^ γ ≤ evalGen L0 u := by
        have hlt := (abs_lt.mp hA1).1
        have := (lt_div_iff₀ hup_γ).mp (by linarith : -(3 / 2) * C2 < (evalGen L0 u - C1) / u ^ γ)
        linarith
      have hG_hi : evalGen L0 u ≤ C1 - (1 / 2) * C2 * u ^ γ := by
        have hlt := (abs_lt.mp hA1).2
        have := (div_lt_iff₀ hup_γ).mp (by linarith : (evalGen L0 u - C1) / u ^ γ < -(1 / 2) * C2)
        linarith
      have hG'_lo : -(3 / 2) * γ * C2 * u ^ (γ - 1) ≤ derivGen L0 u := by
        have hlt := (abs_lt.mp hA2).1
        have := (lt_div_iff₀ hup_γ1).mp (by linarith : -(3 / 2) * γ * C2 < derivGen L0 u / u ^ (γ - 1))
        linarith
      have hG'_hi : derivGen L0 u ≤ -(1 / 2) * γ * C2 * u ^ (γ - 1) := by
        have hlt := (abs_lt.mp hA2).2
        have := (div_lt_iff₀ hup_γ1).mp (by linarith : derivGen L0 u / u ^ (γ - 1) < -(1 / 2) * γ * C2)
        linarith
      exact ⟨by linarith, hG_lo, hG_hi, hG'_lo, hG'_hi⟩
  obtain ⟨uC, huC0, huC_half, huC_lt_roots, huC_bounds⟩ := huC_ex
  -- 4. Get persistence intervals [a_k, b_k] and stability threshold ε > 0 for the R old simple roots!
  have hpers := persist_simple_roots huC0 I.roots I.roots_mono huC_lt_roots I.roots_lt1
    hG_zero hG_simple (fun u hu => hasDerivAt_evalGen L0 hu.1 hu.2) (continuousOn_derivGen L0)
  obtain ⟨old_a, old_b, ε, hε_pos, hold_in, hold_disj, hold_pers⟩ := hpers
  -- 5. Choose integer M ≥ 1 huge enough so:
  --    - uB = (A / (16 M))^(1/(1-γ)) < u3 = (4 A / M)^(1/(1-γ)) < uC
  --    - M * u3 ≤ 1/2 (so Bernoulli holds at both uB and u3!)
  --    - (1 - uC)^M is tiny enough for persistence (both F and F'!) and h(uC) > 2 * C1!
  have hM_ex : ∃ M : ℕ, 1 ≤ M ∧
      (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ)) < uC ∧
      (M : ℝ) * (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ)) ≤ 1 / 2 ∧
      (1 - uC) ^ M < C1 / 8 / (4 * C1) ∧
      2 * C1 * (1 - uC) ^ M < ε ∧
      2 * C1 * (1 - uC) ^ M * (1 / uC + (M : ℝ) / (1 - uC)) < ε ∧
      2 * C1 < (C1 / 4) * ((1 - uC) ^ M)⁻¹ := by
    have h1mg : 0 < 1 - γ := by linarith
    -- (4*A / M)^(1/(1-γ)) → 0 as M → ∞
    have ht_u3 : Tendsto (fun M : ℕ => (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ))) atTop (nhds 0) := by
      have hdiv : Tendsto (fun M : ℕ => 4 * A / (M : ℝ)) atTop (nhds 0) :=
        tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop
      have hcont := (Real.continuous_rpow_const (by positivity : 0 ≤ (1 : ℝ) / (1 - γ))).tendsto 0
      rw [Real.zero_rpow (by positivity)] at hcont
      exact hcont.comp hdiv
    -- M * (4*A / M)^(1/(1-γ)) = (4*A)^(1/(1-γ)) * M^(-γ/(1-γ)) → 0 as M → ∞
    have ht_Mu3 : Tendsto (fun M : ℕ => (M : ℝ) * (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ))) atTop (nhds 0) := by
      have heq : (fun M : ℕ => (M : ℝ) * (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ))) =ᶠ[atTop]
          (fun M : ℕ => (4 * A) ^ ((1 : ℝ) / (1 - γ)) * ((M : ℝ) ^ (γ / (1 - γ)))⁻¹) := by
        filter_upwards [eventually_ge_atTop 1] with M hM
        have hMp : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
        rw [Real.div_rpow (by positivity) hMp.le, ← Real.rpow_neg hMp.le]
        have hexp : (M : ℝ) * ((M : ℝ) ^ ((1 : ℝ) / (1 - γ)))⁻¹ = (M : ℝ) ^ (-(γ / (1 - γ))) := by
          calc (M : ℝ) * ((M : ℝ) ^ ((1 : ℝ) / (1 - γ)))⁻¹
              = (M : ℝ) ^ (1 : ℝ) * (M : ℝ) ^ (-((1 : ℝ) / (1 - γ))) := by
                rw [Real.rpow_one, Real.rpow_neg hMp.le]
            _ = (M : ℝ) ^ (1 + -((1 : ℝ) / (1 - γ))) := (Real.rpow_add hMp _ _).symm
            _ = (M : ℝ) ^ (-(γ / (1 - γ))) := by congr 1; field_simp [h1mg.ne']; ring
        rw [div_eq_mul_inv, mul_left_comm, hexp]
      rw [tendsto_congr' heq]
      have hpow : Tendsto (fun M : ℕ => (M : ℝ) ^ (γ / (1 - γ))) atTop atTop :=
        (tendsto_rpow_atTop (by positivity)).comp tendsto_natCast_atTop_atTop
      simpa using (tendsto_inv_atTop_zero.comp hpow).const_mul ((4 * A) ^ ((1 : ℝ) / (1 - γ)))
    -- (1 - uC)^M → 0 and M * (1 - uC)^M → 0 as M → ∞!
    have hq0 : 0 ≤ 1 - uC := by linarith
    have hq1 : 1 - uC < 1 := by linarith
    have ht_pow : Tendsto (fun M : ℕ => (1 - uC) ^ M) atTop (nhds 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one hq0 hq1
    have ht_Mpow : Tendsto (fun M : ℕ => (M : ℝ) * (1 - uC) ^ M) atTop (nhds 0) := by
      have h := tendsto_self_mul_const_pow_of_lt_one hq0 hq1
      exact h
    have he1 : ∀ᶠ M : ℕ in atTop, 1 ≤ M := eventually_ge_atTop 1
    have he2 : ∀ᶠ M : ℕ in atTop, (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ)) < uC :=
      (tendsto_order.mp ht_u3).2 uC huC0
    have he3 : ∀ᶠ M : ℕ in atTop, (M : ℝ) * (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ)) ≤ 1 / 2 :=
      ((tendsto_order.mp ht_Mu3).2 (1 / 2) (by norm_num)).mono (fun _ h => h.le)
    have he4 : ∀ᶠ M : ℕ in atTop, (1 - uC) ^ M < C1 / 8 / (4 * C1) :=
      (tendsto_order.mp ht_pow).2 _ (by positivity)
    have he5 : ∀ᶠ M : ℕ in atTop, 2 * C1 * (1 - uC) ^ M < ε := by
      have ht := ht_pow.const_mul (2 * C1); rw [mul_zero] at ht
      exact (tendsto_order.mp ht).2 ε hε_pos
    have he6 : ∀ᶠ M : ℕ in atTop, 2 * C1 * (1 - uC) ^ M * (1 / uC + (M : ℝ) / (1 - uC)) < ε := by
      have htA : Tendsto (fun M : ℕ => (2 * C1 / uC) * (1 - uC) ^ M) atTop (nhds 0) := by
        simpa using ht_pow.const_mul (2 * C1 / uC)
      have htB : Tendsto (fun M : ℕ => (2 * C1 / (1 - uC)) * ((M : ℝ) * (1 - uC) ^ M)) atTop (nhds 0) := by
        simpa using ht_Mpow.const_mul (2 * C1 / (1 - uC))
      have htAB : Tendsto (fun M : ℕ => 2 * C1 * (1 - uC) ^ M * (1 / uC + (M : ℝ) / (1 - uC)))
          atTop (nhds 0) := by
        convert htA.add htB using 1
        · ext M; ring
        · ring
      exact (tendsto_order.mp htAB).2 ε hε_pos
    have he7 : ∀ᶠ M : ℕ in atTop, 2 * C1 < (C1 / 4) * ((1 - uC) ^ M)⁻¹ := by
      filter_upwards [(tendsto_order.mp ht_pow).2 (1 / 16) (by norm_num)] with M hM
      have hp : 0 < (1 - uC) ^ M := pow_pos (by linarith) M
      have hinv : (16 : ℝ) < ((1 - uC) ^ M)⁻¹ := by
        rw [lt_inv_comm₀ (by norm_num) hp]; norm_num; linarith
      nlinarith
    exact (he1.and (he2.and (he3.and (he4.and (he5.and (he6.and he7)))))).exists
  obtain ⟨M, hM1, hu3_lt_uC, hMu3_half, hpow_tiny, hpow_ε, hpow_dε, hpow_uC⟩ := hM_ex
  have hMp : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM1
  have h1mg : 0 < 1 - γ := by linarith
  -- Define uB and u3 explicitly!
  let uB : ℝ := (A / (16 * (M : ℝ))) ^ ((1 : ℝ) / (1 - γ))
  let u3 : ℝ := (4 * A / (M : ℝ)) ^ ((1 : ℝ) / (1 - γ))
  have huB0 : 0 < uB := Real.rpow_pos_of_pos (by positivity) _
  have hu30 : 0 < u3 := Real.rpow_pos_of_pos (by positivity) _
  have huB_lt_u3 : uB < u3 := by
    apply Real.rpow_lt_rpow (by positivity) _ (by positivity)
    have : A / (16 * (M : ℝ)) < 4 * A / (M : ℝ) := by
      rw [div_lt_div_iff₀ (by positivity) hMp]; nlinarith
    exact this
  have huB_lt_uC : uB < uC := lt_trans huB_lt_u3 hu3_lt_uC
  have hMuB_half : (M : ℝ) * uB ≤ 1 / 2 := le_trans (mul_le_mul_of_nonneg_left huB_lt_u3.le hMp.le) hMu3_half
  -- Key identities: M * uB = (A/16) * uB^γ and M * u3 = 4 * A * u3^γ!
  have hMuB_eq : (M : ℝ) * uB = (A / 16) * uB ^ γ := by
    have h1 : uB ^ (1 - γ) = A / (16 * (M : ℝ)) := by
      dsimp [uB]; rw [← Real.rpow_mul (by positivity)]
      rw [one_div_mul_cancel h1mg.ne', Real.rpow_one]
    have h2 : uB ^ (1 - γ) * uB ^ γ = uB := by
      rw [← Real.rpow_add huB0]; simp
    calc (M : ℝ) * uB
        = (M : ℝ) * (uB ^ (1 - γ) * uB ^ γ) := by rw [h2]
      _ = (M : ℝ) * (A / (16 * (M : ℝ)) * uB ^ γ) := by rw [h1]
      _ = (A / 16) * uB ^ γ := by field_simp [hMp.ne']
  have hMu3_eq : (M : ℝ) * u3 = 4 * A * u3 ^ γ := by
    have h1 : u3 ^ (1 - γ) = 4 * A / (M : ℝ) := by
      dsimp [u3]; rw [← Real.rpow_mul (by positivity)]
      rw [one_div_mul_cancel h1mg.ne', Real.rpow_one]
    have h2 : u3 ^ (1 - γ) * u3 ^ γ = u3 := by
      rw [← Real.rpow_add hu30]; simp
    calc (M : ℝ) * u3
        = (M : ℝ) * (u3 ^ (1 - γ) * u3 ^ γ) := by rw [h2]
      _ = (M : ℝ) * (4 * A / (M : ℝ) * u3 ^ γ) := by rw [h1]
      _ = 4 * A * u3 ^ γ := by field_simp [hMp.ne']
  -- Prove BOTH G(uB)/(1-uB)^M < C1 AND G(u3)/(1-u3)^M < C1 (thanks to γ < 1/16!!)!
  have hB_lt_C1 : evalGen L0 uB * ((1 - uB) ^ M)⁻¹ < C1 := by
    have hGb := (huC_bounds uB ⟨huB0, huB_lt_uC.le⟩).2.2.1
    have hinv := inv_one_sub_pow_le huB0.le (by linarith) hMuB_half
    have hGb_pos : 0 < evalGen L0 uB := by linarith [(huC_bounds uB ⟨huB0, huB_lt_uC.le⟩).1]
    have h2MuB : 2 * (M : ℝ) * uB ≤ (1 / 4) * (C2 / C1) * uB ^ γ := by
      rw [mul_assoc, hMuB_eq]; dsimp [A]
      have huBγ : 0 < uB ^ γ := Real.rpow_pos_of_pos huB0 _
      have heq : 2 * (γ * C2 / C1 / 16 * uB ^ γ) = (γ / 8) * ((C2 / C1) * uB ^ γ) := by ring
      rw [heq]
      have hpos : 0 < (C2 / C1) * uB ^ γ := by positivity
      have hγ8 : γ / 8 ≤ 1 / 4 := by linarith
      nlinarith
    have hprod : evalGen L0 uB * ((1 - uB) ^ M)⁻¹ ≤
        (C1 - (1 / 2) * C2 * uB ^ γ) * (1 + (1 / 4) * (C2 / C1) * uB ^ γ) := by
      calc evalGen L0 uB * ((1 - uB) ^ M)⁻¹
          ≤ evalGen L0 uB * (1 + 2 * (M : ℝ) * uB) := mul_le_mul_of_nonneg_left hinv hGb_pos.le
        _ ≤ (C1 - (1 / 2) * C2 * uB ^ γ) * (1 + 2 * (M : ℝ) * uB) :=
            mul_le_mul_of_nonneg_right hGb (by positivity)
        _ ≤ (C1 - (1 / 2) * C2 * uB ^ γ) * (1 + (1 / 4) * (C2 / C1) * uB ^ γ) := by
            apply mul_le_mul_of_nonneg_left (by linarith)
            linarith [(huC_bounds uB ⟨huB0, huB_lt_uC.le⟩).1]
    have hexp : (C1 - (1 / 2) * C2 * uB ^ γ) * (1 + (1 / 4) * (C2 / C1) * uB ^ γ) =
        C1 - (1 / 4) * C2 * uB ^ γ - (1 / 8) * (C2 ^ 2 / C1) * (uB ^ γ) ^ 2 := by
      field_simp [hC1.ne']; ring
    have huBγ : 0 < uB ^ γ := Real.rpow_pos_of_pos huB0 _
    have hC2uB : 0 < C2 * uB ^ γ := mul_pos hC2 huBγ
    have hsq : 0 ≤ (1 / 8) * (C2 ^ 2 / C1) * (uB ^ γ) ^ 2 := by positivity
    linarith
  have h3_lt_C1 : evalGen L0 u3 * ((1 - u3) ^ M)⁻¹ < C1 := by
    have hG3 := (huC_bounds u3 ⟨hu30, hu3_lt_uC.le⟩).2.2.1
    have hinv := inv_one_sub_pow_le hu30.le (by linarith) hMu3_half
    have hG3_pos : 0 < evalGen L0 u3 := by linarith [(huC_bounds u3 ⟨hu30, hu3_lt_uC.le⟩).1]
    -- Here 2 * M * u3 = 8 * A * u3^γ = 8 * γ * (C2 / C1) * u3^γ < (1/2) * (C2 / C1) * u3^γ (since γ < 1/16!)
    have h2Mu3 : 2 * (M : ℝ) * u3 < (1 / 2) * (C2 / C1) * u3 ^ γ := by
      rw [mul_assoc, hMu3_eq]; dsimp [A]
      have hu3γ : 0 < u3 ^ γ := Real.rpow_pos_of_pos hu30 _
      have : 2 * (4 * (γ * C2 / C1) * u3 ^ γ) = (8 * γ) * (C2 / C1) * u3 ^ γ := by ring
      rw [this]
      have h8γ : 8 * γ < 1 / 2 := by linarith
      have hpos : 0 < (C2 / C1) * u3 ^ γ := by positivity
      nlinarith
    have hprod : evalGen L0 u3 * ((1 - u3) ^ M)⁻¹ <
        (C1 - (1 / 2) * C2 * u3 ^ γ) * (1 + (1 / 2) * (C2 / C1) * u3 ^ γ) := by
      have hpos_f : 0 < C1 - (1 / 2) * C2 * u3 ^ γ := by
        linarith [(huC_bounds u3 ⟨hu30, hu3_lt_uC.le⟩).1]
      calc evalGen L0 u3 * ((1 - u3) ^ M)⁻¹
          ≤ evalGen L0 u3 * (1 + 2 * (M : ℝ) * u3) := mul_le_mul_of_nonneg_left hinv hG3_pos.le
        _ ≤ (C1 - (1 / 2) * C2 * u3 ^ γ) * (1 + 2 * (M : ℝ) * u3) :=
            mul_le_mul_of_nonneg_right hG3 (by positivity)
        _ < (C1 - (1 / 2) * C2 * u3 ^ γ) * (1 + (1 / 2) * (C2 / C1) * u3 ^ γ) :=
            mul_lt_mul_of_pos_left (by linarith) hpos_f
    have hexp : (C1 - (1 / 2) * C2 * u3 ^ γ) * (1 + (1 / 2) * (C2 / C1) * u3 ^ γ) =
        C1 - (1 / 4) * (C2 ^ 2 / C1) * (u3 ^ γ) ^ 2 := by
      field_simp [hC1.ne']; ring
    have hu3γ : 0 < u3 ^ γ := Real.rpow_pos_of_pos hu30 _
    have hsq : 0 < (1 / 4) * (C2 ^ 2 / C1) * (u3 ^ γ) ^ 2 := by positivity
    linarith
  -- 6. Pick rational c_new ∈ Q strictly between max(hB_raw, h3_raw) and C1!
  let Lmax : ℝ := max (evalGen L0 uB * ((1 - uB) ^ M)⁻¹) (evalGen L0 u3 * ((1 - u3) ^ M)⁻¹)
  have hLmax_lt : Lmax < C1 := max_lt hB_lt_C1 h3_lt_C1
  have hLmax_pos : 0 < Lmax := lt_of_lt_of_le
    (mul_pos (by linarith [(huC_bounds uB ⟨huB0, huB_lt_uC.le⟩).1]) (inv_pos.mpr (pow_pos (by linarith) M)))
    (le_max_left _ _)
  have hc_ex : ∃ c_new : ℚ, Lmax < (c_new : ℝ) ∧ (c_new : ℝ) < C1 := exists_rat_btwn hLmax_lt
  obtain ⟨c_new, hc_gt_Lmax, hc_lt_C1⟩ := hc_ex
  have hc_pos : (0 : ℝ) < (c_new : ℝ) := lt_trans hLmax_pos hc_gt_Lmax
  -- 7. Pick rational δ ∈ Q ∩ (0, γ) tiny enough that:
  --    - u1 = (δ / (6*A))^(1/γ) < u2 = (8*δ / A)^(1/γ) < uB
  --    - evalGen L0 u1 * u1^δ * (1-u1)^(-M) > c_new  (so F_new(u1) > 0!)
  --    - evalGen L0 u2 * u2^δ * (1-u2)^(-M) > c_new  (so F_new(u2) > 0!)
  --    - uC^(-δ) < 2  (so on [uC, 1), c_new * u^(-δ) * (1-u)^M < 2*C1*(1-uC)^M < ε!)
  --    - δ < 1
  have hδ_ex : ∃ δ : ℚ, 0 < δ ∧ δ < γq ∧
      ((8 * (δ : ℝ) / A) ^ ((1 : ℝ) / γ) < uB) ∧
      ((c_new : ℝ) < evalGen L0 (((δ : ℝ) / (6 * A)) ^ ((1 : ℝ) / γ)) *
        (((δ : ℝ) / (6 * A)) ^ ((1 : ℝ) / γ)) ^ (δ : ℝ) *
        ((1 - ((δ : ℝ) / (6 * A)) ^ ((1 : ℝ) / γ)) ^ M)⁻¹) ∧
      ((c_new : ℝ) < evalGen L0 ((8 * (δ : ℝ) / A) ^ ((1 : ℝ) / γ)) *
        ((8 * (δ : ℝ) / A) ^ ((1 : ℝ) / γ)) ^ (δ : ℝ) *
        ((1 - (8 * (δ : ℝ) / A) ^ ((1 : ℝ) / γ)) ^ M)⁻¹) ∧
      (uC ^ (-(δ : ℝ)) < 2) := by
    -- Helper: for any k > 0, as δ → 0⁺, u(δ) = (k*δ)^(1/γ) → 0⁺,
    -- G(u(δ)) → C1, u(δ)^δ = (k*δ)^(δ/γ) → 1, (1 - u(δ))^(-M) → 1, so product → C1 > c_new!
    have hprod_tendsto : ∀ k : ℝ, 0 < k →
        Tendsto (fun δ : ℝ => evalGen L0 ((k * δ) ^ ((1 : ℝ) / γ)) *
          ((k * δ) ^ ((1 : ℝ) / γ)) ^ δ * ((1 - (k * δ) ^ ((1 : ℝ) / γ)) ^ M)⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds C1) := by
      intro k hk
      have hu_tend : Tendsto (fun δ : ℝ => (k * δ) ^ ((1 : ℝ) / γ))
          (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 (Set.Ioi 0)) := by
        rw [tendsto_nhdsWithin_iff]
        refine ⟨?_, ?_⟩
        · have hid : Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
            tendsto_id.mono_left nhdsWithin_le_nhds
          have h1 : Tendsto (fun δ : ℝ => k * δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
            simpa using hid.const_mul k
          have h2 : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / γ)) (nhds 0) (nhds 0) := by
            have hc := (Real.continuous_rpow_const (by positivity : 0 ≤ (1 : ℝ) / γ)).tendsto 0
            rwa [Real.zero_rpow (by positivity)] at hc
          exact h2.comp h1
        · filter_upwards [self_mem_nhdsWithin] with δ hδ
          exact Real.rpow_pos_of_pos (mul_pos hk hδ) _
      -- G(u) → C1 as u → 0⁺
      have hG_tend : Tendsto (evalGen L0) (nhdsWithin 0 (Set.Ioi 0)) (nhds C1) := by
        have heq : (fun u : ℝ => evalGen L0 u) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            (fun u : ℝ => C1 + ((evalGen L0 u - C1) / u ^ γ) * u ^ γ) := by
          filter_upwards [self_mem_nhdsWithin] with u hu
          have hup : u ^ γ ≠ 0 := (Real.rpow_pos_of_pos hu _).ne'
          field_simp [hup]; ring
        rw [tendsto_congr' heq]
        simpa using tendsto_const_nhds.add (hG_asymp.mul (tendsto_rpow_pos_nhdsGT_zero hγ0))
      have hG_comp := hG_tend.comp hu_tend
      have hpow_comp : Tendsto (fun δ : ℝ => ((k * δ) ^ ((1 : ℝ) / γ)) ^ δ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        have heq : (fun δ : ℝ => ((k * δ) ^ ((1 : ℝ) / γ)) ^ δ) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
            (fun δ : ℝ => (k * δ) ^ (δ / γ)) := by
          filter_upwards [self_mem_nhdsWithin] with δ hδ
          rw [← Real.rpow_mul (mul_pos hk hδ).le]; congr 1; ring
        rw [tendsto_congr' heq]
        exact tendsto_const_mul_rpow_div_nhdsGT_zero hk hγ0
      have hinv_comp : Tendsto (fun δ : ℝ => ((1 - (k * δ) ^ ((1 : ℝ) / γ)) ^ M)⁻¹)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        have hc : ContinuousAt (fun u : ℝ => ((1 - u) ^ M)⁻¹) 0 := by
          have : ((1 - (0 : ℝ)) ^ M) ≠ 0 := by norm_num
          fun_prop (disch := assumption)
        have ht : Tendsto (fun δ : ℝ => ((1 - (k * δ) ^ ((1 : ℝ) / γ)) ^ M)⁻¹)
            (nhdsWithin 0 (Set.Ioi 0)) (nhds (((1 - (0 : ℝ)) ^ M)⁻¹)) :=
          (hc.tendsto.mono_left nhdsWithin_le_nhds).comp hu_tend
        simpa using ht
      simpa using (hG_comp.mul hpow_comp).mul hinv_comp
    -- Collect all 4 eventually-true conditions on δ ∈ nhdsWithin 0 (Set.Ioi 0)
    have hcond1 : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), (8 * δ / A) ^ ((1 : ℝ) / γ) < uB := by
      have ht : Tendsto (fun δ : ℝ => (8 * δ / A) ^ ((1 : ℝ) / γ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
        have hid : Tendsto (fun δ : ℝ => δ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
          tendsto_id.mono_left nhdsWithin_le_nhds
        have h1 : Tendsto (fun δ : ℝ => 8 * δ / A) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
          simpa using (hid.const_mul 8).div_const A
        have h2 : Tendsto (fun x : ℝ => x ^ ((1 : ℝ) / γ)) (nhds 0) (nhds 0) := by
          have hc := (Real.continuous_rpow_const (by positivity : 0 ≤ (1 : ℝ) / γ)).tendsto 0
          rwa [Real.zero_rpow (by positivity)] at hc
        exact h2.comp h1
      exact (tendsto_order.mp ht).2 uB huB0
    have hcond2 : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (c_new : ℝ) < evalGen L0 ((δ / (6 * A)) ^ ((1 : ℝ) / γ)) *
          ((δ / (6 * A)) ^ ((1 : ℝ) / γ)) ^ δ *
          ((1 - (δ / (6 * A)) ^ ((1 : ℝ) / γ)) ^ M)⁻¹ := by
      have ht := hprod_tendsto (1 / (6 * A)) (by positivity)
      have heq : ∀ δ : ℝ, 1 / (6 * A) * δ = δ / (6 * A) := fun δ => by ring
      simp only [heq] at ht
      exact (tendsto_order.mp ht).1 (c_new : ℝ) hc_lt_C1
    have hcond3 : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0),
        (c_new : ℝ) < evalGen L0 ((8 * δ / A) ^ ((1 : ℝ) / γ)) *
          ((8 * δ / A) ^ ((1 : ℝ) / γ)) ^ δ *
          ((1 - (8 * δ / A) ^ ((1 : ℝ) / γ)) ^ M)⁻¹ := by
      have ht := hprod_tendsto (8 / A) (by positivity)
      have heq : ∀ δ : ℝ, 8 / A * δ = 8 * δ / A := fun δ => by ring
      simp only [heq] at ht
      exact (tendsto_order.mp ht).1 (c_new : ℝ) hc_lt_C1
    have hcond4 : ∀ᶠ δ : ℝ in nhdsWithin 0 (Set.Ioi 0), uC ^ (-δ) < 2 := by
      have hc : ContinuousAt (fun δ : ℝ => uC ^ (-δ)) 0 :=
        (continuous_const.rpow continuous_neg (fun _ => Or.inl huC0.ne')).continuousAt
      have ht : Tendsto (fun δ : ℝ => uC ^ (-δ)) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
        simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
      exact (tendsto_order.mp ht).2 2 (by norm_num)
    have hall := hcond1.and (hcond2.and (hcond3.and hcond4))
    rw [Filter.Eventually, Metric.mem_nhdsWithin_iff] at hall
    obtain ⟨ρ, hρ_pos, hρ⟩ := hall
    obtain ⟨δ, hδ0, hδ_lt⟩ := exists_rat_btwn (lt_min hρ_pos hγ0)
    have hδr0 : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ0
    have hδ_ρ : (δ : ℝ) ∈ Metric.ball (0 : ℝ) ρ := by
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hδr0]
      exact lt_of_lt_of_le hδ_lt (min_le_left _ _)
    have hδ_γ : δ < γq := by
      have : (δ : ℝ) < (γq : ℝ) := lt_of_lt_of_le hδ_lt (min_le_right _ _)
      exact_mod_cast this
    obtain ⟨c1h, c2h, c3h, c4h⟩ := hρ ⟨hδ_ρ, hδr0⟩
    exact ⟨δ, by exact_mod_cast hδr0, hδ_γ, c1h, c2h, c3h, c4h⟩
  obtain ⟨δ, hδ_pos, hδ_lt_γ, hu2_lt_uB, hF_u1_raw, hF_u2_raw, huC_rpow_lt2⟩ := hδ_ex
  have hδr : (0 : ℝ) < (δ : ℝ) := by exact_mod_cast hδ_pos
  have hδ_lt1 : (δ : ℝ) < 1 := by
    have hδγ : (δ : ℝ) < (γq : ℝ) := by exact_mod_cast hδ_lt_γ
    have : γ = (γq : ℝ) := rfl
    linarith
  -- 8. Define the new (t+1)-term generalized polynomial L_new!
  let L_new : List (ℚ × ℚ × ℚ) := (-c_new, -δ, (M : ℚ)) :: L0
  have hLnew_eval : ∀ u : ℝ, evalGen L_new u =
      evalGen L0 u - (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M := by
    intro u
    simp only [L_new, evalGen, List.map_cons, List.sum_cons, Rat.cast_neg, Rat.cast_natCast,
      Real.rpow_natCast]
    ring
  have hLnew_deriv : ∀ u ∈ Set.Ioo (0 : ℝ) 1, derivGen L_new u =
      derivGen L0 u + (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M *
        ((δ : ℝ) / u + (M : ℝ) / (1 - u)) := by
    intro u hu
    simp only [L_new, derivGen, List.map_cons, List.sum_cons, Rat.cast_neg, Rat.cast_natCast]
    have h1 : u ^ (-(δ : ℝ) - 1) = u ^ (-(δ : ℝ)) / u := by
      rw [Real.rpow_sub hu.1, Real.rpow_one]
    have h2 : (1 - u) ^ ((M : ℝ) - 1) = (1 - u) ^ M / (1 - u) := by
      rw [Real.rpow_sub (by linarith [hu.2]), Real.rpow_one, Real.rpow_natCast]
    rw [h1, h2, Real.rpow_natCast]
    ring
  -- Key identity: at any zero r ∈ (0, 1) of evalGen L_new,
  --   derivGen L_new r = derivGen L0 r + evalGen L0 r * (δ / r + M / (1 - r))!
  have hderiv_at_zero : ∀ r ∈ Set.Ioo (0 : ℝ) 1, evalGen L_new r = 0 →
      derivGen L_new r = derivGen L0 r + evalGen L0 r * ((δ : ℝ) / r + (M : ℝ) / (1 - r)) := by
    intro r hr hzero
    rw [hLnew_deriv r hr]
    rw [hLnew_eval r] at hzero
    have hterm : (c_new : ℝ) * r ^ (-(δ : ℝ)) * (1 - r) ^ M = evalGen L0 r := by linarith
    rw [hterm]
  -- Define the 3 explicit breakpoints u1 < u2 < uB < u3 < uC!
  let u1 : ℝ := ((δ : ℝ) / (6 * A)) ^ ((1 : ℝ) / γ)
  let u2 : ℝ := (8 * (δ : ℝ) / A) ^ ((1 : ℝ) / γ)
  have hu10 : 0 < u1 := Real.rpow_pos_of_pos (by positivity) _
  have hu20 : 0 < u2 := Real.rpow_pos_of_pos (by positivity) _
  have hu1_lt_u2 : u1 < u2 := by
    apply Real.rpow_lt_rpow (by positivity) _ (by positivity)
    rw [div_lt_div_iff₀ (by positivity) hA]; nlinarith
  have hu1_lt_uC : u1 < uC := lt_trans hu1_lt_u2 (lt_trans hu2_lt_uB huB_lt_uC)
  have hu2_lt_uC : u2 < uC := lt_trans hu2_lt_uB huB_lt_uC
  -- Check signs of evalGen L_new at u0 (tiny), u1, u2, uB, u3, uC!
  have hF_u1_pos : 0 < evalGen L_new u1 := by
    rw [hLnew_eval u1]
    have hraw : (c_new : ℝ) < evalGen L0 u1 * u1 ^ (δ : ℝ) * ((1 - u1) ^ M)⁻¹ := hF_u1_raw
    have hpow_pos : 0 < u1 ^ (-(δ : ℝ)) * (1 - u1) ^ M :=
      mul_pos (Real.rpow_pos_of_pos hu10 _) (pow_pos (by linarith) M)
    have hinv_eq : u1 ^ (δ : ℝ) * ((1 - u1) ^ M)⁻¹ = (u1 ^ (-(δ : ℝ)) * (1 - u1) ^ M)⁻¹ := by
      rw [mul_inv, Real.rpow_neg hu10.le, inv_inv]
    have hmul := mul_lt_mul_of_pos_right hraw hpow_pos
    have hsimp : evalGen L0 u1 * u1 ^ (δ : ℝ) * ((1 - u1) ^ M)⁻¹ * (u1 ^ (-(δ : ℝ)) * (1 - u1) ^ M) =
        evalGen L0 u1 := by
      calc evalGen L0 u1 * u1 ^ (δ : ℝ) * ((1 - u1) ^ M)⁻¹ * (u1 ^ (-(δ : ℝ)) * (1 - u1) ^ M)
          = evalGen L0 u1 * ((u1 ^ (δ : ℝ) * ((1 - u1) ^ M)⁻¹) * (u1 ^ (-(δ : ℝ)) * (1 - u1) ^ M)) := by ring
        _ = evalGen L0 u1 * ((u1 ^ (-(δ : ℝ)) * (1 - u1) ^ M)⁻¹ * (u1 ^ (-(δ : ℝ)) * (1 - u1) ^ M)) := by
            rw [hinv_eq]
        _ = evalGen L0 u1 := by rw [inv_mul_cancel₀ hpow_pos.ne', mul_one]
    rw [hsimp] at hmul
    linarith
  have hF_u2_pos : 0 < evalGen L_new u2 := by
    rw [hLnew_eval u2]
    have hraw : (c_new : ℝ) < evalGen L0 u2 * u2 ^ (δ : ℝ) * ((1 - u2) ^ M)⁻¹ := hF_u2_raw
    have hpow_pos : 0 < u2 ^ (-(δ : ℝ)) * (1 - u2) ^ M :=
      mul_pos (Real.rpow_pos_of_pos hu20 _) (pow_pos (by linarith) M)
    have hinv_eq : u2 ^ (δ : ℝ) * ((1 - u2) ^ M)⁻¹ = (u2 ^ (-(δ : ℝ)) * (1 - u2) ^ M)⁻¹ := by
      rw [mul_inv, Real.rpow_neg hu20.le, inv_inv]
    have hmul := mul_lt_mul_of_pos_right hraw hpow_pos
    have hsimp : evalGen L0 u2 * u2 ^ (δ : ℝ) * ((1 - u2) ^ M)⁻¹ * (u2 ^ (-(δ : ℝ)) * (1 - u2) ^ M) =
        evalGen L0 u2 := by
      calc evalGen L0 u2 * u2 ^ (δ : ℝ) * ((1 - u2) ^ M)⁻¹ * (u2 ^ (-(δ : ℝ)) * (1 - u2) ^ M)
          = evalGen L0 u2 * ((u2 ^ (δ : ℝ) * ((1 - u2) ^ M)⁻¹) * (u2 ^ (-(δ : ℝ)) * (1 - u2) ^ M)) := by ring
        _ = evalGen L0 u2 * ((u2 ^ (-(δ : ℝ)) * (1 - u2) ^ M)⁻¹ * (u2 ^ (-(δ : ℝ)) * (1 - u2) ^ M)) := by
            rw [hinv_eq]
        _ = evalGen L0 u2 := by rw [inv_mul_cancel₀ hpow_pos.ne', mul_one]
    rw [hsimp] at hmul
    linarith
  have hF_uB_neg : evalGen L_new uB < 0 := by
    rw [hLnew_eval uB]
    have h1 : evalGen L0 uB * ((1 - uB) ^ M)⁻¹ < (c_new : ℝ) :=
      lt_of_le_of_lt (le_max_left _ _) hc_gt_Lmax
    have h2 : uB ^ (δ : ℝ) < 1 := Real.rpow_lt_one huB0.le (by linarith) hδr
    have h3 : 0 < evalGen L0 uB * ((1 - uB) ^ M)⁻¹ :=
      mul_pos (by linarith [(huC_bounds uB ⟨huB0, huB_lt_uC.le⟩).1]) (inv_pos.mpr (pow_pos (by linarith) M))
    have h4 : evalGen L0 uB * ((1 - uB) ^ M)⁻¹ * uB ^ (δ : ℝ) < (c_new : ℝ) := by nlinarith
    have hpow_pos : 0 < uB ^ (-(δ : ℝ)) * (1 - uB) ^ M :=
      mul_pos (Real.rpow_pos_of_pos huB0 _) (pow_pos (by linarith) M)
    have hmul := mul_lt_mul_of_pos_right h4 hpow_pos
    have hcancel : evalGen L0 uB * ((1 - uB) ^ M)⁻¹ * uB ^ (δ : ℝ) * (uB ^ (-(δ : ℝ)) * (1 - uB) ^ M) =
        evalGen L0 uB := by
      have hp1 : uB ^ (δ : ℝ) * uB ^ (-(δ : ℝ)) = 1 := by rw [← Real.rpow_add huB0]; simp
      have hp2 : ((1 - uB) ^ M)⁻¹ * (1 - uB) ^ M = 1 := inv_mul_cancel₀ (pow_pos (by linarith) M).ne'
      calc evalGen L0 uB * ((1 - uB) ^ M)⁻¹ * uB ^ (δ : ℝ) * (uB ^ (-(δ : ℝ)) * (1 - uB) ^ M)
          = evalGen L0 uB * (((1 - uB) ^ M)⁻¹ * (1 - uB) ^ M) * (uB ^ (δ : ℝ) * uB ^ (-(δ : ℝ))) := by ring
        _ = evalGen L0 uB := by rw [hp1, hp2]; ring
    rw [hcancel] at hmul
    linarith
  have hF_u3_neg : evalGen L_new u3 < 0 := by
    rw [hLnew_eval u3]
    have h1 : evalGen L0 u3 * ((1 - u3) ^ M)⁻¹ < (c_new : ℝ) :=
      lt_of_le_of_lt (le_max_right _ _) hc_gt_Lmax
    have h2 : u3 ^ (δ : ℝ) < 1 := Real.rpow_lt_one hu30.le (by linarith) hδr
    have h3 : 0 < evalGen L0 u3 * ((1 - u3) ^ M)⁻¹ :=
      mul_pos (by linarith [(huC_bounds u3 ⟨hu30, hu3_lt_uC.le⟩).1]) (inv_pos.mpr (pow_pos (by linarith) M))
    have h4 : evalGen L0 u3 * ((1 - u3) ^ M)⁻¹ * u3 ^ (δ : ℝ) < (c_new : ℝ) := by nlinarith
    have hpow_pos : 0 < u3 ^ (-(δ : ℝ)) * (1 - u3) ^ M :=
      mul_pos (Real.rpow_pos_of_pos hu30 _) (pow_pos (by linarith) M)
    have hmul := mul_lt_mul_of_pos_right h4 hpow_pos
    have hcancel : evalGen L0 u3 * ((1 - u3) ^ M)⁻¹ * u3 ^ (δ : ℝ) * (u3 ^ (-(δ : ℝ)) * (1 - u3) ^ M) =
        evalGen L0 u3 := by
      have hp1 : u3 ^ (δ : ℝ) * u3 ^ (-(δ : ℝ)) = 1 := by rw [← Real.rpow_add hu30]; simp
      have hp2 : ((1 - u3) ^ M)⁻¹ * (1 - u3) ^ M = 1 := inv_mul_cancel₀ (pow_pos (by linarith) M).ne'
      calc evalGen L0 u3 * ((1 - u3) ^ M)⁻¹ * u3 ^ (δ : ℝ) * (u3 ^ (-(δ : ℝ)) * (1 - u3) ^ M)
          = evalGen L0 u3 * (((1 - u3) ^ M)⁻¹ * (1 - u3) ^ M) * (u3 ^ (δ : ℝ) * u3 ^ (-(δ : ℝ))) := by ring
        _ = evalGen L0 u3 := by rw [hp1, hp2]; ring
    rw [hcancel] at hmul
    linarith
  have hF_uC_pos : 0 < evalGen L_new uC := by
    rw [hLnew_eval uC]
    have hG_uC : C1 / 2 ≤ evalGen L0 uC := (huC_bounds uC ⟨huC0, le_rfl⟩).1
    have hpert : (c_new : ℝ) * uC ^ (-(δ : ℝ)) * (1 - uC) ^ M < C1 / 4 := by
      have h1 : (c_new : ℝ) * uC ^ (-(δ : ℝ)) < 2 * C1 := by
        have hpos : 0 < uC ^ (-(δ : ℝ)) := Real.rpow_pos_of_pos huC0 _
        nlinarith
      have h2 : (1 - uC) ^ M < 1 / 32 := by
        have hEq : C1 / 8 / (4 * C1) = 1 / 32 := by field_simp [hC1.ne']; ring
        linarith
      have hp : 0 < (1 - uC) ^ M := pow_pos (by linarith) M
      calc (c_new : ℝ) * uC ^ (-(δ : ℝ)) * (1 - uC) ^ M
          ≤ 2 * C1 * (1 - uC) ^ M := mul_le_mul_of_nonneg_right h1.le hp.le
        _ < 2 * C1 * (1 / 32) := mul_lt_mul_of_pos_left h2 (by positivity)
        _ < C1 / 4 := by linarith
    linarith
  -- Find tiny u0 ∈ (0, u1) with evalGen L_new u0 < 0!
  have hu0_ex : ∃ u0 : ℝ, 0 < u0 ∧ u0 < u1 ∧ evalGen L_new u0 < 0 := by
    -- As u → 0⁺, c_new * u^(-δ) * (1-u)^M → +∞ while G(u) ≤ C1!
    have hbig : Tendsto (fun u : ℝ => u ^ (-(δ : ℝ))) (nhdsWithin 0 (Set.Ioi 0)) atTop := by
      have heq : (fun u : ℝ => u ^ (-(δ : ℝ))) =ᶠ[nhdsWithin 0 (Set.Ioi 0)]
          (fun u : ℝ => (u ^ (δ : ℝ))⁻¹) := by
        filter_upwards [self_mem_nhdsWithin] with u hu
        exact Real.rpow_neg hu.le _
      rw [tendsto_congr' heq]
      apply Tendsto.inv_tendsto_nhdsGT_zero
      rw [tendsto_nhdsWithin_iff]
      exact ⟨tendsto_rpow_pos_nhdsGT_zero hδr,
        by filter_upwards [self_mem_nhdsWithin] with u hu; exact Real.rpow_pos_of_pos hu _⟩
    have h0 : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), 0 < u := self_mem_nhdsWithin
    have h1 : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), (2 * C1 / ((c_new : ℝ) * (1 - u1) ^ M)) < u ^ (-(δ : ℝ)) :=
      hbig.eventually_gt_atTop _
    have hid0 : Tendsto (fun u : ℝ => u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
      tendsto_id.mono_left nhdsWithin_le_nhds
    have h2 : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0), u < u1 :=
      (tendsto_order.mp hid0).2 u1 hu10
    have hall : ∀ᶠ u : ℝ in nhdsWithin 0 (Set.Ioi 0),
        0 < u ∧ (2 * C1 / ((c_new : ℝ) * (1 - u1) ^ M)) < u ^ (-(δ : ℝ)) ∧ u < u1 :=
      h0.and (h1.and h2)
    obtain ⟨u0, hu0_pos, hu0_big, hu0_lt⟩ := hall.exists
    refine ⟨u0, hu0_pos, hu0_lt, ?_⟩
    rw [hLnew_eval u0]
    have hGu0 : evalGen L0 u0 ≤ C1 := by
      have := (huC_bounds u0 ⟨hu0_pos, (lt_trans hu0_lt hu1_lt_uC).le⟩).2.2.1
      have : 0 ≤ (1 / 2) * C2 * u0 ^ γ := by positivity
      linarith
    have hpow_mono : (1 - u1) ^ M ≤ (1 - u0) ^ M :=
      pow_le_pow_left₀ (by linarith) (by linarith) M
    have hden : 0 < (c_new : ℝ) * (1 - u1) ^ M := mul_pos hc_pos (pow_pos (by linarith) M)
    have hprod : 2 * C1 < (c_new : ℝ) * u0 ^ (-(δ : ℝ)) * (1 - u0) ^ M := by
      have ha : 2 * C1 < (c_new : ℝ) * (1 - u1) ^ M * u0 ^ (-(δ : ℝ)) := by
        have := (div_lt_iff₀ hden).mp hu0_big; linarith
      have hb : (c_new : ℝ) * (1 - u1) ^ M * u0 ^ (-(δ : ℝ)) ≤
          (c_new : ℝ) * u0 ^ (-(δ : ℝ)) * (1 - u0) ^ M := by
        have hp : 0 < (c_new : ℝ) * u0 ^ (-(δ : ℝ)) := mul_pos hc_pos (Real.rpow_pos_of_pos hu0_pos _)
        nlinarith
      linarith
    linarith
  obtain ⟨u0, hu0_pos, hu0_lt_u1, hF_u0_neg⟩ := hu0_ex
  -- 9. Extract the 3 NEW SIMPLE roots r_a ∈ (u0, u1), r_b ∈ (u2, uB), r_c ∈ (u3, uC)!
  -- Root 1 in (u0, u1): at any zero r ∈ (0, u1], derivGen L_new r > 0!
  have hnew1 : ∃ r, u0 < r ∧ r < u1 ∧ evalGen L_new r = 0 ∧ derivGen L_new r ≠ 0 := by
    have hcont : ContinuousOn (evalGen L_new) (Set.Icc u0 u1) :=
      (continuousOn_evalGen L_new).mono (fun u hu => ⟨lt_of_lt_of_le hu0_pos hu.1, by linarith [hu.2]⟩)
    obtain ⟨r, ⟨hr1, hr2⟩, hFr⟩ := intermediate_value_Icc hu0_lt_u1.le hcont ⟨hF_u0_neg.le, hF_u1_pos.le⟩
    have hr1' : u0 < r := lt_of_le_of_ne hr1 (fun h => by subst h; linarith)
    have hr2' : r < u1 := lt_of_le_of_ne hr2 (fun h => by subst h; linarith)
    have hr0 : 0 < r := lt_trans hu0_pos hr1'
    have hrC : r ≤ uC := (lt_trans hr2' hu1_lt_uC).le
    refine ⟨r, hr1', hr2', hFr, ?_⟩
    rw [hderiv_at_zero r ⟨hr0, by linarith⟩ hFr]
    have hb := huC_bounds r ⟨hr0, hrC⟩
    -- r < u1 = (δ/(6*A))^(1/γ) => r^γ < δ/(6*A) => δ/r > 6*A*r^(γ-1) => G(r)*(δ/r) >= (C1/2)*6*A*r^(γ-1) = 3*γ*C2*r^(γ-1)!
    have hrγ_lt : r ^ γ < (δ : ℝ) / (6 * A) := by
      have hlt := Real.rpow_lt_rpow hr0.le hr2' hγ0
      have hu1γ : u1 ^ γ = (δ : ℝ) / (6 * A) := by
        dsimp [u1]; rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hγ0.ne', Real.rpow_one]
      rwa [hu1γ] at hlt
    have hδr_gt : 6 * A * r ^ (γ - 1) < (δ : ℝ) / r := by
      have h1 : 6 * A * r ^ γ < (δ : ℝ) := by
        have := (lt_div_iff₀ (by positivity : 0 < 6 * A)).mp hrγ_lt
        linarith
      have hrp : r ^ (γ - 1) = r ^ γ / r := by rw [Real.rpow_sub hr0, Real.rpow_one]
      rw [hrp, ← mul_div_assoc]
      exact div_lt_div_of_pos_right h1 hr0
    have hterm_gt : 3 * γ * C2 * r ^ (γ - 1) < evalGen L0 r * ((δ : ℝ) / r) := by
      have hG_lo : C1 / 2 ≤ evalGen L0 r := hb.1
      have hA_eq : (C1 / 2) * (6 * A * r ^ (γ - 1)) = 3 * γ * C2 * r ^ (γ - 1) := by
        dsimp [A]; field_simp [hC1.ne']; ring
      have hpos1 : 0 < 6 * A * r ^ (γ - 1) := by positivity
      calc 3 * γ * C2 * r ^ (γ - 1)
          = (C1 / 2) * (6 * A * r ^ (γ - 1)) := hA_eq.symm
        _ ≤ evalGen L0 r * (6 * A * r ^ (γ - 1)) := mul_le_mul_of_nonneg_right hG_lo hpos1.le
        _ < evalGen L0 r * ((δ : ℝ) / r) := mul_lt_mul_of_pos_left hδr_gt (by linarith)
    have hM_pos : 0 ≤ evalGen L0 r * ((M : ℝ) / (1 - r)) := by
      have : 0 < evalGen L0 r := by linarith [hb.1]
      have : 0 < 1 - r := by linarith
      positivity
    have hpos_d : 0 < derivGen L0 r + evalGen L0 r * ((δ : ℝ) / r + (M : ℝ) / (1 - r)) := by
      have : 0 < γ * C2 * r ^ (γ - 1) := by positivity
      linarith [hb.2.2.2.1]
    exact hpos_d.ne'
  -- Root 2 in (u2, uB): at any zero r ∈ [u2, uB], derivGen L_new r < 0!
  have hnew2 : ∃ r, u2 < r ∧ r < uB ∧ evalGen L_new r = 0 ∧ derivGen L_new r ≠ 0 := by
    have hcont : ContinuousOn (evalGen L_new) (Set.Icc u2 uB) :=
      (continuousOn_evalGen L_new).mono (fun u hu => ⟨lt_of_lt_of_le hu20 hu.1, by linarith [hu.2]⟩)
    obtain ⟨r, ⟨hr1, hr2⟩, hFr⟩ := intermediate_value_Icc' hu2_lt_uB.le hcont ⟨hF_uB_neg.le, hF_u2_pos.le⟩
    have hr1' : u2 < r := lt_of_le_of_ne hr1 (fun h => by subst h; linarith)
    have hr2' : r < uB := lt_of_le_of_ne hr2 (fun h => by subst h; linarith)
    have hr0 : 0 < r := lt_trans hu20 hr1'
    have hrC : r ≤ uC := (lt_trans hr2' huB_lt_uC).le
    refine ⟨r, hr1', hr2', hFr, ?_⟩
    rw [hderiv_at_zero r ⟨hr0, by linarith⟩ hFr]
    have hb := huC_bounds r ⟨hr0, hrC⟩
    -- 1. r > u2 = (8*δ/A)^(1/γ) => δ/r < (A/8) * r^(γ-1)
    have hδr_lt : (δ : ℝ) / r < (A / 8) * r ^ (γ - 1) := by
      have hgt := Real.rpow_lt_rpow hu20.le hr1' hγ0
      have hu2γ : u2 ^ γ = 8 * (δ : ℝ) / A := by
        dsimp [u2]; rw [← Real.rpow_mul (by positivity), one_div_mul_cancel hγ0.ne', Real.rpow_one]
      rw [hu2γ] at hgt
      have h1 : (δ : ℝ) < (A / 8) * r ^ γ := by
        have := (div_lt_iff₀ hA).mp hgt; linarith
      have hrp : r ^ (γ - 1) = r ^ γ / r := by rw [Real.rpow_sub hr0, Real.rpow_one]
      rw [hrp, ← mul_div_assoc]
      exact div_lt_div_of_pos_right h1 hr0
    -- 2. r < uB = (A/(16*M))^(1/(1-γ)) => M < (A/16) * r^(γ-1), and 1-r > 1/2 => M/(1-r) < (A/8) * r^(γ-1)
    have hMr_lt : (M : ℝ) / (1 - r) < (A / 8) * r ^ (γ - 1) := by
      have h1mg : 0 < 1 - γ := by linarith
      have hlt := Real.rpow_lt_rpow hr0.le hr2' h1mg
      have huB1 : uB ^ (1 - γ) = A / (16 * (M : ℝ)) := by
        dsimp [uB]; rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1mg.ne', Real.rpow_one]
      rw [huB1] at hlt
      have hM_lt : (M : ℝ) < (A / 16) * r ^ (γ - 1) := by
        have h1 : (M : ℝ) * r ^ (1 - γ) < A / 16 := by
          have := (lt_div_iff₀ (by positivity)).mp hlt; linarith
        have hinv : r ^ (γ - 1) = (r ^ (1 - γ))⁻¹ := by
          rw [← Real.rpow_neg hr0.le]; congr 1; ring
        rw [hinv, ← div_eq_mul_inv]
        exact (lt_div_iff₀ (Real.rpow_pos_of_pos hr0 _)).mpr h1
      have h1mr : (1 : ℝ) / 2 < 1 - r := by linarith
      have hdiv : (M : ℝ) / (1 - r) < 2 * (M : ℝ) := by
        rw [div_lt_iff₀ (by linarith)]; nlinarith
      linarith
    have hG_le_C1 : evalGen L0 r ≤ C1 := by
      have : 0 ≤ (1 / 2) * C2 * r ^ γ := by positivity
      linarith [hb.2.2.1]
    have hG_pos : 0 < evalGen L0 r := by linarith [hb.1]
    have hsum_lt : evalGen L0 r * ((δ : ℝ) / r + (M : ℝ) / (1 - r)) < (1 / 4) * γ * C2 * r ^ (γ - 1) := by
      have hcomb : (δ : ℝ) / r + (M : ℝ) / (1 - r) < (A / 4) * r ^ (γ - 1) := by linarith
      have hA4 : C1 * ((A / 4) * r ^ (γ - 1)) = (1 / 4) * γ * C2 * r ^ (γ - 1) := by
        dsimp [A]; field_simp [hC1.ne']
      calc evalGen L0 r * ((δ : ℝ) / r + (M : ℝ) / (1 - r))
          < evalGen L0 r * ((A / 4) * r ^ (γ - 1)) := mul_lt_mul_of_pos_left hcomb hG_pos
        _ ≤ C1 * ((A / 4) * r ^ (γ - 1)) := mul_le_mul_of_nonneg_right hG_le_C1 (by positivity)
        _ = (1 / 4) * γ * C2 * r ^ (γ - 1) := hA4
    have hneg_d : derivGen L0 r + evalGen L0 r * ((δ : ℝ) / r + (M : ℝ) / (1 - r)) < 0 := by
      have : 0 < γ * C2 * r ^ (γ - 1) := by positivity
      linarith [hb.2.2.2.2]
    exact hneg_d.ne
  -- Root 3 in (u3, uC): at any zero r ∈ [u3, uC], derivGen L_new r > 0!
  have hnew3 : ∃ r, u3 < r ∧ r < uC ∧ evalGen L_new r = 0 ∧ derivGen L_new r ≠ 0 := by
    have hcont : ContinuousOn (evalGen L_new) (Set.Icc u3 uC) :=
      (continuousOn_evalGen L_new).mono (fun u hu => ⟨lt_of_lt_of_le hu30 hu.1, by linarith [hu.2]⟩)
    obtain ⟨r, ⟨hr1, hr2⟩, hFr⟩ := intermediate_value_Icc hu3_lt_uC.le hcont ⟨hF_u3_neg.le, hF_uC_pos.le⟩
    have hr1' : u3 < r := lt_of_le_of_ne hr1 (fun h => by subst h; linarith)
    have hr2' : r < uC := lt_of_le_of_ne hr2 (fun h => by subst h; linarith)
    have hr0 : 0 < r := lt_trans hu30 hr1'
    refine ⟨r, hr1', hr2', hFr, ?_⟩
    rw [hderiv_at_zero r ⟨hr0, by linarith⟩ hFr]
    have hb := huC_bounds r ⟨hr0, hr2'.le⟩
    -- r > u3 = (4*A/M)^(1/(1-γ)) => M > 4*A*r^(γ-1) => M/(1-r) > 4*A*r^(γ-1)
    -- => G(r) * M/(1-r) > (C1/2)*4*A*r^(γ-1) = 2*γ*C2*r^(γ-1) > (3/2)*γ*C2*r^(γ-1) >= -G'(r)!
    have hMr_gt : 4 * A * r ^ (γ - 1) < (M : ℝ) / (1 - r) := by
      have h1mg : 0 < 1 - γ := by linarith
      have hgt := Real.rpow_lt_rpow hu30.le hr1' h1mg
      have hu31 : u3 ^ (1 - γ) = 4 * A / (M : ℝ) := by
        dsimp [u3]; rw [← Real.rpow_mul (by positivity), one_div_mul_cancel h1mg.ne', Real.rpow_one]
      rw [hu31] at hgt
      have hM_gt : 4 * A * r ^ (γ - 1) < (M : ℝ) := by
        have h1 : 4 * A < (M : ℝ) * r ^ (1 - γ) := by
          have := (div_lt_iff₀ hMp).mp hgt; linarith
        have hinv : r ^ (γ - 1) = (r ^ (1 - γ))⁻¹ := by
          rw [← Real.rpow_neg hr0.le]; congr 1; ring
        rw [hinv, ← div_eq_mul_inv]
        exact (div_lt_iff₀ (Real.rpow_pos_of_pos hr0 _)).mpr h1
      have hlt_div : (M : ℝ) < (M : ℝ) / (1 - r) := by
        rw [lt_div_iff₀ (by linarith)]; nlinarith
      linarith
    have hterm_gt : 2 * γ * C2 * r ^ (γ - 1) < evalGen L0 r * ((M : ℝ) / (1 - r)) := by
      have hG_lo : C1 / 2 ≤ evalGen L0 r := hb.1
      have hA_eq : (C1 / 2) * (4 * A * r ^ (γ - 1)) = 2 * γ * C2 * r ^ (γ - 1) := by
        dsimp [A]; field_simp [hC1.ne']; ring
      calc 2 * γ * C2 * r ^ (γ - 1)
          = (C1 / 2) * (4 * A * r ^ (γ - 1)) := hA_eq.symm
        _ ≤ evalGen L0 r * (4 * A * r ^ (γ - 1)) := mul_le_mul_of_nonneg_right hG_lo (by positivity)
        _ < evalGen L0 r * ((M : ℝ) / (1 - r)) := mul_lt_mul_of_pos_left hMr_gt (by linarith)
    have hδ_pos' : 0 ≤ evalGen L0 r * ((δ : ℝ) / r) := by
      have : 0 < evalGen L0 r := by linarith [hb.1]
      positivity
    have hpos_d : 0 < derivGen L0 r + evalGen L0 r * ((δ : ℝ) / r + (M : ℝ) / (1 - r)) := by
      have : 0 < γ * C2 * r ^ (γ - 1) := by positivity
      linarith [hb.2.2.2.1]
    exact hpos_d.ne'
  -- 10. Persist the R old simple roots in (uC, 1)!
  have hclose_uC : ∀ u ∈ Set.Ico uC 1,
      |evalGen L_new u - evalGen L0 u| < ε ∧ |derivGen L_new u - derivGen L0 u| < ε := by
    intro u hu
    have hu0 : 0 < u := lt_of_lt_of_le huC0 hu.1
    have hu1 : u < 1 := hu.2
    have hur_le : u ^ (-(δ : ℝ)) ≤ uC ^ (-(δ : ℝ)) := by
      rw [Real.rpow_neg hu0.le, Real.rpow_neg huC0.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos huC0 _) (Real.rpow_le_rpow huC0.le hu.1 hδr.le)
    have h1mu_le : (1 - u) ^ M ≤ (1 - uC) ^ M :=
      pow_le_pow_left₀ (by linarith) (by linarith [hu.1]) M
    have h1 : (c_new : ℝ) * u ^ (-(δ : ℝ)) ≤ 2 * C1 := by
      have hpos : 0 < uC ^ (-(δ : ℝ)) := Real.rpow_pos_of_pos huC0 _
      calc (c_new : ℝ) * u ^ (-(δ : ℝ))
          ≤ (c_new : ℝ) * uC ^ (-(δ : ℝ)) := mul_le_mul_of_nonneg_left hur_le hc_pos.le
        _ ≤ C1 * uC ^ (-(δ : ℝ)) := mul_le_mul_of_nonneg_right hc_lt_C1.le hpos.le
        _ ≤ C1 * 2 := mul_le_mul_of_nonneg_left huC_rpow_lt2.le hC1.le
        _ = 2 * C1 := mul_comm C1 2
    have hpert_le : (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M ≤ 2 * C1 * (1 - uC) ^ M := by
      have hp : 0 ≤ (1 - u) ^ M := pow_nonneg (by linarith) M
      have h2 : (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M ≤ 2 * C1 * (1 - u) ^ M :=
        mul_le_mul_of_nonneg_right h1 hp
      exact h2.trans (mul_le_mul_of_nonneg_left h1mu_le (by positivity))
    constructor
    · rw [hLnew_eval u, sub_sub_cancel_left, abs_neg,
        abs_of_pos (mul_pos (mul_pos hc_pos (Real.rpow_pos_of_pos hu0 _)) (pow_pos (by linarith) M))]
      exact lt_of_le_of_lt hpert_le hpow_ε
    · rw [hLnew_deriv u ⟨hu0, hu1⟩, add_sub_cancel_left]
      have hpos_d : 0 < (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M * ((δ : ℝ) / u + (M : ℝ) / (1 - u)) := by
        have : 0 < 1 - u := by linarith
        have : 0 < u ^ (-(δ : ℝ)) := Real.rpow_pos_of_pos hu0 _
        positivity
      rw [abs_of_pos hpos_d]
      -- Bound (c_new * u^(-δ) * (1-u)^M) * (δ/u + M/(1-u)) <= 2*C1*(1-uC)^M * (1/uC + M/(1-uC)) < ε!
      -- Notice (1-u)^M * (M/(1-u)) = M * (1-u)^(M-1) <= M * (1-uC)^(M-1) = (1-uC)^M * (M/(1-uC))!
      have hterm1 : (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M * ((δ : ℝ) / u) ≤
          2 * C1 * (1 - uC) ^ M * (1 / uC) := by
        have hδu : (δ : ℝ) / u ≤ 1 / uC := by
          calc (δ : ℝ) / u ≤ 1 / u := div_le_div_of_nonneg_right hδ_lt1.le hu0.le
            _ ≤ 1 / uC := one_div_le_one_div_of_le huC0 hu.1
        have h1mC : 0 ≤ 1 - uC := by linarith
        exact mul_le_mul hpert_le hδu (div_nonneg hδr.le hu0.le)
          (mul_nonneg (mul_nonneg zero_le_two hC1.le) (pow_nonneg h1mC M))
      have hterm2 : (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M * ((M : ℝ) / (1 - u)) ≤
          2 * C1 * (1 - uC) ^ M * ((M : ℝ) / (1 - uC)) := by
        have hpow_m1 : (1 - u) ^ M * ((M : ℝ) / (1 - u)) = (M : ℝ) * (1 - u) ^ (M - 1) := by
          cases M with
          | zero => omega
          | succ k => simp [pow_succ]; field_simp [(by linarith : 1 - u ≠ 0)]
        have hpow_m1C : (1 - uC) ^ M * ((M : ℝ) / (1 - uC)) = (M : ℝ) * (1 - uC) ^ (M - 1) := by
          cases M with
          | zero => omega
          | succ k => simp [pow_succ]; field_simp [(by linarith : 1 - uC ≠ 0)]
        rw [mul_assoc, hpow_m1, mul_assoc (2 * C1), hpow_m1C]
        have hm1 : (1 - u) ^ (M - 1) ≤ (1 - uC) ^ (M - 1) :=
          pow_le_pow_left₀ (by linarith) (by linarith [hu.1]) (M - 1)
        exact mul_le_mul h1 (mul_le_mul_of_nonneg_left hm1 hMp.le)
          (mul_nonneg hMp.le (pow_nonneg (by linarith) (M - 1)))
          (mul_nonneg zero_le_two hC1.le)
      calc (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M * ((δ : ℝ) / u + (M : ℝ) / (1 - u))
          = (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M * ((δ : ℝ) / u) +
            (c_new : ℝ) * u ^ (-(δ : ℝ)) * (1 - u) ^ M * ((M : ℝ) / (1 - u)) := mul_add _ _ _
        _ ≤ 2 * C1 * (1 - uC) ^ M * (1 / uC) +
            2 * C1 * (1 - uC) ^ M * ((M : ℝ) / (1 - uC)) := add_le_add hterm1 hterm2
        _ = 2 * C1 * (1 - uC) ^ M * (1 / uC + (M : ℝ) / (1 - uC)) := (mul_add _ _ _).symm
        _ < ε := hpow_dε
  obtain ⟨old_nr, hold_nr⟩ := hold_pers (evalGen L_new) (derivGen L_new)
    (fun u hu => hasDerivAt_evalGen L_new hu.1 hu.2) hclose_uC
  -- 11. Assemble all R + 3 = 3*(t+1) - 4 strictly increasing simple roots!
  obtain ⟨ra, hra1, hra2, hra3, hra4⟩ := hnew1
  obtain ⟨rb, hrb1, hrb2, hrb3, hrb4⟩ := hnew2
  obtain ⟨rc, hrc1, hrc2, hrc3, hrc4⟩ := hnew3
  have hra := And.intro hra1 (And.intro hra2 (And.intro hra3 hra4))
  have hrb := And.intro hrb1 (And.intro hrb2 (And.intro hrb3 hrb4))
  have hrc := And.intro hrc1 (And.intro hrc2 (And.intro hrc3 hrc4))
  have hR3 : 3 * (t + 1) - 4 = R + 3 := by dsimp [R]; omega
  let new_roots : Fin (3 * (t + 1) - 4) → ℝ := fun k =>
    if h0 : k.1 = 0 then ra
    else if h1 : k.1 = 1 then rb
    else if h2 : k.1 = 2 then rc
    else old_nr ⟨k.1 - 3, by omega⟩
  have hrest_new_nodup : ((L0).map Prod.snd).Nodup := by
    rw [hL0_eq]
    have hnd := I.terms_nodup
    have hinj : Function.Injective (fun p : ℚ × ℚ => (p.1 - I.a1, p.2)) := by
      intro p1 p2 hp
      simp only [Prod.mk.injEq, sub_left_inj] at hp
      exact Prod.ext hp.1 hp.2
    have hmap : ((shiftScale sgn I.a1 I.terms).map Prod.snd) =
        (I.terms.map Prod.snd).map (fun p => (p.1 - I.a1, p.2)) := by
      simp [shiftScale, List.map_map]
    rw [hmap]
    exact hnd.map hinj
  exact ⟨{
    c1 := -c_new
    c2 := c1'
    a1 := -δ
    a2 := 0
    b1 := (M : ℚ)
    b2 := I.b1
    rest := (c2', γq, I.b2) :: rest'
    len_eq := by simp [rest', shiftScale, I.len_eq]
    hc1 := neg_ne_zero.mpr (by exact_mod_cast hc_pos.ne')
    hc2 := by
      have h : (c1' : ℝ) ≠ 0 := hC1.ne'
      exact_mod_cast h
    hrest_c := by
      intro term ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · exact_mod_cast (by linarith : (c2' : ℝ) ≠ 0)
      · rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
        exact mul_ne_zero hsgn_ne (I.hrest_c orig horig)
    hopp := by
      push_cast
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc_pos) hC1
    ha_lt := by linarith
    ha_gap := by
      have : δ < 1 / 16 := lt_trans hδ_lt_γ I.ha_gap
      linarith
    hrest_a := by
      intro term ht
      simp only [List.mem_cons] at ht
      rcases ht with rfl | ht
      · dsimp [γq]; linarith [I.ha_lt]
      · have hgt := hrest'_a term ht
        have : (0 : ℝ) < (term.2.1 : ℝ) := lt_trans hγ0 hgt
        exact_mod_cast this
    hrest_nodup := by
      simp only [L0, List.map_cons, List.nodup_cons] at hrest_new_nodup ⊢
      exact hrest_new_nodup.2
    roots := new_roots
    roots_mono := by
      intro i j hij
      have hlt_ij : i.1 < j.1 := hij
      dsimp only [new_roots]
      split_ifs <;> try omega
      · linarith [hra.2.1, hu1_lt_u2, hrb.1]
      · linarith [hra.2.1, hu1_lt_u2, hu2_lt_uB, huB_lt_u3, hrc.1]
      · linarith [hra.2.1, hu1_lt_uC, (hold_nr ⟨j.1 - 3, by omega⟩).1, (hold_in ⟨j.1 - 3, by omega⟩).1]
      · linarith [hrb.2.1, huB_lt_u3, hrc.1]
      · linarith [hrb.2.1, huB_lt_uC, (hold_nr ⟨j.1 - 3, by omega⟩).1, (hold_in ⟨j.1 - 3, by omega⟩).1]
      · linarith [hrc.2.1, (hold_nr ⟨j.1 - 3, by omega⟩).1, (hold_in ⟨j.1 - 3, by omega⟩).1]
      · have hbi := (hold_nr ⟨i.1 - 3, by omega⟩).2.1
        have haj := (hold_nr ⟨j.1 - 3, by omega⟩).1
        have hdis := hold_disj ⟨i.1 - 3, by omega⟩ ⟨j.1 - 3, by omega⟩ (by simp [Fin.lt_def]; omega)
        linarith
    roots_pos := by
      intro k; dsimp only [new_roots]
      split_ifs
      · linarith [hra.1]
      · linarith [hrb.1]
      · linarith [hrc.1]
      · linarith [(hold_nr ⟨k.1 - 3, by omega⟩).1, (hold_in ⟨k.1 - 3, by omega⟩).1]
    roots_lt1 := by
      intro k; dsimp only [new_roots]
      split_ifs
      · linarith [hra.2.1, hu1_lt_uC]
      · linarith [hrb.2.1, huB_lt_uC]
      · linarith [hrc.2.1]
      · linarith [(hold_nr ⟨k.1 - 3, by omega⟩).2.1, (hold_in ⟨k.1 - 3, by omega⟩).2.2.2]
    roots_zero := by
      intro k; dsimp only [new_roots]
      change evalGen L_new _ = 0
      split_ifs
      · exact hra.2.2.1
      · exact hrb.2.2.1
      · exact hrc.2.2.1
      · exact (hold_nr ⟨k.1 - 3, by omega⟩).2.2.1
    roots_simple := by
      intro k; dsimp only [new_roots]
      change derivGen L_new _ ≠ 0
      split_ifs
      · exact hra.2.2.2
      · exact hrb.2.2.2
      · exact hrc.2.2.2
      · exact (hold_nr ⟨k.1 - 3, by omega⟩).2.2.2
  }⟩

/-- Prove `Nonempty (GenInv t)` for EVERY `t ≥ 2` by induction! -/
theorem exists_genInv : ∀ t : ℕ, 2 ≤ t → Nonempty (GenInv t)
  | 0, h => absurd h (by omega)
  | 1, h => absurd h (by omega)
  | 2, _ => ⟨baseCase⟩
  | t + 1, h =>
    if h2 : 2 ≤ t then
      let ⟨I⟩ := exists_genInv t h2
      stepInsert_exists h2 I
    else by
      have ht1 : t = 1 := by omega
      subst ht1
      exact ⟨baseCase⟩

/-! ## Section 5: Clearing Denominators to Exact Integer Polynomials `f, g ∈ ℤ[X, Y]` -/

/-- Common positive denominator of all rational exponents `(a, b)` in a list. -/
def expDenom (L : List (ℚ × ℚ × ℚ)) : ℕ :=
  L.foldr (fun t acc => Nat.lcm (Nat.lcm t.2.1.den t.2.2.den) acc) 1

lemma expDenom_pos (L : List (ℚ × ℚ × ℚ)) : 0 < expDenom L := by
  induction L with
  | nil => simp [expDenom]
  | cons hd tl ih =>
    simp only [expDenom, List.foldr_cons]
    exact Nat.lcm_pos (Nat.lcm_pos hd.2.1.pos hd.2.2.pos) ih

lemma dvd_expDenom_a {L : List (ℚ × ℚ × ℚ)} {t : ℚ × ℚ × ℚ} (ht : t ∈ L) :
    t.2.1.den ∣ expDenom L := by
  induction L with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [expDenom, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact dvd_trans (Nat.dvd_lcm_left _ _) (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (ih ht) (Nat.dvd_lcm_right _ _)

lemma dvd_expDenom_b {L : List (ℚ × ℚ × ℚ)} {t : ℚ × ℚ × ℚ} (ht : t ∈ L) :
    t.2.2.den ∣ expDenom L := by
  induction L with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [expDenom, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact dvd_trans (Nat.dvd_lcm_right _ _) (Nat.dvd_lcm_left _ _)
    · exact dvd_trans (ih ht) (Nat.dvd_lcm_right _ _)

/-- Common positive denominator of all rational coefficients `c` in a list. -/
def coeffDenom (L : List (ℚ × ℚ × ℚ)) : ℕ :=
  L.foldr (fun t acc => Nat.lcm t.1.den acc) 1

lemma coeffDenom_pos (L : List (ℚ × ℚ × ℚ)) : 0 < coeffDenom L := by
  induction L with
  | nil => simp [coeffDenom]
  | cons hd tl ih =>
    simp only [coeffDenom, List.foldr_cons]
    exact Nat.lcm_pos hd.1.pos ih

lemma dvd_coeffDenom {L : List (ℚ × ℚ × ℚ)} {t : ℚ × ℚ × ℚ} (ht : t ∈ L) :
    t.1.den ∣ coeffDenom L := by
  induction L with
  | nil => simp at ht
  | cons hd tl ih =>
    simp only [coeffDenom, List.foldr_cons]
    rcases List.mem_cons.mp ht with rfl | ht
    · exact Nat.dvd_lcm_left _ _
    · exact dvd_trans (ih ht) (Nat.dvd_lcm_right _ _)

/-- Exact integer numerator when multiplying `q : ℚ` by a multiple `M : ℕ` of `q.den`. -/
def ratMulInt (M : ℕ) (q : ℚ) : ℤ := q.num * ((M / q.den : ℕ) : ℤ)

lemma ratMulInt_cast {M : ℕ} {q : ℚ} (hdvd : q.den ∣ M) :
    ((ratMulInt M q : ℤ) : ℝ) = (M : ℝ) * (q : ℝ) := by
  dsimp [ratMulInt]
  have hden : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.pos.ne'
  have hM : ((M / q.den : ℕ) : ℝ) * (q.den : ℝ) = (M : ℝ) := by
    exact_mod_cast Nat.div_mul_cancel hdvd
  rw [Rat.cast_def]
  push_cast
  rw [mul_div_assoc', eq_div_iff hden]
  calc (q.num : ℝ) * ((M / q.den : ℕ) : ℝ) * (q.den : ℝ)
      = (q.num : ℝ) * (((M / q.den : ℕ) : ℝ) * (q.den : ℝ)) := by ring
    _ = (q.num : ℝ) * (M : ℝ) := by rw [hM]
    _ = (M : ℝ) * (q.num : ℝ) := by ring

lemma le_foldr_max {α : Type*} (f : α → ℕ) (L : List α) {x : α} (hx : x ∈ L) :
    f x ≤ L.foldr (fun a acc => max (f a) acc) 0 := by
  induction L with
  | nil => simp at hx
  | cons hd tl ih =>
    rw [List.foldr_cons]
    rcases List.mem_cons.mp hx with rfl | hx
    · exact le_max_left _ _
    · exact le_trans (ih hx) (le_max_right _ _)

/-- **Theorem 1 (Formally Certified in Lean 4.36.0 — Infinite Lower Bound `S(3, t) ≥ 3t - 4`):**
    For every integer `t ≥ 3`, there exist explicit bivariate integer polynomials `f, g`
    where `f` is a trinomial (`3` distinct monomials) and `g` is a `t`-nomial (`t` distinct
    monomials) with nonzero integer coefficients, such that `f(x, y) = g(x, y) = 0` has at
    least `3 * t - 4` distinct, nondegenerate (`det J ≠ 0`), strictly positive real solutions
    in `(0, ∞)²`. -/
theorem fewnomial_lower_bound_3t_minus_4 (t : ℕ) (ht : 3 ≤ t) :
    ∃ (f g : List (ℤ × ℕ × ℕ)) (roots : Fin (3 * t - 4) → ℝ × ℝ),
      ValidFewnomial 3 f ∧
      ValidFewnomial t g ∧
      Function.Injective roots ∧
      ∀ k : Fin (3 * t - 4),
        0 < (roots k).1 ∧ 0 < (roots k).2 ∧
        evalPoly f (roots k).1 (roots k).2 = 0 ∧
        evalPoly g (roots k).1 (roots k).2 = 0 ∧
        evalPolyDx f (roots k).1 (roots k).2 * evalPolyDy g (roots k).1 (roots k).2 -
          evalPolyDy f (roots k).1 (roots k).2 * evalPolyDx g (roots k).1 (roots k).2 ≠ 0 := by
  obtain ⟨I⟩ := exists_genInv t (by omega)
  let L := I.terms
  let D : ℕ := expDenom L
  let C : ℕ := coeffDenom L
  have hD : 0 < D := expDenom_pos L
  have hC : 0 < C := coeffDenom_pos L
  -- Nonnegative shifts P, Q clearing all negative integer exponents D*a_j, D*b_j
  let P : ℕ := L.foldr (fun term acc => max (ratMulInt D term.2.1).natAbs acc) 0
  let Q : ℕ := L.foldr (fun term acc => max (ratMulInt D term.2.2).natAbs acc) 0
  have hP_le : ∀ term ∈ L, 0 ≤ ratMulInt D term.2.1 + (P : ℤ) := by
    intro term hmem
    have habs : (ratMulInt D term.2.1).natAbs ≤ P :=
      le_foldr_max (fun t => (ratMulInt D t.2.1).natAbs) L hmem
    omega
  have hQ_le : ∀ term ∈ L, 0 ≤ ratMulInt D term.2.2 + (Q : ℤ) := by
    intro term hmem
    have habs : (ratMulInt D term.2.2).natAbs ≤ Q :=
      le_foldr_max (fun t => (ratMulInt D t.2.2).natAbs) L hmem
    omega
  -- Construct the explicit trinomial f(x, y) = x^D + y^D - 1 and t-nomial g(x, y)!
  let f : List (ℤ × ℕ × ℕ) := [(1, D, 0), (1, 0, D), (-1, 0, 0)]
  let g : List (ℤ × ℕ × ℕ) := L.map fun term =>
    (ratMulInt C term.1,
     (ratMulInt D term.2.1 + (P : ℤ)).toNat,
     (ratMulInt D term.2.2 + (Q : ℤ)).toNat)
  -- Positive roots (x_k, y_k) = (r_k^(1/D), (1 - r_k)^(1/D))!
  let roots : Fin (3 * t - 4) → ℝ × ℝ := fun k =>
    ((I.roots k) ^ ((1 : ℝ) / (D : ℝ)), (1 - I.roots k) ^ ((1 : ℝ) / (D : ℝ)))
  -- Prove exact correspondence: for any x, y > 0 with x^D = u and y^D = 1 - u,
  -- evalPoly g x y = C * x^P * y^Q * evalGen L u!
  have hg_eval : ∀ u : ℝ, 0 < u → u < 1 →
      evalPoly g (u ^ ((1 : ℝ) / (D : ℝ))) ((1 - u) ^ ((1 : ℝ) / (D : ℝ))) =
        (C : ℝ) * (u ^ ((1 : ℝ) / (D : ℝ))) ^ P * ((1 - u) ^ ((1 : ℝ) / (D : ℝ))) ^ Q *
          evalGen L u := by
    intro u hu0 hu1
    have hx0 : 0 < u ^ ((1 : ℝ) / (D : ℝ)) := Real.rpow_pos_of_pos hu0 _
    have hy0 : 0 < (1 - u) ^ ((1 : ℝ) / (D : ℝ)) := Real.rpow_pos_of_pos (by linarith) _
    have hD_ne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    -- Generalize over sublists of L
    have hsub : ∀ sub : List (ℚ × ℚ × ℚ), (∀ term ∈ sub, term ∈ L) →
        evalPoly (sub.map fun term =>
          (ratMulInt C term.1,
           (ratMulInt D term.2.1 + (P : ℤ)).toNat,
           (ratMulInt D term.2.2 + (Q : ℤ)).toNat))
          (u ^ ((1 : ℝ) / (D : ℝ))) ((1 - u) ^ ((1 : ℝ) / (D : ℝ))) =
        (C : ℝ) * (u ^ ((1 : ℝ) / (D : ℝ))) ^ P * ((1 - u) ^ ((1 : ℝ) / (D : ℝ))) ^ Q *
          evalGen sub u := by
      intro sub hmem
      induction sub with
      | nil => simp [evalPoly, evalGen]
      | cons hd tl ih =>
        have hhd := hmem hd (by simp)
        have htl := ih (fun z hz => hmem z (by simp [hz]))
        simp only [evalPoly, evalGen, List.map_cons, List.sum_cons] at htl ⊢
        rw [htl, mul_add]
        congr 1
        have hc_eq : ((ratMulInt C hd.1 : ℤ) : ℝ) = (C : ℝ) * (hd.1 : ℝ) :=
          ratMulInt_cast (dvd_coeffDenom hhd)
        have ha_nn := hP_le hd hhd
        have hb_nn := hQ_le hd hhd
        have ha_cast : (((ratMulInt D hd.2.1 + (P : ℤ)).toNat : ℕ) : ℝ) =
            (D : ℝ) * (hd.2.1 : ℝ) + (P : ℝ) := by
          have hz : ((ratMulInt D hd.2.1 + (P : ℤ)).toNat : ℤ) = ratMulInt D hd.2.1 + (P : ℤ) :=
            Int.toNat_of_nonneg ha_nn
          have hr : (((ratMulInt D hd.2.1 + (P : ℤ)).toNat : ℤ) : ℝ) =
              ((ratMulInt D hd.2.1 + (P : ℤ) : ℤ) : ℝ) := congrArg Int.cast hz
          simp only [Int.cast_natCast, Int.cast_add] at hr
          rw [hr, ratMulInt_cast (dvd_expDenom_a hhd)]
        have hb_cast : (((ratMulInt D hd.2.2 + (Q : ℤ)).toNat : ℕ) : ℝ) =
            (D : ℝ) * (hd.2.2 : ℝ) + (Q : ℝ) := by
          have hz : ((ratMulInt D hd.2.2 + (Q : ℤ)).toNat : ℤ) = ratMulInt D hd.2.2 + (Q : ℤ) :=
            Int.toNat_of_nonneg hb_nn
          have hr : (((ratMulInt D hd.2.2 + (Q : ℤ)).toNat : ℤ) : ℝ) =
              ((ratMulInt D hd.2.2 + (Q : ℤ) : ℤ) : ℝ) := congrArg Int.cast hz
          simp only [Int.cast_natCast, Int.cast_add] at hr
          rw [hr, ratMulInt_cast (dvd_expDenom_b hhd)]
        have hx_pow : (u ^ ((1 : ℝ) / (D : ℝ))) ^ (ratMulInt D hd.2.1 + (P : ℤ)).toNat =
            (u ^ ((1 : ℝ) / (D : ℝ))) ^ P * u ^ (hd.2.1 : ℝ) := by
          rw [← Real.rpow_natCast, ha_cast, ← Real.rpow_mul hu0.le,
            ← Real.rpow_natCast (u ^ _), ← Real.rpow_mul hu0.le, ← Real.rpow_add hu0]
          congr 1; field_simp [hD_ne]; ring
        have hy_pow : ((1 - u) ^ ((1 : ℝ) / (D : ℝ))) ^ (ratMulInt D hd.2.2 + (Q : ℤ)).toNat =
            ((1 - u) ^ ((1 : ℝ) / (D : ℝ))) ^ Q * (1 - u) ^ (hd.2.2 : ℝ) := by
          rw [← Real.rpow_natCast, hb_cast, ← Real.rpow_mul (by linarith),
            ← Real.rpow_natCast ((1 - u) ^ _), ← Real.rpow_mul (by linarith),
            ← Real.rpow_add (by linarith)]
          congr 1; field_simp [hD_ne]; ring
        rw [hc_eq, hx_pow, hy_pow]
        ring
    exact hsub L (fun _ h => h)
  refine ⟨f, g, roots, ?_, ?_, ?_, ?_⟩
  · -- ValidFewnomial 3 f
    refine ⟨rfl, ?_, ?_⟩
    · intro term ht; simp [f] at ht; rcases ht with rfl | rfl | rfl <;> norm_num
    · simp only [f, List.map_cons, List.map_nil, List.nodup_cons, List.mem_cons,
        List.not_mem_nil, or_false, Prod.mk.injEq, not_or]
      refine ⟨⟨?_, ?_⟩, ?_, by simp⟩ <;> omega
  · -- ValidFewnomial t g
    refine ⟨?_, ?_, ?_⟩
    · simp [g, L, GenInv.terms, I.len_eq]
    · intro term ht
      rcases List.mem_map.mp ht with ⟨orig, horig, rfl⟩
      have hne : (orig.1 : ℝ) ≠ 0 := by
        simp only [L, GenInv.terms, List.mem_cons] at horig
        rcases horig with rfl | rfl | horig
        · exact_mod_cast I.hc1
        · exact_mod_cast I.hc2
        · exact_mod_cast I.hrest_c orig horig
      intro h0
      dsimp only at h0
      have hr := ratMulInt_cast (dvd_coeffDenom horig)
      rw [h0] at hr
      have hC_ne : (C : ℝ) ≠ 0 := by exact_mod_cast hC.ne'
      have : (C : ℝ) * (orig.1 : ℝ) = 0 := by simpa using hr.symm
      exact mul_ne_zero hC_ne hne this
    · -- Nodup of exponents of g (injective linear map from Nodup exponents of L!)
      have hnd := I.terms_nodup
      have hmap : g.map Prod.snd =
          (L.map Prod.snd).map (fun ab =>
            ((ratMulInt D ab.1 + (P : ℤ)).toNat, (ratMulInt D ab.2 + (Q : ℤ)).toNat)) := by
        simp [g, List.map_map]
      rw [hmap]
      -- Prove Nodup using pairwise distinctness on elements of L
      rw [List.nodup_map_iff_inj_on hnd]
      intro ab1 hab1 ab2 hab2 heq
      rcases List.mem_map.mp hab1 with ⟨t1, ht1, rfl⟩
      rcases List.mem_map.mp hab2 with ⟨t2, ht2, rfl⟩
      simp only [Prod.mk.injEq] at heq
      have ha1 := hP_le t1 ht1; have ha2 := hP_le t2 ht2
      have hb1 := hQ_le t1 ht1; have hb2 := hQ_le t2 ht2
      have h1 : ((ratMulInt D t1.2.1 : ℤ) : ℝ) = ((ratMulInt D t2.2.1 : ℤ) : ℝ) := by
        have hz : ratMulInt D t1.2.1 + (P : ℤ) = ratMulInt D t2.2.1 + (P : ℤ) := by
          have hcast : ((ratMulInt D t1.2.1 + (P : ℤ)).toNat : ℤ) =
              ((ratMulInt D t2.2.1 + (P : ℤ)).toNat : ℤ) := congrArg Nat.cast heq.1
          rwa [Int.toNat_of_nonneg ha1, Int.toNat_of_nonneg ha2] at hcast
        have : ratMulInt D t1.2.1 = ratMulInt D t2.2.1 := by omega
        exact_mod_cast this
      have h2 : ((ratMulInt D t1.2.2 : ℤ) : ℝ) = ((ratMulInt D t2.2.2 : ℤ) : ℝ) := by
        have hz : ratMulInt D t1.2.2 + (Q : ℤ) = ratMulInt D t2.2.2 + (Q : ℤ) := by
          have hcast : ((ratMulInt D t1.2.2 + (Q : ℤ)).toNat : ℤ) =
              ((ratMulInt D t2.2.2 + (Q : ℤ)).toNat : ℤ) := congrArg Nat.cast heq.2
          rwa [Int.toNat_of_nonneg hb1, Int.toNat_of_nonneg hb2] at hcast
        have : ratMulInt D t1.2.2 = ratMulInt D t2.2.2 := by omega
        exact_mod_cast this
      rw [ratMulInt_cast (dvd_expDenom_a ht1), ratMulInt_cast (dvd_expDenom_a ht2)] at h1
      rw [ratMulInt_cast (dvd_expDenom_b ht1), ratMulInt_cast (dvd_expDenom_b ht2)] at h2
      have hD_ne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
      have ha_eq : t1.2.1 = t2.2.1 := by
        exact_mod_cast (mul_left_cancel₀ hD_ne h1)
      have hb_eq : t1.2.2 = t2.2.2 := by
        exact_mod_cast (mul_left_cancel₀ hD_ne h2)
      exact Prod.ext ha_eq hb_eq
  · -- Injectivity of roots (since x_k^D = I.roots k and I.roots is StrictMono!)
    intro i j hij
    have hx := congrArg Prod.fst hij
    dsimp [roots] at hx
    have hpow := congrArg (fun z : ℝ => z ^ D) hx
    have hi0 := I.roots_pos i; have hj0 := I.roots_pos j
    have hD_ne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have hpi : ((I.roots i) ^ ((1 : ℝ) / (D : ℝ))) ^ D = I.roots i := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hi0.le, one_div_mul_cancel hD_ne, Real.rpow_one]
    have hpj : ((I.roots j) ^ ((1 : ℝ) / (D : ℝ))) ^ D = I.roots j := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hj0.le, one_div_mul_cancel hD_ne, Real.rpow_one]
    rw [hpi, hpj] at hpow
    exact I.roots_mono.injective hpow
  · -- Strictly positive, f = 0, g = 0, and det J ≠ 0 at every root!
    intro k
    set rk := I.roots k
    set xk := rk ^ ((1 : ℝ) / (D : ℝ))
    set yk := (1 - rk) ^ ((1 : ℝ) / (D : ℝ))
    have hrk0 : 0 < rk := I.roots_pos k
    have hrk1 : rk < 1 := I.roots_lt1 k
    have hxk0 : 0 < xk := Real.rpow_pos_of_pos hrk0 _
    have hyk0 : 0 < yk := Real.rpow_pos_of_pos (by linarith) _
    have hD_ne : (D : ℝ) ≠ 0 := by exact_mod_cast hD.ne'
    have hxkD : xk ^ D = rk := by
      dsimp [xk]; rw [← Real.rpow_natCast, ← Real.rpow_mul hrk0.le, one_div_mul_cancel hD_ne, Real.rpow_one]
    have hykD : yk ^ D = 1 - rk := by
      dsimp [yk]; rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith), one_div_mul_cancel hD_ne, Real.rpow_one]
    refine ⟨hxk0, hyk0, ?_, ?_, ?_⟩
    · -- f(xk, yk) = 0
      simp only [f, evalPoly, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
        Int.cast_one, Int.cast_neg, pow_zero, mul_one, one_mul]
      rw [hxkD, hykD]; ring
    · -- g(xk, yk) = 0
      dsimp [roots]
      rw [hg_eval rk hrk0 hrk1, I.terms_zero k, mul_zero]
    · -- Nonzero Jacobian determinant det J(xk, yk) ≠ 0 via chain rule along y(x) = (1 - x^D)^(1/D)!
      let yf : ℝ → ℝ := fun s => (1 - s ^ D) ^ ((1 : ℝ) / (D : ℝ))
      have hyf_eq : yf xk = yk := by dsimp [yf, yk]; rw [hxkD]
      have hyf_deriv : HasDerivAt yf (-(xk ^ (D - 1) / yk ^ (D - 1))) xk := by
        have hsub : HasDerivAt (fun s : ℝ => 1 - s ^ D) (-((D : ℝ) * xk ^ (D - 1))) xk := by
          simpa using (hasDerivAt_pow D xk).const_sub (1 : ℝ)
        have hcomp := hsub.rpow_const (p := (1 : ℝ) / (D : ℝ)) (Or.inl (by rw [hxkD]; linarith))
        refine hcomp.congr_deriv ?_
        have hyk_m1 : (1 - xk ^ D) ^ ((1 : ℝ) / (D : ℝ) - 1) = (yk ^ (D - 1))⁻¹ := by
          rw [hxkD]
          have h1 : (1 - rk) ^ ((1 : ℝ) / (D : ℝ) - 1) = ((1 - rk) ^ (1 - (1 : ℝ) / (D : ℝ)))⁻¹ := by
            rw [← Real.rpow_neg (by linarith)]; congr 1; ring
          rw [h1]; congr 1
          dsimp [yk]
          rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]
          congr 1
          have hDm1 : ((D - 1 : ℕ) : ℝ) = (D : ℝ) - 1 := Nat.cast_sub hD
          rw [hDm1]; field_simp [hD_ne]
        rw [hyk_m1]
        field_simp [hD_ne, (pow_pos hyk0 (D - 1)).ne']
      -- Chain rule 1: d/dx [g(x, yf(x))] at xk = evalPolyDx g xk yk - evalPolyDy g xk yk * (xk^(D-1)/yk^(D-1))
      have hd_poly := hasDerivAt_evalPoly_curve g hyf_eq hyf_deriv
      -- Chain rule 2: locally around xk, g(s, yf(s)) = C * s^P * yf(s)^Q * evalGen L (s^D)!
      have hloc : (fun s => evalPoly g s (yf s)) =ᶠ[nhds xk]
          (fun s => (C : ℝ) * s ^ P * (yf s) ^ Q * evalGen L (s ^ D)) := by
        have hopen : Set.Ioo (0 : ℝ) 1 ∈ nhds xk :=
          isOpen_Ioo.mem_nhds ⟨hxk0, by
            have : xk ^ D < 1 ^ D := by rw [hxkD, one_pow]; exact hrk1
            by_contra h; push Not at h
            have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) h D
            linarith⟩
        filter_upwards [hopen] with s hs
        have hsD0 : 0 < s ^ D := pow_pos hs.1 D
        have hsD1 : s ^ D < 1 := by
          have := pow_lt_pow_left₀ hs.2 hs.1.le hD.ne'; simpa using this
        have hs_eq : (s ^ D) ^ ((1 : ℝ) / (D : ℝ)) = s := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hs.1.le, mul_one_div_cancel hD_ne, Real.rpow_one]
        have h := hg_eval (s ^ D) hsD0 hsD1
        rw [hs_eq] at h
        exact h
      have hd_gen : HasDerivAt (fun s => (C : ℝ) * s ^ P * (yf s) ^ Q * evalGen L (s ^ D))
          ((C : ℝ) * xk ^ P * yk ^ Q * (derivGen L rk * ((D : ℝ) * xk ^ (D - 1)))) xk := by
        have hpref : DifferentiableAt ℝ (fun s => (C : ℝ) * s ^ P * (yf s) ^ Q) xk := by
          have h1 : DifferentiableAt ℝ (fun s : ℝ => (C : ℝ) * s ^ P) xk := by fun_prop
          have h2 : DifferentiableAt ℝ (fun s : ℝ => (yf s) ^ Q) xk :=
            (hyf_deriv.pow Q).differentiableAt
          exact h1.mul h2
        have hF : HasDerivAt (fun s => evalGen L (s ^ D))
            (derivGen L rk * ((D : ℝ) * xk ^ (D - 1))) xk := by
          have h1 := hasDerivAt_evalGen L hrk0 hrk1
          rw [← hxkD] at h1
          have hcomp : HasDerivAt (evalGen L ∘ fun s : ℝ => s ^ D)
              (derivGen L (xk ^ D) * ((D : ℝ) * xk ^ (D - 1))) xk :=
            h1.comp xk (hasDerivAt_pow D xk)
          rw [hxkD] at hcomp
          exact hcomp
        have hmul := hpref.hasDerivAt.mul hF
        rw [hxkD, hyf_eq, I.terms_zero k, mul_zero, zero_add] at hmul
        exact hmul
      have hderiv_eq := (hd_poly.congr_of_eventuallyEq hloc.symm).unique hd_gen
      -- Compute evalPolyDx f xk yk = D * xk^(D-1) and evalPolyDy f xk yk = D * yk^(D-1)!
      have hfdx : evalPolyDx f xk yk = (D : ℝ) * xk ^ (D - 1) := by
        simp [f, evalPolyDx]
      have hfdy : evalPolyDy f xk yk = (D : ℝ) * yk ^ (D - 1) := by
        simp [f, evalPolyDy]
      dsimp only [roots]
      rw [hfdx, hfdy]
      -- Multiply hderiv_eq by -D * yk^(D-1) to obtain the exact Jacobian determinant!
      have hdet_eq : (D : ℝ) * xk ^ (D - 1) * evalPolyDy g xk yk -
          (D : ℝ) * yk ^ (D - 1) * evalPolyDx g xk yk =
          -((D : ℝ) * yk ^ (D - 1)) * ((C : ℝ) * xk ^ P * yk ^ Q * (derivGen L rk * ((D : ℝ) * xk ^ (D - 1)))) := by
        have hy_ne : yk ^ (D - 1) ≠ 0 := (pow_pos hyk0 (D - 1)).ne'
        have hmul := congrArg (fun z => -((D : ℝ) * yk ^ (D - 1)) * z) hderiv_eq
        rw [← hmul]
        field_simp [hy_ne]
        ring
      rw [hdet_eq]
      have h1 : -((D : ℝ) * yk ^ (D - 1)) ≠ 0 :=
        neg_ne_zero.mpr (mul_pos (by exact_mod_cast hD) (pow_pos hyk0 (D - 1))).ne'
      have h2 : (C : ℝ) * xk ^ P * yk ^ Q ≠ 0 := by positivity
      have h3 : derivGen L rk ≠ 0 := I.terms_simple k
      have h4 : (D : ℝ) * xk ^ (D - 1) ≠ 0 := by positivity
      exact mul_ne_zero h1 (mul_ne_zero h2 (mul_ne_zero h3 h4))

end Fewnomial.InfiniteTheorem
