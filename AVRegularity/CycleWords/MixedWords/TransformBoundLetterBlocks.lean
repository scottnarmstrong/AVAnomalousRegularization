-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.TransformBoundLetterTermOp
public import AVRegularity.CycleWords.MixedWords.TransformBoundSameOps
import AVRegularity.CycleWords.MixedWords.ConstituentTransposeStep
public import AVRegularity.CycleWords.MixedWords.TransformBoundSchur
import Mathlib.Combinatorics.SimpleGraph.Basic

section
/-! # the transform of one constituent

`letterGam` is the inner sum of `b1wLetterPart` for one constituent `γ` without the basis factor
`⟨γ.map* e, e'⟩`.  Its conjugate at the conjugate of a classical function `f` is the sum, over the
words `α, ω`, the Taylor order `s` and the transfer index `a`, of the unit terms
`κ D_θ^{(p,q)}(c f)`; each unit is realized by `realizes_unit0/1`, with the
norm bounded through the jets of the envelope. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution

namespace AVRegularity.CycleWords.Assembly

/-- The inner sum of `b1wLetterPart` for one constituent, without the basis factor. -/
def letterGam (θ : Vec 2) (pos : Bool) (slow : ℕ) (δ : ℝ) (X₀ : Vec 2) (r : ℝ) (d : ℕ)
    (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2) (β₀ : ℕ × ℕ) (k : Fin 2)
    (β' : ℕ × ℕ) (ψ : Vec 2 → ℂ) : Vec 2 → ℂ := fun z =>
  ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow,
    ∑ ω : DerivativeWord2 s,
      (((δ ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
        ((-1 : ℂ) ^ (d - 1) * ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
            Finset.range ((wordCount α).2 + 1),
          if β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2) then
            ((((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
                (β₀.1 + (wordCount ω).1).descFactorial a.1 *
                (β₀.2 + (wordCount ω).2).descFactorial a.2 : ℕ) : ℂ) *
              fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
                (fun z' => ((iteratedFDeriv ℝ s (fun X => coeff α r X z' k) X₀
                  (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') z)
          else 0)

/-- The test seen by a variant: the test itself or its twisted derivative `D_{-θ,k}`. -/
def variantFun (pre : Bool) (θ : Vec 2) (k : Fin 2) (φ : Vec 2 → ℂ) : Vec 2 → ℂ :=
  if pre then fibreCovDeriv θ k φ else φ

theorem variantFun_star (pre : Bool) (θ : Vec 2) (k : Fin 2) {f : Vec 2 → ℂ}
    (hf : Differentiable ℝ f) :
    variantFun pre (-θ) k (fun y => star (f y)) = fun y => star (variantFun pre θ k f y) := by
  cases pre
  · rfl
  · simp only [variantFun, ite_true]
    exact fibreCovDeriv_star θ k hf

theorem contDiff_variantFun (pre : Bool) (θ : Vec 2) (k : Fin 2) {f : Vec 2 → ℂ} {m : ℕ}
    (hf : ContDiff ℝ ((m + 1 : ℕ) : ℕ∞) f) : ContDiff ℝ (m : ℕ∞) (variantFun pre θ k f) := by
  cases pre
  · exact hf.of_le (by exact_mod_cast Nat.le_succ m)
  · exact contDiff_fibreCovDeriv (j := m) hf θ k

/-- The extra twisted derivative of a variant, as an exponent. -/
def preExp (pre : Bool) : ℕ := if pre then 1 else 0

/-- The natural coefficient of the transfer (binomials and falling factorials). -/
def gamCoefNat (u v : ℕ) (β₀ w a : ℕ × ℕ) : ℕ :=
  u.choose a.1 * v.choose a.2 * (β₀.1 + w.1).descFactorial a.1 *
    (β₀.2 + w.2).descFactorial a.2

/-- The transfer condition: the moment of the stage and the admissible index. -/
def gamCond (β₀ w a β' : ℕ × ℕ) : Prop :=
  β' = (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2) ∧ a.1 ≤ β₀.1 + w.1 ∧ a.2 ≤ β₀.2 + w.2

open Classical in
/-- The real scalar of one unit term. -/
def gamK (Rcv δ : ℝ) (d s u v : ℕ) (β₀ w a β' : ℕ × ℕ) : ℝ :=
  Rcv * ((δ ^ s / (s.factorial : ℝ)) *
    ((-1 : ℝ) ^ (d - 1) * (if gamCond β₀ w a β' then (gamCoefNat u v β₀ w a : ℝ) else 0)))

theorem gamCoefNat_eq_zero (u v : ℕ) (β₀ w a : ℕ × ℕ)
    (h : ¬ (a.1 ≤ β₀.1 + w.1 ∧ a.2 ≤ β₀.2 + w.2)) : gamCoefNat u v β₀ w a = 0 := by
  rcases not_and_or.1 h with h1 | h2
  · have : (β₀.1 + w.1).descFactorial a.1 = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    simp [gamCoefNat, this]
  · have : (β₀.2 + w.2).descFactorial a.2 = 0 := Nat.descFactorial_eq_zero_iff_lt.2 (by omega)
    simp [gamCoefNat, this]

theorem star_covPow_term (θ : Vec 2) (b : ℕ × ℕ) (c : Vec 2 → ℝ) {fv : Vec 2 → ℂ}
    (hb : ContDiff ℝ (b.1 + b.2 : ℕ) (fun y => (c y : ℂ) * fv y)) (z : Vec 2) :
    star (fibreCovPow (-θ) b (fun z' => (c z' : ℂ) * star (fv z')) z) =
      fibreCovPow θ b (fun y => (c y : ℂ) * fv y) z := by
  have : (fun z' => (c z' : ℂ) * star (fv z')) = fun y => star ((c y : ℂ) * fv y) := by
    funext y; simp [star_mul', Complex.conj_ofReal]
  rw [this]
  exact star_fibreCovPow θ b hb z

open Classical in
theorem star_gam_alpha (θ : Vec 2) (d s : ℕ) (δ : ℝ) (u v : ℕ) (β₀ w β' : ℕ × ℕ)
    (c : Vec 2 → ℝ) (fv : Vec 2 → ℂ) (Rcv : ℝ)
    (hb : ∀ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
      ContDiff ℝ ((u - a.1) + (v - a.2) : ℕ) (fun y => (c y : ℂ) * fv y)) (z : Vec 2) :
    (Rcv : ℂ) * star ((((δ ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
      ((-1 : ℂ) ^ (d - 1) * ∑ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
        if β' = (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2) then
          ((gamCoefNat u v β₀ w a : ℕ) : ℂ) *
            fibreCovPow (-θ) (u - a.1, v - a.2) (fun z' => (c z' : ℂ) * star (fv z')) z
        else 0)) =
    ∑ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
      ((gamK Rcv δ d s u v β₀ w a β' : ℝ) : ℂ) *
        fibreCovPow θ (u - a.1, v - a.2) (fun y => (c y : ℂ) * fv y) z := by
  simp only [star_mul', star_sum, Complex.star_def, Complex.conj_ofReal, star_pow, star_neg,
    star_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a ha => ?_
  have hcov := star_covPow_term θ (u - a.1, v - a.2) c (hb a ha) z
  rw [Complex.star_def] at hcov
  unfold gamK
  by_cases h1 : β' = (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2)
  · by_cases h2 : a.1 ≤ β₀.1 + w.1 ∧ a.2 ≤ β₀.2 + w.2
    · subst h1
      have hc : gamCond β₀ w a (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2) := ⟨rfl, h2⟩
      simp only [ite_true, hc, map_mul, map_natCast]
      rw [hcov]
      push_cast
      ring
    · have hc : ¬ gamCond β₀ w a β' := fun hh => h2 ⟨hh.2.1, hh.2.2⟩
      simp [hc, gamCoefNat_eq_zero u v β₀ w a h2]
  · have hc : ¬ gamCond β₀ w a β' := fun hh => h1 hh.1
    simp [h1, hc]


/-- The norm bound of a variant, as an explicit sum over the unit terms. -/
def gamBound (ρ : ℝ) (n : ℕ) (pre : Bool) (slow : ℕ) (pos : Bool) (d : ℕ) (Rcv δ : ℝ)
    (β₀ β' : ℕ × ℕ) (P : DerivativeWord2 (d - 1) → ℕ → ℝ) : ℝ :=
  ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow,
    ∑ ω : DerivativeWord2 s, ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
        Finset.range ((wordCount α).2 + 1),
      |gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β'| *
        ((1 + ρ) ^ (((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre) *
          (|cellDriftNativePrice (n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2))| *
            P α s))

/-- **A variant of one constituent is realized** with the explicit bound `gamBound`. -/
theorem realizes_gam (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n N J : ℕ) (d : ℕ) (hd2 : 2 ≤ d)
    (hnd : n + d ≤ J) (hN1 : n + d ≤ N) (hN2 : d + 2 ≤ N) (pos : Bool) (slow : ℕ) (δ : ℝ)
    (X₀ : Vec 2) (r : ℝ) (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ) (hjet0 : ∀ α s l, 0 ≤ jet α s l)
    (hfacts : ∀ α s, s ≤ slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
      ContDiff ℝ (J : ℕ∞) (tbTermCoef (coeff α r) s ω X₀ k') ∧
      AVenhance.IsZ2Periodic (tbTermCoef (coeff α r) s ω X₀ k') ∧
      ∀ l ≤ J, ∀ z, ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s ω X₀ k') z‖ ≤ jet α s l)
    (Rcv : ℝ) (β₀ : ℕ × ℕ) (k : Fin 2) (β' : ℕ × ℕ) (pre : Bool) :
    Realizes N n (fun f z => (Rcv : ℂ) * star (letterGam θ pos slow δ X₀ r d coeff β₀ k β'
        (variantFun pre (-θ) k (fun y => star (f y))) z))
      (gamBound ρ n pre slow pos d Rcv δ β₀ β' (fun α s => ∑ l ∈ Finset.range (J + 1), jet α s l)) := by
  classical
  have hd1 : d - 1 + 1 = d := by omega
  -- the unit terms
  have unit : ∀ (α : DerivativeWord2 (d - 1)) (s : ℕ), s ≤ slow → ∀ (ω : DerivativeWord2 s)
      (a : ℕ × ℕ), a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1) →
      Realizes N n (fun f z => ((gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω)
          a β' : ℝ) : ℂ) * fibreCovPow θ ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
          (fun y => (tbTermCoef (coeff α r) s ω X₀ k y : ℂ) * variantFun pre θ k f y) z)
        (|gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β'| *
          ((1 + ρ) ^ (((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre) *
            (|cellDriftNativePrice (n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2))| *
              ∑ l ∈ Finset.range (J + 1), jet α s l))) := by
    intro α s hs ω a ha
    have hwc := wordCount_sum α
    have hpq : ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) ≤ d - 1 := by omega
    obtain ⟨hc, hp, hj⟩ := hfacts α s hs ω k
    have hc' : ContDiff ℝ ((n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) : ℕ) : ℕ∞)
        (tbTermCoef (coeff α r) s ω X₀ k) := hc.of_le (by exact_mod_cast (by omega))
    have hP : ∀ l ≤ n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2), ∀ x,
        ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s ω X₀ k) x‖ ≤
          ∑ l ∈ Finset.range (J + 1), jet α s l := by
      intro l hl x
      refine (hj l (by omega) x).trans ?_
      exact Finset.single_le_sum (f := fun l => jet α s l) (fun l _ => hjet0 α s l)
        (Finset.mem_range.2 (by omega))
    cases pre
    · have := realizes_unit0 θ ρ hθ n N ((wordCount α).1 - a.1) ((wordCount α).2 - a.2)
        (by omega) (by omega) hc' hp hP
        (gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β')
      simpa [variantFun, preExp] using this
    · have := realizes_unit1 θ ρ hθ n N ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) k
        (by omega) (by omega) hc' hp hP
        (gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β')
      simpa [variantFun, preExp] using this
  have hsum : Realizes N n (fun f z => ∑ α : DerivativeWord2 (d - 1),
      ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow, ∑ ω : DerivativeWord2 s,
        ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1),
          ((gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β' : ℝ) : ℂ) *
            fibreCovPow θ ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
              (fun y => (tbTermCoef (coeff α r) s ω X₀ k y : ℂ) * variantFun pre θ k f y) z)
      (gamBound ρ n pre slow pos d Rcv δ β₀ β' (fun α s => ∑ l ∈ Finset.range (J + 1), jet α s l)) :=
    Realizes.finset_sum (N := N) (n := n) Finset.univ (fun α _ =>
      Realizes.finset_sum _ (fun s hs =>
        Realizes.finset_sum _ (fun ω _ =>
          Realizes.finset_sum _ (fun a ha =>
            unit α s (Finset.mem_Icc.1 hs).2 ω a ha))))
  refine hsum.congr (fun ψ => ?_)
  funext z
  have hcd : ContDiff ℝ (d : ℕ∞) (torusHigherClassicalValue N ψ) :=
    torusHigherClassicalValue_contDiff N d (by omega) ψ
  have hdiff : Differentiable ℝ (torusHigherClassicalValue N ψ) :=
    (hcd.of_le (by exact_mod_cast (by omega : 1 ≤ d))).differentiable one_ne_zero
  have hfv : ContDiff ℝ ((d - 1 : ℕ) : ℕ∞) (variantFun pre θ k (torusHigherClassicalValue N ψ)) :=
    contDiff_variantFun pre θ k (m := d - 1) (by rw [hd1]; exact hcd)
  rw [variantFun_star pre θ k hdiff]
  unfold letterGam
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun s hs => ?_
  rw [star_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  have hwc := wordCount_sum α
  have hJd : d - 1 ≤ J := by omega
  have key := star_gam_alpha θ d s δ (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) β'
    (tbTermCoef (coeff α r) s ω X₀ k) (variantFun pre θ k (torusHigherClassicalValue N ψ)) Rcv
    (fun a ha => by
      obtain ⟨hc, -, -⟩ := hfacts α s (Finset.mem_Icc.1 hs).2 ω k
      have hle : (wordCount α).1 - a.1 + ((wordCount α).2 - a.2) ≤ J := by omega
      have hle2 : (wordCount α).1 - a.1 + ((wordCount α).2 - a.2) ≤ d - 1 := by omega
      exact contDiff_real_mul_complex (m := (wordCount α).1 - a.1 + ((wordCount α).2 - a.2))
        (hc.of_le (by exact_mod_cast hle)) (hfv.of_le (by exact_mod_cast hle2))) z
  exact key.symm


section Numeric

/-- The constant bounding the scalar factors of a unit term. -/
def gamCc (D M0 slow : ℕ) : ℝ :=
  ((M0.factorial : ℕ) : ℝ) * ((M0 : ℝ) + 1) * ((2 : ℝ) ^ D) ^ 2 * (((M0 + slow + 1 : ℕ) : ℝ) ^ D) ^ 2

theorem gamCc_nonneg (D M0 slow : ℕ) : 0 ≤ gamCc D M0 slow := by unfold gamCc; positivity

theorem gamCoefNat_le (u v D M0 slow : ℕ) (β₀ w a : ℕ × ℕ) (hu : u ≤ D) (hv : v ≤ D)
    (hau : a.1 ≤ u) (hav : a.2 ≤ v) (h1 : β₀.1 + w.1 ≤ M0 + slow) (h2 : β₀.2 + w.2 ≤ M0 + slow) :
    gamCoefNat u v β₀ w a ≤ (2 ^ D) ^ 2 * ((M0 + slow + 1) ^ D) ^ 2 := by
  unfold gamCoefNat
  have c1 : u.choose a.1 ≤ 2 ^ D := (Nat.choose_le_two_pow u a.1).trans
    (Nat.pow_le_pow_right (by norm_num) hu)
  have c2 : v.choose a.2 ≤ 2 ^ D := (Nat.choose_le_two_pow v a.2).trans
    (Nat.pow_le_pow_right (by norm_num) hv)
  have d1 : (β₀.1 + w.1).descFactorial a.1 ≤ (M0 + slow + 1) ^ D :=
    (Nat.descFactorial_le_pow _ _).trans
      ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (hau.trans hu)))
  have d2 : (β₀.2 + w.2).descFactorial a.2 ≤ (M0 + slow + 1) ^ D :=
    (Nat.descFactorial_le_pow _ _).trans
      ((Nat.pow_le_pow_left (by omega) _).trans (Nat.pow_le_pow_right (by omega) (hav.trans hv)))
  calc _ ≤ 2 ^ D * 2 ^ D * (M0 + slow + 1) ^ D * (M0 + slow + 1) ^ D := by gcongr
    _ = _ := by ring

theorem factorial_pair_le (b0 b1 M0 : ℕ) (h : b0 + b1 ≤ M0) :
    b0.factorial * b1.factorial ≤ M0.factorial :=
  (Nat.le_of_dvd (Nat.factorial_pos _) (Nat.factorial_mul_factorial_dvd_factorial_add b0 b1)).trans
    (Nat.factorial_le h)

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {D Nw : ℕ}

theorem gamK_abs_le (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (x x' : ι) (β β' β₀ w a : ℕ × ℕ) (s d u v M0 slow Dm : ℕ) (cv : ℝ) (hcv : |cv| ≤ (M0 : ℝ) + 1)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta) (hs : (if (letters l).positive then 1 else 0) ≤ s)
    (hsl : s ≤ slow) (hw : w.1 + w.2 = s) (hb0 : β₀.1 + β₀.2 ≤ β.1 + β.2)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) (hu : u ≤ Dm) (hv : v ≤ Dm)
    (hau : a.1 ≤ u) (hav : a.2 ≤ v) :
    |gamK (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s u v β₀ w a β'| ≤
      gamCc Dm M0 slow * (Real.sqrt (π x' / π x) / (letters l).theta) := by
  have hCc := gamCc_nonneg Dm M0 slow
  have hsq : 0 ≤ Real.sqrt (π x' / π x) / (letters l).theta := by positivity
  unfold gamK
  by_cases hc : gamCond β₀ w a β'
  · obtain ⟨h1, h2, h3⟩ := hc
    have e1 : β'.1 = β₀.1 + w.1 - a.1 := by rw [h1]
    have e2 : β'.2 = β₀.2 + w.2 - a.2 := by rw [h1]
    have hexp : β'.1 + β'.2 + (a.1 + a.2) = β₀.1 + β₀.2 + s := by omega
    have hsc := letter_scale_abs_le π ϖ ηg letters l x x' β β' β₀ a s hx hx' hϖ0 hϖ1 hg0 hg1 hθ hs
      hexp hb0
    have hfa : (((β'.1.factorial * β'.2.factorial : ℕ)) : ℝ) ≤ ((M0.factorial : ℕ) : ℝ) := by
      exact_mod_cast factorial_pair_le _ _ _ hβ'M
    have hcoef : ((gamCoefNat u v β₀ w a : ℕ) : ℝ) ≤ ((2 : ℝ) ^ Dm) ^ 2 *
        (((M0 + slow + 1 : ℕ) : ℝ) ^ Dm) ^ 2 := by
      have := gamCoefNat_le u v Dm M0 slow β₀ w a hu hv hau hav (by omega) (by omega)
      exact_mod_cast this
    have hgc : gamCond β₀ w a β' := ⟨h1, h2, h3⟩
    simp only [hgc, ite_true]
    have hrw : letterRatioReal π ϖ ηg letters l x x' β β' * cv *
        ((ϖ * ηg) ^ s / (s.factorial : ℝ) * ((-1 : ℝ) ^ (d - 1) * (gamCoefNat u v β₀ w a : ℝ))) =
        (letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ))) * cv *
          ((-1 : ℝ) ^ (d - 1) * (gamCoefNat u v β₀ w a : ℝ)) := by ring
    rw [hrw]
    simp only [abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul, Nat.abs_cast]
    have hsc' : |letterRatioReal π ϖ ηg letters l x x' β β' * ((ϖ * ηg) ^ s / (s.factorial : ℝ))| ≤
        Real.sqrt (π x' / π x) * ((M0.factorial : ℕ) : ℝ) / (letters l).theta :=
      hsc.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfa (Real.sqrt_nonneg _)) hθ.le)
    rw [abs_mul] at hsc'
    calc _ ≤ (Real.sqrt (π x' / π x) * ((M0.factorial : ℕ) : ℝ) / (letters l).theta) *
          ((M0 : ℝ) + 1) * (((2 : ℝ) ^ Dm) ^ 2 * (((M0 + slow + 1 : ℕ) : ℝ) ^ Dm) ^ 2) := by
          gcongr
      _ = _ := by unfold gamCc; ring
  · simp only [hc, ite_false, mul_zero, abs_zero]
    positivity


/-- The sum of the native prices of the multiplier orders that occur. -/
def gamPr (n Dm : ℕ) : ℝ := ∑ K ∈ Finset.range (n + Dm + 1), |cellDriftNativePrice K|

/-- The constant of a variant. -/
def gamCfin (Dm n : ℕ) (ρ : ℝ) (M0 slow : ℕ) : ℝ :=
  (2 : ℝ) ^ slow * ((Dm : ℝ) + 1) ^ 2 * gamCc Dm M0 slow * (1 + ρ) ^ Dm * gamPr n Dm

theorem gamBound_le (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (x x' : ι) (β β' β₀ : ℕ × ℕ) (d M0 Dm n J Sm : ℕ) (hSm : (letters l).slow ≤ Sm) (ρ : ℝ) (hρ : 0 ≤ ρ) (pre : Bool)
    (cv : ℝ) (hcv : |cv| ≤ (M0 : ℝ) + 1)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta)
    (hd : d ≤ Dm) (hd2 : 2 ≤ d) (hb0 : β₀.1 + β₀.2 ≤ β.1 + β.2)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0)
    (jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ) (hjet0 : ∀ α s l, 0 ≤ jet α s l) :
    gamBound ρ n pre (letters l).slow (letters l).positive d
        (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) β₀ β'
        (fun α s => ∑ q ∈ Finset.range (J + 1), jet α s q) ≤
      gamCfin Dm n ρ M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) *
        ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range ((letters l).slow + 1),
          ∑ q ∈ Finset.range (J + 1), jet α s q := by
  classical
  set slow := (letters l).slow with hslow
  set Ccb := gamCc Dm M0 Sm * (Real.sqrt (π x' / π x) / (letters l).theta) with hCcb
  set Pr := gamPr n Dm with hPr
  have hCc := gamCc_nonneg Dm M0 Sm
  have hsq : 0 ≤ Real.sqrt (π x' / π x) / (letters l).theta := by positivity
  have hCcb0 : 0 ≤ Ccb := by positivity
  have hPr0 : 0 ≤ Pr := Finset.sum_nonneg fun _ _ => abs_nonneg _
  set Q := Ccb * ((1 + ρ) ^ Dm * Pr) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hP0 : ∀ α s, 0 ≤ ∑ q ∈ Finset.range (J + 1), jet α s q :=
    fun α s => Finset.sum_nonneg fun q _ => hjet0 α s q
  -- the bound of one unit term
  have term : ∀ (α : DerivativeWord2 (d - 1)) (s : ℕ),
      s ∈ Finset.Icc (if (letters l).positive then 1 else 0) slow →
      ∀ (ω : DerivativeWord2 s) (a : ℕ × ℕ),
      a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1) →
      |gamK (letterRatioReal π ϖ ηg letters l x x' β β' * cv) (ϖ * ηg) d s (wordCount α).1
          (wordCount α).2 β₀ (wordCount ω) a β'| *
        ((1 + ρ) ^ (((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre) *
          (|cellDriftNativePrice (n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2))| *
            ∑ q ∈ Finset.range (J + 1), jet α s q)) ≤
        Q * ∑ q ∈ Finset.range (J + 1), jet α s q := by
    intro α s hs ω a ha
    obtain ⟨hs1, hs2⟩ := Finset.mem_Icc.1 hs
    have hwa := wordCount_sum α
    have hwo := wordCount_sum ω
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.1 ha
    have ha1' := Finset.mem_range.1 ha1
    have ha2' := Finset.mem_range.1 ha2
    have hK := gamK_abs_le π ϖ ηg letters l x x' β β' β₀ (wordCount ω) a s d (wordCount α).1
      (wordCount α).2 M0 Sm Dm cv hcv hx hx' hϖ0 hϖ1 hg0 hg1 hθ hs1 (hs2.trans hSm) hwo hb0 hβM hβ'M
      (by omega) (by omega) (by omega) (by omega)
    have hpow : (1 + ρ) ^ (((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre) ≤
        (1 + ρ) ^ Dm := by
      refine pow_le_pow_right₀ (by linarith) ?_
      unfold preExp; split_ifs <;> omega
    have hpr : |cellDriftNativePrice (n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2))| ≤ Pr :=
      Finset.single_le_sum (f := fun K => |cellDriftNativePrice K|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by omega))
    have hP := hP0 α s
    calc _ ≤ Ccb * ((1 + ρ) ^ Dm * (Pr * ∑ q ∈ Finset.range (J + 1), jet α s q)) := by
          gcongr
      _ = _ := by rw [hQ]; ring
  have hcardw : ∀ s : ℕ, (Fintype.card (DerivativeWord2 s) : ℝ) = 2 ^ s := by
    intro s; simp [DerivativeWord2, DerivativeWord]
  unfold gamBound
  calc _ ≤ ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if (letters l).positive then 1 else 0) slow,
        ∑ ω : DerivativeWord2 s, ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
          Finset.range ((wordCount α).2 + 1), Q * ∑ q ∈ Finset.range (J + 1), jet α s q :=
        Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun s hs => Finset.sum_le_sum fun ω _ =>
          Finset.sum_le_sum fun a ha => term α s hs ω a ha
    _ ≤ ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if (letters l).positive then 1 else 0) slow,
        (2 : ℝ) ^ Sm * ((Dm : ℝ) + 1) ^ 2 * Q * ∑ q ∈ Finset.range (J + 1), jet α s q := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum fun s hs => ?_
        have hwa := wordCount_sum α
        simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Finset.card_product,
          Finset.card_range, hcardw]
        have hP := hP0 α s
        have hs2 := (Finset.mem_Icc.1 hs).2
        have h1 : (2 : ℝ) ^ s ≤ 2 ^ Sm := pow_le_pow_right₀ (by norm_num) (hs2.trans hSm)
        have h2 : (((wordCount α).1 + 1) * ((wordCount α).2 + 1) : ℕ) ≤ (Dm + 1) ^ 2 := by
          have : (wordCount α).1 + 1 ≤ Dm + 1 := by omega
          have h' : (wordCount α).2 + 1 ≤ Dm + 1 := by omega
          calc _ ≤ (Dm + 1) * (Dm + 1) := Nat.mul_le_mul this h'
            _ = _ := by ring
        have h2' : ((((wordCount α).1 + 1) * ((wordCount α).2 + 1) : ℕ) : ℝ) ≤ ((Dm : ℝ) + 1) ^ 2 := by
          exact_mod_cast h2
        push_cast at h2' ⊢
        have hW : 0 ≤ Q * ∑ q ∈ Finset.range (J + 1), jet α s q := mul_nonneg hQ0 hP
        calc _ ≤ (2 : ℝ) ^ Sm * (((Dm : ℝ) + 1) ^ 2 *
              (Q * ∑ q ∈ Finset.range (J + 1), jet α s q)) :=
              mul_le_mul h1 (mul_le_mul_of_nonneg_right h2' hW) (by positivity) (by positivity)
          _ = _ := by ring
    _ ≤ ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range (slow + 1),
        (2 : ℝ) ^ Sm * ((Dm : ℝ) + 1) ^ 2 * Q * ∑ q ∈ Finset.range (J + 1), jet α s q := by
        refine Finset.sum_le_sum fun α _ => Finset.sum_le_sum_of_subset_of_nonneg ?_
          (fun s _ _ => mul_nonneg (by positivity) (hP0 α s))
        intro s hs
        obtain ⟨-, h2⟩ := Finset.mem_Icc.1 hs
        exact Finset.mem_range.2 (by omega)
    _ = _ := by
        simp only [← Finset.mul_sum]
        unfold gamCfin
        rw [hQ, hCcb]
        ring

end Numeric

end AVRegularity.CycleWords.Assembly
end
end

section
/-! # the block operators of a letter

`BRealizes N n G c` says that the family of functionals `G b b'` (indexed by the basis vectors of two
components) is realized by a family of real-linear maps `T b b' : H^N → H^n` that obeys the block
bound `BlockBound c T`.  It is closed under sums and real multiples, and `BRealizes.of_realizes`
produces it from a `Realizes` and the matrix of `M*` (`letterMat`).  `letterGfam` is the conjugated
letter transform of a pair of components and moments, built from `letterGam`; `letterBlock_exists`
realizes it with the block constant `C₀ κ(β,β') majorant/θ`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution

namespace AVRegularity.CycleWords.Assembly

section BR

variable {m₁ m₂ N n : ℕ}

/-- A family of functionals realized by a family of maps with a block bound. -/
def BRealizes (N n : ℕ) (G : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ) (c : ℝ) : Prop :=
  ∃ T : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    (∀ b b' ψ, (torusHkValueCLM (T b b' ψ) : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      G b b' (torusHigherClassicalValue N ψ)) ∧ BlockBound c T

variable {G G' : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c c' : ℝ}

theorem BRealizes.zero : BRealizes (m₁ := m₁) (m₂ := m₂) N n (fun _ _ _ _ => 0) 0 :=
  ⟨fun _ _ => 0, fun b b' ψ => by
    rw [zero_apply, map_zero]; exact Lp.coeFn_zero _ _ _, BlockBound.zero⟩

theorem BRealizes.mono (h : BRealizes N n G c) (hc : c ≤ c') : BRealizes N n G c' := by
  obtain ⟨T, hv, hb⟩ := h
  exact ⟨T, hv, hb.mono hc⟩

theorem BRealizes.congr (h : BRealizes N n G c)
    (hG : ∀ b b' (ψ : TorusHk N ℂ), G b b' (torusHigherClassicalValue N ψ) =
      G' b b' (torusHigherClassicalValue N ψ)) : BRealizes N n G' c := by
  obtain ⟨T, hv, hb⟩ := h
  exact ⟨T, fun b b' ψ => by rw [← hG]; exact hv b b' ψ, hb⟩

theorem BRealizes.add (h : BRealizes N n G c) (h' : BRealizes N n G' c') :
    BRealizes N n (fun b b' f z => G b b' f z + G' b b' f z) (c + c') := by
  obtain ⟨T, hv, hb⟩ := h
  obtain ⟨T', hv', hb'⟩ := h'
  refine ⟨fun b b' => T b b' + T' b b', fun b b' ψ => ?_, hb.add hb'⟩
  rw [add_apply, map_add]
  filter_upwards [Lp.coeFn_add (torusHkValueCLM (T b b' ψ)) (torusHkValueCLM (T' b b' ψ)),
    hv b b' ψ, hv' b b' ψ] with z h1 h2 h3
  rw [h1, Pi.add_apply, h2, h3]

theorem BRealizes.finset_sum {κ : Type*} (s : Finset κ) {G : κ → Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {c : κ → ℝ} (h : ∀ j ∈ s, BRealizes N n (G j) (c j)) :
    BRealizes N n (fun b b' f z => ∑ j ∈ s, G j b b' f z) (∑ j ∈ s, c j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (BRealizes.zero (m₁ := m₁) (m₂ := m₂) (N := N) (n := n))
  | insert a s ha ih =>
    have := (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

theorem BRealizes.list_sum {κ : Type*} (l : List κ) {G : κ → Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ}
    {c : κ → ℝ} (h : ∀ j ∈ l, BRealizes N n (G j) (c j)) :
    BRealizes N n (fun b b' f z => (l.map fun j => G j b b' f z).sum) (l.map c).sum := by
  induction l with
  | nil => simpa using (BRealizes.zero (m₁ := m₁) (m₂ := m₂) (N := N) (n := n))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun j hj => h j (List.mem_cons_of_mem _ hj))
    simpa using this

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [FiniteDimensional ℝ H₁]
  [FiniteDimensional ℝ H₂]

theorem BRealizes.of_realizes (e : OrthonormalBasis (Fin m₁) ℝ H₁)
    (e' : OrthonormalBasis (Fin m₂) ℝ H₂) (M : H₂ →L[ℝ] H₁) {G : (Vec 2 → ℂ) → Vec 2 → ℂ} {B : ℝ}
    (hB : 0 ≤ B) (h : Realizes N n G B) :
    BRealizes N n (fun b b' f z => ((letterMat e e' M b b' : ℝ) : ℂ) * G f z) (‖M‖ * B) := by
  obtain ⟨A, hv, hn⟩ := h
  have hA : ‖A‖ ≤ B := ContinuousLinearMap.opNorm_le_bound _ hB hn
  refine ⟨fun b b' => letterMat e e' M b b' • A, fun b b' ψ => ?_,
    (blockBound_mat_smul e e' M A).mono (mul_le_mul_of_nonneg_left hA (norm_nonneg _))⟩
  rw [smul_apply, map_smul]
  filter_upwards [Lp.coeFn_smul (letterMat e e' M b b') (torusHkValueCLM (A ψ)), hv ψ] with z h1 h2
  rw [h1]
  simp only [Pi.smul_apply, h2, Complex.real_smul]

end BR

theorem list_map_sum_get {α β : Type*} [AddCommMonoid β] (l : List α) (f : α → β) :
    (l.map f).sum = ∑ k : Fin l.length, f (l.get k) := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ih]
    exact (Fin.sum_univ_succ (fun k : Fin (l.length + 1) => f ((a :: l).get k))).symm

section Letter

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

/-- The four variants of the letter transform: the coefficient, the moment `β₀`, the component `k`
and whether the test is differentiated. -/
def letterVars (β : ℕ × ℕ) : List (ℝ × (ℕ × ℕ) × Fin 2 × Bool) :=
  [(-(β.1 : ℝ), (β.1 - 1, β.2), 0, false), (-(β.2 : ℝ), (β.1, β.2 - 1), 1, false),
    (-1, β, 0, true), (-1, β, 1, true)]

open Classical in
/-- The conjugated letter transform of the components `x, x'` and the moments `β, β'`, as a family
of functionals indexed by the basis vectors: `R` times the conjugate of the transform of the
conjugate, with the basis factor `⟨γ.map* e_b, e'_{b'}⟩` of each constituent. -/
def letterGfam (θ : Vec 2) (L : CycleLetter ι h D) (A : Finset ℕ) (δ : ℝ) (X₀ : Vec 2) (r : ℝ)
    (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) :
    Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → (Vec 2 → ℂ) → Vec 2 → ℂ :=
  fun b b' f z =>
    ((letterVars β).map fun w => ∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
      ((L.edge x x' ⟨d, hd⟩).map fun γ =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((R * w.1 : ℝ) : ℂ) * star (letterGam θ L.positive L.slow δ X₀ r d γ.coeff w.2.1
            w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z))).sum
      else 0).sum

theorem letterGam_eq_zero_of_not_rel (θ : Vec 2) (pos : Bool) (slow : ℕ) (δ : ℝ) (X₀ : Vec 2)
    (r : ℝ) (d : ℕ) (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (β₀ β β' : ℕ × ℕ) (k : Fin 2) (ψ : Vec 2 → ℂ) (S Dmax : ℕ) (hd : d ≤ Dmax) (hsl : slow ≤ S)
    (hb1 : β.1 ≤ β₀.1 + 1) (hb2 : β.2 ≤ β₀.2 + 1) (hb3 : β₀.1 ≤ β.1) (hb4 : β₀.2 ≤ β.2)
    (hn : ¬ LetterMomRel S (Dmax + 1) β β') :
    letterGam θ pos slow δ X₀ r d coeff β₀ k β' ψ = 0 := by
  funext z
  unfold letterGam
  refine Finset.sum_eq_zero fun α _ => Finset.sum_eq_zero fun s hs => Finset.sum_eq_zero fun ω _ => ?_
  have hs2 := (Finset.mem_Icc.1 hs).2
  have hwa := wordCount_sum α
  have hwo := wordCount_sum ω
  have : ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1),
      (if β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2) then
        ((((wordCount α).1.choose a.1 * (wordCount α).2.choose a.2 *
          (β₀.1 + (wordCount ω).1).descFactorial a.1 *
          (β₀.2 + (wordCount ω).2).descFactorial a.2 : ℕ) : ℂ) *
        fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
          (fun z' => ((iteratedFDeriv ℝ s (fun X => coeff α r X z' k) X₀
            (fun n => basisVec (ω n)) : ℝ) : ℂ) * ψ z') z) else 0) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    obtain ⟨ha1, ha2⟩ := Finset.mem_product.1 ha
    have ha1' := Finset.mem_range.1 ha1
    have ha2' := Finset.mem_range.1 ha2
    by_cases h1 : β' = (β₀.1 + (wordCount ω).1 - a.1, β₀.2 + (wordCount ω).2 - a.2)
    · by_cases h2 : a.1 ≤ β₀.1 + (wordCount ω).1 ∧ a.2 ≤ β₀.2 + (wordCount ω).2
      · exfalso
        apply hn
        have e1 : β'.1 = β₀.1 + (wordCount ω).1 - a.1 := by rw [h1]
        have e2 : β'.2 = β₀.2 + (wordCount ω).2 - a.2 := by rw [h1]
        unfold LetterMomRel
        omega
      · have := gamCoefNat_eq_zero (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a h2
        unfold gamCoefNat at this
        simp [h1, this]
    · simp [h1]
  rw [this]
  simp

theorem letterVars_props (β : ℕ × ℕ) (M0 : ℕ) (hβM : β.1 + β.2 ≤ M0) :
    ∀ w ∈ letterVars β, |w.1| ≤ (M0 : ℝ) + 1 ∧ w.2.1.1 + w.2.1.2 ≤ β.1 + β.2 ∧
      β.1 ≤ w.2.1.1 + 1 ∧ β.2 ≤ w.2.1.2 + 1 ∧ w.2.1.1 ≤ β.1 ∧ w.2.1.2 ≤ β.2 := by
  intro w hw
  have h1 : (β.1 : ℝ) ≤ M0 := by exact_mod_cast (by omega : β.1 ≤ M0)
  have h2 : (β.2 : ℝ) ≤ M0 := by exact_mod_cast (by omega : β.2 ≤ M0)
  simp only [letterVars, List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl | rfl
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> first | omega | linarith
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp <;> first | omega | linarith
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp

theorem gamBound_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (pre : Bool) (slow : ℕ) (pos : Bool) (d : ℕ)
    (Rcv δ : ℝ) (β₀ β' : ℕ × ℕ) (P : DerivativeWord2 (d - 1) → ℕ → ℝ) (hP : ∀ α s, 0 ≤ P α s) :
    0 ≤ gamBound ρ n pre slow pos d Rcv δ β₀ β' P :=
  Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun ω _ =>
    Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (abs_nonneg _) (hP α s)))

/-- The jet total of a constituent: `∑_{α, s ≤ slow, q ≤ J}` of the essential mixed jets. -/
def jetTotal (I : Set ℝ) (slow J d : ℕ) (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2) :
    ℝ :=
  ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.range (slow + 1), ∑ q ∈ Finset.range (J + 1),
    (jetSupOn (I ×ˢ Set.univ) s q (coeff α)).toReal

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **One constituent, one variant**: the block family of a single `(w, d, γ)`. -/
theorem br_gamma (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (a b : ℝ)
    (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (r : ℝ)
    (hr : r ∈ Icc a b) (hg : LetterGood (letters l) (Icc a b) J r) (hπ : ∀ x, 0 < π x)
    (ϖ ηg : ℝ) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1) (θ : Vec 2) (ρ : ℝ)
    (hθ : ∀ k, |θ k| ≤ ρ) (X₀ : Vec 2) (n N Dmax M0 S : ℕ)
    (hord : (letters l).order ≤ Dmax) (hslow : (letters l).slow ≤ S) (hJ : n + Dmax ≤ J)
    (hN1 : n + (letters l).order ≤ N) (hN2 : Dmax + 3 ≤ N) (x x' : ι) (β β' : ℕ × ℕ)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) (hθpos : 0 < (letters l).theta)
    (w : ℝ × (ℕ × ℕ) × Fin 2 × Bool) (hw : w ∈ letterVars β) (d : ℕ) (hd : d ∈ Finset.Icc 2 D)
    (γ : Constituent d (h x') (h x)) (hγ : γ ∈ (letters l).edge x x' ⟨d, hd⟩) :
    BRealizes (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) N n
      (fun b b' f z =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
            star (letterGam θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d γ.coeff w.2.1
              w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z)))
      (‖γ.map‖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff)) := by
  classical
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  by_cases hm : γ.map = 0
  · have h0 : ‖γ.map‖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff) = 0 := by simp [hm]
    rw [h0]
    refine BRealizes.zero.congr fun b b' ψ => ?_
    simp [letterMat, hm]
  · obtain ⟨k, hk⟩ := List.mem_iff_get.1 hγ
    subst hk
    obtain ⟨hwb, hw1, hw2, hw3, hw4, hw5⟩ := letterVars_props β M0 hβM w hw
    set γ := ((letters l).edge x x' ⟨d, hd⟩).get k with hγdef
    have hdle : d ≤ (letters l).order := by
      by_contra hlt
      have := hL.edge_order x x' ⟨d, hd⟩ (by simpa using not_le.1 hlt)
      have hk' := k.2
      simp [this] at hk'
    have hd2 : 2 ≤ d := (Finset.mem_Icc.1 hd).1
    let jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ := fun α s q =>
      (jetSupOn (Icc a b ×ˢ Set.univ) s q (γ.coeff α)).toReal
    have hjet0 : ∀ α s q, 0 ≤ jet α s q := fun _ _ _ => ENNReal.toReal_nonneg
    have hfacts : ∀ α s, s ≤ (letters l).slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
        ContDiff ℝ (J : ℕ∞) (tbTermCoef (γ.coeff α r) s ω X₀ k') ∧
        AVenhance.IsZ2Periodic (tbTermCoef (γ.coeff α r) s ω X₀ k') ∧
        ∀ q ≤ J, ∀ z, ‖iteratedFDeriv ℝ q (tbTermCoef (γ.coeff α r) s ω X₀ k') z‖ ≤ jet α s q :=
      fun α s hs ω k' => letter_term_facts π (letters l) a b J H hL r hr hg x x' ⟨d, hd⟩ k hm α s hs
        ω X₀ k'
    have hreal := realizes_gam θ ρ hθ n N J d hd2 (by omega) (by omega) (by omega)
      (letters l).positive (letters l).slow (ϖ * ηg) X₀ r γ.coeff jet hjet0 hfacts
      (letterRatioReal π ϖ ηg letters l x x' β β' * w.1) w.2.1 w.2.2.1 β' w.2.2.2
    have hBnn := gamBound_nonneg ρ hρ n w.2.2.2 (letters l).slow (letters l).positive d
      (letterRatioReal π ϖ ηg letters l x x' β β' * w.1) (ϖ * ηg) w.2.1 β'
      (fun α s => ∑ q ∈ Finset.range (J + 1), jet α s q)
      (fun α s => Finset.sum_nonneg fun q _ => hjet0 α s q)
    have hbr := BRealizes.of_realizes (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x'))
      γ.map hBnn hreal
    refine hbr.mono ?_
    have hb := gamBound_le π ϖ ηg letters l x x' β β' w.2.1 d M0 D n J S hslow ρ hρ w.2.2.2 w.1 hwb
      (hπ x) (hπ x') hϖ0 hϖ1 hg0 hg1 hθpos (Finset.mem_Icc.1 hd).2 hd2 (by omega) hβM hβ'M jet hjet0
    exact mul_le_mul_of_nonneg_left (hb.trans (le_of_eq (by unfold jetTotal; rfl))) (norm_nonneg _)

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem letterGfam_zero_R (θ : Vec 2) (L : CycleLetter ι h D) (A : Finset ℕ) (δ : ℝ) (X₀ : Vec 2)
    (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (b b' f z) :
    letterGfam θ L A δ X₀ r x x' β β' 0 b b' f z = 0 := by
  classical
  unfold letterGfam
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨w, -, rfl⟩ := List.mem_map.1 hy
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    refine List.sum_eq_zero fun u hu => ?_
    obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hu
    simp
  · simp [hd]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem letterGfam_zero_rel (θ : Vec 2) (π : ι → ℝ) (Jstar H : ℕ) (dom : Set (ℝ × Vec 2))
    (L : CycleLetter ι h D) (hL : IsCycleLetter π L dom Jstar H) (A : Finset ℕ) (δ : ℝ)
    (X₀ : Vec 2) (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) (S Dmax : ℕ)
    (hord : L.order ≤ Dmax) (hslow : L.slow ≤ S) (hn : ¬ LetterMomRel S (Dmax + 1) β β') (b b' f z) :
    letterGfam θ L A δ X₀ r x x' β β' R b b' f z = 0 := by
  classical
  unfold letterGfam
  refine List.sum_eq_zero fun y hy => ?_
  obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hy
  obtain ⟨-, -, hw2, hw3, hw4, hw5⟩ := letterVars_props β (β.1 + β.2) le_rfl w hw
  refine Finset.sum_eq_zero fun d _ => ?_
  by_cases hd : d ∈ Finset.Icc 2 D
  · simp only [hd, dite_true]
    refine List.sum_eq_zero fun u hu => ?_
    obtain ⟨γ, hγ, rfl⟩ := List.mem_map.1 hu
    have hdle : d ≤ L.order := by
      by_contra hlt
      have := hL.edge_order x x' ⟨d, hd⟩ (by simpa using not_le.1 hlt)
      simp [this] at hγ
    have hz := letterGam_eq_zero_of_not_rel θ L.positive L.slow δ X₀ r d γ.coeff w.2.1 β β'
      w.2.2.1 (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) S Dmax (hdle.trans hord) hslow hw2 hw3 hw4 hw5 hn
    rw [hz]
    simp
  · simp [hd]

omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The block operators of a pair of components and moments.** -/
theorem letterBlock_exists (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (a b : ℝ) (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (r : ℝ)
    (hr : r ∈ Icc a b) (hg : LetterGood (letters l) (Icc a b) J r) (hπ : ∀ x, 0 < π x)
    (ϖ ηg : ℝ) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1) (θ : Vec 2) (ρ : ℝ)
    (hθ : ∀ k, |θ k| ≤ ρ) (X₀ : Vec 2) (A : Finset ℕ) (n N Dmax M0 S : ℕ)
    (hord : (letters l).order ≤ Dmax) (hslow : (letters l).slow ≤ S) (hJ : n + Dmax ≤ J)
    (hN1 : n + (letters l).order ≤ N) (hN2 : Dmax + 3 ≤ N) (x x' : ι) (β β' : ℕ × ℕ)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) :
    BRealizes (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) N n
      (letterGfam θ (letters l) A (ϖ * ηg) X₀ r x x' β β'
        (letterRatioReal π ϖ ηg letters l x x' β β'))
      (4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x') := by
  classical
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  by_cases hrel : LetterMomRel S (Dmax + 1) β β'
  swap
  · have h0 : 4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x' = 0 := by simp [hrel]
    rw [h0]
    exact BRealizes.zero.congr fun b' b'' ψ => funext fun z => (letterGfam_zero_rel θ π J H _
      (letters l) hL A (ϖ * ηg) X₀ r x x' β β' _ S Dmax hord hslow hrel _ _ _ z).symm
  by_cases hθ0 : (letters l).theta = 0
  · have hR : letterRatioReal π ϖ ηg letters l x x' β β' = 0 := by
      unfold letterRatioReal letterFac
      simp [hθ0]
    have h0 : 4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x' = 0 := by simp [letterCompWeight, hθ0]
    rw [h0, hR]
    exact BRealizes.zero.congr fun b' b'' ψ => funext fun z => (letterGfam_zero_R θ (letters l) A
      (ϖ * ηg) X₀ r x x' β β' _ _ _ z).symm
  have hθpos : 0 < (letters l).theta := lt_of_le_of_ne hL.theta_nonneg (Ne.symm hθ0)
  set K := gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) with hK
  set Jt : ∀ d : ℕ, Constituent d (h x') (h x) → ℝ := fun d γ =>
    jetTotal (Icc a b) (letters l).slow J d γ.coeff with hJt
  -- the family per variant
  have hvar : ∀ w ∈ letterVars β, BRealizes (m₁ := Module.finrank ℝ (h x))
      (m₂ := Module.finrank ℝ (h x')) N n
      (fun b b' f z => ∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ =>
          ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
            (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
              star (letterGam θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d γ.coeff w.2.1
                w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 (fun y => star (f y))) z))).sum)
        else 0)
      (∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0) := by
    intro w hw
    refine BRealizes.finset_sum A fun d _ => ?_
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hd, dite_true]
      exact BRealizes.list_sum _ fun γ hγ => br_gamma π letters l a b J H hL r hr hg hπ ϖ ηg hϖ0
        hϖ1 hg0 hg1 θ ρ hθ X₀ n N Dmax M0 S hord hslow hJ hN1 hN2 x x' β β' hβM hβ'M hθpos w hw d hd
        γ hγ
    · simpa [hd] using (BRealizes.zero (m₁ := Module.finrank ℝ (h x))
        (m₂ := Module.finrank ℝ (h x')) (N := N) (n := n))
  have hmain := BRealizes.list_sum (letterVars β) hvar
  refine hmain.mono ?_
  -- the numerical bound of the block constant
  have hJt0 : ∀ d γ, 0 ≤ Jt d γ := fun d γ =>
    Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
      ENNReal.toReal_nonneg
  set Ψ : ℕ → ℝ := fun d => if hd : d ∈ Finset.Icc 2 D then
      ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * Jt d γ)).sum else 0 with hΨ
  have hΨ0 : ∀ d, 0 ≤ Ψ d := by
    intro d
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hΨ, hd, dite_true]
      rw [list_map_sum_get]
      exact Finset.sum_nonneg fun k _ => mul_nonneg (norm_nonneg _) (hJt0 _ _)
    · simp only [hΨ]
      split_ifs
      exact le_rfl
  have hcw : ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0) =
      K * ∑ d ∈ A, Ψ d := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun d _ => ?_
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hΨ, hd, dite_true]
      rw [list_map_sum_get, list_map_sum_get, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    · simp only [hΨ]
      split_ifs
      simp
  have hsub : ∑ d ∈ A, Ψ d ≤ ∑ o : Finset.Icc 2 D, ∑ k : Fin ((letters l).edge x x' o).length,
      ‖(((letters l).edge x x' o).get k).map‖ * Jt o.1 (((letters l).edge x x' o).get k) := by
    calc ∑ d ∈ A, Ψ d = ∑ d ∈ A.filter (· ∈ Finset.Icc 2 D), Ψ d :=
          (Finset.sum_filter_of_ne (fun d _ hne => by
            by_contra hnd; exact hne (by
              simp only [hΨ]
              split_ifs
              rfl))).symm
      _ ≤ ∑ d ∈ Finset.Icc 2 D, Ψ d := Finset.sum_le_sum_of_subset_of_nonneg
          (fun d hd => (Finset.mem_filter.1 hd).2) (fun d _ _ => hΨ0 d)
      _ = ∑ o : Finset.Icc 2 D, Ψ o.1 := (Finset.sum_coe_sort (Finset.Icc 2 D) Ψ).symm
      _ = _ := by
          refine Finset.sum_congr rfl fun o _ => ?_
          simp only [hΨ, o.2, dite_true]
          rw [list_map_sum_get]
  have henv := envelope_real_sum_le π (letters l) (Icc a b ×ˢ Set.univ) J H hL x x'
  have hθ' : 0 < (letters l).theta := hθpos
  have hcwle : K * ∑ d ∈ A, Ψ d ≤ gamCfin D n ρ M0 S * ((letters l).majorant x x' / (letters l).theta) := by
    have hK0 : 0 ≤ K := by
      have : 0 ≤ gamCfin D n ρ M0 S := by
        unfold gamCfin gamPr
        have := gamCc_nonneg D M0 S
        have h1 : 0 ≤ ((D : ℝ) + 1) ^ 2 := by positivity
        have h2 : 0 ≤ (1 + ρ) ^ D := by positivity
        have h3 : 0 ≤ ∑ K ∈ Finset.range (n + D + 1), |cellDriftNativePrice K| :=
          Finset.sum_nonneg fun _ _ => abs_nonneg _
        positivity
      positivity
    calc K * ∑ d ∈ A, Ψ d ≤ K * ∑ o : Finset.Icc 2 D, ∑ k : Fin ((letters l).edge x x' o).length,
          ‖(((letters l).edge x x' o).get k).map‖ * Jt o.1 (((letters l).edge x x' o).get k) :=
          mul_le_mul_of_nonneg_left hsub hK0
      _ = gamCfin D n ρ M0 S / (letters l).theta * (Real.sqrt (π x' / π x) *
          ∑ o : Finset.Icc 2 D, ∑ k : Fin ((letters l).edge x x' o).length,
          ‖(((letters l).edge x x' o).get k).map‖ * Jt o.1 (((letters l).edge x x' o).get k)) := by
          rw [hK]; field_simp
      _ ≤ gamCfin D n ρ M0 S / (letters l).theta * (letters l).majorant x x' := by
          refine mul_le_mul_of_nonneg_left ?_ (div_nonneg ?_ hθ'.le)
          · exact henv
          · unfold gamCfin gamPr
            have := gamCc_nonneg D M0 S
            have h1 : 0 ≤ ((D : ℝ) + 1) ^ 2 := by positivity
            have h2 : 0 ≤ (1 + ρ) ^ D := by positivity
            have h3 : 0 ≤ ∑ K ∈ Finset.range (n + D + 1), |cellDriftNativePrice K| :=
              Finset.sum_nonneg fun _ _ => abs_nonneg _
            positivity
      _ = _ := by ring
  have hw : letterCompWeight (letters l) x x' = (letters l).majorant x x' / (letters l).theta := by
    unfold letterCompWeight; simp [hθ0]
  simp only [hrel, ↓reduceIte, hw]
  have hsum : ((letterVars β).map fun _ => ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0)).sum =
      4 * ∑ d ∈ A, (if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0) := by
    simp [letterVars]; ring
  refine (le_of_eq hsum).trans ?_
  rw [hcw]
  linarith [hcwle]

end Letter

end AVRegularity.CycleWords.Assembly
end
end
