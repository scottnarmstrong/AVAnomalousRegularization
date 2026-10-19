-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.B1WRepresentation
public import AVRegularity.CycleWords.MixedWords.Discard.Unit
public import AVRegularity.CycleWords.MixedWords.TransformBoundLetterBlocks
import AVRegularity.CycleWords.MixedWords.ConstituentTransposeStep
import Mathlib.Combinatorics.SimpleGraph.Basic

section
section
/-! # the transposed same-level transform as a combination of test functions

For a differentiable test `φ`, `ratio · b1wSameTransform φ` is the combination, with the
effective coefficients of `same_star_eff`, of `φ` and the twisted derivatives `D_{-θ,k} φ`
(`ratio_same`), and the integral of a combination is the combination of the integrals
(`int_comb`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

theorem int_comb {μ : Measure (Vec 2)} (f1 f2 f3 f4 f5 : Vec 2 → ℂ)
    (h1 : Integrable f1 μ) (h2 : Integrable f2 μ) (h3 : Integrable f3 μ) (h4 : Integrable f4 μ)
    (h5 : Integrable f5 μ) (c1 c2 c3 c4 c5 c6 c7 : ℂ) :
    ∫ y, (c1 * f1 y + c2 * (f2 y + (c3 * f3 y + c4 * f4 y)) +
      c5 * (f5 y + (c6 * f3 y + c7 * f4 y))) ∂μ =
    c1 * ∫ y, f1 y ∂μ + c2 * (∫ y, f2 y ∂μ + (c3 * ∫ y, f3 y ∂μ + c4 * ∫ y, f4 y ∂μ)) +
      c5 * (∫ y, f5 y ∂μ + (c6 * ∫ y, f3 y ∂μ + c7 * ∫ y, f4 y ∂μ)) := by
  have a1 : Integrable (fun y => c1 * f1 y) μ := h1.const_mul c1
  have a3 : Integrable (fun y => c3 * f3 y) μ := h3.const_mul c3
  have a4 : Integrable (fun y => c4 * f4 y) μ := h4.const_mul c4
  have a6 : Integrable (fun y => c6 * f3 y) μ := h3.const_mul c6
  have a7 : Integrable (fun y => c7 * f4 y) μ := h4.const_mul c7
  have d3 : Integrable (fun y => c3 * f3 y + c4 * f4 y) μ := a3.add a4
  have d6 : Integrable (fun y => c6 * f3 y + c7 * f4 y) μ := a6.add a7
  have b2 : Integrable (fun y => f2 y + (c3 * f3 y + c4 * f4 y)) μ := h2.add d3
  have b5 : Integrable (fun y => f5 y + (c6 * f3 y + c7 * f4 y)) μ := h5.add d6
  have e2 : Integrable (fun y => c2 * (f2 y + (c3 * f3 y + c4 * f4 y))) μ := b2.const_mul c2
  have e5 : Integrable (fun y => c5 * (f5 y + (c6 * f3 y + c7 * f4 y))) μ := b5.const_mul c5
  have g : Integrable (fun y => c1 * f1 y + c2 * (f2 y + (c3 * f3 y + c4 * f4 y))) μ := a1.add e2
  rw [integral_add g e5, integral_add a1 e2, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_add h2 d3, integral_add a3 a4,
    integral_add h5 d6, integral_add a6 a7, integral_const_mul, integral_const_mul,
    integral_const_mul, integral_const_mul]

section Alg

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
open Classical in
/-- **The transposed same-level transform, pointwise.** -/
theorem ratio_same (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (hπ : ∀ x, 0 < π x) (hϖ : ϖ ≠ 0) (θ : Vec 2) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (vf : Vec 2 → Vec 2) (i i' : B1WIndex ι h Nw m Ks) (f : Vec 2 → ℂ) (z : Vec 2)
    (hf : DifferentiableAt ℝ f z) :
    b1wScaleRatio π ϖ ηg letters i i' * b1wSameTransform θ G vf i i' f z =
      (sameE123 (sameAlive ηg letters i) ϖ G i i' : ℝ) * f z +
      ((sameE (sameAlive ηg letters i) i i' (1, 0) (1 * ϖ ^ (1 + 0)) : ℝ) : ℂ) *
        ((vf z 0 : ℂ) * f z +
          (((G 0 0 + G 0 0 : ℝ) : ℂ) * fibreCovDeriv (-θ) 0 f z +
            ((G 1 0 + G 0 1 : ℝ) : ℂ) * fibreCovDeriv (-θ) 1 f z)) +
      ((sameE (sameAlive ηg letters i) i i' (0, 1) (1 * ϖ ^ (0 + 1)) : ℝ) : ℂ) *
        ((vf z 1 : ℂ) * f z +
          (((G 0 1 + G 1 0 : ℝ) : ℂ) * fibreCovDeriv (-θ) 0 f z +
            ((G 1 1 + G 1 1 : ℝ) : ℂ) * fibreCovDeriv (-θ) 1 f z)) := by
  have hf' : DifferentiableAt ℝ (fun y => star (f y)) z :=
    (Complex.conjCLE.toContinuousLinearMap.differentiableAt.comp z hf :)
  have h1 := same_star_eff π ϖ ηg letters hπ hϖ θ G vf i i' (fun y => star (f y)) z hf'
  have h2 := congrArg star h1
  have hcov : ∀ k, star (fibreCovDeriv θ k (fun y => star (f y)) z) =
      fibreCovDeriv (-θ) k f z := fun k => by
    have := tb_star_cov (-θ) k f z hf
    rw [neg_neg] at this
    exact this
  simp only [star_mul', star_add, star_star, hcov, b1wScaleRatio_star,
    Fin.sum_univ_two] at h2
  simp only [Complex.star_def, Complex.conj_ofReal] at h2
  rw [h2]
  simp only [sameE123]

end Alg

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the pairing identity of the forward same-level operator

`∫ (A X) φ = ratio · ∫ X · b1wSameTransform φ` for `A = sameOp` with the signs of the twisted
derivatives flipped (`same_pair_eq`): the pairing of `sameOp_pair` against the
pointwise formula `ratio_same`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

section Pair

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
open Classical in
theorem same_pair_eq (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D)
    (hπ : ∀ x, 0 < π x) (hϖ : ϖ ≠ 0) (θ : Vec 2) (G : Matrix (Fin 2) (Fin 2) ℝ)
    (vf : Vec 2 → Vec 2) (hvc : ∀ c, Continuous fun x => vf x c) (i i' : B1WIndex ι h Nw m Ks)
    (n N : ℕ) (hnN : n + 1 ≤ N) (M : Fin 2 → TorusHk n ℂ →L[ℝ] TorusHk n ℂ)
    (hMv : ∀ c U, (torusHkValueCLM (M c U) : Vec 2 → ℂ)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => (vf x c : ℂ) * torusHkValueCLM U x)
    (X : TorusHk N ℂ) (φ : Vec 2 → ℂ) (hφ : ContDiff ℝ 1 φ) (hφp : AVenhance.IsZ2Periodic φ) :
    ∫ y in AVenhance.unitCube,
        (torusHkValueCLM (sameOp n N hnN θ M (fun k => -(G k 0 + G 0 k))
          (fun k => -(G k 1 + G 1 k)) (sameE123 (sameAlive ηg letters i) ϖ G i i')
          (sameE (sameAlive ηg letters i) i i' (1, 0) (1 * ϖ ^ (1 + 0)))
          (sameE (sameAlive ηg letters i) i i' (0, 1) (1 * ϖ ^ (0 + 1))) X) :
          Vec 2 → ℂ) y * φ y =
      b1wScaleRatio π ϖ ηg letters i i' *
        ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
          b1wSameTransform θ G vf i i' φ y := by
  have hp := sameOp_pair n N hnN θ M vf hMv (fun k => G k 0 + G 0 k)
    (fun k => G k 1 + G 1 k) (sameE123 (sameAlive ηg letters i) ϖ G i i')
    (sameE (sameAlive ηg letters i) i i' (1, 0) (1 * ϖ ^ (1 + 0)))
    (sameE (sameAlive ηg letters i) i i' (0, 1) (1 * ϖ ^ (0 + 1))) X φ hφ hφp
  refine hp.trans ?_
  have hcφ := hφ.continuous
  have hD : ∀ k, Continuous (fibreCovDeriv (-θ) k φ) := fun k =>
    (contDiff_fibreCovDeriv (j := 0) (by simpa using hφ) _ k).continuous
  have hI : ∀ ψ : Vec 2 → ℂ, Continuous ψ → Integrable (fun y =>
      (torusHkValueCLM X : Vec 2 → ℂ) y * ψ y) (volume.restrict AVenhance.unitCube) :=
    fun ψ hψ => pair_integrable ψ hψ _
  have hvφ : ∀ c, Continuous fun y => (vf y c : ℂ) * φ y := fun c =>
    (Complex.continuous_ofReal.comp (hvc c)).mul hcφ
  have hint := int_comb (μ := volume.restrict AVenhance.unitCube)
    (fun y => (torusHkValueCLM X : Vec 2 → ℂ) y * φ y)
    (fun y => (torusHkValueCLM X : Vec 2 → ℂ) y * ((vf y 0 : ℂ) * φ y))
    (fun y => (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) 0 φ y)
    (fun y => (torusHkValueCLM X : Vec 2 → ℂ) y * fibreCovDeriv (-θ) 1 φ y)
    (fun y => (torusHkValueCLM X : Vec 2 → ℂ) y * ((vf y 1 : ℂ) * φ y))
    (hI _ hcφ) (hI _ (hvφ 0)) (hI _ (hD 0)) (hI _ (hD 1)) (hI _ (hvφ 1))
    ((sameE123 (sameAlive ηg letters i) ϖ G i i' : ℝ) : ℂ)
    ((sameE (sameAlive ηg letters i) i i' (1, 0) (1 * ϖ ^ (1 + 0)) : ℝ) : ℂ)
    ((G 0 0 + G 0 0 : ℝ) : ℂ) ((G 1 0 + G 0 1 : ℝ) : ℂ)
    ((sameE (sameAlive ηg letters i) i i' (0, 1) (1 * ϖ ^ (0 + 1)) : ℝ) : ℂ)
    ((G 0 1 + G 1 0 : ℝ) : ℂ) ((G 1 1 + G 1 1 : ℝ) : ℂ)
  have hpt : ∀ y, (torusHkValueCLM X : Vec 2 → ℂ) y * (b1wScaleRatio π ϖ ηg letters i i' *
      b1wSameTransform θ G vf i i' φ y) =
      ((sameE123 (sameAlive ηg letters i) ϖ G i i' : ℝ) : ℂ) *
          ((torusHkValueCLM X : Vec 2 → ℂ) y * φ y) +
        ((sameE (sameAlive ηg letters i) i i' (1, 0) (1 * ϖ ^ (1 + 0)) : ℝ) : ℂ) *
          ((torusHkValueCLM X : Vec 2 → ℂ) y * ((vf y 0 : ℂ) * φ y) +
            (((G 0 0 + G 0 0 : ℝ) : ℂ) * ((torusHkValueCLM X : Vec 2 → ℂ) y *
                fibreCovDeriv (-θ) 0 φ y) +
              ((G 1 0 + G 0 1 : ℝ) : ℂ) * ((torusHkValueCLM X : Vec 2 → ℂ) y *
                fibreCovDeriv (-θ) 1 φ y))) +
        ((sameE (sameAlive ηg letters i) i i' (0, 1) (1 * ϖ ^ (0 + 1)) : ℝ) : ℂ) *
          ((torusHkValueCLM X : Vec 2 → ℂ) y * ((vf y 1 : ℂ) * φ y) +
            (((G 0 1 + G 1 0 : ℝ) : ℂ) * ((torusHkValueCLM X : Vec 2 → ℂ) y *
                fibreCovDeriv (-θ) 0 φ y) +
              ((G 1 1 + G 1 1 : ℝ) : ℂ) * ((torusHkValueCLM X : Vec 2 → ℂ) y *
                fibreCovDeriv (-θ) 1 φ y))) := fun y => by
    rw [ratio_same π ϖ ηg letters hπ hϖ θ G vf i i' φ y
      ((hφ.differentiable one_ne_zero) y)]
    ring
  have e1 : b1wScaleRatio π ϖ ηg letters i i' * ∫ y in AVenhance.unitCube,
      (torusHkValueCLM X : Vec 2 → ℂ) y * b1wSameTransform θ G vf i i' φ y =
      ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y *
        (b1wScaleRatio π ϖ ηg letters i i' * b1wSameTransform θ G vf i i' φ y) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (ae_of_all _ fun y => by simp only; ring)
  rw [e1]
  simp only [hpt]
  rw [hint]

end Pair

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the forward transform of one constituent

The transpose of `realizes_gam`: for a variant of one constituent,
`φ ↦ Rcv · letterGam θ … (variantFun pre (-θ) k φ)` is the transpose of a real-linear map
`H^N → H^n` of norm `≤ GamBound`, the sum of the transposed unit terms
(`unit0`, `unit1`). The conjugation of the test form is absent. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

open Classical in
theorem gam_alpha (θ : Vec 2) (d s : ℕ) (δ : ℝ) (u v : ℕ) (β₀ w β' : ℕ × ℕ)
    (c : Vec 2 → ℝ) (fv : Vec 2 → ℂ) (Rcv : ℝ) (z : Vec 2) :
    (Rcv : ℂ) * ((((δ ^ s / (s.factorial : ℝ)) : ℝ) : ℂ) *
      ((-1 : ℂ) ^ (d - 1) * ∑ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
        if β' = (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2) then
          ((gamCoefNat u v β₀ w a : ℕ) : ℂ) *
            fibreCovPow (-θ) (u - a.1, v - a.2) (fun z' => (c z' : ℂ) * fv z') z
        else 0)) =
    ∑ a ∈ Finset.range (u + 1) ×ˢ Finset.range (v + 1),
      ((gamK Rcv δ d s u v β₀ w a β' : ℝ) : ℂ) *
        fibreCovPow (-θ) (u - a.1, v - a.2) (fun y => (c y : ℂ) * fv y) z := by
  simp only [Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  unfold gamK
  by_cases h1 : β' = (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2)
  · by_cases h2 : a.1 ≤ β₀.1 + w.1 ∧ a.2 ≤ β₀.2 + w.2
    · subst h1
      have hc : gamCond β₀ w a (β₀.1 + w.1 - a.1, β₀.2 + w.2 - a.2) := ⟨rfl, h2⟩
      simp only [ite_true, hc]
      push_cast
      ring
    · have hc : ¬ gamCond β₀ w a β' := fun hh => h2 ⟨hh.2.1, hh.2.2⟩
      simp [hc, gamCoefNat_eq_zero u v β₀ w a h2]
  · have hc : ¬ gamCond β₀ w a β' := fun hh => h1 hh.1
    simp [h1, hc]

/-- The norm bound of a forward variant: `gamBound` with the multiplier price at order
`n + preExp pre` (the coefficient is multiplied after the derivatives fall on `X`). -/
def GamBound (ρ : ℝ) (n : ℕ) (pre : Bool) (slow : ℕ) (pos : Bool) (d : ℕ) (Rcv δ : ℝ)
    (β₀ β' : ℕ × ℕ) (P : DerivativeWord2 (d - 1) → ℕ → ℝ) : ℝ :=
  ∑ α : DerivativeWord2 (d - 1), ∑ s ∈ Finset.Icc (if pos then 1 else 0) slow,
    ∑ ω : DerivativeWord2 s, ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ
        Finset.range ((wordCount α).2 + 1),
      |gamK Rcv δ d s (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β'| *
        ((1 + ρ) ^ (((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre) *
          (|cellDriftNativePrice (n + preExp pre)| * P α s))

/-- **A forward variant of one constituent is realized** with the bound `GamBound`. -/
theorem forward_variant_realized (θ : Vec 2) (ρ : ℝ) (hθ : ∀ k, |θ k| ≤ ρ) (n N s J : ℕ) (d : ℕ)
    (hd2 : 2 ≤ d) (hnd : n + d ≤ J) (hN1 : n + d ≤ N) (hs : d ≤ s) (pos : Bool) (slow : ℕ)
    (δ : ℝ) (X₀ : Vec 2) (r : ℝ) (coeff : DerivativeWord2 (d - 1) → ℝ → Vec 2 → Vec 2 → Vec 2)
    (jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ) (hjet0 : ∀ α s l, 0 ≤ jet α s l)
    (hfacts : ∀ α s, s ≤ slow → ∀ (ω : DerivativeWord2 s) (k' : Fin 2),
      ContDiff ℝ (J : ℕ∞) (tbTermCoef (coeff α r) s ω X₀ k') ∧
      AVenhance.IsZ2Periodic (tbTermCoef (coeff α r) s ω X₀ k') ∧
      ∀ l ≤ J, ∀ z, ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s ω X₀ k') z‖ ≤ jet α s l)
    (Rcv : ℝ) (β₀ : ℕ × ℕ) (k : Fin 2) (β' : ℕ × ℕ) (pre : Bool) :
    FReal N n s (fun f z => (Rcv : ℂ) * letterGam θ pos slow δ X₀ r d coeff β₀ k β'
        (variantFun pre (-θ) k f) z)
      (GamBound ρ n pre slow pos d Rcv δ β₀ β'
        (fun α s => ∑ l ∈ Finset.range (J + 1), jet α s l)) := by
  classical
  have unit : ∀ (α : DerivativeWord2 (d - 1)) (s' : ℕ), s' ≤ slow → ∀ (ω : DerivativeWord2 s')
      (a : ℕ × ℕ), a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1) →
      FReal N n s (fun f z => ((gamK Rcv δ d s' (wordCount α).1 (wordCount α).2 β₀
          (wordCount ω) a β' : ℝ) : ℂ) * fibreCovPow (-θ)
          ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
          (fun y => (tbTermCoef (coeff α r) s' ω X₀ k y : ℂ) * variantFun pre (-θ) k f y) z)
        (|gamK Rcv δ d s' (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β'| *
          ((1 + ρ) ^ (((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) + preExp pre) *
            (|cellDriftNativePrice (n + preExp pre)| *
              ∑ l ∈ Finset.range (J + 1), jet α s' l))) := by
    intro α s' hs' ω a ha
    have hwc := wordCount_sum α
    obtain ⟨hc, hp, hj⟩ := hfacts α s' hs' ω k
    cases pre
    · have hc' : ContDiff ℝ ((n + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) : ℕ) : ℕ∞)
          (tbTermCoef (coeff α r) s' ω X₀ k) := hc.of_le (by exact_mod_cast (by omega))
      have hP : ∀ l ≤ n, ∀ x, ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s' ω X₀ k) x‖ ≤
          ∑ l ∈ Finset.range (J + 1), jet α s' l := by
        intro l hl x
        refine (hj l (by omega) x).trans ?_
        exact Finset.single_le_sum (f := fun l => jet α s' l) (fun l _ => hjet0 α s' l)
          (Finset.mem_range.2 (by omega))
      have := unit0 θ ρ hθ n N s ((wordCount α).1 - a.1) ((wordCount α).2 - a.2)
        (by omega) (by omega) hc' hp hP
        (gamK Rcv δ d s' (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β')
      simpa [variantFun, preExp] using this
    · have hc' : ContDiff ℝ ((n + 1 + ((wordCount α).1 - a.1) + ((wordCount α).2 - a.2) : ℕ) : ℕ∞)
          (tbTermCoef (coeff α r) s' ω X₀ k) := hc.of_le (by exact_mod_cast (by omega))
      have hP : ∀ l ≤ n + 1, ∀ x, ‖iteratedFDeriv ℝ l (tbTermCoef (coeff α r) s' ω X₀ k) x‖ ≤
          ∑ l ∈ Finset.range (J + 1), jet α s' l := by
        intro l hl x
        refine (hj l (by omega) x).trans ?_
        exact Finset.single_le_sum (f := fun l => jet α s' l) (fun l _ => hjet0 α s' l)
          (Finset.mem_range.2 (by omega))
      have := unit1 θ ρ hθ n N s ((wordCount α).1 - a.1) ((wordCount α).2 - a.2) k
        (by omega) (by omega) hc' hp hP
        (gamK Rcv δ d s' (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β')
      simpa [variantFun, preExp] using this
  have hsum : FReal N n s (fun f z => ∑ α : DerivativeWord2 (d - 1),
      ∑ s' ∈ Finset.Icc (if pos then 1 else 0) slow, ∑ ω : DerivativeWord2 s',
        ∑ a ∈ Finset.range ((wordCount α).1 + 1) ×ˢ Finset.range ((wordCount α).2 + 1),
          ((gamK Rcv δ d s' (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) a β' : ℝ) : ℂ) *
            fibreCovPow (-θ) ((wordCount α).1 - a.1, (wordCount α).2 - a.2)
              (fun y => (tbTermCoef (coeff α r) s' ω X₀ k y : ℂ) * variantFun pre (-θ) k f y) z)
      (GamBound ρ n pre slow pos d Rcv δ β₀ β'
        (fun α s => ∑ l ∈ Finset.range (J + 1), jet α s l)) :=
    FReal.finset_sum (N := N) (n := n) Finset.univ (fun α _ =>
      FReal.finset_sum _ (fun s' hs' =>
        FReal.finset_sum _ (fun ω _ =>
          FReal.finset_sum _ (fun a ha =>
            unit α s' (Finset.mem_Icc.1 hs').2 ω a ha))))
  refine hsum.congr (fun φ _ _ => ?_)
  funext z
  unfold letterGam
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun s' hs' => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun ω _ => ?_
  exact (gam_alpha θ d s' δ (wordCount α).1 (wordCount α).2 β₀ (wordCount ω) β'
    (tbTermCoef (coeff α r) s' ω X₀ k) (variantFun pre (-θ) k φ) Rcv z).symm

end AVRegularity.CycleWords.Discard
end
end
end

section
section
/-! # the numerical bound of a forward variant

`GamBound_le` is `gamBound_le` for `GamBound`: the multiplier price is at order
`n + preExp pre ≤ n + D`, which `gamPr n D` covers. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] {D Nw : ℕ}

theorem GamBound_le (π : ι → ℝ) (ϖ ηg : ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (x x' : ι) (β β' β₀ : ℕ × ℕ) (d M0 Dm n J Sm : ℕ) (hSm : (letters l).slow ≤ Sm) (ρ : ℝ) (hρ : 0 ≤ ρ) (pre : Bool)
    (cv : ℝ) (hcv : |cv| ≤ (M0 : ℝ) + 1)
    (hx : 0 < π x) (hx' : 0 < π x') (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1)
    (hθ : 0 < (letters l).theta)
    (hd : d ≤ Dm) (hd2 : 2 ≤ d) (hb0 : β₀.1 + β₀.2 ≤ β.1 + β.2)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0)
    (jet : DerivativeWord2 (d - 1) → ℕ → ℕ → ℝ) (hjet0 : ∀ α s l, 0 ≤ jet α s l) :
    GamBound ρ n pre (letters l).slow (letters l).positive d
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
          (|cellDriftNativePrice (n + preExp pre)| *
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
    have hpr : |cellDriftNativePrice (n + preExp pre)| ≤ Pr :=
      Finset.single_le_sum (f := fun K => |cellDriftNativePrice K|) (fun _ _ => abs_nonneg _)
        (Finset.mem_range.2 (by unfold preExp; split_ifs <;> omega))
    have hP := hP0 α s
    calc _ ≤ Ccb * ((1 + ρ) ^ Dm * (Pr * ∑ q ∈ Finset.range (J + 1), jet α s q)) := by
          gcongr
      _ = _ := by rw [hQ]; ring
  have hcardw : ∀ s : ℕ, (Fintype.card (DerivativeWord2 s) : ℝ) = 2 ^ s := by
    intro s; simp [DerivativeWord2, DerivativeWord]
  unfold GamBound
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


end AVRegularity.CycleWords.Discard
end
end

section
/-! # forward block realizations

`FBRealizes N n s G c`: the family of functionals `G b b'` is the transpose of a family of
real-linear maps `T b b' : H^N → H^n` (`b` an output basis index, `b'` an input one) whose block
bound is `∑_b ‖∑_{b'} T b b' (f b')‖² ≤ c² ∑_{b'} ‖f b'‖²`, i.e. `BlockBound c` of the swapped
family.  The basis matrix of the swapped family is that of the adjoint (`letterMat_adjoint`). -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

section FB

variable {m₁ m₂ N n s : ℕ}

/-- A family of functionals that is the transpose of a family of maps with a block bound. -/
def FBRealizes (N n s : ℕ) (G : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ) (c : ℝ) : Prop :=
  ∃ T : Fin m₁ → Fin m₂ → TorusHk N ℂ →L[ℝ] TorusHk n ℂ,
    BlockBound c (fun b' b => T b b') ∧
    ∀ φ : Vec 2 → ℂ, ContDiff ℝ (s : ℕ) φ → AVenhance.IsZ2Periodic φ →
      (∀ b b', Continuous (G b b' φ)) ∧ ∀ b b' (X : TorusHk N ℂ),
        ∫ y in AVenhance.unitCube, (torusHkValueCLM (T b b' X) : Vec 2 → ℂ) y * φ y =
          ∫ y in AVenhance.unitCube, (torusHkValueCLM X : Vec 2 → ℂ) y * G b b' φ y

variable {G G' : Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c c' : ℝ}

theorem FBRealizes.zero : FBRealizes (m₁ := m₁) (m₂ := m₂) N n s (fun _ _ _ _ => 0) 0 :=
  ⟨fun _ _ => 0, BlockBound.zero, fun φ h1 _ => ⟨fun _ _ => continuous_const, fun b b' X => by
    simp only [zero_apply, map_zero, mul_zero, integral_zero]
    rw [int_eq _ _ h1.continuous, map_zero]⟩⟩

theorem FBRealizes.mono (h : FBRealizes N n s G c) (hc : c ≤ c') : FBRealizes N n s G c' := by
  obtain ⟨T, hb, hp⟩ := h
  exact ⟨T, hb.mono hc, hp⟩

theorem FBRealizes.congr (h : FBRealizes N n s G c)
    (hG : ∀ b b' (φ : Vec 2 → ℂ), ContDiff ℝ (s : ℕ) φ → AVenhance.IsZ2Periodic φ →
      G b b' φ = G' b b' φ) : FBRealizes N n s G' c := by
  obtain ⟨T, hb, hp⟩ := h
  refine ⟨T, hb, fun φ h1 h2 => ?_⟩
  obtain ⟨hc, he⟩ := hp φ h1 h2
  refine ⟨fun b b' => ?_, fun b b' X => ?_⟩
  · rw [← hG b b' φ h1 h2]; exact hc b b'
  · rw [← hG b b' φ h1 h2]; exact he b b' X

theorem FBRealizes.add (h : FBRealizes N n s G c) (h' : FBRealizes N n s G' c') :
    FBRealizes N n s (fun b b' f z => G b b' f z + G' b b' f z) (c + c') := by
  obtain ⟨T, hb, hp⟩ := h
  obtain ⟨T', hb', hp'⟩ := h'
  refine ⟨fun b b' => T b b' + T' b b', hb.add hb', fun φ h1 h2 => ?_⟩
  obtain ⟨c1, e1⟩ := hp φ h1 h2
  obtain ⟨c2, e2⟩ := hp' φ h1 h2
  refine ⟨fun b b' => (c1 b b').add (c2 b b'), fun b b' X => ?_⟩
  have hφ := h1.continuous
  rw [add_apply, map_add, int_eq _ _ hφ, map_add, ← int_eq _ _ hφ,
    ← int_eq _ _ hφ, e1, e2]
  simp only [mul_add]
  exact (integral_add (pair_integrable _ (c1 b b') _)
    (pair_integrable _ (c2 b b') _)).symm

theorem FBRealizes.finset_sum {κ : Type*} (S : Finset κ)
    {G : κ → Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c : κ → ℝ}
    (h : ∀ j ∈ S, FBRealizes N n s (G j) (c j)) :
    FBRealizes N n s (fun b b' f z => ∑ j ∈ S, G j b b' f z) (∑ j ∈ S, c j) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using (FBRealizes.zero (m₁ := m₁) (m₂ := m₂) (N := N) (n := n) (s := s))
  | insert a S ha ih =>
    have := (h a (Finset.mem_insert_self a S)).add
      (ih fun j hj => h j (Finset.mem_insert_of_mem hj))
    simpa [Finset.sum_insert ha] using this

theorem FBRealizes.list_sum {κ : Type*} (l : List κ)
    {G : κ → Fin m₁ → Fin m₂ → (Vec 2 → ℂ) → Vec 2 → ℂ} {c : κ → ℝ}
    (h : ∀ j ∈ l, FBRealizes N n s (G j) (c j)) :
    FBRealizes N n s (fun b b' f z => (l.map fun j => G j b b' f z).sum) (l.map c).sum := by
  induction l with
  | nil => simpa using (FBRealizes.zero (m₁ := m₁) (m₂ := m₂) (N := N) (n := n) (s := s))
  | cons a l ih =>
    have := (h a List.mem_cons_self).add (ih fun j hj => h j (List.mem_cons_of_mem _ hj))
    simpa using this

variable {H₁ H₂ : Type*} [NormedAddCommGroup H₁] [InnerProductSpace ℝ H₁]
  [NormedAddCommGroup H₂] [InnerProductSpace ℝ H₂] [FiniteDimensional ℝ H₁]
  [FiniteDimensional ℝ H₂]

theorem letterMat_adjoint (e : OrthonormalBasis (Fin m₁) ℝ H₁)
    (e' : OrthonormalBasis (Fin m₂) ℝ H₂) (M : H₂ →L[ℝ] H₁) (b : Fin m₁) (b' : Fin m₂) :
    letterMat e' e (ContinuousLinearMap.adjoint M) b' b = letterMat e e' M b b' := by
  unfold letterMat
  rw [ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.adjoint_inner_left, real_inner_comm]

theorem FBRealizes.of_freal (e : OrthonormalBasis (Fin m₁) ℝ H₁)
    (e' : OrthonormalBasis (Fin m₂) ℝ H₂) (M : H₂ →L[ℝ] H₁) {G : (Vec 2 → ℂ) → Vec 2 → ℂ}
    {B : ℝ} (hB : 0 ≤ B) (h : FReal N n s G B) :
    FBRealizes N n s (fun b b' f z => ((letterMat e e' M b b' : ℝ) : ℂ) * G f z) (‖M‖ * B) := by
  obtain ⟨A, hn, hp⟩ := h
  have hA : ‖A‖ ≤ B := ContinuousLinearMap.opNorm_le_bound _ hB hn
  have hbb := blockBound_mat_smul e' e (ContinuousLinearMap.adjoint M) A
  refine ⟨fun b b' => lrSmul (letterMat e e' M b b') A, ?_, fun φ h1 h2 => ?_⟩
  · have := hbb
    simp only [letterMat_adjoint, ContinuousLinearMap.adjoint.norm_map] at this
    exact this.mono (mul_le_mul_of_nonneg_left hA (norm_nonneg _))
  obtain ⟨c1, e1⟩ := hp φ h1 h2
  refine ⟨fun b b' => continuous_const.mul c1, fun b b' X => ?_⟩
  have hφ := h1.continuous
  rw [lrSmul_apply, map_smul, int_eq _ _ hφ, map_smul, ← int_eq _ _ hφ, e1]
  simp only [Complex.real_smul]
  rw [← integral_const_mul]
  exact integral_congr_ae (Filter.Eventually.of_forall fun y => by ring)

end FB

end AVRegularity.CycleWords.Discard
end
end

section
/-! # the forward block operators of a pair of components and moments

The transpose of `letterBlock_exists`: `fwdGfam` is the transform of a pair of components and
moments (the test-form `letterGfam` without the conjugations), realized by `fwd_letterBlock_exists`
with the block constant `4 gamCfin κ(β,β') majorant/θ`. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
  AVRegularity.CycleEvolution
open AVRegularity.CycleWords.Assembly

namespace AVRegularity.CycleWords.Discard

universe u v

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D Nw : ℕ}

theorem GamBound_nonneg (ρ : ℝ) (hρ : 0 ≤ ρ) (n : ℕ) (pre : Bool) (slow : ℕ) (pos : Bool)
    (d : ℕ) (Rcv δ : ℝ) (β₀ β' : ℕ × ℕ) (P : DerivativeWord2 (d - 1) → ℕ → ℝ)
    (hP : ∀ α s, 0 ≤ P α s) : 0 ≤ GamBound ρ n pre slow pos d Rcv δ β₀ β' P :=
  Finset.sum_nonneg fun α _ => Finset.sum_nonneg fun s _ => Finset.sum_nonneg fun ω _ =>
    Finset.sum_nonneg fun a _ => mul_nonneg (abs_nonneg _)
      (mul_nonneg (pow_nonneg (by linarith) _) (mul_nonneg (abs_nonneg _) (hP α s)))

open Classical in
/-- The conjugated letter transform of the components `x, x'` and the moments `β, β'`, as a family
of functionals indexed by the basis vectors: `R` times the conjugate of the transform of the
conjugate, with the basis factor `⟨γ.map* e_b, e'_{b'}⟩` of each constituent. -/
def fwdGfam (θ : Vec 2) (L : CycleLetter ι h D) (A : Finset ℕ) (δ : ℝ) (X₀ : Vec 2) (r : ℝ)
    (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) :
    Fin (Module.finrank ℝ (h x)) → Fin (Module.finrank ℝ (h x')) → (Vec 2 → ℂ) → Vec 2 → ℂ :=
  fun b b' f z =>
    ((letterVars β).map fun w => ∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
      ((L.edge x x' ⟨d, hd⟩).map fun γ =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((R * w.1 : ℝ) : ℂ) * (letterGam θ L.positive L.slow δ X₀ r d γ.coeff w.2.1
            w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 f) z))).sum
      else 0).sum


omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **One constituent, one variant**: the block family of a single `(w, d, γ)`. -/
theorem fbr_gamma (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw) (a b : ℝ)
    (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (r : ℝ)
    (hr : r ∈ Icc a b) (hg : LetterGood (letters l) (Icc a b) J r) (hπ : ∀ x, 0 < π x)
    (ϖ ηg : ℝ) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1) (θ : Vec 2) (ρ : ℝ)
    (hθ : ∀ k, |θ k| ≤ ρ) (X₀ : Vec 2) (n N Dmax M0 S : ℕ)
    (hord : (letters l).order ≤ Dmax) (hslow : (letters l).slow ≤ S) (hJ : n + Dmax ≤ J)
    (hN1 : n + (letters l).order ≤ N) (s : ℕ) (hs : Dmax ≤ s) (x x' : ι) (β β' : ℕ × ℕ)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) (hθpos : 0 < (letters l).theta)
    (w : ℝ × (ℕ × ℕ) × Fin 2 × Bool) (hw : w ∈ letterVars β) (d : ℕ) (hd : d ∈ Finset.Icc 2 D)
    (γ : Constituent d (h x') (h x)) (hγ : γ ∈ (letters l).edge x x' ⟨d, hd⟩) :
    FBRealizes (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) N n s
      (fun b b' f z =>
        ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
          (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
            (letterGam θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d γ.coeff w.2.1
              w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 f) z)))
      (‖γ.map‖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff)) := by
  classical
  have hρ : 0 ≤ ρ := (abs_nonneg _).trans (hθ 0)
  by_cases hm : γ.map = 0
  · have h0 : ‖γ.map‖ * (gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) *
        jetTotal (Icc a b) (letters l).slow J d γ.coeff) = 0 := by simp [hm]
    rw [h0]
    refine FBRealizes.zero.congr fun b b' φ _ _ => ?_
    funext z
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
    have hreal := forward_variant_realized θ ρ hθ n N s J d hd2 (by omega) (by omega) (by omega)
      (letters l).positive (letters l).slow (ϖ * ηg) X₀ r γ.coeff jet hjet0 hfacts
      (letterRatioReal π ϖ ηg letters l x x' β β' * w.1) w.2.1 w.2.2.1 β' w.2.2.2
    have hBnn := GamBound_nonneg ρ hρ n w.2.2.2 (letters l).slow (letters l).positive d
      (letterRatioReal π ϖ ηg letters l x x' β β' * w.1) (ϖ * ηg) w.2.1 β'
      (fun α s => ∑ q ∈ Finset.range (J + 1), jet α s q)
      (fun α s => Finset.sum_nonneg fun q _ => hjet0 α s q)
    have hbr := FBRealizes.of_freal (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x'))
      γ.map hBnn hreal
    refine hbr.mono ?_
    have hb := GamBound_le π ϖ ηg letters l x x' β β' w.2.1 d M0 D n J S hslow ρ hρ w.2.2.2 w.1 hwb
      (hπ x) (hπ x') hϖ0 hϖ1 hg0 hg1 hθpos (Finset.mem_Icc.1 hd).2 hd2 (by omega) hβM hβ'M jet hjet0
    exact mul_le_mul_of_nonneg_left (hb.trans (le_of_eq (by unfold jetTotal; rfl))) (norm_nonneg _)


omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
theorem fwdGfam_zero_R (θ : Vec 2) (L : CycleLetter ι h D) (A : Finset ℕ) (δ : ℝ) (X₀ : Vec 2)
    (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (b b' f z) :
    fwdGfam θ L A δ X₀ r x x' β β' 0 b b' f z = 0 := by
  classical
  unfold fwdGfam
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
theorem fwdGfam_zero_rel (θ : Vec 2) (π : ι → ℝ) (Jstar H : ℕ) (dom : Set (ℝ × Vec 2))
    (L : CycleLetter ι h D) (hL : IsCycleLetter π L dom Jstar H) (A : Finset ℕ) (δ : ℝ)
    (X₀ : Vec 2) (r : ℝ) (x x' : ι) (β β' : ℕ × ℕ) (R : ℝ) (S Dmax : ℕ)
    (hord : L.order ≤ Dmax) (hslow : L.slow ≤ S) (hn : ¬ LetterMomRel S (Dmax + 1) β β') (b b' f z) :
    fwdGfam θ L A δ X₀ r x x' β β' R b b' f z = 0 := by
  classical
  unfold fwdGfam
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
      w.2.2.1 (variantFun w.2.2.2 (-θ) w.2.2.1 f) S Dmax (hdle.trans hord) hslow hw2 hw3 hw4 hw5 hn
    rw [hz]
    simp
  · simp [hd]


omit [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] in
/-- **The block operators of a pair of components and moments.** -/
theorem fwd_letterBlock_exists (π : ι → ℝ) (letters : Fin Nw → CycleLetter ι h D) (l : Fin Nw)
    (a b : ℝ) (J H : ℕ) (hL : IsCycleLetter π (letters l) (Icc a b ×ˢ Set.univ) J H) (r : ℝ)
    (hr : r ∈ Icc a b) (hg : LetterGood (letters l) (Icc a b) J r) (hπ : ∀ x, 0 < π x)
    (ϖ ηg : ℝ) (hϖ0 : 0 < ϖ) (hϖ1 : ϖ ≤ 1) (hg0 : 0 < ηg) (hg1 : ηg ≤ 1) (θ : Vec 2) (ρ : ℝ)
    (hθ : ∀ k, |θ k| ≤ ρ) (X₀ : Vec 2) (A : Finset ℕ) (n N Dmax M0 S : ℕ)
    (hord : (letters l).order ≤ Dmax) (hslow : (letters l).slow ≤ S) (hJ : n + Dmax ≤ J)
    (hN1 : n + (letters l).order ≤ N) (s : ℕ) (hs : Dmax ≤ s) (x x' : ι) (β β' : ℕ × ℕ)
    (hβM : β.1 + β.2 ≤ M0) (hβ'M : β'.1 + β'.2 ≤ M0) :
    FBRealizes (m₁ := Module.finrank ℝ (h x)) (m₂ := Module.finrank ℝ (h x')) N n s
      (fwdGfam θ (letters l) A (ϖ * ηg) X₀ r x x' β β'
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
    exact FBRealizes.zero.congr fun b' b'' φ _ _ => funext fun z => (fwdGfam_zero_rel θ π J H _
      (letters l) hL A (ϖ * ηg) X₀ r x x' β β' _ S Dmax hord hslow hrel _ _ _ z).symm
  by_cases hθ0 : (letters l).theta = 0
  · have hR : letterRatioReal π ϖ ηg letters l x x' β β' = 0 := by
      unfold letterRatioReal letterFac
      simp [hθ0]
    have h0 : 4 * gamCfin D n ρ M0 S * (if LetterMomRel S (Dmax + 1) β β' then 1 else 0) *
        letterCompWeight (letters l) x x' = 0 := by simp [letterCompWeight, hθ0]
    rw [h0, hR]
    exact FBRealizes.zero.congr fun b' b'' φ _ _ => funext fun z => (fwdGfam_zero_R θ (letters l) A
      (ϖ * ηg) X₀ r x x' β β' _ _ _ z).symm
  have hθpos : 0 < (letters l).theta := lt_of_le_of_ne hL.theta_nonneg (Ne.symm hθ0)
  set K := gamCfin D n ρ M0 S * (Real.sqrt (π x' / π x) / (letters l).theta) with hK
  set Jt : ∀ d : ℕ, Constituent d (h x') (h x) → ℝ := fun d γ =>
    jetTotal (Icc a b) (letters l).slow J d γ.coeff with hJt
  -- the family per variant
  have hvar : ∀ w ∈ letterVars β, FBRealizes (m₁ := Module.finrank ℝ (h x))
      (m₂ := Module.finrank ℝ (h x')) N n s
      (fun b b' f z => ∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ =>
          ((letterMat (stdOrthonormalBasis ℝ (h x)) (stdOrthonormalBasis ℝ (h x')) γ.map b b' : ℝ) : ℂ) *
            (((letterRatioReal π ϖ ηg letters l x x' β β' * w.1 : ℝ) : ℂ) *
              (letterGam θ (letters l).positive (letters l).slow (ϖ * ηg) X₀ r d γ.coeff w.2.1
                w.2.2.1 β' (variantFun w.2.2.2 (-θ) w.2.2.1 f) z))).sum)
        else 0)
      (∑ d ∈ A, if hd : d ∈ Finset.Icc 2 D then
        ((((letters l).edge x x' ⟨d, hd⟩).map fun γ => ‖γ.map‖ * (K * Jt d γ))).sum else 0) := by
    intro w hw
    refine FBRealizes.finset_sum A fun d _ => ?_
    by_cases hd : d ∈ Finset.Icc 2 D
    · simp only [hd, dite_true]
      exact FBRealizes.list_sum _ fun γ hγ => fbr_gamma π letters l a b J H hL r hr hg hπ ϖ ηg hϖ0
        hϖ1 hg0 hg1 θ ρ hθ X₀ n N Dmax M0 S hord hslow hJ hN1 s hs x x' β β' hβM hβ'M hθpos w hw d hd
        γ hγ
    · simpa [hd] using (FBRealizes.zero (m₁ := Module.finrank ℝ (h x))
        (m₂ := Module.finrank ℝ (h x')) (N := N) (n := n) (s := s))
  have hmain := FBRealizes.list_sum (letterVars β) hvar
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
end AVRegularity.CycleWords.Discard
end
end
end
