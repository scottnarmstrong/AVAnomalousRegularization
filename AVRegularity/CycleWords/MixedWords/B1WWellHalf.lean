-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.MixedWords.SharpBlocksSameComm
public import AVRegularity.CycleWords.MixedWords.SharpLetterFinal
import AVRegularity.CycleWords.MixedWords.WeightedPlainDecayKappa
public import AVRegularity.CycleWords.MixedWords.B1WWeightedMember
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit
import AVRegularity.CycleWords.MixedWords.B1WWeightedNormFacts
import AVRegularity.CycleWords.MixedWords.StageExpansionLetter

@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # The weighted H4 at every time

The AFW hypothesis `H4` for the weighted test norm `ν k r = b1wNuW s Ω e k r`. The test families
are weighted adjoint curves (`hadj`, the form of `b1w_weighted_adjoint`): at every `r` they split
along `e(r)` with the weight `1` and with the weights `Ω k' r` of the lower levels `k' < k` (the
weighted sharp decay with two levels drops a level).
* `b1w_weighted_family` bounds the representatives and their weighted defects.
* At the endpoint `a` the weight is `1` (`hΩa`), so `ν k a ≤ ‖U‖ + ‖U − PU‖`.
* At a good time, `b1w_weighted_H4_at` with `Y = 2C_d e^{-π²(a+t−r)/8}`.
* At a bad time, the forcing is `0`.

Constants: `c_f = π²/8`, `C_f = 3C_d`, `ε_f = 0`, and any `Θ ≥ b1wWeightedΘ B c_E C_w`. -/

universe u v

theorem wH4_coeff_le {Θw Θ ζ Cd X : ℝ} (hΘ : Θw ≤ Θ) (hΘw : 0 ≤ Θw) (hζ : 0 ≤ ζ)
    (hCd : 0 ≤ Cd) (hX : 0 ≤ X) : Θw * ζ * (2 * Cd * X) ≤ Θ * ζ * (3 * Cd) * X :=
  calc Θw * ζ * (2 * Cd * X) = (Θw * ζ) * (2 * (Cd * X)) := by ring
    _ ≤ (Θ * ζ) * (3 * (Cd * X)) :=
        mul_le_mul (mul_le_mul_of_nonneg_right hΘ hζ) (by linarith [mul_nonneg hCd hX])
          (by positivity) (mul_nonneg (hΘw.trans hΘ) hζ)
    _ = Θ * ζ * (3 * Cd) * X := by ring

theorem wH4_nu_le {Θw Θ Cd X : ℝ} (hΘ : Θw ≤ Θ) (hΘw : 0 ≤ Θw) (hCd : 0 ≤ Cd) (hX : 0 ≤ X) :
    Θw * (2 * Cd * X) ≤ Θ * (3 * Cd) * X := by
  have := wH4_coeff_le hΘ hΘw zero_le_one hCd hX
  simpa only [mul_one] using this

theorem wH4_end_le {a b c Cd X : ℝ} (h1 : a ≤ b + 1 * c) (hb : b ≤ Cd * X)
    (hc : 1 * c ≤ 2 * Cd * X) : a ≤ 3 * Cd * X := by
  linarith

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The weighted H4 at every time.** -/
theorem b1w_weighted_H4 {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (hπ : ∀ x, 0 < F.π x) (hϖ : 0 < F.ϖ) (hη : 0 < F.η) (s : ℕ → ℕ) (n : ℕ)
    (hn : ∀ k, n + 3 ≤ s k)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ) (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (Good : Set ℝ)
    (hGsrc : ∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
      src i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
      (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r)
    (hGexp : ∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ (i i' : B1WIndex ι h Nw m Ks), ¬ b1wSt i' < b1wSt i →
      ∀ (r : ℝ) (φ : Vec 2 → ℂ), b1wTestTransform F θ i i' r φ = 0)
    (B M₀ : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ r ∈ Good, ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          B1WSharpFamily F θ r k k' (s k) (s k') ψ Φ B M₀)
    (tr q : ℝ → ComplexCellL2) (E : ℝ → ℂ)
    (hE : ∀ r ∈ Icc F.a F.b, cellComplexPair (tr r + cellConstantCLM 1) (q r) = E r)
    (hE0 : ∀ r, E r ≠ 0)
    (htr : ∀ r ∈ Good, ‖tr r‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ))
    (cE Cw : ℝ) (hcE : 0 ≤ cE) (hCw : 0 ≤ Cw) (M : ℕ)
    (Ω : ℕ → ℝ → ℝ) (e : ℝ → Fin 2) (hΩ1 : ∀ k r, 1 ≤ Ω k r) (hΩa : ∀ k, Ω k F.a = 1)
    (Uq : ℝ → ∀ k', TorusHk (s k') ℂ)
    (hUq : ∀ r ∈ Good, ∀ k' < M, torusHkValueCLM (Uq r k') = q r)
    (hUqn : ∀ r ∈ Good, ∀ k' < M, ‖Uq r k'‖ ≤ Cw * ‖E r‖)
    (hwin : ∀ r ∈ Good, ∀ k' < M, 1 < Ω k' r →
      ∃ p, IsLeastWindow F.reg p r ∧ F.reg.orient p = e r)
    (hΩq : ∀ r ∈ Good, ∀ k' < M, 1 < Ω k' r →
      ∀ P : TorusHk (s k') ℂ →L[ℝ] TorusHk (s k') ℂ,
        (∀ U, torusHkValueCLM (P U) = cellTransverseProjection (e r) (torusHkValueCLM U)) →
        Ω k' r * ‖Uq r k' - P (Uq r k')‖ ≤ ‖E r‖)
    (N₀ : ℂ) (Γ : ℝ → ℝ) (hNΓ : ∀ r ∈ Icc F.a F.b, ‖N₀‖ * Γ r = ‖E r‖)
    (C : CellCoefficients) (hCθ : C.θ = fun j => (Real.sqrt F.η : ℂ) * planeFibreFrequency F.η θ j)
    (hG : IsCellMetric C.G) (V : ℝ) (hv : IsCellDrift C.v)
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (Cd : ℝ) (hCd : 0 ≤ Cd)
    (hadj : ∀ k < M, ∀ T ∈ Icc F.a F.b, ∀ ψ : ComplexCellL2, b1wAdm s tr k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve F.a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        (∀ r ∈ Icc F.a T, b1wAdm s tr k r (Ψv r)) ∧
        ∀ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ →
          cellTransverseProjection (e T) (torusHkValueCLM UT) = torusHkValueCLM UT →
        ∀ r ∈ Icc F.a T, ∀ ω ∈ {ω : ℝ | ω = 1 ∨ ∃ k' < k, Ω k' r = ω},
          ∃ VT VN : TorusHk (s k) ℂ,
          torusHkValueCLM (VT + VN) = Ψv r ∧
          cellTransverseProjection (e r) (torusHkValueCLM VT) = torusHkValueCLM VT ∧
          ‖VT‖ + ω * ‖VN‖ ≤
            Cd * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) * (‖UT‖ + Ω k T * ‖UN‖))
    (Θ : ℝ) (hΘ : b1wWeightedΘ B cE Cw ≤ Θ) :
    ∀ t ∈ Icc 0 (F.b - F.a), ∀ k < M, ∀ ψ : B1WIndex ι h Nw m Ks → ComplexCellL2,
      (∀ i ∈ stageSet b1wSt k, b1wAdm s tr k (F.a + t) (ψ i)) →
      Real.sqrt (∑ i ∈ stageSet b1wSt k, b1wNuW s Ω e k (F.a + t) (ψ i) ^ 2) ≤ 1 →
      ∃ (Ψv : B1WIndex ι h Nw m Ks → ℝ → ComplexCellL2)
        (Ψs : B1WIndex ι h Nw m Ks → ℝ → TorusHk 1 ℂ),
        (∀ i ∈ stageSet b1wSt k, CellWeakHilbertCurve F.a (F.a + t) (Ψv i) (Ψs i) (fun r =>
          -cellDualDerivative (cellAdjointCoefficients C) hG V (cellDrift_neg hv).1
            (cellDrift_neg_bound hb) r (Ψs i r) 0 0) ∧ Ψv i (F.a + t) = ψ i) ∧
        (∀ i ∈ stageSet b1wSt k, b1wAdm s tr k F.a (Ψv i F.a)) ∧
        Real.sqrt (∑ i ∈ stageSet b1wSt k, b1wNuW s Ω e k F.a (Ψv i F.a) ^ 2) ≤
          3 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * t) ∧
        ∀ r ∈ Icc F.a (F.a + t),
          ∃ (κ : B1WIndex ι h Nw m Ks → ℂ) (φ : B1WIndex ι h Nw m Ks → ComplexCellL2),
          (∀ k' < k, ∀ i' ∈ stageSet b1wSt k', b1wAdm s tr k' r (φ i')) ∧
          (∀ k' < k, stageNorm b1wSt k' κ ≤
            Θ * min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) * (3 * Cd) *
              Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) / (‖N₀‖ * Γ r)) ∧
          (∀ k' < k, Real.sqrt (∑ i' ∈ stageSet b1wSt k', b1wNuW s Ω e k' r (φ i') ^ 2) ≤
            Θ * (3 * Cd) * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r))) ∧
          ‖∑ i ∈ stageSet b1wSt k, cellComplexSource C.θ
              (Good.indicator (fun t =>
                cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) t)) r)
              (Good.indicator (fun t j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
                (cellSourceSlice (fun r z => Fl i r z j) t)) r) (Ψs i r) -
            ∑ k' ∈ Finset.range k, ∑ i' ∈ stageSet b1wSt k',
              (κ i' * cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
                  (cellRawTrace (Dθ i') r)) (q r) +
                cellComplexPair (cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i')
                  (cellRawTrace (Dθ i') r)) (φ i'))‖ ≤
            0 / Γ (F.a + t) := by
  intro t ht k hk ψ hψ hψ1
  have hT : F.a + t ∈ Icc F.a F.b := ⟨by linarith [ht.1], by linarith [ht.2]⟩
  have hs1 : 1 ≤ s k := by have := hn k; omega
  have hΘw0 : 0 ≤ b1wWeightedΘ B cE Cw := by unfold b1wWeightedΘ; positivity
  have hΩ0 : ∀ k' r, 0 ≤ Ω k' r := fun k' r => zero_le_one.trans (hΩ1 k' r)
  obtain ⟨Ψv, Ψs, U, hcurve, hfin, hvalU, hprop, hsz, hdef⟩ := b1w_weighted_family b1wSt s k
    hs1 tr C hG V hv hb F.a (F.a + t) Cd (Ω k (F.a + t)) hCd e
    (fun r => {ω : ℝ | ω = 1 ∨ ∃ k' < k, Ω k' r = ω})
    (fun r ω hω => hω.elim (fun h1 => h1 ▸ le_rfl) fun ⟨k', _, hω⟩ => hω ▸ hΩ1 k' r)
    (fun r => ⟨1, Or.inl rfl⟩) (hadj k hk (F.a + t) hT) ψ hψ
  have hn1 : Real.sqrt (∑ i ∈ stageSet b1wSt k,
      b1wNuW s (fun _ _ => Ω k (F.a + t)) e k (F.a + t) (ψ i) ^ 2) ≤ 1 := hψ1
  have hX : ∀ r : ℝ, 0 ≤ Cd * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) :=
    fun r => mul_nonneg hCd (Real.exp_pos _).le
  have hX2 : ∀ r : ℝ, 0 ≤ 2 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) :=
    fun r => mul_nonneg (mul_nonneg zero_le_two hCd) (Real.exp_pos _).le
  -- the sizes and the weighted defects of the representatives
  have hsize : ∀ r ∈ Icc F.a (F.a + t), Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖U i r‖ ^ 2) ≤
      Cd * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) := fun r hr =>
    (hsz r hr).trans ((mul_le_mul_of_nonneg_left hn1 (hX r)).trans_eq (mul_one _))
  have hdefect : ∀ r ∈ Icc F.a (F.a + t), ∀ ω ∈ {ω : ℝ | ω = 1 ∨ ∃ k' < k, Ω k' r = ω},
      ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
      (∀ W, torusHkValueCLM (P W) = cellTransverseProjection (e r) (torusHkValueCLM W)) →
      (∀ W, ‖P W‖ ≤ ‖W‖) →
      ω * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖U i r - P (U i r)‖ ^ 2) ≤
        2 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * (F.a + t - r)) := fun r hr ω hω P hP hPn =>
    (hdef r hr ω hω P hP hPn).trans
      ((mul_le_mul_of_nonneg_left hn1 (hX2 r)).trans_eq (mul_one _))
  have haT : F.a ∈ Icc F.a (F.a + t) := ⟨le_rfl, by linarith [ht.1]⟩
  -- the endpoint, where the weight is `1`
  have hend : Real.sqrt (∑ i ∈ stageSet b1wSt k, b1wNuW s Ω e k F.a (Ψv i F.a) ^ 2) ≤
      3 * Cd * Real.exp (-(Real.pi ^ 2 / 8) * t) := by
    obtain ⟨Pa, hPa, hPan⟩ := transverseHsProjection (e F.a) (s k)
    have hle : ∀ i ∈ stageSet b1wSt k, b1wNuW s Ω e k F.a (Ψv i F.a) ≤
        ‖U i F.a‖ + Ω k F.a * ‖U i F.a - Pa (U i F.a)‖ := fun i hi =>
      (b1wNuW_le_proj s Ω e k F.a (hΩ0 k F.a) Pa hPa (U i F.a) (hprop i hi F.a haT).2).trans
        (add_le_add_left (hPan _) _)
    have h1 := sqrt_sum_le_add_mul (stageSet b1wSt k)
      (fun i => b1wNuW s Ω e k F.a (Ψv i F.a)) (fun i => ‖U i F.a‖)
      (fun i => ‖U i F.a - Pa (U i F.a)‖) (Ω k F.a) (hΩ0 k F.a)
      (fun i _ => b1wNuW_nonneg s Ω e k F.a (hΩ0 k F.a) _) (fun i _ => norm_nonneg _) hle
    have h2 := hsize F.a haT
    have h3 := hdefect F.a haT 1 (Or.inl rfl) Pa hPa hPan
    have he : F.a + t - F.a = t := by ring
    rw [he] at h2 h3
    rw [hΩa k] at h1
    exact wH4_end_le h1 h2 h3
  refine ⟨Ψv, Ψs, fun i hi => ⟨hcurve i, hfin i hi⟩, fun i hi => (hprop i hi F.a haT).1, hend,
    fun r hr => ?_⟩
  have hrI : r ∈ Icc F.a F.b := ⟨hr.1, hr.2.trans hT.2⟩
  have hXΓ : 0 ≤ ‖N₀‖ * Γ r := by rw [hNΓ r hrI]; exact norm_nonneg _
  have hζ0 : 0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
    le_min zero_le_one (add_nonneg (fibreNorm_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _)))
  by_cases hg : r ∈ Good
  swap
  · -- no forcing off the good times
    simp only [Set.indicator_of_notMem hg]
    have hν : ∀ k', b1wNuW s Ω e k' r 0 = 0 := fun k' => le_antisymm
      ((b1wNuW_le_mul s Ω e k' r (hΩ0 k' r) 0 (map_zero _)).trans_eq
        (by rw [norm_zero, mul_zero]))
      (b1wNuW_nonneg s Ω e k' r (hΩ0 k' r) 0)
    refine ⟨0, 0, fun k' _ i' _ => ⟨⟨0, map_zero _⟩, cellComplexPair_zero_right _⟩,
      fun k' _ => ?_, fun k' _ => ?_, ?_⟩
    · have h0 : stageNorm b1wSt k' (0 : B1WIndex ι h Nw m Ks → ℂ) = 0 := by
        unfold stageNorm
        simp
      rw [h0]
      exact div_nonneg (by have := hX r; have := hΘw0.trans hΘ; positivity) hXΓ
    · simp only [Pi.zero_apply, hν, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow,
        Finset.sum_const_zero, Real.sqrt_zero]
      have := hX r
      have := hΘw0.trans hΘ
      positivity
    · have hz : ∀ i, cellComplexSource C.θ 0 0 (Ψs i r) = 0 := fun i =>
        cellComplexSource_zero C.θ (Ψs i r)
      simp only [hz, Finset.sum_const_zero, Pi.zero_apply, zero_mul,
        cellComplexPair_zero_right, add_zero, sub_zero, norm_zero, zero_div, le_refl]
  -- a good time
  obtain ⟨hS', hF', hW'⟩ := b1w_good_stage_ae F θ Dθ src Fl r (fun i => hval i r hrI)
    (fun i => hmem i r hrI) (hGsrc r hg)
  obtain ⟨PN, hPN, hPNn⟩ := transverseHsProjection (e r) (s k)
  choose Pw hPw hPwn using fun k' => transverseHsProjection (e r) (s k')
  obtain ⟨κ, φ, h1, h2, h3, h4⟩ := b1w_weighted_H4_at F θ r k hπ hϖ s n (s k) (hn k)
    (fun i' => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i') (cellRawTrace (Dθ i') r))
    (fun i => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i) (cellSourceSlice (src i) r))
    (fun i j => cellScalarCLM (b1wScale F.π F.ϖ F.ηg F.letters i)
      (cellSourceSlice (fun r z => Fl i r z j) r))
    (fun i _ => hS' i) (fun i _ j => hF' i j) (fun i _ => hGexp r hg i)
    (fun i hi i' hi' => hearly i i' (by rw [(Finset.mem_filter.1 hi).2]; exact hi') r)
    hW' B M₀ (fun ψ k' hk' => hprov r hg k k' hk' ψ) hB tr Ω e (fun k' => hΩ0 k' r)
    (htr r hg) (q r) (E r) (hE r hrI) (hE0 r) cE Cw hcE hCw (Uq r)
    (fun k' hk' => hUq r hg k' (hk'.trans hk)) (fun k' hk' => hUqn r hg k' (hk'.trans hk))
    PN hPN Pw hPw hPwn (fun k' hk' => hwin r hg k' (hk'.trans hk))
    (fun k' hk' hΩ => hΩq r hg k' (hk'.trans hk) hΩ (Pw k') (hPw k'))
    (fun i => Ψs i r) (fun i => U i r) (fun i => hvalU i r hr) _ (hX2 r)
    ((hsize r hr).trans (by linarith [hX r]))
    (fun k' hk' _ => hdefect r hr (Ω k' r) (Or.inr ⟨k', hk', rfl⟩) PN hPN hPNn)
  refine ⟨κ, φ, h1, fun k' hk' => (h2 k' hk').trans ?_, fun k' hk' => (h3 k' hk').trans ?_, ?_⟩
  · rw [hNΓ r hrI]
    exact div_le_div_of_nonneg_right (wH4_coeff_le hΘ hΘw0 hζ0 hCd (Real.exp_pos _).le)
      (norm_nonneg _)
  · exact wH4_nu_le hΘ hΘw0 hCd (Real.exp_pos _).le
  · simp only [Set.indicator_of_mem hg]
    rw [hCθ, fibreShift_eq hη θ, h4, sub_self, norm_zero, zero_div]

end Frame

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # B1.W, the well-buffered instantiation on one frame

Objects (`b1w_well_frame`):
* the stage curves, with the forcing set to zero off the good times;
* the slow test `q`, with its stage representatives `Ē·1 + D`;
* the weighted class: `Adm = b1wAdm s tr` and `ν = b1wNuW s Ω e`, with `Ω = b1wOmega F Λ` and
  `e = b1wOrient F`.

Constants:
* `ζ = min 1 (|ξ| + S^{-1/2})`;
* `ε_s = ε_f = 0`;
* `C_f = 3C_d`, with `C_d` the constant of the weighted adjoint families;
* `D = (c_q + C_f) b1wDd`, `D_p = C_f b1wDd`.

H3s and H4 come from `b1w_weighted_H3s` and `b1w_weighted_H4`. The output clauses come from
`b1w_out_common`, and the fast start data from `b1w_fast_data`. -/

universe u v

theorem zeta_dp_le {ζ cq Cf X : ℝ} (hζ1 : ζ ≤ 1) (hcq : 0 ≤ cq) (hCf : 0 ≤ Cf) (hX : 0 ≤ X) :
    ζ * (Cf * X) ≤ (cq + Cf) * X := by
  have h1 : ζ * (Cf * X) ≤ 1 * (Cf * X) := mul_le_mul_of_nonneg_right hζ1 (mul_nonneg hCf hX)
  have h2 : 0 ≤ cq * X := mul_nonneg hcq hX
  linarith

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

/-- **The well-buffered instantiation of B1.W on one frame.** -/
theorem b1w_well_frame (hL : LevelZeroDataStatement.{v}) (hZ : ZeroAmplitudeWordStatement.{u, v})
    (hTO : TerminalOutputStatement.{u, v}) {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hθ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ)
    (hmom : AmplitudeIdMoments F) (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2)
    (s : ℕ → ℕ) (n : ℕ) (hn : ∀ k, n + 3 ≤ s k)
    (Dθ : B1WIndex ι h Nw m Ks → ℝ → RawJet2 1 ℂ)
    (src : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → ℂ)
    (Fl : B1WIndex ι h Nw m Ks → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)) (Good : Set ℝ)
    (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ)
    (hW : ∀ i, CellWeakHilbertCurve F.a F.b (b1wW F Dθ i) (b1wWs F Dθ i) (fun t =>
      cellDualDerivative (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb t (b1wWs F Dθ i t)
        (b1wSr F src Good i t) (b1wFl F Fl Good i t)))
    (hq : CellWeakHilbertCurve F.a F.b q qs (fun t =>
      -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
        (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) t (qs t) 0 0))
    (hqb : q F.b = cellConstantCLM 1)
    (hval : ∀ i, ∀ t ∈ Icc F.a F.b, cellValue (Dθ i) t =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight i.2.2.1.1 y *
        inner ℝ (stdOrthonormalBasis ℝ (h i.2.1) i.2.2.2) (planeValue (F.u i.1 i.2.1 t) y)))
    (hmem : ∀ i, ∀ t ∈ Icc F.a F.b,
      MemLp (cellValue (Dθ i) t) 2 (volume.restrict AVenhance.unitCube))
    (hGsrc : ∀ r ∈ Good, ∀ i, MemLp (src i r) 2 (volume.restrict AVenhance.unitCube) ∧
      src i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r ∧
      (∀ j : Fin 2, MemLp (fun z => Fl i r z j) 2 (volume.restrict AVenhance.unitCube)) ∧
      Fl i r =ᵐ[volume.restrict AVenhance.unitCube]
        amplitudeIdLiteralFlux F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r)
    (hGexp : ∀ r ∈ Good, ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ n φ →
      AVenhance.IsZ2Periodic φ →
      b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
        ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
          b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y)
    (hearly : ∀ (i i' : B1WIndex ι h Nw m Ks), ¬ b1wSt i' < b1wSt i →
      ∀ (r : ℝ) (φ : Vec 2 → ℂ), b1wTestTransform F θ i i' r φ = 0)
    (B M₀ : ℝ) (hB : 0 ≤ B)
    (hprov : ∀ r ∈ Good, ∀ (k k' : ℕ), k' < k →
      ∀ ψ : B1WIndex ι h Nw m Ks → TorusHk (s k) ℂ,
        ∃ Φ : B1WIndex ι h Nw m Ks → TorusHk (s k') ℂ,
          B1WSharpFamily F θ r k k' (s k) (s k') ψ Φ B M₀)
    (hGq : ∀ r ∈ Good, torusHkValueCLM (qs r) = q r)
    (hE : ∀ r ∈ Icc F.a F.b,
      cellComplexPair (b1wRow F θ r + cellConstantCLM 1) (q r) = b1wSlowE F θ r)
    (htr : ∀ r ∈ Good, ‖b1wRow F θ r‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ))
    (Cw : ℝ) (hCw : 0 ≤ Cw) (Λ : ℝ) (Dd : ℝ → ∀ k, TorusHk (s k) ℂ)
    (hUq : ∀ r ∈ Good, ∀ k' < b1wM Nw m Ks,
      torusHkValueCLM (torusHigherConstant (s k') (star (b1wSlowE F θ r)) + Dd r k') = q r)
    (hUqn : ∀ r ∈ Good, ∀ k' < b1wM Nw m Ks,
      ‖torusHigherConstant (s k') (star (b1wSlowE F θ r)) + Dd r k'‖ ≤ Cw * ‖b1wSlowE F θ r‖)
    (hDd : ∀ r ∈ Good, ∀ k' < b1wM Nw m Ks,
      ‖Dd r k'‖ ≤ M₀ * fibreNorm (planeFibreFrequency F.η θ) * ‖star (b1wSlowE F θ r)‖)
    (hwin : ∀ r ∈ Good, ∀ k' < b1wM Nw m Ks, 1 < b1wOmega F Λ k' r →
      ∃ p, IsLeastWindow F.reg p r ∧ F.reg.orient p = b1wOrient F r)
    (hΩw : ∀ r ∈ Good, ∀ k < b1wM Nw m Ks, ∀ k' < k, 1 < b1wOmega F Λ k' r →
      ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
        (∀ U, torusHkValueCLM (P U) =
          cellTransverseProjection (b1wOrient F r) (torusHkValueCLM U)) →
        b1wOmega F Λ k' r * ‖torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k -
            P (torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k)‖ ≤
          min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) *
            ‖b1wSlowE F θ r‖)
    (hΩq : ∀ r ∈ Good, ∀ k' < b1wM Nw m Ks, 1 < b1wOmega F Λ k' r →
      ∀ P : TorusHk (s k') ℂ →L[ℝ] TorusHk (s k') ℂ,
        (∀ U, torusHkValueCLM (P U) =
          cellTransverseProjection (b1wOrient F r) (torusHkValueCLM U)) →
        b1wOmega F Λ k' r * ‖torusHigherConstant (s k') (star (b1wSlowE F θ r)) + Dd r k' -
            P (torusHigherConstant (s k') (star (b1wSlowE F θ r)) + Dd r k')‖ ≤
          ‖b1wSlowE F θ r‖)
    (Cad : ℝ) (hCad : 0 ≤ Cad)
    (hadj : ∀ k < b1wM Nw m Ks, ∀ T ∈ Icc F.a F.b, ∀ ψ : ComplexCellL2,
      b1wAdm s (b1wRow F θ) k T ψ →
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ),
        CellWeakHilbertCurve F.a T Ψv Ψs (fun r =>
          -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
            (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv T = ψ ∧
        (∀ r ∈ Icc F.a T, b1wAdm s (b1wRow F θ) k r (Ψv r)) ∧
        ∀ UT UN : TorusHk (s k) ℂ, torusHkValueCLM (UT + UN) = ψ →
          cellTransverseProjection (b1wOrient F T) (torusHkValueCLM UT) = torusHkValueCLM UT →
        ∀ r ∈ Icc F.a T, ∀ ω ∈ {ω : ℝ | ω = 1 ∨ ∃ k' < k, b1wOmega F Λ k' r = ω},
          ∃ VT VN : TorusHk (s k) ℂ, torusHkValueCLM (VT + VN) = Ψv r ∧
            cellTransverseProjection (b1wOrient F r) (torusHkValueCLM VT) =
              torusHkValueCLM VT ∧
            ‖VT‖ + ω * ‖VN‖ ≤ Cad * Real.exp (-(Real.pi ^ 2 / 8) * (T - r)) *
              (‖UT‖ + b1wOmega F Λ k T * ‖UN‖))
    (cq : ℝ) (hcq : 0 ≤ cq)
    (hD0 : ∀ k, slowStage b1wSt k (b1wW F Dθ) q (b1wN₀ F θ) F.a 0 ≤
      cq * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k)
    (Q : ℕ) (Cz Cd Cout Θ cE Dq : ℝ) (hΘ : b1wWeightedΘ B 1 Cw ≤ Θ) (hCd : cq + 3 * Cad ≤ Cd)
    (hCout : (m.factorial : ℝ) ≤ Cout)
    (hCz : min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ^ 2 *
      (F.b - F.a) ≤ Cz * (1 + Real.sqrt (vecDot θ θ) / F.ϖ) ^ 2) :
    WordFibreFactsAt K m Ks (b1wM Nw m Ks) (b1wOut Nw Ks) Q Cz Cd Cout Θ (3 * Cad) cE F.letters
      F.η F.S F.ηg F.t₀ F.Sw F.ϖ F.a F.b Dq F.G F.v F.reg F.pkg
      (fun n => datumJets F.π F.ϖ n F.φ θ)
      (fun β => momentAmpNorm F.π F.ϖ β (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ) θ := by
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  have hξ0 : fibreNorm (planeFibreFrequency F.η θ) < K.ξ0 := lt_of_le_of_lt hθ hρ
  have hbd0 : ∀ k, 0 ≤ b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k :=
    b1wDd_nonneg _ _ _ hϖ.le _ _ zero_le_one
  have hbdm : Monotone (b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1) :=
    b1wDd_mono _ _ _ hϖ.le _ _ zero_le_one
  have hΓ := b1wGamma_pos F.pkg.actual.lam F.η F.a θ
  have hT0 : 0 ≤ F.b - F.a := sub_nonneg.2 F.ordered
  have hCf : 0 ≤ 3 * Cad := by positivity
  have hζ0 : 0 ≤ min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
    le_min zero_le_one (add_nonneg (fibreNorm_nonneg _) (inv_nonneg.2 (Real.sqrt_nonneg _)))
  have hζ1 : min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) ≤ 1 :=
    min_le_left _ _
  have hNΓ : ∀ r ∈ Icc F.a F.b, ‖b1wN₀ F θ‖ * b1wGamma F.pkg.actual.lam F.η F.a θ r =
      ‖b1wSlowE F θ r‖ := fun r hr => b1w_gauge_eq F θ hξ0 hr
  have hE0 : ∀ r, b1wSlowE F θ r ≠ 0 := fun r => Complex.exp_ne_zero _
  have hΩ0 : ∀ k r, 0 ≤ b1wOmega F Λ k r := fun k r => zero_le_one.trans (one_le_b1wOmega F Λ k r)
  have H3s := b1w_weighted_H3s F θ F.piece.hπ hϖ F.piece.hη s n hn Dθ src Fl hval hmem Good hGsrc
    hGexp hearly B M₀ hB hprov (b1wRow F θ) q qs hGq (b1wSlowE F θ) hE hE0 htr 1 Cw zero_le_one
    hCw (b1wM Nw m Ks) (b1wOmega F Λ) (b1wOrient F) hΩ0
    (fun r k => torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k)
    (fun r => star (b1wSlowE F θ r)) Dd hUq hUqn (fun _ _ _ _ => rfl) hDd
    (fun r _ => by rw [norm_star, one_mul]) hwin hΩw hΩq (b1wN₀ F θ)
    (b1wGamma F.pkg.actual.lam F.η F.a θ) hNΓ Θ hΘ
  have H4 := b1w_weighted_H4 F θ F.piece.hπ hϖ F.piece.hη s n hn Dθ src Fl hval hmem Good hGsrc
    hGexp hearly B M₀ hB hprov (b1wRow F θ) q (b1wSlowE F θ) hE hE0 htr 1 Cw zero_le_one hCw
    (b1wM Nw m Ks) (b1wOmega F Λ) (b1wOrient F) (one_le_b1wOmega F Λ) (b1wOmega_a F Λ)
    (fun r k => torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k) hUq hUqn hwin hΩq
    (b1wN₀ F θ) (b1wGamma F.pkg.actual.lam F.η F.a θ) hNΓ (b1wCoeff F θ) rfl F.piece.hGm V
    F.piece.hv hb Cad hCad hadj Θ hΘ
  have hνL : ∀ k' r ψ, b1wAdm s (b1wRow F θ) k' r ψ →
      ‖ψ‖ ≤ b1wNuW s (b1wOmega F Λ) (b1wOrient F) k' r ψ := fun k' r ψ hψ =>
    b1wNuW_ge s (b1wOmega F Λ) (b1wOrient F) k' r (one_le_b1wOmega F Λ k' r) ψ hψ.1
  have hfast0 : ∀ k t, 0 ≤ fastStage b1wSt k (b1wW F Dθ) (b1wAdm s (b1wRow F θ))
      (b1wNuW s (b1wOmega F Λ) (b1wOrient F)) (b1wGamma F.pkg.actual.lam F.η F.a θ) F.a t :=
    fun k t => mul_nonneg (hΓ _).le (fastRaw_nonneg _ _ _ _ _)
  refine ⟨B1WIndex ι h Nw m Ks, inferInstance, b1wSt, b1wCoeff F θ, F.piece.hGm, V, F.piece.hv,
    hb, b1wW F Dθ, b1wWs F Dθ, b1wSr F src Good, b1wFl F Fl Good, q, qs, b1wN₀ F θ,
    b1wGamma F.pkg.actual.lam F.η F.a θ, b1wAdm s (b1wRow F θ),
    b1wNuW s (b1wOmega F Λ) (b1wOrient F),
    min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹), fun _ => 0, fun _ => 0,
    fun k => (cq + 3 * Cad) * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k,
    fun k => 3 * Cad * b1wDd Nw (b1wLevelMoments m Ks 0) F.π F.ϖ F.φ θ 1 k,
    hW, hq, Complex.exp_ne_zero _, hΓ, b1w_gauge_growth F θ hρ hρlo hθ,
    fun k' r c ψ h => b1wAdm_smul s _ k' r c ψ h,
    fun k' r c ψ => b1wNuW_smul s (b1wOmega F Λ) (b1wOrient F) k' r (hΩ0 k' r) c ψ, hνL,
    hζ0, hζ1, hCz, monotone_const, monotone_const, fun _ => le_rfl, fun _ => le_rfl,
    fun k k' hk => mul_le_mul_of_nonneg_left (hbdm hk) (by positivity),
    fun k k' hk => mul_le_mul_of_nonneg_left (hbdm hk) hCf,
    fun k => mul_nonneg (by positivity) (hbd0 k), fun k => mul_nonneg hCf (hbd0 k),
    fun k => zeta_dp_le hζ1 hcq hCf (hbd0 k),
    fun k _ => (hD0 k).trans (mul_le_mul_of_nonneg_right (by linarith) (hbd0 k)),
    fun k _ => mul_le_mul_of_nonneg_left (b1w_fast_data hL F θ Dθ hval hmem _ _ k
      (fun ψ hψ => hνL k F.a ψ hψ)) hCf,
    H3s, H4, fun β hβ => ?_⟩
  have herr : (0 : ℝ) ≤ (0 + 0) * (F.b - F.a) := by rw [add_zero, zero_mul]
  obtain ⟨h1, h3⟩ := b1w_out_common hL hZ hTO F θ hmom Dθ hval hmem q hqb (cq + 3 * Cad)
    (by positivity) Cd Cout hCd hCout _ _ (hfast0 (b1wOut Nw Ks β) (F.b - F.a)) herr β hβ
  obtain ⟨h2, -⟩ := b1w_out_common hL hZ hTO F θ hmom Dθ hval hmem q hqb (3 * Cad) hCf Cd Cout
    (by linarith) hCout _ _ (hfast0 (b1wOut Nw Ks β) (F.b - F.a)) herr β hβ
  refine ⟨h1, h2, ?_, h3⟩
  rw [add_zero, zero_mul, ENNReal.ofReal_zero]
  exact bot_le

end Frame

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Assembly

/-! # B1.W well-buffered: the slow test from the sharp slow test

The slow test of a frame is `q(r) = conj u(−r)`, with `u` the reversed curve from `u(−b) = 1`.
* Conserved pairing (`rowCurve_pair`): `⟨1 + r(r), q(r)⟩ = E(r)`, with `E(r) = b1wSlowE F θ r`.
* At each stage `k < M`, `q(r) = Ē(r)·1 + D(r, k)`, with `‖D‖ ≤ C_v |ξ| |E|` (the sharp slow test,
  clause 1).
* In a least window of orientation `e`, the transverse defect satisfies
  `‖(1 − P_e)(Ē·1 + D)‖ ≤ C_v P_e^Q e^{-cD} |ξ| |E|` (the sharp slow test, clause 2).

Hypotheses: the regime of the sharp slow test, and a quiet end `b`. Split: `well_slow_clauses` (the sharp slow test at every
stage, uniform constants), `well_slow_parts` (the stage parts from the two clauses). -/

section
universe u v

/-- The regime with smaller constants. -/
theorem regime_mono₀ {Cb Cb' cb cb' J P D : ℝ} {Q Q' : ℕ} (hCb : Cb' ≤ Cb) (hcb : cb ≤ cb')
    (hQ : Q' ≤ Q) (hJ : 0 ≤ J) (hP : 1 ≤ P) (hD : 0 ≤ D)
    (h : Cb * J * P ^ Q * Real.exp (-cb * D) ≤ 1) :
    Cb' * J * P ^ Q' * Real.exp (-cb' * D) ≤ 1 := by
  have := regime_mono_pow (Λ := 1) (k := 0) (M := 0) hCb hcb hQ le_rfl le_rfl hJ hP hD
    (by simpa only [pow_zero, mul_one] using h)
  simpa only [pow_zero, mul_one] using this

/-- The two clauses of the sharp slow test for the reversed curve `u`, with uniform constants. -/
def WellSlowClauses (Nw m : ℕ) (Ks : Fin Nw → ℕ) (s : ℕ → ℕ) {K : ScalarConstants} {η : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {reg : BlockRegions}
    (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (ξ : Fin 2 → ℂ) (a b Cv c : ℝ) (Q : ℕ)
    (u : ℝ → ComplexCellL2) : Prop :=
  ∀ k < b1wM Nw m Ks, ∀ r ∈ Icc a b,
    (∃ w : TorusHk (s k) ℂ, torusHkValueCLM w =
        cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) -
          cellConstantCLM (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) ∧
      ‖w‖ ≤ Cv * fibreNorm ξ * ‖Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ)‖) ∧
    ∀ p, IsLeastWindow reg p r →
      ∃ w : TorusHk (s k) ℂ, torusHkValueCLM w =
          cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) -
            cellTransverseProjection (reg.orient p)
              (cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r))) ∧
        ‖w‖ ≤ Cv * peFactor η ^ Q * Real.exp (-c * reg.buffer) * fibreNorm ξ *
          ‖Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ)‖

/-- The stage parts of `q(r) = conj u(−r)` and their transverse defects. -/
theorem well_slow_parts {Nw m : ℕ} {Ks : Fin Nw → ℕ} {s : ℕ → ℕ} {K : ScalarConstants} {η : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2} {t₀ S ϖ : ℝ} {reg : BlockRegions}
    (pkg : CoreScalarPackage K η G v t₀ S ϖ reg) (ξ : Fin 2 → ℂ) {a b Cv c : ℝ} {Q : ℕ}
    (u : ℝ → ComplexCellL2) (h26 : WellSlowClauses Nw m Ks s pkg ξ a b Cv c Q u) :
    ∃ Dd : ℝ → ∀ k, TorusHk (s k) ℂ, ∀ r ∈ Icc a b, ∀ k < b1wM Nw m Ks,
      torusHkValueCLM (torusHigherConstant (s k)
          (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k) =
        cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) ∧
      ‖Dd r k‖ ≤ Cv * fibreNorm ξ * ‖Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ)‖ ∧
      ∀ p, IsLeastWindow reg p r → ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
        (∀ U, torusHkValueCLM (P U) =
          cellTransverseProjection (reg.orient p) (torusHkValueCLM U)) →
        ‖torusHigherConstant (s k)
            (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k -
            P (torusHigherConstant (s k)
              (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k)‖ ≤
          Cv * peFactor η ^ Q * Real.exp (-c * reg.buffer) * fibreNorm ξ *
            ‖Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ)‖ := by
  classical
  have hDex : ∀ (r : ℝ) (k : ℕ), ∃ w : TorusHk (s k) ℂ, r ∈ Icc a b → k < b1wM Nw m Ks →
      torusHkValueCLM w = cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) -
        cellConstantCLM (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) ∧
      ‖w‖ ≤ Cv * fibreNorm ξ * ‖Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ)‖ :=
    fun r k => by
      by_cases hrk : r ∈ Icc a b ∧ k < b1wM Nw m Ks
      · obtain ⟨w, hw⟩ := (h26 k hrk.2 r hrk.1).1
        exact ⟨w, fun _ _ => hw⟩
      · exact ⟨0, fun hr hk => absurd ⟨hr, hk⟩ hrk⟩
  choose Dd hDd using hDex
  refine ⟨Dd, fun r hr k hk => ?_⟩
  obtain ⟨hDv, hDn⟩ := hDd r k hr hk
  have hval : torusHkValueCLM (torusHigherConstant (s k)
      (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k) =
      cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)) := by
    rw [map_add, AVRegularity.CycleWords.torusHigherConstant_value, hDv, add_sub_cancel]
  refine ⟨hval, hDn, fun p hp P hPv => ?_⟩
  obtain ⟨w, hwv, hwn⟩ := (h26 k hk r hr).2 p hp
  have hw : torusHigherConstant (s k)
      (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k -
      P (torusHigherConstant (s k)
        (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k) = w := by
    apply TorusHk.ext_value
    change torusHkValueCLM (torusHigherConstant (s k)
        (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k -
        P (torusHigherConstant (s k)
          (star (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))) + Dd r k)) =
      torusHkValueCLM w
    rw [map_sub, hPv, hval, hwv]
  rw [hw]
  exact hwn

/-- The sharp slow test at every stage, with uniform constants. -/
theorem well_slow_clauses (hSlow : SharpSlowTestStatement) (K : ScalarConstants) (Nw m : ℕ)
    (Ks : Fin Nw → ℕ) (s : ℕ → ℕ) {ρ : ℝ} (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) :
    ∃ (Cv Cb c : ℝ) (Q : ℕ), 1 ≤ Cv ∧ 0 < c ∧
    ∀ (η t₀ S ϖ : ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (g : ℝ)
      (reg : BlockRegions) (pkg : CoreScalarPackage K η G v t₀ S ϖ reg),
      0 < η → (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
      (∀ (i : ℕ) t z, ‖iteratedFDeriv ℝ i (fun z' => Real.sqrt η • v t z') z‖ ≤ K.Cvj i) →
      0 ≤ g → g ≤ K.g0 → IsMetricNearIdentity (fun t _ => G t) g →
    ∀ (ξ : Fin 2 → ℂ) (H : TransverseLocalHyp K η G v ξ), fibreNorm ξ ≤ ρ →
      Cb * (1 + (reg.joins : ℝ)) * peFactor η ^ Q * Real.exp (-c * reg.buffer) ≤ 1 →
    ∀ (V : ℝ) (hb' : ∀ s x, ∑ i, (-v (-s) x) i ^ 2 ≤ V ^ 2) {a b : ℝ}, t₀ ≤ a → a ≤ b →
      b ≤ t₀ + S → b ∈ reg.quiet →
    ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ), IsRevCurve H V hb' (-b) (-a) u slice →
      u (-b) = cellConstantCLM 1 → WellSlowClauses Nw m Ks s pkg ξ a b Cv c Q u := by
  choose Ck Cbk ck Qk hCk hck hslow using fun k => hSlow K (s k) ρ hρ hρlo
  set M := b1wM Nw m Ks with hM
  obtain ⟨Cv, hCv1, hCv⟩ := exists_one_le_ge_all M Ck
  obtain ⟨Cb, -, hCb⟩ := exists_one_le_ge_all M Cbk
  obtain ⟨c, hc0, hc⟩ := exists_pos_le_all M ck hck
  obtain ⟨Q, hQ⟩ := exists_nat_ge_all M Qk
  refine ⟨Cv, Cb, c, Q, hCv1, hc0, ?_⟩
  intro η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg hnear ξ H hξ hreg V hb' a b ha hab hb hq u slice
    hu hu0 k hk r hr
  have hP := one_le_peFactor η
  have hJ : (0 : ℝ) ≤ 1 + (reg.joins : ℝ) := by positivity
  have hD := pkg.buffer_nonneg
  obtain ⟨h1, h2⟩ := hslow k η t₀ S ϖ G v g reg pkg hη hvs hvj hg0 hg hnear ξ H hξ
    (regime_mono₀ (hCb k hk) (hc k hk) (hQ k hk) hJ hP hD hreg) V hb' ha hab hb hq u slice hu
    hu0 r hr
  have hξ0 := fibreNorm_nonneg ξ
  have hE0 := norm_nonneg (Complex.exp (∫ τ in r..b, fibreSeriesC pkg.actual.lam ξ τ))
  refine ⟨?_, fun p hp => ?_⟩
  · obtain ⟨w, hwv, hwn⟩ := h1
    exact ⟨w, hwv, hwn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (hCv k hk) hξ0) hE0)⟩
  · obtain ⟨w, hwv, hwn⟩ := h2 p hp
    refine ⟨w, hwv, hwn.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right ?_ hξ0) hE0)⟩
    have hPk : peFactor η ^ Qk k ≤ peFactor η ^ Q := pow_le_pow_right₀ hP (hQ k hk)
    have he : Real.exp (-ck k * reg.buffer) ≤ Real.exp (-c * reg.buffer) :=
      Real.exp_le_exp.2 (by nlinarith [hc k hk])
    exact mul_le_mul (mul_le_mul (hCv k hk) hPk (pow_nonneg (by linarith) _)
      (zero_le_one.trans hCv1)) he (Real.exp_pos _).le
      (mul_nonneg (zero_le_one.trans hCv1) (pow_nonneg (by linarith) _))
end

/-! # B1.W well-buffered: the slow test of a frame

The reversed curve `u` from `u(−b) = 1`, and the slow test `q(r) = conj u(−r)`:
* it is an adjoint curve (`CellWeakHilbertCurve.reflected_adjoint`), with `q(b) = 1`;
* its pairing with the forward slow mode is conserved (`rowCurve_pair`);
* its stage parts (`well_slow_parts`) follow from the clauses of the sharp slow test for `u` (`hcl`). -/

section
universe u v

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- **The slow test of a well-buffered frame.** -/
theorem b1w_well_slow_frame {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hθ : fibreNorm (planeFibreFrequency F.η θ) ≤ ρ)
    (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (m : ℕ) (Ks : Fin Nw → ℕ) (s : ℕ → ℕ)
    (Cv c : ℝ) (Q : ℕ)
    (hcl : ∀ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      IsRevCurve (b1w_transverseLocalHyp F θ hρ hρlo hθ) V (rev_bound hb) (-F.b) (-F.a) u
        slice →
      u (-F.b) = cellConstantCLM 1 →
      WellSlowClauses Nw m Ks s F.pkg (planeFibreFrequency F.η θ) F.a F.b Cv c Q u) :
    ∃ (q : ℝ → ComplexCellL2) (qs : ℝ → TorusHk 1 ℂ) (Dd : ℝ → ∀ k, TorusHk (s k) ℂ),
      CellWeakHilbertCurve F.a F.b q qs (fun t =>
        -cellDualDerivative (cellAdjointCoefficients (b1wCoeff F θ)) F.piece.hGm V
          (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) t (qs t) 0 0) ∧
      q F.b = cellConstantCLM 1 ∧
      (∀ r ∈ Icc F.a F.b,
        cellComplexPair (b1wRow F θ r + cellConstantCLM 1) (q r) = b1wSlowE F θ r) ∧
      ∀ r ∈ Icc F.a F.b, ∀ k < b1wM Nw m Ks,
        torusHkValueCLM (torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k) = q r ∧
        ‖Dd r k‖ ≤ Cv * fibreNorm (planeFibreFrequency F.η θ) * ‖b1wSlowE F θ r‖ ∧
        ∀ p, IsLeastWindow F.reg p r → ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
          (∀ U, torusHkValueCLM (P U) =
            cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
          ‖torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k -
              P (torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k)‖ ≤
            Cv * peFactor F.η ^ Q * Real.exp (-c * F.reg.buffer) *
              fibreNorm (planeFibreFrequency F.η θ) * ‖b1wSlowE F θ r‖ := by
  have H := b1w_transverseLocalHyp F θ hρ hρlo hθ
  obtain ⟨u, slice, hu, hu0⟩ := revCurve_exists H V (rev_bound hb) (a := -F.b) (b := -F.a)
    (by linarith [F.ordered]) (cellConstantCLM 1)
  obtain ⟨Dd, hDd⟩ := well_slow_parts F.pkg (planeFibreFrequency F.η θ) u (hcl u slice hu hu0)
  refine ⟨fun r => cellFiberCLM Complex.conjCLE.toContinuousLinearMap (u (-r)),
    fun r => cellH1Conj (slice (-r)), Dd,
    CellWeakHilbertCurve.reflected_adjoint (fun t _ => F.G t) H.hG H.hv V hb _ hu, ?_,
    fun r hr => rowCurve_pair H F.pkg.actual V (rev_bound hb) hu hu0 r hr,
    fun r hr k hk => hDd r hr k hk⟩
  simp only [hu0, cellFiberConj_constant, star_one]

end Frame
end

/-! # B1.W well-buffered: the facts of the weights

For the weights `Ω = b1wOmega F Λ` and the orientation `e = b1wOrient F` of a frame (with
`Λ^M e^{-(3π²/8)D/2} ≤ 1` and `Λ^M C_v P_e^Q e^{-cD} ≤ 1`):
* where `Ω_{k'}(r) > 1` there is a least window, of orientation `e(r)`
  (`exists_leastWindow_of_weight`, `least_orient_eq_activityOrient`);
* there the slow test's weighted transverse defect is at most `|ξ||E(r)|` at every stage
  (the sharp slow test, clause 2, with `Ω_{k'} ≤ Λ^M`).

These are the hypotheses `hwin`, `hΩw` and `hΩq` of the weighted H3s/H4, since
`|ξ| ≤ ζ ≤ 1`. -/

section
universe u v

theorem weight_defect_le {Ω L X A Y : ℝ} (hΩ0 : 0 ≤ Ω) (hΩL : Ω ≤ L) (hX0 : 0 ≤ X)
    (hX : X ≤ A * Y) (hA : L * A ≤ 1) (hY : 0 ≤ Y) : Ω * X ≤ Y := by
  have hA0 : 0 ≤ A * Y := hX0.trans hX
  calc Ω * X ≤ L * (A * Y) := mul_le_mul hΩL hX hX0 (hΩ0.trans hΩL)
    _ = (L * A) * Y := by ring
    _ ≤ 1 * Y := mul_le_mul_of_nonneg_right hA hY
    _ = Y := one_mul Y

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ}

/-- **The facts of the weights on a well-buffered frame.** -/
theorem b1w_well_weights {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (s : ℕ → ℕ) (M : ℕ) (Λ : ℝ) (hΛ1 : 1 ≤ Λ)
    (hact : Λ ^ M * Real.exp (-(3 * Real.pi ^ 2 / 8) * (F.reg.buffer / 2)) ≤ 1)
    (Cv c : ℝ) (Q : ℕ)
    (hslow : Λ ^ M * (Cv * peFactor F.η ^ Q * Real.exp (-c * F.reg.buffer)) ≤ 1)
    (q : ℝ → ComplexCellL2) (Dd : ℝ → ∀ k, TorusHk (s k) ℂ)
    (hparts : ∀ r ∈ Icc F.a F.b, ∀ k < M,
      torusHkValueCLM (torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k) = q r ∧
      ‖Dd r k‖ ≤ Cv * fibreNorm (planeFibreFrequency F.η θ) * ‖b1wSlowE F θ r‖ ∧
      ∀ p, IsLeastWindow F.reg p r → ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
        (∀ U, torusHkValueCLM (P U) =
          cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U)) →
        ‖torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k -
            P (torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k)‖ ≤
          Cv * peFactor F.η ^ Q * Real.exp (-c * F.reg.buffer) *
            fibreNorm (planeFibreFrequency F.η θ) * ‖b1wSlowE F θ r‖) :
    (∀ r ∈ Icc F.a F.b, ∀ k' < M, 1 < b1wOmega F Λ k' r →
      ∃ p, IsLeastWindow F.reg p r ∧ F.reg.orient p = b1wOrient F r) ∧
    ∀ r ∈ Icc F.a F.b, ∀ k < M, ∀ k' < M, 1 < b1wOmega F Λ k' r →
      ∀ P : TorusHk (s k) ℂ →L[ℝ] TorusHk (s k) ℂ,
        (∀ U, torusHkValueCLM (P U) =
          cellTransverseProjection (b1wOrient F r) (torusHkValueCLM U)) →
        b1wOmega F Λ k' r *
          ‖torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k -
            P (torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k)‖ ≤
          fibreNorm (planeFibreFrequency F.η θ) * ‖b1wSlowE F θ r‖ := by
  have hc : (0 : ℝ) < 3 * Real.pi ^ 2 / 8 := by positivity
  -- the least windows
  have hwin : ∀ r ∈ Icc F.a F.b, ∀ k' < M, 1 < b1wOmega F Λ k' r →
      ∃ p, IsLeastWindow F.reg p r ∧ F.reg.orient p = b1wOrient F r := by
    intro r hr k' hk' hΩ
    have hra : r ≠ F.a := fun h => by
      rw [h, b1wOmega_a] at hΩ
      exact lt_irrefl _ hΩ
    rw [b1wOmega_of_ne F Λ k' hra] at hΩ
    have hΛk : Λ ^ (k' + 1) * Real.exp (-(3 * Real.pi ^ 2 / 8) * (F.reg.buffer / 2)) ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hΛ1 hk') (Real.exp_pos _).le)
        hact
    obtain ⟨p, hp⟩ := exists_leastWindow_of_weight F.pkg hc hΛk (hr.2.trans F.right) hΩ
    exact ⟨p, hp, least_orient_eq_activityOrient F.pkg hc hΛk
      ⟨F.left.trans hr.1, hr.2.trans F.right⟩ hΩ p hp⟩
  refine ⟨hwin, fun r hr k hk k' hk' hΩ P hP => ?_⟩
  obtain ⟨p, hp, hpo⟩ := hwin r hr k' hk' hΩ
  have hP' : ∀ U, torusHkValueCLM (P U) =
      cellTransverseProjection (F.reg.orient p) (torusHkValueCLM U) := by
    rw [hpo]
    exact hP
  have hdef := (hparts r hr k hk).2.2 p hp P hP'
  have hra : r ≠ F.a := fun h => by
    rw [h, b1wOmega_a] at hΩ
    exact lt_irrefl _ hΩ
  have hΩL : b1wOmega F Λ k' r ≤ Λ ^ M := by
    rw [b1wOmega_of_ne F Λ k' hra]
    exact (activityWeight_le (one_le_pow₀ hΛ1) hc.le).trans (pow_le_pow_right₀ hΛ1 hk')
  exact weight_defect_le (zero_le_one.trans (one_le_b1wOmega F Λ k' r)) hΩL (norm_nonneg _)
    (hdef.trans_eq (by ring)) hslow
    (mul_nonneg (fibreNorm_nonneg _) (norm_nonneg _))

end Frame
end

end AVRegularity.CycleWords.Assembly
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped ENNReal
namespace AVRegularity.CycleWords.Assembly

/-! # B1.W, the well-buffered half on a frame

`b1w_well_half` gives `WordFibreFactsAt` on every frame above the threshold
`C₀ P_e^{Q₀}(1+S)^{Q₀}((1+J)e^{-c₀D} + e^{-c₀D_q}) < 1`.

The constants come before the frame, and the exponent `Q₀` comes before `C_H`:
* the weighted sharp decay, through the weighted adjoint families (`b1w_weighted_adj_frame`), with
  `Λ = P_e^{Q'}`;
* the sharp slow test at every stage (`well_slow_clauses`);
* the sharp stage-transform families (`b1w_sharp_family_provider`).

On a frame:
* the threshold gives the four regimes (`well_regimes`) and the quiet end `b`
  (`threshold_quiet`);
* the stage curves, the good times, the slow test and the facts of the weights are built;
* `b1w_well_frame` assembles them. -/

universe u v

/-- **The four regimes from the threshold.** -/
theorem well_regimes {P S J D Dq Cb29 cb29 Cb26 c26 Cv : ℝ} {Q29 Q'29 Q26 M : ℕ} (hP : 1 ≤ P)
    (hS : 0 ≤ S) (hJ : 0 ≤ J) (hD : 0 ≤ D) (hCv : 0 ≤ Cv)
    (hth : max (max Cb29 Cb26) (max Cv 1) * P ^ (Q'29 * M + Q29 + Q26) *
      (1 + S) ^ (Q'29 * M + Q29 + Q26) *
      ((1 + J) * Real.exp (-(min (min cb29 c26) (3 * Real.pi ^ 2 / 16)) * D) +
        Real.exp (-(min (min cb29 c26) (3 * Real.pi ^ 2 / 16)) * Dq)) < 1) :
    Cb29 * (P ^ Q'29) ^ M * (1 + J) * P ^ Q29 * Real.exp (-cb29 * D) ≤ 1 ∧
    Cb26 * (1 + J) * P ^ Q26 * Real.exp (-c26 * D) ≤ 1 ∧
    (P ^ Q'29) ^ M * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2)) ≤ 1 ∧
    (P ^ Q'29) ^ M * (Cv * P ^ Q26 * Real.exp (-c26 * D)) ≤ 1 := by
  have hP0 : 0 ≤ P := by linarith
  have hJ1 : 1 ≤ 1 + J := by linarith
  have h1 := threshold_le (C := Cb29) (Q := Q'29 * M + Q29) (c := cb29) hP hS hJ hD
    (le_max_of_le_left (le_max_left _ _)) (by omega)
    ((min_le_left _ _).trans (min_le_left _ _)) hth
  have h2 := threshold_le (C := Cb26) (Q := Q26) (c := c26) hP hS hJ hD
    (le_max_of_le_left (le_max_right _ _)) (by omega)
    ((min_le_left _ _).trans (min_le_right _ _)) hth
  have h3 := threshold_le (C := 1) (Q := Q'29 * M) (c := 3 * Real.pi ^ 2 / 16) hP hS hJ hD
    (le_max_of_le_right (le_max_right _ _)) (by omega) (min_le_right _ _) hth
  have h4 := threshold_le (C := Cv) (Q := Q'29 * M + Q26) (c := c26) hP hS hJ hD
    (le_max_of_le_right (le_max_left _ _)) (by omega)
    ((min_le_left _ _).trans (min_le_right _ _)) hth
  have hPM : (P ^ Q'29) ^ M = P ^ (Q'29 * M) := (pow_mul P Q'29 M).symm
  refine ⟨?_, ?_, ?_, ?_⟩
  · calc Cb29 * (P ^ Q'29) ^ M * (1 + J) * P ^ Q29 * Real.exp (-cb29 * D)
        = Cb29 * P ^ (Q'29 * M + Q29) * (1 + J) * Real.exp (-cb29 * D) := by
          rw [hPM, pow_add]; ring
      _ ≤ 1 := h1
  · calc Cb26 * (1 + J) * P ^ Q26 * Real.exp (-c26 * D)
        = Cb26 * P ^ Q26 * (1 + J) * Real.exp (-c26 * D) := by ring
      _ ≤ 1 := h2
  · have he : Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2)) =
        Real.exp (-(3 * Real.pi ^ 2 / 16) * D) := by congr 1; ring
    have hX : 0 ≤ P ^ (Q'29 * M) * Real.exp (-(3 * Real.pi ^ 2 / 16) * D) :=
      mul_nonneg (pow_nonneg hP0 _) (Real.exp_pos _).le
    calc (P ^ Q'29) ^ M * Real.exp (-(3 * Real.pi ^ 2 / 8) * (D / 2))
        = P ^ (Q'29 * M) * Real.exp (-(3 * Real.pi ^ 2 / 16) * D) := by rw [hPM, he]
      _ ≤ (P ^ (Q'29 * M) * Real.exp (-(3 * Real.pi ^ 2 / 16) * D)) * (1 + J) :=
          le_mul_of_one_le_right hX hJ1
      _ = 1 * P ^ (Q'29 * M) * (1 + J) * Real.exp (-(3 * Real.pi ^ 2 / 16) * D) := by ring
      _ ≤ 1 := h3
  · have hX : 0 ≤ Cv * P ^ (Q'29 * M + Q26) * Real.exp (-c26 * D) :=
      mul_nonneg (mul_nonneg hCv (pow_nonneg hP0 _)) (Real.exp_pos _).le
    calc (P ^ Q'29) ^ M * (Cv * P ^ Q26 * Real.exp (-c26 * D))
        = Cv * P ^ (Q'29 * M + Q26) * Real.exp (-c26 * D) := by rw [hPM, pow_add]; ring
      _ ≤ (Cv * P ^ (Q'29 * M + Q26) * Real.exp (-c26 * D)) * (1 + J) :=
          le_mul_of_one_le_right hX hJ1
      _ = Cv * P ^ (Q'29 * M + Q26) * (1 + J) * Real.exp (-c26 * D) := by ring
      _ ≤ 1 := h4

/-- The fibre frequency of the transverse hypotheses is at most `1`. -/
theorem fibre_le_one_of_sep {x a : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a)
    (h : (2 + a) * x ^ 2 ≤ Real.pi ^ 2 / 16) : x ≤ 1 := by
  have hpi : Real.pi ^ 2 ≤ 16 := by
    have := Real.pi_le_four
    have := Real.pi_pos
    nlinarith
  have h2 : 2 * x ^ 2 ≤ 1 := by nlinarith [mul_nonneg ha (sq_nonneg x)]
  nlinarith

/-- The stage representative of the slow test is at most `(W₁ + C_v)|E|`. -/
theorem uq_bound {c d e w W1 Cv x : ℝ} (hc : c ≤ e * w) (hw : w ≤ W1) (hd : d ≤ Cv * x * e)
    (hx : x ≤ 1) (he : 0 ≤ e) (hCv : 0 ≤ Cv) : c + d ≤ (W1 + Cv) * e := by
  have h1 : e * w ≤ e * W1 := mul_le_mul_of_nonneg_left hw he
  have h2 : Cv * x * e ≤ Cv * 1 * e :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hx hCv) he
  nlinarith

theorem sqrt_div_varpi (v η S : ℝ) (hη : 0 ≤ η) :
    Real.sqrt v / Real.sqrt (η / S) = Real.sqrt v / Real.sqrt η * Real.sqrt S := by
  rw [Real.sqrt_div hη, div_div_eq_mul_div, mul_div_right_comm]

/-- **The well-buffered half of B1.W on a frame.** -/
theorem b1w_well_half (hR : CellDriftRegularityStatement) (hL : LevelZeroDataStatement.{v})
    (hLB : LetterBlochStatement.{u, v}) (hExp : StageExpansionStatement.{u, v})
    (hEarly : StageTransformEarlierStatement.{u, v}) (hZ : ZeroAmplitudeWordStatement.{u, v})
    (hTO : TerminalOutputStatement.{u, v}) (hSS : SharpSameLevelStatement.{u, v})
    (hSLa : SharpLetterAEStatement.{u, v}) (hW : WeightedSharpDecayStatement)
    (hSlow : SharpSlowTestStatement)
    (K : ScalarConstants) (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) {ρ : ℝ}
    (hρ : ρ < K.ξ0) (hρlo : ρ ≤ 2 * K.ξlo) (hρ0 : 0 ≤ ρ) :
    ∃ (C₀ c₀ : ℝ) (Q₀ : ℕ) (Cad Θ cq : ℝ), 1 ≤ C₀ ∧ 0 < c₀ ∧ 0 ≤ Cad ∧ 0 ≤ Θ ∧ 0 ≤ cq ∧
    ∀ (g₁ : ℝ) {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
      (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
        (F.letters l).positive = pos l) →
      b1wLadderTop (Finset.univ.sup d + 4) d Ks m + Finset.univ.sup d ≤ F.J →
      fibreNorm (planeFibreFrequency F.η θ) ≤ ρ →
      AmplitudeIdMoments F →
      (∀ (j : Fin (Nw + 1)) (x : ι) (e : h x) (β : ℕ × ℕ),
        ∃ (Dθ : ℝ → RawJet2 1 ℂ) (src : ℝ → Vec 2 → ℂ)
          (Fl : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)),
          MemLp (Function.uncurry src) 2
            ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube)) ∧
          (∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Fl p.1 p.2 k) 2
            ((volume.restrict (Icc F.a F.b)).prod (volume.restrict AVenhance.unitCube))) ∧
          (∀ᵐ r ∂volume.restrict (Icc F.a F.b),
            src r =ᵐ[volume.restrict AVenhance.unitCube]
              amplitudeIdLiteralSource F θ j x e β r ∧
            Fl r =ᵐ[volume.restrict AVenhance.unitCube] amplitudeIdLiteralFlux F θ j x e β r) ∧
          IsCellSolution (Icc F.a F.b)
            (fibreCoefficients F.η F.G F.v (planeFibreFrequency F.η θ) (fun _ => 0)) src Fl Dθ ∧
          ∀ t ∈ Icc F.a F.b, cellValue Dθ t =ᵐ[volume.restrict AVenhance.unitCube]
            planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y))) →
      ∀ (CH Dq : ℝ), 0 ≤ CH → F.b - F.a ≤ CH * F.S → 0 ≤ Dq →
        Set.Ioc (F.b - Dq) F.b ⊆ F.reg.quiet →
      C₀ * peFactor F.η ^ Q₀ * (1 + F.S) ^ Q₀ * ((1 + (F.reg.joins : ℝ)) *
        Real.exp (-c₀ * F.reg.buffer) + Real.exp (-c₀ * Dq)) < 1 →
      ∀ (Q : ℕ) (Cz Cd Cout cE : ℝ), 2 * CH ≤ Cz → cq + 3 * Cad ≤ Cd →
        (m.factorial : ℝ) ≤ Cout →
      WordFibreFactsAt K m Ks (b1wM Nw m Ks) (b1wOut Nw Ks) Q Cz Cd Cout Θ (3 * Cad) cE
        F.letters F.η F.S F.ηg F.t₀ F.Sw F.ϖ F.a F.b Dq F.G F.v F.reg F.pkg
        (fun n => datumJets F.π F.ϖ n F.φ θ)
        (fun β => momentAmpNorm F.π F.ϖ β (fun x => planeValue (F.u (Fin.last Nw) x F.b)) θ)
        θ := by
  classical
  set s := b1wCrudeS d Ks with hs
  set M := b1wM Nw m Ks with hM
  obtain ⟨Cv, Cb26, c26, Q26, hCv1, hc26, hcl⟩ := well_slow_clauses hSlow K Nw m Ks s hρ hρlo
  obtain ⟨M₀, hM₀⟩ : ∃ M₀ : ℝ, M₀ = max |K.Cg| Cv := ⟨_, rfl⟩
  obtain ⟨B, hB0, hprovS⟩ := b1w_sharp_family_provider hSS hSLa K Nw D m d Ks pos ρ
    (Finset.univ.sup d + 4) (by omega) M₀
  obtain ⟨Cad, Cb29, cb29, Q29, Q'29, hCad1, hcb29, hadjF⟩ :=
    b1w_weighted_adj_frame hR hW K Nw m Ks s hρ hρlo hρ0
  obtain ⟨W1, hW1⟩ : ∃ W1 : ℝ, W1 = ∑ k ∈ Finset.range M, ‖torusHigherConstant (s k) 1‖ :=
    ⟨_, rfl⟩
  have hW10 : 0 ≤ W1 := hW1 ▸ Finset.sum_nonneg fun k _ => norm_nonneg _
  have hW1k : ∀ k < M, ‖torusHigherConstant (s k) 1‖ ≤ W1 := fun k hk => hW1 ▸
    Finset.single_le_sum (f := fun k => ‖torusHigherConstant (s k) 1‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_range.2 hk)
  have hCv0 : 0 ≤ Cv := zero_le_one.trans hCv1
  have hCw0 : 0 ≤ W1 + Cv := add_nonneg hW10 hCv0
  have hΘ0 : 0 ≤ b1wWeightedΘ B 1 (W1 + Cv) := by unfold b1wWeightedΘ; positivity
  refine ⟨max (max Cb29 Cb26) (max Cv 1), min (min cb29 c26) (3 * Real.pi ^ 2 / 16),
    Q'29 * M + Q29 + Q26, Cad, b1wWeightedΘ B 1 (W1 + Cv), W1 + Cv,
    le_max_of_le_right (le_max_right _ _), lt_min (lt_min hcb29 hc26) (by positivity), zero_le_one.trans hCad1, hΘ0, hCw0, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F θ hlet hJF hθ hmom hmeas CH Dq hCH hT hDq hqt hth Q Cz Cd Cout cE
    hCz hCd hCout
  have hP := one_le_peFactor F.η
  have hS0 : 0 ≤ F.S := zero_le_one.trans F.piece.hS
  have hJ0 : (0 : ℝ) ≤ (F.reg.joins : ℝ) := Nat.cast_nonneg _
  have hD := F.pkg.buffer_nonneg
  obtain ⟨hR29, hR26, hact, hslowR⟩ := well_regimes hP hS0 hJ0 hD hCv0 hth
  have hDq0 : 0 < Dq := threshold_quiet (le_max_of_le_right (le_max_right _ _)) hP hS0 hJ0 hDq hth
  have hquiet : F.b ∈ F.reg.quiet := hqt ⟨by linarith, le_rfl⟩
  have H := b1w_transverseLocalHyp F θ hρ hρlo hθ
  have hξ0 : fibreNorm (planeFibreFrequency F.η θ) < K.ξ0 := lt_of_le_of_lt hθ hρ
  have hx0 := fibreNorm_nonneg (planeFibreFrequency F.η θ)
  have hx1 : fibreNorm (planeFibreFrequency F.η θ) ≤ 1 :=
    fibre_le_one_of_sep hx0 (mul_nonneg H.hCw H.hCg) H.hsep
  obtain ⟨V, hb⟩ := F.piece.hv.2.1
  obtain ⟨Dθ, src, Fl, hcur, hval, hlit, hmem, hsl⟩ := b1w_stage_curves F m Ks θ hmeas V hb
    (b1wScale F.π F.ϖ F.ηg F.letters)
  -- the expansion of the tested sources
  have hdl : ∀ l, d l ≤ Finset.univ.sup d := fun l => Finset.le_sup (f := d) (Finset.mem_univ l)
  have hord : ∀ l, (F.letters l).order ≤ F.J := fun l => by
    rw [(hlet l).1]
    have := hdl l
    omega
  have hsup : (Finset.univ.sup fun l => (F.letters l).order) = Finset.univ.sup d := by
    congr 1
    funext l
    exact (hlet l).1
  have hexp : ∀ᵐ r ∂volume.restrict (Icc F.a F.b),
      ∀ (i : B1WIndex ι h Nw m Ks) (φ : Vec 2 → ℂ), ContDiff ℝ (Finset.univ.sup d + 1) φ →
        AVenhance.IsZ2Periodic φ →
        b1wTestedSource F θ i.1 i.2.1 (b1wVec i) (b1wMom i) r φ =
          ∑ i' : B1WIndex ι h Nw m Ks, ∫ y in AVenhance.unitCube,
            b1wStageVal F θ i' r y * b1wTestTransform F θ i i' r φ y := by
    filter_upwards [hExp K g₁ F θ m Ks (fun l => (hlet l).2.1) hord hLB hmom] with r hr i φ hφ hper
    refine hr i φ ?_ hper
    rw [hsup]
    exact_mod_cast hφ
  -- the slow test, the good times, the weights, the adjoint families
  obtain ⟨q, qs, Dd, hqc, hqb, hE, hparts⟩ := b1w_well_slow_frame F θ hρ hρlo hθ V hb m Ks s Cv
    c26 Q26 (fun u slice hu hu0 => hcl F.η F.t₀ F.Sw F.ϖ F.G F.v F.g F.reg F.pkg F.piece.hη
      F.piece.hvs F.piece.hvj F.piece.hg0 F.piece.hg F.piece.hGn _ H hθ hR26 V (rev_bound hb)
      F.left F.ordered F.right hquiet u slice hu hu0)
  obtain ⟨Good, hGfull, hGI, hG1, hG2, hG3, hG4⟩ := b1w_well_good F θ s (Finset.univ.sup d + 1)
    B M₀ src Fl q qs hlit hsl hexp (hprovS g₁ F θ hlet hJF hθ) hqc.agrees
  have hΛ1 : 1 ≤ peFactor F.η ^ Q'29 := one_le_pow₀ hP
  obtain ⟨hwin0, hdef⟩ := b1w_well_weights F θ s M (peFactor F.η ^ Q'29) hΛ1 hact Cv c26 Q26
    hslowR q Dd hparts
  have hadj := hadjF g₁ F θ hθ V hb (peFactor F.η ^ Q'29) hΛ1 le_rfl hR29
  -- the slow-test representatives
  have hUqn : ∀ r ∈ Icc F.a F.b, ∀ k < M,
      ‖torusHigherConstant (s k) (star (b1wSlowE F θ r)) + Dd r k‖ ≤
        (W1 + Cv) * ‖b1wSlowE F θ r‖ := fun r hr k hk => by
    refine (norm_add_le _ _).trans (uq_bound ?_ (hW1k k hk) (hparts r hr k hk).2.1 hx1
      (norm_nonneg _) hCv0)
    rw [torusHigherConstant_norm, norm_star]
  have hM0 : 0 < M := by rw [hM]; unfold b1wM; positivity
  have hqa : ‖q F.a‖ ≤ (W1 + Cv) * ‖b1wSlowE F θ F.a‖ := by
    have haI : F.a ∈ Icc F.a F.b := ⟨le_rfl, F.ordered⟩
    rw [← (hparts F.a haI 0 hM0).1]
    exact (torusHk_value_norm_le _).trans (hUqn F.a haI 0 hM0)
  have hCg : 0 ≤ K.Cg := F.pkg.consts_pos.2.2.2.1.le
  have hCgM : K.Cg ≤ M₀ := hM₀ ▸ (le_abs_self _).trans (le_max_left _ _)
  have hCvM : Cv ≤ M₀ := hM₀ ▸ le_max_right _ _
  have hζx : fibreNorm (planeFibreFrequency F.η θ) ≤
      min 1 (fibreNorm (planeFibreFrequency F.η θ) + (Real.sqrt F.S)⁻¹) :=
    le_min hx1 (le_add_of_nonneg_right (inv_nonneg.2 (Real.sqrt_nonneg _)))
  have hSpos : 0 < F.S := lt_of_lt_of_le zero_lt_one F.piece.hS
  have hy : Real.sqrt (vecDot θ θ) / F.ϖ =
      fibreNorm (planeFibreFrequency F.η θ) * Real.sqrt F.S := by
    rw [F.piece.hϖ, sqrt_div_varpi _ _ _ F.piece.hη.le,
      fibreNorm_planeFibreFrequency_eq_div F.piece.hη θ]
  exact b1w_well_frame hL hZ hTO F θ hρ hρlo hθ hmom V hb s (Finset.univ.sup d + 1)
    (fun k => by rw [hs]; unfold b1wCrudeS b1wLadderAt; omega) Dθ src Fl Good q qs
    (fun i => cellWeakHilbertCurve_indicator_forcing (b1wCoeff F θ) F.piece.hGm V F.piece.hv hb
      (hcur i) Good hGfull) hqc hqb hval hmem hG1 hG2
    (fun i i' hii r φ => hEarly K g₁ F θ m Ks (fun l => (hlet l).2.1) i i' hii r φ) B M₀ hB0 hG3
    hG4 hE (fun r _ => (scalarPackageGraphCorrection_norm_le F.pkg.actual hCg _ hξ0 r).trans
      (mul_le_mul_of_nonneg_right hCgM hx0)) (W1 + Cv) hCw0 (peFactor F.η ^ Q'29) Dd
    (fun r hr k hk => (hparts r (hGI r hr) k hk).1) (fun r hr k hk => hUqn r (hGI r hr) k hk)
    (fun r hr k hk => by
      rw [norm_star]
      exact (hparts r (hGI r hr) k hk).2.1.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hCvM hx0) (norm_nonneg _)))
    (fun r hr k hk hΩ => hwin0 r (hGI r hr) k hk hΩ)
    (fun r hr k hk k' hk' hΩ P hP => (hdef r (hGI r hr) k hk k' (hk'.trans hk) hΩ P hP).trans
      (mul_le_mul_of_nonneg_right hζx (norm_nonneg _)))
    (fun r hr k' hk' hΩ P hP => (hdef r (hGI r hr) k' hk' k' hk' hΩ P hP).trans
      ((mul_le_mul_of_nonneg_right hx1 (norm_nonneg _)).trans_eq (one_mul _)))
    Cad (zero_le_one.trans hCad1) hadj (W1 + Cv) hCw0
    (fun k => (b1w_crude_data hL F θ s (b1wRow F θ) Dθ hval hmem q (W1 + Cv) hqa k).1)
    Q Cz Cd Cout (b1wWeightedΘ B 1 (W1 + Cv)) cE Dq le_rfl hCd hCout
    ((zeta_window_le hx0 hSpos hCH hT hy).trans
      (mul_le_mul_of_nonneg_right hCz (sq_nonneg _)))

end AVRegularity.CycleWords.Assembly
end
