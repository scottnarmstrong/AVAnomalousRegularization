-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.B1PlainFrame
import AVRegularity.CycleWords.Seam.S3bRoughCore
public import AVRegularity.CycleWords.Seam.B1NegPair
import AVRegularity.CycleWords.InteriorBufferedGraphRowData
import AVRegularity.CycleWords.Seam.OldScalar.Bessel
import AVRegularity.CycleWords.Seam.OldAdjointIdentification
import AVRegularity.CycleWords.Seam.B1PlainNeg
import AVRegularity.CycleWords.MixedWords.Discard.MarksBand
import AVRegularity.CycleWords.MixedWords.RetainedAmplitudeFactor
import AVRegularity.CycleWords.Seam.LetterTransposeNorm

section
/-! # The stage data in negative order and in the low band

`quietMarginDatum : QuietMarginDatumStatement`. Per frequency of the zone, the stage norms are bounded
by the sums over the moments `β` of the fibre norms of the Bloch parts of the scaled components
(`stageQ_sum_le`); these are measurable majorants. The integral over the zone is the plane
integral of the transform (the bridge); the negative band is bounded by the negative jet norm
(`neg_total`, duality with a Fourier multiplier test), the low band by the moment norm of
`μ₂(D)φ` (`low_scalar`).
-/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard AVRegularity.CycleWords.Seam
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam

open AVRegularity.CycleWords.Seam.NegLowBand AVRegularity.CycleWords.Seam.YoungKernel

universe u v

theorem lintegral_triple_sum {α : Type*} [MeasurableSpace α] (μ : Measure α) {β ι : Type*}
    {ε : ι → Type*} [Fintype ι] [∀ x, Fintype (ε x)] (s : Finset β) (c : β → ι → ℝ≥0∞)
    (f : ∀ (_ : β) (x : ι), ε x → α → ℝ≥0∞) (hf : ∀ b x e, Measurable (f b x e)) :
    ∫⁻ a, ∑ b ∈ s, ∑ x, c b x * ∑ e, f b x e a ∂μ =
      ∑ b ∈ s, ∑ x, c b x * ∑ e, ∫⁻ a, f b x e a ∂μ := by
  rw [lintegral_finsetSum _ fun b _ => Finset.measurable_sum _ fun x _ =>
    (Finset.measurable_sum _ fun e _ => hf b x e).const_mul _]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [lintegral_finsetSum _ fun x _ => (Finset.measurable_sum _ fun e _ => hf b x e).const_mul _]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [lintegral_const_mul _ (Finset.measurable_sum _ fun e _ => hf b x e),
    lintegral_finsetSum _ fun e _ => hf b x e]

theorem low_vector {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] {d : ℕ} (b : OrthonormalBasis (Fin d) ℝ E) (μ₂ : Vec 2 → ℝ)
    (hs : ContDiff ℝ (⊤ : ℕ∞) μ₂) (hc : HasCompactSupport μ₂) {φ : Vec 2 → E}
    (hφ1 : Integrable φ volume) (β : ℕ × ℕ) :
    ∑ e, ∫⁻ z, ENNReal.ofReal ((momentWeight β z *
        fourierCutoff μ₂ (fun y => inner ℝ (b e) (φ y)) z) ^ 2) =
      eLpNorm (fun y => momentWeight β y • fourierCutoff μ₂ φ y) 2 volume ^ 2 := by
  have hV : Continuous (fourierCutoff μ₂ φ) := (fourierCutoff_contDiff μ₂ hs hc hφ1).continuous
  have hmw : Continuous fun y : Vec 2 => momentWeight β y := continuous_momentWeight β
  have hcomp : ∀ e z, fourierCutoff μ₂ (fun y => inner ℝ (b e) (φ y)) z =
      inner ℝ (b e) (fourierCutoff μ₂ φ z) := fun e z => fourierCutoff_inner μ₂ hs hc hφ1 _ z
  have hmeas : ∀ e, Measurable fun z => ENNReal.ofReal ((momentWeight β z *
      fourierCutoff μ₂ (fun y => inner ℝ (b e) (φ y)) z) ^ 2) := by
    intro e
    have : Continuous fun z => momentWeight β z * fourierCutoff μ₂ (fun y => inner ℝ (b e) (φ y)) z := by
      simp_rw [hcomp]
      exact hmw.mul (continuous_const.inner hV)
    exact ENNReal.measurable_ofReal.comp (this.pow 2).measurable
  rw [← lintegral_finsetSum _ fun e _ => hmeas e,
    eLpNorm_two_sq''' (fun y => momentWeight β y • fourierCutoff μ₂ φ y)
      (by exact (hmw.smul hV).aestronglyMeasurable)]
  refine lintegral_congr fun z => ?_
  simp_rw [hcomp]
  rw [← ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _, enorm_smul]
  have : ∑ e, (momentWeight β z * inner ℝ (b e) (fourierCutoff μ₂ φ z)) ^ 2 =
      (‖momentWeight β z‖ * ‖fourierCutoff μ₂ φ z‖) ^ 2 := by
    simp_rw [mul_pow]
    rw [← Finset.mul_sum, sum_inner_sq, Real.norm_eq_abs, sq_abs]
  rw [this, ENNReal.ofReal_pow (by positivity), ENNReal.ofReal_mul (norm_nonneg _),
    ofReal_norm, ofReal_norm]

/-- **The stage data of the quiet margin.** The stage data in negative order and in the low band. -/
theorem quietMarginDatum : QuietMarginDatumStatement.{u, v} := by
  intro K Nw D m k Ks μ₂ hs hc hev h1
  set n : ℕ := wordReserveN m Ks with hn
  have hneg := fun β : {β : ℕ × ℕ // β ∈ momentIndices n} =>
    neg_total.{u, v} n k β.1 (Finset.mem_filter.1 β.2).2
  choose Cb hCb0 hCb using hneg
  set Cn : ℝ := ∑ β : {β : ℕ × ℕ // β ∈ momentIndices n}, Cb β ^ 2 with hCn
  have hCn0 : 0 ≤ Cn := Finset.sum_nonneg fun β _ => sq_nonneg _
  have h2π : 0 < (2 * Real.pi) ^ 2 := by positivity
  have hmul := mul_nonneg h2π.le hCn0
  refine ⟨(2 * Real.pi) ^ 2 * Cn + (2 * Real.pi) ^ 2 + 1, by linarith, ?_⟩
  intro g₁ ι _ h _ _ _ _ _ _ F hslow A
  have hπ := F.piece.hπ
  have hϖ0 : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.2 (div_pos F.piece.hη (by linarith [F.piece.hS]))
  have hϖ1 : F.ϖ ≤ 1 := by
    rw [F.piece.hϖ]
    exact Real.sqrt_le_one.2 ((div_le_one (by linarith [F.piece.hS])).2
      (by linarith [F.piece.hη1, F.piece.hS]))
  have hφm : ∀ x, StronglyMeasurable (F.φ x) := fun x => (F.compact x).1
  have hφc : ∀ x, HasCompactSupport (F.φ x) := fun x => (F.compact x).2
  have hφ2 : ∀ x, MemLp (F.φ x) 2 volume := fun x =>
    MemLp.ae_eq (F.datum x) (planeValue_memLp (F.f x))
  have hφ1 : ∀ x, Integrable (F.φ x) volume := fun x => integrable_of_memLp_compact (hφ2 x) (hφc x)
  set b : ∀ x, OrthonormalBasis (Fin (Module.finrank ℝ (h x))) ℝ (h x) :=
    fun x => stdOrthonormalBasis ℝ (h x) with hb
  set Hs : (ℕ × ℕ) → ∀ x, Fin (Module.finrank ℝ (h x)) → Vec 2 → ℝ :=
    fun β x e y => momentWeight β y * inner ℝ (b x e) (F.φ x y) with hHs
  have hH : ∀ β x e, Integrable (Hs β x e) volume := fun β x e =>
    moment_integrable_compact (inner_integrable (hφc x) (hφ2 x) _)
      (inner_hasCompactSupport (hφc x) _) β
  set cβ : ℕ × ℕ → ℝ := fun β => F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)
    with hcβ
  set cw : ℕ × ℕ → ι → ℝ≥0∞ := fun β x =>
    ENNReal.ofReal ((F.π x)⁻¹) * ENNReal.ofReal (cβ β ^ 2) with hcw
  set Nt : Vec 2 → ℝ≥0∞ := fun θ => ∑ β ∈ momentIndices n, ∑ x, cw β x *
    ∑ e, cellNegSq k θ (planeBlochC θ (Hs β x e)) with hNt
  set Lt : Vec 2 → ℝ≥0∞ := fun θ => ∑ β ∈ momentIndices n, ∑ x, cw β x *
    ∑ e, cellLowSq (Real.pi / 8) θ (planeBlochC θ (Hs β x e)) with hLt
  have hNm : Measurable Nt := Finset.measurable_sum _ fun β _ => Finset.measurable_sum _ fun x _ =>
    (Finset.measurable_sum _ fun e _ => cellNegSq_measurable k (hH β x e)).const_mul _
  have hLm : Measurable Lt := Finset.measurable_sum _ fun β _ => Finset.measurable_sum _ fun x _ =>
    (Finset.measurable_sum _ fun e _ => cellLowSq_measurable (Real.pi / 8) (hH β x e)).const_mul _
  have hN : ∀ θ, stageDatumNegSq F m Ks k θ ≤ Nt θ := fun θ => by
    unfold stageDatumNegSq
    exact stageQ_sum_le (fun f => cellNegSq k θ f) (fun f g hfg => cellNegSq_congr_ae k θ hfg)
      (fun s f => cellNegSq_const_mul k θ s f) (cellNegSq_zero k θ) F θ
  have hL : ∀ θ, stageDatumLowSq F m Ks (Real.pi / 8) θ ≤ Lt θ := fun θ => by
    unfold stageDatumLowSq
    exact stageQ_sum_le (fun f => cellLowSq (Real.pi / 8) θ f)
      (fun f g hfg => cellLowSq_congr_ae _ θ hfg) (fun s f => cellLowSq_const_mul _ θ s f)
      (cellLowSq_zero _ θ) F θ
  set D := AVRegularity.CycleWords.Assembly.negJetNorm F.π ((n : ℕ) : ℝ) k F.ϖ 1 F.φ with hD
  set MN := momentNorm F.π n F.ϖ (fun x => fourierCutoff μ₂ (F.φ x)) with hMN
  -- the negative part
  have hNeg : ∫⁻ θ in freqCube, Nt θ ≤
      ENNReal.ofReal ((2 * Real.pi) ^ 2 * Cn) * D ^ 2 := by
    rw [hNt, lintegral_triple_sum _ (momentIndices n) cw
      (fun β x e θ => cellNegSq k θ (planeBlochC θ (Hs β x e)))
      (fun β x e => cellNegSq_measurable k (hH β x e))]
    have e1 : ∀ β ∈ momentIndices n, ∑ x, cw β x * ∑ e, ∫⁻ θ in freqCube,
        cellNegSq k θ (planeBlochC θ (Hs β x e)) =
        ∑ x, ENNReal.ofReal ((F.π x)⁻¹) * ∑ e,
          ∫⁻ ξ, negBandIntegrand k (gsc F.ϖ β (F.φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ := by
      intro β _
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hcw]
      simp only
      rw [mul_assoc]
      congr 1
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun e _ => ?_
      rw [cellNegSq_bridge k (hH β x e)]
      have : gsc F.ϖ β (F.φ x) (stdOrthonormalBasis ℝ (h x) e) = fun y => cβ β * Hs β x e y := rfl
      rw [this]
      simp_rw [negBand_const_mul]
      rw [lintegral_const_mul _ (negBand_measurable k (hH β x e))]
    rw [Finset.sum_congr rfl e1]
    have e2 := fun β : {β : ℕ × ℕ // β ∈ momentIndices n} =>
      hCb β (π := F.π) hπ F.ϖ hϖ0 hϖ1 F.φ hφm hφc hφ2
    calc ∑ β ∈ momentIndices n, ∑ x, ENNReal.ofReal ((F.π x)⁻¹) * ∑ e,
          ∫⁻ ξ, negBandIntegrand k (gsc F.ϖ β (F.φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ
        = ∑ β : {β : ℕ × ℕ // β ∈ momentIndices n}, ∑ x, ENNReal.ofReal ((F.π x)⁻¹) * ∑ e,
          ∫⁻ ξ, negBandIntegrand k (gsc F.ϖ β.1 (F.φ x) (stdOrthonormalBasis ℝ (h x) e)) ξ :=
          (Finset.sum_coe_sort (momentIndices n) (fun β => ∑ x, ENNReal.ofReal ((F.π x)⁻¹) *
            ∑ e, ∫⁻ ξ, negBandIntegrand k (gsc F.ϖ β (F.φ x)
              (stdOrthonormalBasis ℝ (h x) e)) ξ)).symm
      _ ≤ ∑ β : {β : ℕ × ℕ // β ∈ momentIndices n}, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
          (ENNReal.ofReal (Cb β) * D) ^ 2 := Finset.sum_le_sum fun β _ => e2 β
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 2 * Cn) * D ^ 2 := by
          rw [hCn, ENNReal.ofReal_mul h2π.le, ENNReal.ofReal_sum_of_nonneg fun β _ => sq_nonneg _,
            mul_assoc, Finset.sum_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun β _ => ?_
          rw [ENNReal.ofReal_pow (hCb0 β).le, mul_pow]
          ring
  -- the low part
  have hLow : ∫⁻ θ in freqCube, Lt θ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) * MN ^ 2 := by
    rw [hLt, lintegral_triple_sum _ (momentIndices n) cw
      (fun β x e θ => cellLowSq (Real.pi / 8) θ (planeBlochC θ (Hs β x e)))
      (fun β x e => cellLowSq_measurable (Real.pi / 8) (hH β x e))]
    have e1 : ∀ β ∈ momentIndices n, ∑ x, cw β x * ∑ e, ∫⁻ θ in freqCube,
        cellLowSq (Real.pi / 8) θ (planeBlochC θ (Hs β x e)) ≤
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * (ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
          (∑ v, ENNReal.ofReal ((F.π v)⁻¹) * eLpNorm (fun z => ((F.ϖ * z 0) ^ β.1 *
            (F.ϖ * z 1) ^ β.2) • fourierCutoff μ₂ (F.φ v) z) 2 volume ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
      intro β _
      rw [BandDatum.momentNorm_term_sq F.π F.ϖ (fun x => fourierCutoff μ₂ (F.φ x)) β, Finset.mul_sum]
      refine Finset.sum_le_sum fun x _ => ?_
      · rw [hcw]
        simp only
        have hb1 : ∑ e, ∫⁻ θ in freqCube, cellLowSq (Real.pi / 8) θ (planeBlochC θ (Hs β x e)) =
            ∑ e, ∫⁻ ξ, lowBandIntegrand (Real.pi / 8) (Hs β x e) ξ :=
          Finset.sum_congr rfl fun e _ => cellLowSq_bridge _ (hH β x e)
        rw [hb1]
        have hb2 : ∑ e, ∫⁻ ξ, lowBandIntegrand (Real.pi / 8) (Hs β x e) ξ ≤
            ENNReal.ofReal ((2 * Real.pi) ^ 2) * eLpNorm (fun y => momentWeight β y •
              fourierCutoff μ₂ (F.φ x) y) 2 volume ^ 2 := by
          rw [← low_vector (b x) μ₂ hs hc (hφ1 x) β, Finset.mul_sum]
          refine Finset.sum_le_sum fun e _ => ?_
          exact low_scalar μ₂ hs hc hev h1 (inner_integrable (hφc x) (hφ2 x) _)
            (inner_hasCompactSupport (hφc x) _) (inner_memLp (hφc x) (hφ2 x) ((b x).norm_eq_one e)) β
        calc ENNReal.ofReal ((F.π x)⁻¹) * ENNReal.ofReal (cβ β ^ 2) *
              ∑ e, ∫⁻ ξ, lowBandIntegrand (Real.pi / 8) (Hs β x e) ξ
            ≤ ENNReal.ofReal ((F.π x)⁻¹) * ENNReal.ofReal (cβ β ^ 2) *
              (ENNReal.ofReal ((2 * Real.pi) ^ 2) * eLpNorm (fun y => momentWeight β y •
                fourierCutoff μ₂ (F.φ x) y) 2 volume ^ 2) := mul_le_mul' le_rfl hb2
          _ = _ := by ring
    calc _ ≤ ∑ β ∈ momentIndices n, ENNReal.ofReal ((2 * Real.pi) ^ 2) *
          (ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
          (∑ v, ENNReal.ofReal ((F.π v)⁻¹) * eLpNorm (fun z => ((F.ϖ * z 0) ^ β.1 *
            (F.ϖ * z 1) ^ β.2) • fourierCutoff μ₂ (F.φ v) z) 2 volume ^ 2) ^ (1 / 2 : ℝ)) ^ 2 :=
          Finset.sum_le_sum e1
      _ = ENNReal.ofReal ((2 * Real.pi) ^ 2) * ∑ β ∈ momentIndices n,
          (ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
          (∑ v, ENNReal.ofReal ((F.π v)⁻¹) * eLpNorm (fun z => ((F.ϖ * z 0) ^ β.1 *
            (F.ϖ * z 1) ^ β.2) • fourierCutoff μ₂ (F.φ v) z) 2 volume ^ 2) ^ (1 / 2 : ℝ)) ^ 2 := by
          rw [Finset.mul_sum]
      _ ≤ ENNReal.ofReal ((2 * Real.pi) ^ 2) * MN ^ 2 :=
          mul_le_mul' le_rfl (Finset.sum_sq_le_sq_sum_of_nonneg fun _ _ => zero_le)
  calc ∫⁻ θ in freqCube, (A * stageDatumNegSq F m Ks k θ +
        stageDatumLowSq F m Ks (Real.pi / 8) θ)
      ≤ ∫⁻ θ in freqCube, (A * Nt θ + Lt θ) :=
        lintegral_mono fun θ => add_le_add (mul_le_mul' le_rfl (hN θ)) (hL θ)
    _ = A * (∫⁻ θ in freqCube, Nt θ) + ∫⁻ θ in freqCube, Lt θ := by
        rw [lintegral_add_left (μ := volume.restrict freqCube) (hNm.const_mul A),
          lintegral_const_mul (μ := volume.restrict freqCube) _ hNm]
    _ ≤ A * (ENNReal.ofReal ((2 * Real.pi) ^ 2 * Cn) * D ^ 2) +
        ENNReal.ofReal ((2 * Real.pi) ^ 2) * MN ^ 2 :=
        by gcongr
    _ ≤ A * (ENNReal.ofReal ((2 * Real.pi) ^ 2 * Cn + (2 * Real.pi) ^ 2 + 1) * D ^ 2) +
        ENNReal.ofReal ((2 * Real.pi) ^ 2 * Cn + (2 * Real.pi) ^ 2 + 1) * MN ^ 2 :=
        add_le_add (mul_le_mul' le_rfl (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl))
          (mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl)
    _ = _ := by ring

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords.Seam

/-! **The flux realizations of a word chain from a compactly supported datum.** The level-`j`
letter flux of the forward chain has an `L²`-in-time realization in `PlaneFluxL2` for every level,
when the datum vanishes outside a ball: the chain capped at the Sobolev reserve of the word has
finite polynomial energies (`wordChain_capped_successor_l2_duhamel`), and the capped flux is the
actual flux (`wordChainPreviousFlux_truncate`). -/

/-- The jets of the forward drift through order `k`. -/
theorem forwardDrift_jets {η : ℝ} (hη : 0 < η) (v : ℝ → Vec 2 → Vec 2)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (k : ℕ) (t : ℝ) (l : ℕ) (hlk : l ≤ k) (x : Vec 2) :
    ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
      Interior.negAdjointJetConstant Cvj k / Real.sqrt η * (l.factorial : ℝ) := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have h1 := driftCoefficient_array_norm_le_iterated (v t) l ((hvs t).of_le (by simp)) x
  have h2 : Real.sqrt η * ‖iteratedFDeriv ℝ l (v t) x‖ ≤ Cvj l := by
    have h := hvj l t x
    change ‖iteratedFDeriv ℝ l (Real.sqrt η • v t) x‖ ≤ _ at h
    rw [iteratedFDeriv_const_smul_apply ((hvs t).contDiffAt.of_le (by exact_mod_cast le_top)),
      norm_smul, Real.norm_of_nonneg hsη.le] at h
    exact h
  have h3 := Interior.negAdjointJetConstant_term Cvj hlk
  have hc : 0 ≤ (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ := by
    positivity
  have hit : ‖iteratedFDeriv ℝ l (v t) x‖ ≤ |Cvj l| / Real.sqrt η := by
    rw [le_div_iff₀ hsη, mul_comm]
    exact h2.trans (le_abs_self _)
  have hfac : (1 : ℝ) ≤ l.factorial := by exact_mod_cast Nat.factorial_pos l
  have hA : 0 ≤ Interior.negAdjointJetConstant Cvj k / Real.sqrt η :=
    div_nonneg (zero_le_one.trans (Interior.one_le_negAdjointJetConstant Cvj k)) hsη.le
  calc ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖
      ≤ (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ *
          ‖iteratedFDeriv ℝ l (v t) x‖ := h1
    _ ≤ (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ *
          (|Cvj l| / Real.sqrt η) := mul_le_mul_of_nonneg_left hit hc
    _ = (Fintype.card (DerivativeWord2 l) : ℝ) * ‖driftCoefficientEmbedding‖ * |Cvj l| /
          Real.sqrt η := by ring
    _ ≤ Interior.negAdjointJetConstant Cvj k / Real.sqrt η :=
        div_le_div_of_nonneg_right h3 hsη.le
    _ ≤ Interior.negAdjointJetConstant Cvj k / Real.sqrt η * l.factorial :=
        le_mul_of_one_le_right hA hfac

/-- The factorial radius of the energy estimates for jets of size `A/√η`. -/
theorem jet_radius_small {η : ℝ} (hη : 0 < η) (A : ℝ) (hA : 1 ≤ A) :
    0 < 1 / (3 * A * (1 + (Real.sqrt η)⁻¹)) ∧ 1 / (3 * A * (1 + (Real.sqrt η)⁻¹)) ≤ 1 / 2 ∧
      A / Real.sqrt η * (1 / (3 * A * (1 + (Real.sqrt η)⁻¹))) ^ 2 ≤ 1 / 8 := by
  have hsη : 0 < Real.sqrt η := Real.sqrt_pos.mpr hη
  have hP : 1 ≤ 1 + (Real.sqrt η)⁻¹ := by
    have := inv_pos.mpr hsη
    linarith
  refine ⟨by positivity, ?_, ?_⟩
  · apply one_div_le_one_div_of_le (by norm_num)
    nlinarith
  · have hsP : Real.sqrt η * (1 + (Real.sqrt η)⁻¹) = Real.sqrt η + 1 := by
      field_simp
    have hX : 1 ≤ A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹) := by
      rw [hsP]
      have h1 : 1 ≤ Real.sqrt η + 1 := by linarith
      calc (1 : ℝ) = 1 * 1 * 1 := by ring
        _ ≤ A * (Real.sqrt η + 1) * (1 + (Real.sqrt η)⁻¹) := by gcongr
    have he : A / Real.sqrt η * (1 / (3 * A * (1 + (Real.sqrt η)⁻¹))) ^ 2 =
        1 / (9 * (A * (Real.sqrt η * (1 + (Real.sqrt η)⁻¹)) * (1 + (Real.sqrt η)⁻¹))) := by
      have : 0 < A := lt_of_lt_of_le one_pos hA
      field_simp
      ring
    rw [he, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith

/-- A point outside the closed sup-ball of radius `|R|` has `R² < z₀² + z₁²`. -/
theorem sq_lt_of_not_mem_closedBall {R : ℝ} {z : Vec 2}
    (hz : z ∉ Metric.closedBall (0 : Vec 2) |R|) : R ^ 2 < z 0 ^ 2 + z 1 ^ 2 := by
  by_contra hcon
  push Not at hcon
  apply hz
  rw [Metric.mem_closedBall, dist_zero_right]
  refine (pi_norm_le_iff_of_nonneg (abs_nonneg R)).mpr fun i => ?_
  rw [Real.norm_eq_abs]
  have h0 := sq_nonneg (z 0)
  have h1 := sq_nonneg (z 1)
  have hi : z i ^ 2 ≤ R ^ 2 := by
    fin_cases i
    · simp only [Fin.zero_eta, Fin.isValue]; linarith
    · simp only [Fin.mk_one, Fin.isValue]; linarith
  exact sq_le_sq.mp hi

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

/-- **The flux realizations from a compactly supported datum.** -/
theorem wordChain_flux_of_compactDatum (hD : 2 ≤ D) (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ) (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (hreserve : ∑ j, (letters j).order ≤ J)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    {η : ℝ} (hη : 0 < η) (Cvj : ℕ → ℝ)
    (hvj : ∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S : ℝ) (Cw : ℕ → ℝ) (W : ∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X0 δ) κ a b v f (fun _ _ _ => 0) U Uw)
    (R : ℝ) (hsupp : ∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0)
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) :
    ∀ (i : Fin N) (x : ι), ∃ S' : ℝ → PlaneFluxL2 (h x),
      MemLp S' 2 (volume.restrict (Icc a b)) ∧
        ∀ᵐ r ∂volume.restrict (Icc a b), ∀ k, S' r k =ᵐ[volume] fun z =>
          wordChainPreviousFlux letters X0 δ κ (fun p => Uw p.1 p.2 r) (i.succ, x) r z k := by
  intro i x
  set d : Fin N → ℕ := fun j => (letters j).order with hddef
  set A := Interior.negAdjointJetConstant Cvj (0 + ∑ j, d j) with hAdef
  have hA : 1 ≤ A := Interior.one_le_negAdjointJetConstant Cvj _
  obtain ⟨hr0, hrh, hsmall⟩ := jet_radius_small hη A hA
  have hstrain : 0 ≤ A / Real.sqrt η :=
    div_nonneg (zero_le_one.trans hA) (Real.sqrt_nonneg _)
  have hjets : ∀ l, 1 ≤ l → l ≤ (0 + ∑ j, d j) → ∀ t z,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l z‖ ≤
        A / Real.sqrt η * (l.factorial : ℝ) := fun l _ hl t z =>
    forwardDrift_jets hη v hvs Cvj hvj _ t l hl z
  have hf : ∀ x n, weightedFactorialNormSq n ϖ 0 (1 / (3 * A * (1 + (Real.sqrt η)⁻¹)))
      (cappedWordSlots κ 0 d 0 x)
      (truncatePlaneHk (cappedWordSlots_le_original κ 0 d 0 x)
        (wordLevelDatum κ f 0 x)) ≠ ⊤ := by
    intro x n
    refine weightedFactorialNormSq_compact_value_ne_top n ϖ 0 _ _
      (isCompact_closedBall (0 : Vec 2) |R|) ?_
    filter_upwards [hsupp x] with z hz hzA
    have h0 := hz (sq_lt_of_not_mem_closedBall hzA)
    simp only [planeValue, planeJetOrder, Nat.zero_le, dite_true] at h0
    simp only [wordLevelDatum_zero]
    exact h0
  have hcap := wordChain_capped_successor_l2_duhamel hD π hπ letters J H a b hab hL κ 0 d
    (fun j => rfl) (by simpa using hreserve) hc X0 δ hm v hv hvs (A / Real.sqrt η)
    (1 / (3 * A * (1 + (Real.sqrt η)⁻¹))) ϖ hstrain hr0 hϖ hrh hsmall hjets G hG tw S Cw W hwa
    hwb f U Uw hsol hf M hb i x
  obtain ⟨F, hF, hFid, -⟩ := hcap
  have hc' : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      cappedWordSlots κ 0 d j.succ x + o.1 ≤ cappedWordSlots κ 0 d j.castSucc y + 2 :=
    fun j x y o hne => cappedWordSlots_edge_compatible κ 0 d j x y o.1 (Finset.mem_Icc.mp o.2).1
      (nonempty_letter_order_le (hL j) x y o hne) (hc j x y o hne)
  refine ⟨F, hF, ?_⟩
  filter_upwards [hFid] with t ht k
  refine (ht k).trans (Filter.Eventually.of_forall fun z => ?_)
  have htr := wordChainPreviousFlux_truncate letters κ (cappedWordSlots κ 0 d)
    (cappedWordSlots_le_original κ 0 d) hc hc' X0 δ (fun p => Uw p.1 p.2 t) (i.succ, x) t z
  exact congrArg (fun y => y k) htr

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The moment supply of the seam datum (statements)

The fast clause of `SeamFutureKernelStatement` now assumes finite moments of the seam datum
`f_F = (old endpoint) ∘ Υ`. `cycle_seam` supplies them from the compact support of the old datum:

* `CompactChainEndpointMomentsStatement`: a word chain from a compactly supported datum (the
  premises of `wordChain_flux_of_compactDatum`) has an endpoint with finite moments of every order.
  Route: `wordChain_capped_finite_polynomial_energy` at the last level with moment budget
  `m ≥ p` (`hf` as in `wordChain_flux_of_compactDatum`: the compact datum has every weighted
  factorial norm finite, `weightedFactorialNormSq_compact_value_ne_top`); the supremum over `[a, b]`
  includes `t = b`; the capped value is the value (`truncatePlaneHk` keeps order `0`); the order-`0`
  term of `weightedFactorialNormSq` with weight `≥ p` dominates `momentNorm π p ϖ`.
* `CenteredTransitionMomentsStatement`: composition with a centered volume-preserving transition
  keeps the moments finite: `Υ⁻¹(0) = 0` and `‖DΥ⁻¹ − I‖ ≤ Cg` give `|Υ⁻¹ w| ≤ (1 + Cg)|w|`, and the
  change of variables `w = Υ z` has Jacobian `1`. -/

universe u v

/-- **The endpoint of a word chain from a compactly supported datum has finite moments.**

For `N = 0` the chain is the scalar cell flow of `f`, compact data have every moment, and the
weighted energies propagate (the chart weights). For zero datum the endpoint is `0`; for `p = 0`
the endpoint is in `L²`. -/
def CompactChainEndpointMomentsStatement : Prop :=
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ},
  (2 ≤ D) →
  ∀ (π : ι → ℝ),
  (∀ x, 0 < π x) →
  ∀ (letters : Fin N → CycleLetter ι h D),
  ∀ (J H : ℕ),
  ∀ (a b : ℝ),
  (a ≤ b) →
  (∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H) →
  ∀ (κ : Fin (N + 1) → ι → ℕ),
  (∑ j, (letters j).order ≤ J) →
  (∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2) →
  ∀ (X0 : Vec 2),
  ∀ (δ : ℝ),
  (∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z)) →
  ∀ (v : ℝ → Vec 2 → Vec 2),
  (IsCellDrift v) →
  (∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t)) →
  ∀ (η : ℝ),
  (0 < η) →
  ∀ (Cvj : ℕ → ℝ),
  (∀ (j : ℕ) t z, ‖iteratedFDeriv ℝ j (fun z' => Real.sqrt η • v t z') z‖ ≤ Cvj j) →
  ∀ (ϖ : ℝ),
  (0 < ϖ) →
  ∀ (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ),
  (IsCellMetric (fun t _ => G t)) →
  ∀ (tw S : ℝ),
  ∀ (Cw : ℕ → ℝ),
  (∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw) →
  (tw ≤ a) →
  (b ≤ tw + S) →
  ∀ (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x)),
  ∀ (U : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x)),
  ∀ (Uw : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x)),
  (IsPlaneChain (wordChainData G letters X0 δ) κ a b v f (fun _ _ _ => 0) U Uw) →
  ∀ (R : ℝ),
  (∀ x, ∀ᵐ z ∂volume, R ^ 2 < z 0 ^ 2 + z 1 ^ 2 → planeValue (f x) z = 0) →
  ∀ (M : ℝ),
  (∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) →
  ∀ p : ℕ, momentNorm π p ϖ (fun x => planeValue (U (Fin.last N) x b)) < ⊤

/-- **Composition with a centered transition keeps the moments finite.**

For `Υ = id` (`g = 0`) this is an equality; for `p = 0` it is volume preservation,
`‖F ∘ Υ‖₂ = ‖F‖₂`. -/
def CenteredTransitionMomentsStatement : Prop :=
  ∀ (p : ℕ) (Υ Υinv : Vec 2 → Vec 2) (g δ C : ℝ) (q : ℕ), 1 ≤ q → 0 ≤ C * g →
    IsCenteredTransition Υ Υinv g δ C q →
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] (π : ι → ℝ), (∀ x, 0 < π x) →
  ∀ (s : ℝ) (F : ∀ x, Vec 2 → h x), (∀ x, AEStronglyMeasurable (F x) volume) →
    momentNorm π p s F < ⊤ → momentNorm π p s (fun x z => F x (Υ z)) < ⊤

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords AVRegularity.CycleWords.Assembly AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # `CompactChainEndpointMomentsStatement`

The order-`0` term of the weighted factorial norm controls the weighted `L²` norm of the value
(`eLpNorm_weight_lt_top`), and `momentNorm_le_weighted` turns it into the moment norm. -/

/-- A finite weighted factorial norm gives a finite weighted `L²` norm of the value. -/
theorem eLpNorm_weight_lt_top {K' : ℕ} {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    (V : PlaneHk Set.univ K' E) (n : ℕ) (ϖ r : ℝ) (Kc : ℕ)
    (h : weightedFactorialNormSq n ϖ 0 r Kc V ≠ ⊤) :
    eLpNorm (fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) *
      ‖planeValue V z‖) 2 volume < ⊤ := by
  have h0 : ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
      (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n * ∑ w : DerivativeWord2 0, ‖planeJetOrder V 0 w z‖ ^ 2)
      ≠ ⊤ := by
    refine ne_top_of_le_ne_top h ?_
    unfold weightedFactorialNormSq
    have := Finset.single_le_sum (f := fun j : ℕ => ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) *
      ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 + (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n *
        ∑ w : DerivativeWord2 j, ‖planeJetOrder V j w z‖ ^ 2))
      (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.succ_pos Kc))
    simpa using this
  have hword : ∀ z : Vec 2, ∑ w : DerivativeWord2 0, ‖planeJetOrder V 0 w z‖ ^ 2 =
      ‖planeValue V z‖ ^ 2 := by
    intro z
    have hdef : ∀ w : DerivativeWord2 0, planeJetOrder V 0 w = planeValue V := fun w => by
      rw [Subsingleton.elim w (fun i => i.elim0)]
      rfl
    simp only [hdef]
    rw [Fintype.sum_unique]
  have hmeas : AEStronglyMeasurable (fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^
      ((n : ℝ) / 2) * ‖planeValue V z‖) volume := by
    refine AEStronglyMeasurable.mul ?_ (planeValue_memLp V).aestronglyMeasurable.norm
    apply Continuous.aestronglyMeasurable
    exact ((continuous_const.add (continuous_const.mul (((continuous_apply 0).pow 2).add
      ((continuous_apply 1).pow 2)))).rpow_const (fun z => Or.inr (by positivity)))
  have hw0 : ∀ z : Vec 2, 0 ≤ 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := fun z => by positivity
  have key : ∀ c : ℝ, 0 ≤ c → (c ^ ((n : ℝ) / 2)) ^ 2 = c ^ n := fun c hc => by
    rw [← Real.rpow_natCast (c ^ ((n : ℝ) / 2)) 2, ← Real.rpow_mul hc, ← Real.rpow_natCast c n]
    congr 1
    push_cast
    ring
  have hg2 : ∀ z : Vec 2, ‖(1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) *
      ‖planeValue V z‖‖ ^ 2 =
      (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ n * ‖planeValue V z‖ ^ 2 := by
    intro z
    rw [norm_mul, mul_pow, norm_norm, Real.norm_of_nonneg (Real.rpow_nonneg (hw0 z) _),
      key _ (hw0 z)]
  have hint : Integrable (fun z : Vec 2 => ‖(1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((n : ℝ) / 2) *
      ‖planeValue V z‖‖ ^ 2) volume := by
    simp_rw [hg2]
    rw [← lintegral_ofReal_ne_top_iff_integrable]
    · have h0' := h0
      simp only [Pi.zero_apply, sub_zero, hword] at h0'
      exact h0'
    · refine AEStronglyMeasurable.mul ?_ ((planeValue_memLp V).aestronglyMeasurable.norm.pow 2)
      apply Continuous.aestronglyMeasurable
      fun_prop
    · exact Filter.Eventually.of_forall fun z => by positivity
  exact ((memLp_two_iff_integrable_sq_norm hmeas).2 hint).eLpNorm_lt_top

theorem wordMomentSlot_last {N : ℕ} (m : ℕ) (Ks : Fin N → ℕ) :
    wordMomentSlot m Ks (Fin.last N) = m := by
  unfold wordMomentSlot
  have : ∀ i : Fin N, ¬ (Fin.last N).val ≤ i.val := fun i => by
    have := i.isLt
    simp only [Fin.val_last]
    omega
  simp

theorem planeValue_truncate' {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L : ℕ} (hKL : K ≤ L) (f : PlaneHk Set.univ L E) :
    planeValue (truncatePlaneHk hKL f) = planeValue f :=
  AVRegularity.CycleWords.planeJetOrder_truncate hKL (Nat.zero_le K) f _

/-- **`CompactChainEndpointMomentsStatement`.** -/
theorem compactChainEndpointMoments : CompactChainEndpointMomentsStatement := by
  intro ι _ h _ _ _ _ _ _ D N hD π hπ letters J H a b hab hL κ hreserve hc X0 δ hm v hv hvs η hη
    Cvj hvj ϖ hϖ G hG tw S Cw W hwa hwb f U Uw hsol R hsupp M hb p
  classical
  set d : Fin N → ℕ := fun j => (letters j).order with hddef
  set A := Interior.negAdjointJetConstant Cvj (0 + ∑ j, d j) with hAdef
  have hA : 1 ≤ A := Interior.one_le_negAdjointJetConstant Cvj _
  obtain ⟨hr0, hrh, hsmall⟩ := jet_radius_small hη A hA
  have hstrain : 0 ≤ A / Real.sqrt η :=
    div_nonneg (zero_le_one.trans hA) (Real.sqrt_nonneg _)
  have hjets : ∀ l, 1 ≤ l → l ≤ (0 + ∑ j, d j) → ∀ t z,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l z‖ ≤
        A / Real.sqrt η * (l.factorial : ℝ) := fun l _ hl t z =>
    forwardDrift_jets hη v hvs Cvj hvj _ t l hl z
  have hf : ∀ x n, weightedFactorialNormSq n ϖ 0 (1 / (3 * A * (1 + (Real.sqrt η)⁻¹)))
      (cappedWordSlots κ 0 d 0 x)
      (truncatePlaneHk (cappedWordSlots_le_original κ 0 d 0 x)
        (wordLevelDatum κ f 0 x)) ≠ ⊤ := by
    intro x n
    refine weightedFactorialNormSq_compact_value_ne_top n ϖ 0 _ _
      (isCompact_closedBall (0 : Vec 2) |R|) ?_
    filter_upwards [hsupp x] with z hz hzA
    have h0 := hz (sq_lt_of_not_mem_closedBall hzA)
    simp only [planeValue, planeJetOrder, Nat.zero_le, dite_true] at h0
    simp only [wordLevelDatum_zero]
    exact h0
  have hen := wordChain_capped_finite_polynomial_energy hD π hπ letters J H a b hab hL κ 0 d
    (fun j => rfl) (by simpa using hreserve) hc X0 δ hm v hv hvs (A / Real.sqrt η)
    (1 / (3 * A * (1 + (Real.sqrt η)⁻¹))) ϖ hstrain hr0 hϖ hrh hsmall hjets G hG tw S Cw W hwa
    hwb p f U Uw hsol hf (Fin.last N)
  have hX : ∀ x, eLpNorm (fun z : Vec 2 => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) *
      ‖planeValue (U (Fin.last N) x b) z‖) 2 volume < ⊤ := by
    intro x
    have h1 := hen x
    have h2 : weightedFactorialNormSq (wordMomentSlot p (fun j => (letters j).slow) (Fin.last N))
        ϖ 0 (1 / (3 * A * (1 + (Real.sqrt η)⁻¹))) (cappedWordSlots κ 0 d (Fin.last N) x)
        (truncatePlaneHk (cappedWordSlots_le_original κ 0 d (Fin.last N) x)
          (U (Fin.last N) x b)) ≠ ⊤ := by
      refine ne_top_of_le_ne_top h1 ?_
      refine le_trans ?_ le_self_add
      exact le_iSup₂ (f := fun t (_ : t ∈ Icc a b) => weightedFactorialNormSq
        (wordMomentSlot p (fun j => (letters j).slow) (Fin.last N)) ϖ 0
        (1 / (3 * A * (1 + (Real.sqrt η)⁻¹))) (cappedWordSlots κ 0 d (Fin.last N) x)
        (truncatePlaneHk (cappedWordSlots_le_original κ 0 d (Fin.last N) x)
          (U (Fin.last N) x t))) b ⟨hab, le_rfl⟩
    rw [wordMomentSlot_last] at h2
    have := eLpNorm_weight_lt_top _ p ϖ _ _ h2
    rwa [planeValue_truncate'] at this
  refine lt_of_le_of_lt (momentNorm_le_weighted π p ϖ _
    (fun x => (planeValue_memLp (U (Fin.last N) x b)).aestronglyMeasurable)) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  unfold familyNorm
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  exact ENNReal.sum_lt_top.2 fun x _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top (hX x))

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # `CenteredTransitionMomentsStatement`

`⟨Υ⁻¹ w⟩ ≤ (3 + 2 C g) ⟨w⟩` (mean value theorem for `Υ⁻¹ - id`, `Υ⁻¹ 0 = 0`), so the bracket-weighted
`L²` norm of `F ∘ Υ` is that of `⟨Υ⁻¹ ·⟩^m F` (volume preservation), at most `(3 + 2Cg)^m` times
that of `⟨·⟩^m F`; `momentNorm_le_bracket` and `memLp_bracket_of_momentNorm` convert. -/

/-- The bracket of the inverse is at most a constant times the bracket. -/
theorem jbracket_inv_le (Υinv : Vec 2 → Vec 2) (K : ℝ) (hK : 0 ≤ K) (h0 : Υinv 0 = 0)
    (hd : ∀ z, DifferentiableAt ℝ Υinv z)
    (hdev : ∀ z, ‖fderiv ℝ Υinv z - ContinuousLinearMap.id ℝ (Vec 2)‖ ≤ K) (w : Vec 2) :
    jbracket (Υinv w) ≤ (3 + 2 * K) * jbracket w := by
  have hφ : ∀ z, DifferentiableAt ℝ (fun y => Υinv y - y) z := fun z =>
    (hd z).sub differentiableAt_id
  have hmv := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := fun y => Υinv y - y)
    (s := Set.univ) (x := 0) (y := w) (C := K) (fun z _ => hφ z)
    (fun z _ => by
      have : fderiv ℝ (fun y => Υinv y - y) z = fderiv ℝ Υinv z - ContinuousLinearMap.id ℝ (Vec 2) := by
        rw [fderiv_fun_sub (hd z) differentiableAt_fun_id, fderiv_fun_id]
      rw [this]; exact hdev z)
    convex_univ (mem_univ _) (mem_univ _)
  simp only [h0, sub_zero] at hmv
  have hw : ‖w‖ ≤ jbracket w := by
    refine (pi_norm_le_iff_of_nonneg (jbracket_pos w).le).2 fun i => ?_
    rw [Real.norm_eq_abs]; exact abs_coord_le_jbracket w i
  have hy : ‖Υinv w‖ ≤ (1 + K) * ‖w‖ := by
    calc ‖Υinv w‖ = ‖(Υinv w - w) + w‖ := by rw [sub_add_cancel]
      _ ≤ ‖Υinv w - w‖ + ‖w‖ := norm_add_le _ _
      _ ≤ K * ‖w‖ + ‖w‖ := by gcongr
      _ = (1 + K) * ‖w‖ := by ring
  have hc : ∀ i, |Υinv w i| ≤ ‖Υinv w‖ := fun i => by
    have := norm_le_pi_norm (Υinv w) i
    rwa [Real.norm_eq_abs] at this
  have h1 := jbracket_le (Υinv w)
  have hj1 := one_le_jbracket w
  have hn0 := norm_nonneg w
  calc jbracket (Υinv w) ≤ 1 + |Υinv w 0| + |Υinv w 1| := h1
    _ ≤ 1 + 2 * ((1 + K) * ‖w‖) := by linarith [hc 0, hc 1]
    _ ≤ 1 + 2 * ((1 + K) * jbracket w) := by gcongr
    _ ≤ (3 + 2 * K) * jbracket w := by nlinarith

/-- **`CenteredTransitionMomentsStatement`.** -/
theorem centeredTransitionMoments : CenteredTransitionMomentsStatement := by
  intro p Υ Υinv g δ C q hq hCg hΥ ι _ h _ _ π hπ s F hFm hF
  have hΥ1 : ContDiff ℝ 1 Υ := hΥ.smooth.1.of_le (by exact_mod_cast hq)
  have hΥi1 : ContDiff ℝ 1 Υinv := hΥ.smooth.2.of_le (by exact_mod_cast hq)
  have hmp : MeasurePreserving Υ volume volume := by
    apply ChartTransport.measurePreserving_of_det hΥ1 hΥ.left_inv hΥ.right_inv
    intro z
    rw [← ChartTransport.det_fderiv_eq_jac]
    exact hΥ.volume z
  have h0 : Υinv 0 = 0 := by
    have := hΥ.left_inv 0
    rwa [hΥ.centered] at this
  have hd : ∀ z, DifferentiableAt ℝ Υinv z := fun z =>
    (hΥi1.differentiable one_ne_zero) z
  set m : ℕ := if s = 0 then 0 else p with hm
  set c : ℝ := 3 + 2 * (C * g) with hc
  have hc0 : 0 ≤ c := by rw [hc]; linarith
  have hbr : ∀ w, jbracket (Υinv w) ^ m ≤ c ^ m * jbracket w ^ m := fun w => by
    rw [← mul_pow]
    exact pow_le_pow_left₀ (jbracket_pos _).le
      (jbracket_inv_le Υinv (C * g) hCg h0 hd hΥ.dev.2 w) m
  have hcont : Continuous fun w => jbracket (Υinv w) ^ m :=
    ((jbracket_contDiff.continuous.comp hΥi1.continuous).pow m)
  have hFv : ∀ v, MemLp (fun z => jbracket z ^ m • F v z) 2 volume := fun v =>
    memLp_bracket_of_momentNorm hF (hπ v) (hFm v)
  have hG : ∀ v, MemLp (fun w => jbracket (Υinv w) ^ m • F v w) 2 volume := by
    intro v
    refine ((hFv v).const_smul (c ^ m)).of_le (hcont.aestronglyMeasurable.smul (hFm v))
      (Filter.Eventually.of_forall fun w => ?_)
    simp only [Pi.smul_apply, norm_smul, Real.norm_eq_abs]
    rw [abs_of_nonneg (pow_nonneg (jbracket_pos _).le _),
      abs_of_nonneg (pow_nonneg hc0 _), abs_of_nonneg (pow_nonneg (jbracket_pos _).le _), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (hbr w) (norm_nonneg _)
  have hGΥ : ∀ v, MemLp (fun z => jbracket z ^ m • F v (Υ z)) 2 volume := by
    intro v
    have := (hG v).comp_measurePreserving hmp
    convert this using 2 with z
    simp only [Function.comp_apply, hΥ.left_inv z]
  refine lt_of_le_of_lt (momentNorm_le_bracket π p s _
    (fun v => (hFm v).comp_quasiMeasurePreserving hmp.quasiMeasurePreserving)) ?_
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ne_of_lt ?_)
  exact ENNReal.sum_lt_top.2 fun v _ =>
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.pow_lt_top (hGΥ v).eLpNorm_lt_top)

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! Tools for the level claim of the adjoint word chain:
- the vector reversed-adjoint bound from a scalar adjoint bound with power independent of the
  weight (`reversedAdjoint_vector_bound`);
- the weighted Cauchy–Schwarz bound of the inverse-mass value pairing (`weighted_value_pairing_le`);
- the transposed-letter integrand of the step as an `L²` pairing with `letterTransposeHk`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- **The vector reversed-adjoint bound.** A scalar bound for the reversed chain on every
subwindow of `[a, b]`, with constant `Ca k p`, power `Qa k` and factor `P`, gives the bound of the
family assembled from the coordinate chains of a test `Φ`, with the factor `√(m+1)`. -/
theorem reversedAdjoint_vector_bound (π : ι → ℝ) {n : ι → Type*} [∀ x, Fintype (n x)]
    (B : ∀ x, OrthonormalBasis (n x) ℝ (h x)) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (ϖ P : ℝ) (Ca : ℕ → ℕ → ℝ) (Qa : ℕ → ℕ) {a b : ℝ}
    (hadj : ∀ (k p : ℕ) (s t : ℝ), a ≤ s → s ≤ t → t ≤ b →
      ∀ (f : ∀ _ : Unit, PlaneHk Set.univ k ℝ)
        (u : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ k ℝ)
        (w : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (k + 1) ℝ),
        IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => k) (-t) (-s)
          (fun τ z => -(v (-τ) z)) f (fun _ _ _ => 0) u w →
        weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
            (fun x a w' => planeJetOrder (u 0 x (-s)) a w') ≤
          ENNReal.ofReal (Ca k p * P ^ Qa k * (1 + (t - s)) ^ Qa k) *
            weightedJetNorm (fun _ : Unit => (1 : ℝ)) (-(p : ℝ)) k ϖ 1
              (fun x a w' => planeJetOrder (f x) a w'))
    (m p : ℕ) {t : ℝ} (ht : t ≤ b) (Φ : ∀ x, PlaneHk Set.univ m (h x))
    (ψ : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ x, n x → ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : ∀ x e, IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-t) (-a)
      (fun τ z => -(v (-τ) z)) (fun _ => planeHkCoord (B x e) (Φ x)) (fun _ _ _ => 0)
      (ψ x e) (ψw x e))
    (s : ℝ) (has : a ≤ s) (hst : s ≤ t) :
    weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z =>
        planeJetOrder (planeHkAssemble (B x) (fun e => ψ x e 0 () (-s))) i w z) ≤
      ENNReal.ofReal (Real.sqrt (m + 1)) *
        ENNReal.ofReal (Ca m p * P ^ Qa m * (1 + (t - s)) ^ Qa m) *
        weightedJetNorm π (-(p : ℝ)) m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) :=
  planeHkAssemble_weightedJetNorm_le π B m (-(p : ℝ)) ϖ Φ (fun x e => ψ x e 0 () (-s))
    (Ca m p * P ^ Qa m * (1 + (t - s)) ^ Qa m) fun x e =>
      hadj m p s t has hst ht (fun _ => planeHkCoord (B x e) (Φ x)) (ψ x e) (ψw x e)
        (reversedAdjoint_restrict G (fun τ z => -(v (-τ) z)) m has hst _ (ψ x e) (ψw x e)
          (hψ x e))

/-- The value component of a carrier is its order-zero ordered jet. -/
theorem planeJetL2_value_ae {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ} (U : PlaneHk Set.univ K E) :
    (planeHkValueOperator K U : Vec 2 → E) =ᵐ[volume] planeJetOrder U 0 Fin.elim0 := by
  rw [planeHkValueOperator_eq_planeJetL2]
  filter_upwards [planeJetL2_ae U (valueIndex2 K)] with z hz
  rw [hz]
  simp only [planeJetOrder, Nat.zero_le, dite_true]
  rfl

/-- One pairing, through the weights `w_q w_{-q} = 1`. -/
theorem weighted_value_pairing_one_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K m : ℕ} (g : PlaneHk Set.univ K E)
    (Φ : PlaneHk Set.univ m E) (q ϖ : ℝ) :
    ENNReal.ofReal |inner ℝ (planeHkValueOperator K g) (planeHkValueOperator m Φ)| ≤
      eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) *
          ‖planeJetOrder g 0 Fin.elim0 z‖) 2 volume *
        eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) *
          ‖planeJetOrder Φ 0 Fin.elim0 z‖) 2 volume := by
  set wq : Vec 2 → ℝ := fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) with hwq
  set wq' : Vec 2 → ℝ := fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) with hwq'
  have hpos : ∀ z : Vec 2, 0 < 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := fun z => by positivity
  have hprod : ∀ z, wq z * wq' z = 1 := fun z => by
    rw [hwq, hwq']
    dsimp only
    rw [← Real.rpow_add (hpos z), show q / 2 + -q / 2 = 0 by ring, Real.rpow_zero]
  have hwq0 : ∀ z, 0 ≤ wq z := fun z => Real.rpow_nonneg (hpos z).le _
  have hwq0' : ∀ z, 0 ≤ wq' z := fun z => Real.rpow_nonneg (hpos z).le _
  set A : Vec 2 → ℝ := fun z => wq z * ‖planeJetOrder g 0 Fin.elim0 z‖ with hA
  set Bf : Vec 2 → ℝ := fun z => wq' z * ‖planeJetOrder Φ 0 Fin.elim0 z‖ with hB
  have hAm : AEStronglyMeasurable A volume :=
    (weight_continuous ϖ q).aestronglyMeasurable.mul
      (planeJetOrder_aestronglyMeasurable g 0 Fin.elim0).norm
  have hBm : AEStronglyMeasurable Bf volume :=
    (weight_continuous ϖ (-q)).aestronglyMeasurable.mul
      (planeJetOrder_aestronglyMeasurable Φ 0 Fin.elim0).norm
  have hint : inner ℝ (planeHkValueOperator K g) (planeHkValueOperator m Φ) =
      ∫ z, inner ℝ (planeJetOrder g 0 Fin.elim0 z) (planeJetOrder Φ 0 Fin.elim0 z) := by
    rw [L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [planeJetL2_value_ae g, planeJetL2_value_ae Φ] with z h1 h2
    rw [h1, h2]
  have hholder := ENNReal.lintegral_mul_le_Lp_mul_Lq volume Real.HolderConjugate.two_two
    (hAm.aemeasurable.ennreal_ofReal) (hBm.aemeasurable.ennreal_ofReal)
  have heL : ∀ (f : Vec 2 → ℝ), AEStronglyMeasurable f volume → (∀ z, 0 ≤ f z) →
      eLpNorm f 2 volume = (∫⁻ z, ENNReal.ofReal (f z) ^ (2 : ℝ)) ^ (1 / (2 : ℝ)) := by
    intro f hf hf0
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num) hf,
      ENNReal.toReal_ofNat]
    congr 1
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hf0 z)]
  rw [heL A hAm fun z => mul_nonneg (hwq0 z) (norm_nonneg _),
    heL Bf hBm fun z => mul_nonneg (hwq0' z) (norm_nonneg _)]
  refine le_trans ?_ hholder
  rw [hint, ← Real.enorm_eq_ofReal_abs]
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  rw [Real.enorm_eq_ofReal_abs, Pi.mul_apply, ← ENNReal.ofReal_mul (mul_nonneg (hwq0 z)
    (norm_nonneg _))]
  refine ENNReal.ofReal_le_ofReal ((abs_real_inner_le_norm _ _).trans (le_of_eq ?_))
  show _ = wq z * ‖planeJetOrder g 0 Fin.elim0 z‖ * (wq' z * ‖planeJetOrder Φ 0 Fin.elim0 z‖)
  calc ‖planeJetOrder g 0 Fin.elim0 z‖ * ‖planeJetOrder Φ 0 Fin.elim0 z‖
      = (wq z * wq' z) * (‖planeJetOrder g 0 Fin.elim0 z‖ * ‖planeJetOrder Φ 0 Fin.elim0 z‖) := by
        rw [hprod, one_mul]
    _ = _ := by ring

/-- **The weighted value pairing**: the inverse-mass pairing of two families is bounded by the
order-zero weighted norm of the first at weight `q` times the weighted jet norm of the second at
weight `-q`. -/
theorem weighted_value_pairing_le (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {K : ι → ℕ}
    (g : ∀ x, PlaneHk Set.univ (K x) (h x)) {m : ℕ} (Φ : ∀ x, PlaneHk Set.univ m (h x))
    (q ϖ : ℝ) :
    ENNReal.ofReal |∑ x, (π x)⁻¹ *
        inner ℝ (planeHkValueOperator (K x) (g x)) (planeHkValueOperator m (Φ x))| ≤
      weightedJetNorm π q 0 ϖ 1 (fun x i w z => planeJetOrder (g x) i w z) *
        weightedJetNorm π (-q) m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) := by
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hc
  set A : ι → ℝ≥0∞ := fun x => eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (q / 2) *
    ‖planeJetOrder (g x) 0 Fin.elim0 z‖) 2 volume with hA
  set Bf : ι → ℝ≥0∞ := fun x => eLpNorm (fun z => (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) *
    ‖planeJetOrder (Φ x) 0 Fin.elim0 z‖) 2 volume with hB
  -- the sum over components
  have h1 : ENNReal.ofReal |∑ x, (π x)⁻¹ *
      inner ℝ (planeHkValueOperator (K x) (g x)) (planeHkValueOperator m (Φ x))| ≤
      ∑ x, c x * (A x * Bf x) := by
    refine (ENNReal.ofReal_le_ofReal (Finset.abs_sum_le_sum_abs _ _)).trans ?_
    rw [ENNReal.ofReal_sum_of_nonneg fun x _ => abs_nonneg _]
    refine Finset.sum_le_sum fun x _ => ?_
    rw [abs_mul, abs_of_nonneg (inv_pos.mpr (hπ x)).le, ENNReal.ofReal_mul
      (inv_pos.mpr (hπ x)).le]
    exact mul_le_mul_right (weighted_value_pairing_one_le (g x) (Φ x) q ϖ) _
  -- Cauchy–Schwarz over the components
  have h2 : ∑ x, c x * (A x * Bf x) ≤ familyNorm c A * familyNorm c Bf := by
    have hcs := ENNReal.inner_le_Lp_mul_Lq (s := Finset.univ)
      (fun x => c x ^ (1 / 2 : ℝ) * A x) (fun x => c x ^ (1 / 2 : ℝ) * Bf x)
      Real.HolderConjugate.two_two
    have hsq : ∀ x, (c x ^ (1 / 2 : ℝ)) * (c x ^ (1 / 2 : ℝ)) = c x := fun x => by
      rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
      norm_num
    have hpow : ∀ (X : ℝ≥0∞) x, (c x ^ (1 / 2 : ℝ) * X) ^ (2 : ℝ) = c x * X ^ 2 := by
      intro X x
      rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num), ← ENNReal.rpow_mul]
      norm_num
    unfold familyNorm
    calc ∑ x, c x * (A x * Bf x)
        = ∑ x, (c x ^ (1 / 2 : ℝ) * A x) * (c x ^ (1 / 2 : ℝ) * Bf x) :=
          Finset.sum_congr rfl fun x _ => by
            rw [mul_mul_mul_comm, hsq]
      _ ≤ _ := hcs
      _ = _ := by simp only [hpow]
  -- the norms
  have hgN : familyNorm c A = weightedJetNorm π q 0 ϖ 1
      (fun x i w z => planeJetOrder (g x) i w z) := by
    rw [weightedJetNorm_eq_familyNorm, Finset.sum_range_one]
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, one_mul]
    congr 1
    funext x
    simp only [hA]
    congr 1
    funext z
    congr 1
    rw [Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    congr 2
  have hΦN : familyNorm c Bf ≤ weightedJetNorm π (-q) m ϖ 1
      (fun x i w z => planeJetOrder (Φ x) i w z) := by
    rw [weightedJetNorm_eq_familyNorm]
    refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun a =>
      ENNReal.ofReal ((1 : ℝ) ^ a / (a.factorial : ℝ)) *
        familyNorm (fun v => ENNReal.ofReal ((π v)⁻¹)) (fun v => eLpNorm (fun z =>
          (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-q / 2) *
            Real.sqrt (∑ w : DerivativeWord2 a, ‖planeJetOrder (Φ v) a w z‖ ^ 2)) 2 volume))
      (fun _ _ => zero_le) (Finset.mem_range.mpr (Nat.succ_pos m)))
    simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, one_mul]
    congr 1
    funext x
    simp only [hB]
    congr 1
    funext z
    congr 1
    rw [Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    congr 2
  calc _ ≤ ∑ x, c x * (A x * Bf x) := h1
    _ ≤ familyNorm c A * familyNorm c Bf := h2
    _ ≤ _ := by
        rw [hgN]
        exact mul_le_mul_right hΦN _

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords.Seam

/-! # Quiet margin fibre bound: the plain pass with negative input

`B1PlainStageNegStatement`: `PlainStageStatement` from a start `a₁ ∈ [a, b]`, with the scaled
stage values at `a₁` measured by their pairings with the tests of their order (`X_i`) instead of
their `L²` norms.
`b1_plainStageNeg_of_adjointKernel`: proved from `CellAdjointKernelHsStatement` as `plainStageAssembly`, through
`b1_plain_stage_frame_neg`. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

universe u v

/-- **The plain pass with negative input** (the statement). -/
def B1PlainStageNegStatement : Prop :=
  ∀ K : ScalarConstants, ∃ g₁ : ℝ, 0 < g₁ ∧
  ∀ (Nw D m : ℕ) (d Ks : Fin Nw → ℕ) (pos : Fin Nw → Bool) (s₀ : ℕ) (A : ℝ),
    (Finset.univ.sup d) + 3 ≤ s₀ → 1 ≤ A →
  ∃ (C : ℝ) (Q : ℕ), 0 < C ∧
  ∀ {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2),
    (∀ l, (F.letters l).order = d l ∧ (F.letters l).slow = Ks l ∧
      (F.letters l).positive = pos l) →
    b1wLadderTop s₀ d Ks m + (Finset.univ.sup d) ≤ F.J →
    θ ∈ freqCube →
  ∀ (V : ℝ) (hb : ∀ t x, ∑ i, F.v t x i ^ 2 ≤ V ^ 2) (κ : ℝ → ℝ → ℝ),
    IsFibreKernel (b1wCoeff F θ) F.piece.hGm V F.piece.hv.1 hb F.a F.b A κ →
  ∀ a₁ ∈ Icc F.a F.b, ∀ Xn : B1WIndex ι h Nw m Ks → ℝ,
    (∀ (k : ℕ) (i : B1WIndex ι h Nw m Ks), b1wSt i = k → ∀ w : ComplexCellL2,
      (w : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] stageScaled F θ i a₁ →
      ∀ φ : TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
        ‖cellComplexPair w (torusHkValueCLM φ)‖ ≤ Xn i * ‖φ‖) →
  ∀ t ∈ Icc a₁ F.b, ∀ W : B1WIndex ι h Nw m Ks → ComplexCellL2, IsScaledStage F θ t W →
  ∀ (k : ℕ) (ψ : B1WIndex ι h Nw m Ks → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
    ‖∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i))‖ ≤
      C * peFactor F.η ^ Q * (1 + (t - a₁)) ^ Q * κ a₁ t *
        Real.sqrt (∑ i, Xn i ^ 2) * Real.sqrt (∑ i ∈ stageSet b1wSt k, ‖ψ i‖ ^ 2)

/-- **The plain pass with negative input**, from `CellAdjointKernelHsStatement`. -/
theorem b1_plainStageNeg_of_adjointKernel (hK2 : CellAdjointKernelHsStatement) :
    B1PlainStageNegStatement.{u, v} := by
  have hZ := stageFamilyZone.{u, v}
  intro K
  obtain ⟨g₁, hg₁, hMK⟩ := amplitudeIdFibresMeas_of_literal.{u, v} amplitudeIdentification
    amplitudeIdForcingCurves K
  refine ⟨g₁, hg₁, ?_⟩
  intro Nw D m d Ks pos s₀ A hs₀ hA
  obtain ⟨B, hB, hprov⟩ := hZ K Nw D m d Ks pos Real.pi s₀ hs₀
  choose Ck Qk hCk hadjk using fun k =>
    adjoint_kernel_frame.{u, v} hK2 K (b1wLadderAt Nw s₀ d Ks k) hA
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = ∑ k ∈ Finset.range (b1wM Nw m Ks), Ck k := ⟨_, rfl⟩
  obtain ⟨Qm, hQm⟩ : ∃ Qm : ℕ, Qm = ∑ k ∈ Finset.range (b1wM Nw m Ks), Qk k := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]
    exact Finset.sum_nonneg fun k _ => (hCk k).le
  have hA0 : 0 ≤ A := zero_le_one.trans hA
  refine ⟨1 + ∑ k ∈ Finset.range (b1wM Nw m Ks), plainConst 1 A B k * max 1 c₀ ^ (k + 1),
    Qm * b1wM Nw m Ks + b1wM Nw m Ks, ?_, ?_⟩
  · have : 0 ≤ ∑ k ∈ Finset.range (b1wM Nw m Ks), plainConst 1 A B k * max 1 c₀ ^ (k + 1) :=
      Finset.sum_nonneg fun k _ =>
        mul_nonneg (plainConst_nonneg zero_le_one hA0 hB k) (by positivity)
    linarith
  intro ι _ h _ _ _ _ _ _ F θ hlet hJF hθ V hb κ hκ a₁ ha₁ Xn hX t ht W hW k ψ
  have hP := one_le_peFactor F.η
  have hP0 : 0 ≤ peFactor F.η := zero_le_one.trans hP
  have hT : 0 ≤ t - a₁ := sub_nonneg.2 ht.1
  have hκ0 : 0 ≤ κ a₁ t := (hκ.pos a₁ t).le
  by_cases hk : k < b1wM Nw m Ks
  swap
  · -- no stage of order `k`
    have he : stageSet b1wSt k = (∅ : Finset (B1WIndex ι h Nw m Ks)) := by
      refine Finset.eq_empty_of_forall_notMem fun i hi => hk ?_
      rw [← (Finset.mem_filter.1 hi).2]
      exact b1wSt_lt i
    rw [he, Finset.sum_empty, norm_zero]
    have : 0 ≤ 1 + ∑ k ∈ Finset.range (b1wM Nw m Ks), plainConst 1 A B k * max 1 c₀ ^ (k + 1) :=
      add_nonneg zero_le_one (Finset.sum_nonneg fun k _ =>
        mul_nonneg (plainConst_nonneg zero_le_one hA0 hB k) (by positivity))
    have hpow : 0 ≤ (1 + (t - a₁)) ^ (Qm * b1wM Nw m Ks + b1wM Nw m Ks) :=
      pow_nonneg (by linarith) _
    exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg this (pow_nonneg hP0 _)) hpow)
      hκ0) (Real.sqrt_nonneg _)) (Real.sqrt_nonneg _)
  -- the adjoint curves with one constant
  have hadj : ∀ k < b1wM Nw m Ks, ∀ t ∈ Icc F.a F.b,
      ∀ ψ : TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ,
      ∃ (Ψv : ℝ → ComplexCellL2) (Ψs : ℝ → TorusHk 1 ℂ)
        (U : ℝ → TorusHk (b1wLadderAt Nw s₀ d Ks k) ℂ),
        CellWeakHilbertCurve F.a t Ψv Ψs (fun r =>
          -cellDualDerivative
            (cellAdjointCoefficients ⟨fun s _ => F.G s, F.v, fun k => ((θ k : ℝ) : ℂ), 0⟩)
            F.piece.hGm V (cellDrift_neg F.piece.hv).1 (cellDrift_neg_bound hb) r (Ψs r) 0 0) ∧
        Ψv t = torusHkValueCLM ψ ∧
        ∀ r ∈ Icc F.a t, torusHkValueCLM (U r) = Ψv r ∧
          ‖U r‖ ≤ c₀ * peFactor F.η ^ Qm * κ r t * ‖ψ‖ := by
    intro k hk t ht ψ
    obtain ⟨Ψv, Ψs, U, h1, h2, h3⟩ := hadjk k g₁ F θ hθ V hb κ hκ t ht ψ
    refine ⟨Ψv, Ψs, U, h1, h2, fun r hr => ⟨(h3 r hr).1, (h3 r hr).2.trans ?_⟩⟩
    have hk' : k ∈ Finset.range (b1wM Nw m Ks) := Finset.mem_range.2 hk
    have hC : Ck k * peFactor F.η ^ Qk k ≤ c₀ * peFactor F.η ^ Qm := by
      rw [hc₀, hQm]
      exact mul_le_mul (Finset.single_le_sum (f := Ck) (fun k _ => (hCk k).le) hk')
        (pow_le_pow_right₀ hP (Finset.single_le_sum (f := Qk) (fun _ _ => Nat.zero_le _) hk'))
        (pow_nonneg hP0 _) (by rw [← hc₀]; exact hc₀0)
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC (hκ.pos r t).le)
      (norm_nonneg _)
  obtain ⟨Wc, hWc, hbd⟩ := b1_plain_stage_frame_neg F θ d s₀ hs₀
    (fun l => ⟨(hlet l).1, (hlet l).2.1⟩)
    (by omega) (fun j x e β => hMK F j x e θ β) B hB (hprov g₁ F θ hlet hJF fun k => hθ k) V hb κ
    hA0 hκ (c₀ * peFactor F.η ^ Qm) (mul_nonneg hc₀0 (pow_nonneg hP0 _)) hadj a₁ ha₁ Xn
    (fun k _ i hi w hw φ => hX k i hi w hw φ)
  have hWt : ∀ i, W i = Wc i t := fun i =>
    Lp.ext ((hW i).trans (hWc i t ⟨ha₁.1.trans ht.1, ht.2⟩).symm)
  have e1 : ∑ i ∈ stageSet b1wSt k, cellComplexPair (W i) (torusHkValueCLM (ψ i)) =
      ∑ i ∈ stageSet b1wSt k, cellComplexPair (Wc i t) (torusHkValueCLM (ψ i)) :=
    Finset.sum_congr rfl fun i _ => by rw [hWt i]
  rw [e1]
  exact (hbd k hk t ht ψ).trans (plain_final_le hA0 hB hc₀0 hP hT hκ0 (Real.sqrt_nonneg _)
    (Real.sqrt_nonneg _) hk)

end AVRegularity.CycleWords.Seam
end
end
