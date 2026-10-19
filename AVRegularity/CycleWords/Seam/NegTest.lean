-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.Seam.B1NegPair
import AVRegularity.CycleWords.MixedWords.Discard.JetFourier
import AVRegularity.CycleWords.Seam.CutoffComplementTaylor
public import AVRegularity.CycleWords.Seam.CrudeChartWeights
public import AVRegularity.CycleWords.MixedWords.Discard.BandRep
import Mathlib.Analysis.CStarAlgebra.Module.Constructions

section
/-! # The bridge from the fibres to the plane for the negative and low-band norms

`∫_zone cellNegSq k θ (B_θ g) = ∫ (1 + |ξ|²)^{-k} |ĝ|²` and
`∫_zone cellLowSq ρ θ (B_θ g) = ∫_{|ξ|<ρ} |ĝ|²` for integrable real `g` (the tiling of the plane
by the lattice translates of the zone, `tiling`), the measurability of the fibre integrands,
and the behaviour of the fibre norms under scaling and almost everywhere changes.
-/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard AVRegularity.CycleWords.Seam
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam.NegLowBand

theorem cellFourierCoeff_congr_ae {f g : Vec 2 → ℂ}
    (h : f =ᵐ[volume.restrict AVenhance.unitCube] g) (n : Fin 2 → ℤ) :
    cellFourierCoeff f n = cellFourierCoeff g n := by
  unfold cellFourierCoeff
  refine integral_congr_ae ?_
  filter_upwards [h] with z hz
  rw [hz]

theorem cellFourierCoeff_const_mul (c : ℂ) (f : Vec 2 → ℂ) (n : Fin 2 → ℤ) :
    cellFourierCoeff (fun z => c * f z) n = c * cellFourierCoeff f n := by
  unfold cellFourierCoeff
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  simp only
  ring

theorem cellNegSq_congr_ae (k : ℕ) (θ : Vec 2) {f g : Vec 2 → ℂ}
    (h : f =ᵐ[volume.restrict AVenhance.unitCube] g) : cellNegSq k θ f = cellNegSq k θ g := by
  unfold cellNegSq
  refine tsum_congr fun n => ?_
  rw [cellFourierCoeff_congr_ae h n]

theorem cellLowSq_congr_ae (ρ : ℝ) (θ : Vec 2) {f g : Vec 2 → ℂ}
    (h : f =ᵐ[volume.restrict AVenhance.unitCube] g) : cellLowSq ρ θ f = cellLowSq ρ θ g := by
  unfold cellLowSq
  refine tsum_congr fun n => ?_
  rw [cellFourierCoeff_congr_ae h n]

theorem cellNegSq_const_mul (k : ℕ) (θ : Vec 2) (s : ℝ) (f : Vec 2 → ℂ) :
    cellNegSq k θ (fun z => (s : ℂ) * f z) = ENNReal.ofReal (s ^ 2) * cellNegSq k θ f := by
  unfold cellNegSq
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  rw [cellFourierCoeff_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_mul
    (sq_nonneg _)]
  congr 1
  rw [mul_pow, sq_abs]
  ring

theorem cellLowSq_const_mul (ρ : ℝ) (θ : Vec 2) (s : ℝ) (f : Vec 2 → ℂ) :
    cellLowSq ρ θ (fun z => (s : ℂ) * f z) = ENNReal.ofReal (s ^ 2) * cellLowSq ρ θ f := by
  unfold cellLowSq
  rw [← ENNReal.tsum_mul_left]
  refine tsum_congr fun n => ?_
  split_ifs
  · rw [cellFourierCoeff_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    rw [mul_pow, sq_abs]
  · simp

theorem cellNegSq_zero (k : ℕ) (θ : Vec 2) : cellNegSq k θ (fun _ => 0) = 0 := by
  unfold cellNegSq cellFourierCoeff
  simp

theorem cellLowSq_zero (ρ : ℝ) (θ : Vec 2) : cellLowSq ρ θ (fun _ => 0) = 0 := by
  unfold cellLowSq cellFourierCoeff
  simp

/-- The plane integrand of the negative norm. -/
def negBandIntegrand (k : ℕ) (g : Vec 2 → ℝ) (ξ : Vec 2) : ℝ≥0∞ :=
  ENNReal.ofReal (((1 + vecDot ξ ξ) ^ k)⁻¹ * ‖planeTransform g ξ‖ ^ 2)

/-- The plane integrand of the low band. -/
def lowBandIntegrand (ρ : ℝ) (g : Vec 2 → ℝ) (ξ : Vec 2) : ℝ≥0∞ :=
  if vecDot ξ ξ < ρ ^ 2 then ENNReal.ofReal (‖planeTransform g ξ‖ ^ 2) else 0

theorem Ft_const_mul (c : ℝ) (H : Vec 2 → ℝ) (ξ : Vec 2) :
    planeTransform (fun y => c * H y) ξ = (c : ℂ) * planeTransform H ξ := by
  unfold planeTransform
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  push_cast
  ring

theorem negBand_const_mul (k : ℕ) (c : ℝ) (H : Vec 2 → ℝ) (ξ : Vec 2) :
    negBandIntegrand k (fun y => c * H y) ξ = ENNReal.ofReal (c ^ 2) * negBandIntegrand k H ξ := by
  unfold negBandIntegrand
  rw [Ft_const_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    ← ENNReal.ofReal_mul (sq_nonneg c)]
  congr 1
  rw [mul_pow, sq_abs]
  ring

theorem vecDot_cont : Continuous fun ξ : Vec 2 => vecDot ξ ξ := by
  unfold vecDot; fun_prop

theorem one_add_vecDot_pos' (ξ : Vec 2) : 0 < 1 + vecDot ξ ξ := by
  have : 0 ≤ vecDot ξ ξ := by
    simp only [vecDot, Fin.sum_univ_two]
    exact add_nonneg (mul_self_nonneg _) (mul_self_nonneg _)
  linarith

theorem negBand_measurable (k : ℕ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Measurable (negBandIntegrand k g) := by
  unfold negBandIntegrand
  have hc := Ft_continuous hg
  exact ENNReal.measurable_ofReal.comp
    ((((continuous_const.add vecDot_cont).pow k).inv₀
      fun ξ => (pow_pos (one_add_vecDot_pos' ξ) k).ne').mul (hc.norm.pow 2)).measurable

theorem lowBand_measurable (ρ : ℝ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Measurable (lowBandIntegrand ρ g) := by
  unfold lowBandIntegrand
  have hc := Ft_continuous hg
  exact Measurable.ite (measurableSet_lt vecDot_cont.measurable measurable_const)
    (ENNReal.measurable_ofReal.comp (hc.norm.pow 2).measurable) measurable_const

theorem cellNegSq_eq_tsum (k : ℕ) (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) :
    cellNegSq k θ (planeBlochC θ g) =
      ∑' n : Fin 2 → ℤ, negBandIntegrand k g (quietFourierFrequency θ n) := by
  unfold cellNegSq negBandIntegrand
  refine tsum_congr fun n => ?_
  rw [cellCoeff_eq θ n hg]

theorem cellLowSq_eq_tsum (ρ : ℝ) (θ : Vec 2) {g : Vec 2 → ℝ} (hg : Integrable g) :
    cellLowSq ρ θ (planeBlochC θ g) =
      ∑' n : Fin 2 → ℤ, lowBandIntegrand ρ g (quietFourierFrequency θ n) := by
  unfold cellLowSq lowBandIntegrand
  refine tsum_congr fun n => ?_
  rw [cellCoeff_eq θ n hg]

theorem measurable_quietFourierFrequency (n : Fin 2 → ℤ) :
    Measurable fun θ : Vec 2 => quietFourierFrequency θ n := by
  unfold quietFourierFrequency
  fun_prop

theorem cellNegSq_measurable (k : ℕ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Measurable fun θ => cellNegSq k θ (planeBlochC θ g) := by
  simp_rw [cellNegSq_eq_tsum k _ hg]
  exact Measurable.tsum fun n => (negBand_measurable k hg).comp
    (measurable_quietFourierFrequency n)

theorem cellLowSq_measurable (ρ : ℝ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    Measurable fun θ => cellLowSq ρ θ (planeBlochC θ g) := by
  simp_rw [cellLowSq_eq_tsum ρ _ hg]
  exact Measurable.tsum fun n => (lowBand_measurable ρ hg).comp
    (measurable_quietFourierFrequency n)

theorem cellNegSq_bridge (k : ℕ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    ∫⁻ θ in freqCube, cellNegSq k θ (planeBlochC θ g) = ∫⁻ ξ, negBandIntegrand k g ξ := by
  rw [tiling _ (negBand_measurable k hg)]
  refine setLIntegral_congr_fun measurableSet_freqCube (fun θ _ => ?_)
  rw [cellNegSq_eq_tsum k θ hg]

theorem cellLowSq_bridge (ρ : ℝ) {g : Vec 2 → ℝ} (hg : Integrable g) :
    ∫⁻ θ in freqCube, cellLowSq ρ θ (planeBlochC θ g) = ∫⁻ ξ, lowBandIntegrand ρ g ξ := by
  rw [tiling _ (lowBand_measurable ρ hg)]
  refine setLIntegral_congr_fun measurableSet_freqCube (fun θ _ => ?_)
  rw [cellLowSq_eq_tsum ρ θ hg]

end AVRegularity.CycleWords.Seam.NegLowBand
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords.Seam

/-! # Composition of cell cutoffs

`s3b_fourierCutoff_comp`: if `μ₂ μ = μ₂`, then `μ₂(D)(μ(D)g) = μ₂(D)g` almost everywhere, for
integrable square-integrable fields with values in a finite-dimensional space. For a real `g`
both sides have the transform `μ₂ ĝ` (`cutoff_base`, `fourierL2_of_integrable`), and the `L²`
transform is injective; a vector field is treated componentwise. -/

open AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard

/-- The integrand of the cutoff of a square-integrable function is integrable. -/
theorem s3b_cutoff_integrand_integrable {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    {g : Vec 2 → E} (hg : MemLp g 2 volume) (y : Vec 2) :
    Integrable (fun x => cutoffKernel m x • g (y - x)) volume := by
  have hk : MemLp (cutoffKernel m) 2 volume := by
    rw [← seamRealCutoffSchwartz_eq m R hm hs]
    exact (seamRealCutoffSchwartz m R hm hs).memLp 2
  have hg' : MemLp (fun x => g (y - x)) 2 volume :=
    hg.comp_measurePreserving ((volume : Measure (Vec 2)).measurePreserving_sub_left y)
  exact memLp_one_iff_integrable.1 (hk.smul hg')

/-- The cutoff commutes with a fixed component. -/
theorem s3b_inner_fourierCutoff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] (m : Vec 2 → ℝ) (R : ℝ) (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : ContDiff ℝ (⊤ : ℕ∞) m) {g : Vec 2 → E} (hg : MemLp g 2 volume) (e : E) (y : Vec 2) :
    inner ℝ e (fourierCutoff m g y) = fourierCutoff m (fun z => inner ℝ e (g z)) y := by
  unfold fourierCutoff
  rw [← integral_inner (s3b_cutoff_integrand_integrable m R hm hs hg y)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [inner_smul_right, smul_eq_mul]

/-- **Composition of cell cutoffs for real functions.** -/
theorem s3b_fourierCutoff_comp_real {μ μ₂ : Vec 2 → ℝ} (hμs : ContDiff ℝ (⊤ : ℕ∞) μ)
    (hμc : HasCompactSupport μ) (hμe : ∀ θ, μ (-θ) = μ θ) (hμ₂s : ContDiff ℝ (⊤ : ℕ∞) μ₂)
    (hμ₂c : HasCompactSupport μ₂) (hμ₂e : ∀ θ, μ₂ (-θ) = μ₂ θ) (hprod : ∀ θ, μ₂ θ * μ θ = μ₂ θ)
    {G : Vec 2 → ℝ} (hG1 : Integrable G) (hG2 : MemLp G 2 volume) :
    fourierCutoff μ₂ (fourierCutoff μ G) =ᵐ[volume] fourierCutoff μ₂ G := by
  obtain ⟨R, hR⟩ := radius' μ hμc
  have hH1 : Integrable (fourierCutoff μ G) := fourierCutoff_integrable μ R hR hμs hG1
  have hH2 : MemLp (fourierCutoff μ G) 2 volume := fourierCutoff_memLp μ R hR hμs hG2
  obtain ⟨hA, eA⟩ := cutoff_base μ₂ hμ₂s hμ₂c hμ₂e hH1 hH2
  obtain ⟨hB, eB⟩ := cutoff_base μ₂ hμ₂s hμ₂c hμ₂e hG1 hG2
  obtain ⟨hC, eH⟩ := cutoff_base μ hμs hμc hμe hG1 hG2
  have eH' := fourierL2_of_integrable hH1 hH2
  -- the two transforms agree
  have hFT : fourierL2 (ofRealL2 volume (hA.toLp (fourierCutoff μ₂ (fourierCutoff μ G)))) =
      fourierL2 (ofRealL2 volume (hB.toLp (fourierCutoff μ₂ G))) := by
    refine Lp.ext ?_
    filter_upwards [eA, eB, eH, eH'] with x h1 h2 h3 h4
    rw [h1, h2, ← h4, h3, ← mul_assoc, ← Complex.ofReal_mul, hprod]
  have hL := (fourierL2 (F := ℂ)).injective hFT
  have h1 := ofRealL2_ae volume (hA.toLp (fourierCutoff μ₂ (fourierCutoff μ G)))
  have h2 := ofRealL2_ae volume (hB.toLp (fourierCutoff μ₂ G))
  rw [hL] at h1
  filter_upwards [h1, h2, hA.coeFn_toLp, hB.coeFn_toLp] with x hx1 hx2 hx3 hx4
  rw [← hx3, ← hx4]
  exact_mod_cast hx1.symm.trans hx2

/-- **Composition of cell cutoffs.** If `μ₂ μ = μ₂`, then `μ₂(D)(μ(D)g) = μ₂(D)g` almost
everywhere. -/
theorem s3b_fourierCutoff_comp {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E] {μ μ₂ : Vec 2 → ℝ}
    (hμs : ContDiff ℝ (⊤ : ℕ∞) μ) (hμc : HasCompactSupport μ) (hμe : ∀ θ, μ (-θ) = μ θ)
    (hμ₂s : ContDiff ℝ (⊤ : ℕ∞) μ₂) (hμ₂c : HasCompactSupport μ₂) (hμ₂e : ∀ θ, μ₂ (-θ) = μ₂ θ)
    (hprod : ∀ θ, μ₂ θ * μ θ = μ₂ θ) {g : Vec 2 → E} (hg1 : Integrable g)
    (hg2 : MemLp g 2 volume) :
    fourierCutoff μ₂ (fourierCutoff μ g) =ᵐ[volume] fourierCutoff μ₂ g := by
  obtain ⟨R, hR⟩ := radius' μ hμc
  obtain ⟨R₂, hR₂⟩ := radius' μ₂ hμ₂c
  have hH2 : MemLp (fourierCutoff μ g) 2 volume := by
    have h := seamFourierCutoff_memLp μ R hR hμs (hg2.toLp g)
    rwa [fourierCutoff_congr_ae' μ hg2.coeFn_toLp] at h
  let b := (stdOrthonormalBasis ℝ E).toBasis
  have hcomp : ∀ i, (fun y => inner ℝ (b i) (fourierCutoff μ₂ (fourierCutoff μ g) y)) =ᵐ[volume]
      fun y => inner ℝ (b i) (fourierCutoff μ₂ g y) := by
    intro i
    have hGi1 : Integrable fun z => inner ℝ (b i) (g z) := hg1.const_inner (b i)
    have hGi2 : MemLp (fun z => inner ℝ (b i) (g z)) 2 volume := hg2.const_inner (b i)
    have hreal := s3b_fourierCutoff_comp_real hμs hμc hμe hμ₂s hμ₂c hμ₂e hprod hGi1 hGi2
    have hl : (fun y => inner ℝ (b i) (fourierCutoff μ₂ (fourierCutoff μ g) y)) =
        fourierCutoff μ₂ (fourierCutoff μ fun z => inner ℝ (b i) (g z)) := by
      funext y
      rw [s3b_inner_fourierCutoff μ₂ R₂ hR₂ hμ₂s hH2 (b i) y]
      congr 1
      funext z
      exact s3b_inner_fourierCutoff μ R hR hμs hg2 (b i) z
    have hr : (fun y => inner ℝ (b i) (fourierCutoff μ₂ g y)) =
        fourierCutoff μ₂ fun z => inner ℝ (b i) (g z) := by
      funext y
      exact s3b_inner_fourierCutoff μ₂ R₂ hR₂ hμ₂s hg2 (b i) y
    rw [hl, hr]
    exact hreal
  filter_upwards [ae_all_iff.2 hcomp] with y hy
  exact InnerProductSpace.ext_inner_left_basis b hy

end AVRegularity.CycleWords.Seam
end
end

section
/-! # Plancherel for the jets of `m(D) g` and the pairing `⟨g, m(D) g⟩`

For `g ∈ L¹ ∩ L²` and an even smooth compactly supported multiplier `m ≥ 0`:
* `∫ |D^w m(D)g|² = (2π)⁻² ∫ |ξ^w|² m² |ĝ|²`, and the sum over the words of length `l` is
  `(2π)⁻² ∫ |ξ|^{2l} m² |ĝ|²`;
* `∫ g · m(D)g = (2π)⁻² ∫ m |ĝ|²`.
-/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard
open AVRegularity.CoupledEnergyPlane.Fourier
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam.NegLowBand

/-- Plancherel for a real `L²` function with a given transform. -/
theorem plancherel_of_hasFT {v : Vec 2 → ℝ} {Φ : Vec 2 → ℂ} (hv : HasFT v Φ)
    (hΦ : Measurable Φ) :
    ∫⁻ z, ENNReal.ofReal (v z ^ 2) =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, ‖Φ ξ‖ₑ ^ 2 := by
  obtain ⟨hv2, hft⟩ := hv
  set g : Lp ℂ 2 (volume : Measure (Vec 2)) := ofRealL2 volume (hv2.toLp v) with hg
  have hn : eLpNorm g 2 volume = eLpNorm (fourierL2 g) 2 volume := by
    have h := fourierL2_norm g
    rw [Lp.norm_def, Lp.norm_def] at h
    exact ((ENNReal.toReal_eq_toReal_iff' (Lp.eLpNorm_ne_top _) (Lp.eLpNorm_ne_top _)).mp h).symm
  have h1 : eLpNorm g 2 volume ^ 2 = ∫⁻ z, ENNReal.ofReal (v z ^ 2) := by
    rw [eLpNorm_two_sq' _ (Lp.aestronglyMeasurable g)]
    apply lintegral_congr_ae
    filter_upwards [ofRealL2_ae volume (hv2.toLp v), hv2.coeFn_toLp] with z h1 h2
    rw [hg, h1, h2, ← ofReal_norm, Complex.norm_real, Real.norm_eq_abs,
      ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  have h2 : eLpNorm (fourierL2 g) 2 volume ^ 2 =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, ‖Φ ξ‖ₑ ^ 2 := by
    rw [eLpNorm_two_sq' _ (Lp.aestronglyMeasurable _),
      ← lintegral_dilate (fun ξ => ‖Φ ξ‖ₑ ^ 2) (hΦ.enorm.pow_const 2)]
    apply lintegral_congr_ae
    filter_upwards [hft] with x hx
    rw [hx]
  rw [← h1, hn, h2]

theorem symbol_sq_sum (a : ℕ) (ξ : Vec 2) :
    ∑ w : DerivativeWord2 a, ‖derivativeWordSymbol w ξ‖ ^ 2 = (ξ 0 ^ 2 + ξ 1 ^ 2) ^ a := by
  have h1 : ∀ w : DerivativeWord2 a, ‖derivativeWordSymbol w ξ‖ ^ 2 = ∏ j : Fin a, ξ (w j) ^ 2 := by
    intro w
    unfold derivativeWordSymbol
    rw [norm_prod, ← Finset.prod_pow]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [norm_mul, Complex.norm_I, one_mul, Complex.norm_real, Real.norm_eq_abs, sq_abs]
  simp_rw [h1]
  have := Finset.prod_univ_sum (fun _ : Fin a => (Finset.univ : Finset (Fin 2)))
    (fun _ c => ξ c ^ 2)
  rw [Fintype.piFinset_univ] at this
  rw [← this]
  simp [Fin.sum_univ_two]

/-- The transform of a derivative of `m(D) g`, squared, integrated. -/
theorem jet_plancherel (m : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) m) (hc : HasCompactSupport m)
    (hev : ∀ θ, m (-θ) = m θ) {g : Vec 2 → ℝ} (hg : Integrable g) (hg2 : MemLp g 2 volume)
    {a : ℕ} (w : DerivativeWord2 a) :
    ∫⁻ z, ENNReal.ofReal (orderedDerivative w (fourierCutoff m g) z ^ 2) =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ,
        ‖derivativeWordSymbol w ξ * ((m ξ : ℂ) * planeTransform g ξ)‖ₑ ^ 2 := by
  have hF := cutoff_fourier m hs hc hev hg hg2 _ w
  refine plancherel_of_hasFT hF ?_
  have : Continuous fun ξ : Vec 2 => derivativeWordSymbol w ξ * ((m ξ : ℂ) * planeTransform g ξ) :=
    (symbol_continuous w).mul ((Complex.continuous_ofReal.comp hs.continuous).mul
      (Ft_continuous hg))
  exact this.measurable

/-- The sum over the words of length `l`. -/
theorem jets_plancherel (m : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) m) (hc : HasCompactSupport m)
    (hev : ∀ θ, m (-θ) = m θ) {g : Vec 2 → ℝ} (hg : Integrable g) (hg2 : MemLp g 2 volume)
    (l : ℕ) :
    ∑ w : DerivativeWord2 l, ∫⁻ z, ENNReal.ofReal (orderedDerivative w (fourierCutoff m g) z ^ 2) =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ,
        ENNReal.ofReal ((ξ 0 ^ 2 + ξ 1 ^ 2) ^ l * m ξ ^ 2) * ‖planeTransform g ξ‖ₑ ^ 2 := by
  have hmeas : ∀ w : DerivativeWord2 l, Measurable fun ξ : Vec 2 =>
      ‖derivativeWordSymbol w ξ * ((m ξ : ℂ) * planeTransform g ξ)‖ₑ ^ 2 := by
    intro w
    have : Continuous fun ξ : Vec 2 => derivativeWordSymbol w ξ * ((m ξ : ℂ) * planeTransform g ξ) :=
      (symbol_continuous w).mul ((Complex.continuous_ofReal.comp hs.continuous).mul
        (Ft_continuous hg))
    exact this.measurable.enorm.pow_const 2
  simp_rw [jet_plancherel m hs hc hev hg hg2]
  rw [← Finset.mul_sum, ← lintegral_finsetSum _ fun w _ => hmeas w]
  congr 1
  refine lintegral_congr fun ξ => ?_
  have h1 : ∀ w : DerivativeWord2 l, ‖derivativeWordSymbol w ξ * ((m ξ : ℂ) * planeTransform g ξ)‖ₑ ^ 2 =
      ENNReal.ofReal (‖derivativeWordSymbol w ξ‖ ^ 2) * (ENNReal.ofReal (m ξ ^ 2) * ‖planeTransform g ξ‖ₑ ^ 2) := by
    intro w
    have e1 : ‖derivativeWordSymbol w ξ‖ₑ ^ 2 = ENNReal.ofReal (‖derivativeWordSymbol w ξ‖ ^ 2) := by
      rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
    have e2 : ‖(m ξ : ℂ)‖ₑ ^ 2 = ENNReal.ofReal (m ξ ^ 2) := by
      rw [← ofReal_norm, Complex.norm_real, Real.norm_eq_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
        sq_abs]
    calc ‖derivativeWordSymbol w ξ * ((m ξ : ℂ) * planeTransform g ξ)‖ₑ ^ 2
        = (‖derivativeWordSymbol w ξ‖ₑ * (‖(m ξ : ℂ)‖ₑ * ‖planeTransform g ξ‖ₑ)) ^ 2 := by
          rw [enorm_mul, enorm_mul]
      _ = ‖derivativeWordSymbol w ξ‖ₑ ^ 2 * (‖(m ξ : ℂ)‖ₑ ^ 2 * ‖planeTransform g ξ‖ₑ ^ 2) := by ring
      _ = _ := by rw [e1, e2]
  simp_rw [h1]
  rw [← Finset.sum_mul, ← ENNReal.ofReal_sum_of_nonneg fun w _ => sq_nonneg _, symbol_sq_sum,
    ← mul_assoc, ← ENNReal.ofReal_mul (pow_nonneg (by positivity) _)]

/-- The pairing as a plane integral of the transform. -/
theorem pairing_eq_integral (m : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hc : HasCompactSupport m) (hev : ∀ θ, m (-θ) = m θ) {g : Vec 2 → ℝ} (hg : Integrable g)
    (hg2 : MemLp g 2 volume) :
    (∫ z, g z * fourierCutoff m g z =
      ∫ x : Vec 2, m ((2 * Real.pi) • x) * ‖planeTransform g ((2 * Real.pi) • x)‖ ^ 2) ∧
    Integrable (fun x : Vec 2 => m ((2 * Real.pi) • x) *
      ‖planeTransform g ((2 * Real.pi) • x)‖ ^ 2) volume := by
  obtain ⟨hh, hft⟩ := cutoff_base m hs hc hev hg hg2
  have hgft := fourierL2_of_integrable hg hg2
  set G : Lp ℂ 2 (volume : Measure (Vec 2)) := ofRealL2 volume (hg2.toLp g) with hG
  set V : Lp ℂ 2 (volume : Measure (Vec 2)) :=
    ofRealL2 volume (hh.toLp (fourierCutoff m g)) with hV
  have hinner : (inner ℂ G V).re = ∫ z, g z * fourierCutoff m g z := by
    rw [hG, hV, ofRealL2_inner_re, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hg2.coeFn_toLp, hh.coeFn_toLp] with z h1 h2
    rw [h1, h2]
    simp [RCLike.inner_apply, mul_comm]
  have hpl : inner ℂ G V = inner ℂ (fourierL2 G) (fourierL2 V) := (fourierL2_inner G V).symm
  have hkey : ∀ᵐ x : Vec 2, (inner ℂ (fourierL2 G x) (fourierL2 V x)).re =
      m ((2 * Real.pi) • x) * ‖planeTransform g ((2 * Real.pi) • x)‖ ^ 2 := by
    filter_upwards [hgft, hft] with x h1 h2
    rw [h1, h2]
    simp only [RCLike.inner_apply]
    rw [show ((m ((2 * Real.pi) • x) : ℂ) * planeTransform g ((2 * Real.pi) • x)) *
        (starRingEnd ℂ) (planeTransform g ((2 * Real.pi) • x)) =
      (m ((2 * Real.pi) • x) : ℂ) * ((planeTransform g ((2 * Real.pi) • x)) *
        (starRingEnd ℂ) (planeTransform g ((2 * Real.pi) • x))) by ring, Complex.mul_conj,
      Complex.normSq_eq_norm_sq]
    rw [← Complex.ofReal_mul]
    exact Complex.ofReal_re _
  have hint : Integrable (fun x : Vec 2 => (inner ℂ (fourierL2 G x) (fourierL2 V x)).re) volume := by
    have := (L2.integrable_inner (𝕜 := ℂ) (fourierL2 G) (fourierL2 V)).re
    simpa using this
  have hre : (inner ℂ (fourierL2 G) (fourierL2 V)).re =
      ∫ x, (inner ℂ (fourierL2 G x) (fourierL2 V x)).re := by
    rw [L2.inner_def]
    simpa [RCLike.re_to_complex] using
      (integral_re (𝕜 := ℂ) (L2.integrable_inner (𝕜 := ℂ) (fourierL2 G) (fourierL2 V))).symm
  refine ⟨?_, hint.congr hkey⟩
  rw [← hinner, hpl, hre]
  exact integral_congr_ae hkey

theorem pairing_nonneg (m : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) m)
    (hc : HasCompactSupport m) (hev : ∀ θ, m (-θ) = m θ) (hm0 : ∀ ξ, 0 ≤ m ξ) {g : Vec 2 → ℝ}
    (hg : Integrable g) (hg2 : MemLp g 2 volume) : 0 ≤ ∫ z, g z * fourierCutoff m g z := by
  rw [(pairing_eq_integral m hs hc hev hg hg2).1]
  exact integral_nonneg fun x => mul_nonneg (hm0 _) (sq_nonneg _)

/-- **The pairing** `∫ g · m(D)g = (2π)⁻² ∫ m |ĝ|²`. -/
theorem pairing_eq (m : Vec 2 → ℝ) (hs : ContDiff ℝ (⊤ : ℕ∞) m) (hc : HasCompactSupport m)
    (hev : ∀ θ, m (-θ) = m θ) (hm0 : ∀ ξ, 0 ≤ m ξ) {g : Vec 2 → ℝ} (hg : Integrable g)
    (hg2 : MemLp g 2 volume) :
    ENNReal.ofReal (∫ z, g z * fourierCutoff m g z) =
      ENNReal.ofReal (((2 * Real.pi) ^ 2)⁻¹) * ∫⁻ ξ, ENNReal.ofReal (m ξ) * ‖planeTransform g ξ‖ₑ ^ 2 := by
  obtain ⟨h1, hint2⟩ := pairing_eq_integral m hs hc hev hg hg2
  rw [h1, ofReal_integral_eq_lintegral_ofReal hint2
    (Filter.Eventually.of_forall fun x => mul_nonneg (hm0 _) (sq_nonneg _))]
  have hF : Measurable fun ξ : Vec 2 => ENNReal.ofReal (m ξ) * ‖planeTransform g ξ‖ₑ ^ 2 :=
    (ENNReal.measurable_ofReal.comp hs.continuous.measurable).mul
      ((Ft_continuous hg).measurable.enorm.pow_const 2)
  rw [← lintegral_dilate _ hF]
  refine lintegral_congr fun x => ?_
  rw [ENNReal.ofReal_mul (hm0 _), ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

end AVRegularity.CycleWords.Seam.NegLowBand
end
end

section
/-! # The stage data at the start of a frame

For a functional `Q` of the Bloch parts (the negative norm or the low band) which depends only on
the class on the cell, scales quadratically and vanishes on zero, the sum of `Q` over the scaled
stage values at the start of the frame is at most
`∑_β ∑_x π_x⁻¹ (ϖ^{|β|}/β!)² ∑_e Q(B_θ(y^β ⟨b_e, φ_x⟩))`
(only the level `0` stages contribute; `StageDatumStatement` is the same with `Q = ‖·‖²_{L²}`).
-/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
  AVRegularity.CycleWords.Assembly
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam.NegLowBand

universe u v

open AVRegularity.CycleWords.Discard.BandDatum AVRegularity.CycleWords.Discard

section Frame

variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw m : ℕ} {Ks : Fin Nw → ℕ}

variable (Q : (Vec 2 → ℂ) → ℝ≥0∞)
  (hQae : ∀ f g : Vec 2 → ℂ, f =ᵐ[volume.restrict AVenhance.unitCube] g → Q f = Q g)
  (hQmul : ∀ (s : ℝ) (f : Vec 2 → ℂ), Q (fun z => (s : ℂ) * f z) = ENNReal.ofReal (s ^ 2) * Q f)
  (hQ0 : Q (fun _ => 0) = 0)

include hQae hQ0 in
theorem stageQ_level_succ {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2)
    (i : B1WIndex ι h Nw m Ks) (hi : i.1 ≠ 0) : Q (stageScaled F θ i F.a) = 0 := by
  have h0 := frame_initial_level_succ F θ i.1 hi i.2.1 (b1wVec i) (b1wMom i)
  rw [← hQ0]
  refine hQae _ _ ?_
  filter_upwards [h0] with z hz
  have hz' : planeBlochC θ (fun y => momentWeight (b1wMom i) y *
      inner ℝ (b1wVec i) (planeValue (F.u i.1 i.2.1 F.a) y)) z = 0 := hz
  simp [stageScaled, b1wStageVal, b1wStageFun, hz']

include hQae hQmul in
theorem stageQ_level_zero_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) (x : ι)
    (β : ℕ × ℕ) (hβ : β ∈ momentIndices (b1wLevelMoments m Ks 0)) :
    ∑ e : Fin (Module.finrank ℝ (h x)), Q (stageScaled F θ ⟨0, x, ⟨β, hβ⟩, e⟩ F.a) ≤
      ENNReal.ofReal ((F.π x)⁻¹) *
        ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        ∑ e : Fin (Module.finrank ℝ (h x)), Q (planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y))) := by
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun e _ => ?_
  set i : B1WIndex ι h Nw m Ks := ⟨0, x, ⟨β, hβ⟩, e⟩ with hi
  have h0 := frame_initial_level_zero F θ x (b1wVec i) (b1wMom i)
  set s : ℝ := (F.π x ^ (-(1 / 2 : ℝ)) * F.ϖ ^ (β.1 + β.2) /
    ((β.1.factorial * β.2.factorial : ℕ) : ℝ) * (b1wAmp F.ηg F.letters 0)⁻¹) with hs
  have hamp : b1wAmp F.ηg F.letters (0 : Fin (Nw + 1)) = 1 := by
    simp [b1wAmp]
  have hae : stageScaled F θ i F.a =ᵐ[volume.restrict AVenhance.unitCube]
      fun z => (s : ℂ) * planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y)) z := by
    filter_upwards [h0] with z hz
    have hz' : planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) e) (planeValue (F.u 0 x F.a) y)) z =
        planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y)) z := hz
    have hsv : stageScaled F θ i F.a z = (s : ℂ) * planeBlochC θ (fun y => momentWeight β y *
        inner ℝ (stdOrthonormalBasis ℝ (h x) e) (planeValue (F.u 0 x F.a) y)) z := rfl
    rw [hsv, hz']
  rw [hQae _ _ hae, hQmul]
  gcongr
  have hs2 : s ^ 2 = (F.π x ^ (-(1 / 2 : ℝ))) ^ 2 *
      (F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2 := by
    rw [hs, hamp]; simp only [inv_one, mul_one]; rw [mul_div_assoc, mul_pow]
  rw [hs2, ENNReal.ofReal_mul (sq_nonneg _)]
  exact mul_le_mul_left (rpow_neg_half_sq_le _) _

include hQae hQmul hQ0 in
theorem stageQ_sum_le {K : ScalarConstants} {g₁ : ℝ}
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁) (θ : Vec 2) :
    ∑ i : B1WIndex ι h Nw m Ks, Q (stageScaled F θ i F.a) ≤
      ∑ β ∈ momentIndices (wordReserveN m Ks), ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
        ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
        ∑ e : Fin (Module.finrank ℝ (h x)), Q (planeBlochC θ (fun y => momentWeight β y *
          inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y))) := by
  simp only [Fintype.sum_sigma, Fintype.sum_prod_type]
  rw [Fin.sum_univ_succ]
  have hz : ∀ j : Fin Nw, (∑ x : ι, ∑ β : {β : ℕ × ℕ // β ∈ momentIndices
      (b1wLevelMoments m Ks j.succ)}, ∑ e : Fin (Module.finrank ℝ (h x)),
        Q (stageScaled F θ (⟨j.succ, x, β, e⟩ : B1WIndex ι h Nw m Ks) F.a)) = 0 := by
    intro j
    refine Finset.sum_eq_zero fun x _ => Finset.sum_eq_zero fun β _ =>
      Finset.sum_eq_zero fun e _ => ?_
    exact stageQ_level_succ Q hQae hQ0 F θ ⟨j.succ, x, β, e⟩ (Fin.succ_ne_zero j)
  rw [Finset.sum_eq_zero fun j _ => hz j, add_zero]
  calc _ ≤ ∑ x : ι, ∑ β : {β : ℕ × ℕ // β ∈ momentIndices (b1wLevelMoments m Ks 0)},
        ENNReal.ofReal ((F.π x)⁻¹) *
          ENNReal.ofReal ((F.ϖ ^ (β.1.1 + β.1.2) /
            ((β.1.1.factorial * β.1.2.factorial : ℕ) : ℝ)) ^ 2) *
          ∑ e : Fin (Module.finrank ℝ (h x)), Q (planeBlochC θ (fun y => momentWeight β.1 y *
            inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y))) :=
        Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun β _ =>
          stageQ_level_zero_le Q hQae hQmul F θ x β.1 β.2
    _ = ∑ β ∈ momentIndices (b1wLevelMoments m Ks 0), ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
          ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) /
            ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
          ∑ e : Fin (Module.finrank ℝ (h x)), Q (planeBlochC θ (fun y => momentWeight β y *
            inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y))) := by
        rw [Finset.sum_comm]
        exact Finset.sum_coe_sort (momentIndices (b1wLevelMoments m Ks 0))
          (fun β => ∑ x : ι, ENNReal.ofReal ((F.π x)⁻¹) *
            ENNReal.ofReal ((F.ϖ ^ (β.1 + β.2) /
              ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) ^ 2) *
            ∑ e : Fin (Module.finrank ℝ (h x)), Q (planeBlochC θ (fun y => momentWeight β y *
              inner ℝ (stdOrthonormalBasis ℝ (h x) e) (F.φ x y))))
    _ = _ := by rw [b1wLevelMoments_zero]

end Frame

end AVRegularity.CycleWords.Seam.NegLowBand
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # The cell-scale low pass is lossless

`cellLowPassMoment : CellLowPassMomentStatement`. The statement is for `G_x ∈ L²` (not
necessarily measurable representatives): replace `G` by a measurable version, which changes
neither `μ(D)G` nor the negative jet norm.
-/

open AVRegularity.CycleWords.Seam.NegLowBand AVRegularity.CycleWords.Seam.YoungKernel

universe u v

/-- The negative jet norm does not see null sets of the datum. -/
theorem negJetNorm_congr_ae' {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] (π : ι → ℝ) (p : ℝ)
    (j : ℕ) (s r : ℝ) {G G' : ∀ x, Vec 2 → h x} (hG : ∀ x, G x =ᵐ[volume] G' x) :
    AVRegularity.CycleWords.Assembly.negJetNorm π p j s r G =
      AVRegularity.CycleWords.Assembly.negJetNorm π p j s r G' := by
  unfold AVRegularity.CycleWords.Assembly.negJetNorm
  refine iSup_congr fun φ => iSup_congr fun hφ => iSup_congr fun hb => ?_
  congr 2
  refine Finset.sum_congr rfl fun x _ => ?_
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hG x] with z hz
  rw [hz]

/-- **The cell low pass.** The cell-scale low pass is lossless. -/
theorem cellLowPassMoment : CellLowPassMomentStatement.{u, v} := by
  intro n k μ hs hc hev hm
  obtain ⟨C, hC, hcore⟩ := moment_le_core.{u, v} hm hs n k
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ ϖ hϖ0 hϖ1 G hG
  let G' : ∀ x, Vec 2 → h x := fun x => (hG x).aestronglyMeasurable.mk (G x)
  have hG'm : ∀ x, Measurable (G' x) := fun x =>
    (hG x).aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hae : ∀ x, G x =ᵐ[volume] G' x := fun x => (hG x).aestronglyMeasurable.ae_eq_mk
  have hG'2 : ∀ x, MemLp (G' x) 2 volume := fun x => (hG x).ae_eq (hae x)
  have e1 : (fun x => fourierCutoff μ (G x)) = fun x => conv (cutoffKernel μ) (G' x) := by
    funext x
    exact conv_congr_ae _ (hae x)
  rw [e1, negJetNorm_congr_ae' π (n : ℝ) k ϖ 1 hae]
  exact hcore π hπ ϖ hϖ0 hϖ1 G' hG'm hG'2

end AVRegularity.CycleWords.Seam
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open scoped ENNReal SchwartzMap
namespace AVRegularity.CycleWords.Seam

/-! # Low-pass moments: the low pass of a field of finite negative norm has finite moments

`seamLowPassMoment : SeamLowPassMomentStatement`.

Proof (duality, on balls). Fix a moment monomial `w = (ϖz₀)^{β₁}(ϖz₁)^{β₂}`, `|β| ≤ n`, a radius
`R`, and put `u = 1_{B_R} w F`, `χ = w u` for the low pass `F = μ(D)G`. Then
`∑_v π_v⁻¹ ‖u_v‖₂² = ∑_v π_v⁻¹ ⟨F_v, χ_v⟩ = ∑_v π_v⁻¹ ⟨G_v, μ(D)χ_v⟩` (the cutoff is symmetric,
`integral_inner_fourierCutoff_comm`). The test `μ(D)χ` is smooth, and its test norm of weight
`-n` is at most `C ‖⟨ϖz⟩^{-n} χ‖₂ ≤ C ‖u‖₂` (`weightedJetNorm_conv_le`; `⟨ϖz⟩^{-n}|w| ≤ 1`), so the
negative norm bounds the pairing (`pair_le_of_test`): `‖u‖² ≤ C' ‖u‖ · negJet(G)`, a bound
uniform in `R` (`lowPass_ball_le`). Monotone convergence in `R` gives `w F_v ∈ L²`. -/

open AVRegularity.CycleWords.Assembly

universe u v

section Weights

/-- The moment monomial `(ϖz₀)^{β₁}(ϖz₁)^{β₂}` of `momentNorm`. -/
def MomW (ϖ : ℝ) (β : ℕ × ℕ) (z : Vec 2) : ℝ := (ϖ * z 0) ^ β.1 * (ϖ * z 1) ^ β.2

theorem MomW_continuous (ϖ : ℝ) (β : ℕ × ℕ) : Continuous (MomW ϖ β) := by
  unfold MomW
  fun_prop

theorem abs_coord_le_sqrt' (ϖ : ℝ) (z : Vec 2) (i : Fin 2) :
    |ϖ * z i| ≤ Real.sqrt (cutoffBracket ϖ z) := by
  rw [← Real.sqrt_sq_eq_abs]
  refine Real.sqrt_le_sqrt ?_
  have hs : z i ^ 2 ≤ z 0 ^ 2 + z 1 ^ 2 := by
    have := Finset.single_le_sum (f := fun j => z j ^ 2) (fun j _ => sq_nonneg (z j))
      (Finset.mem_univ i)
    simpa [Fin.sum_univ_two] using this
  unfold cutoffBracket
  rw [mul_pow]
  nlinarith [mul_le_mul_of_nonneg_left hs (sq_nonneg ϖ)]

theorem abs_momW_le_sqrt (ϖ : ℝ) (β : ℕ × ℕ) (z : Vec 2) :
    |MomW ϖ β z| ≤ Real.sqrt (cutoffBracket ϖ z) ^ (β.1 + β.2) := by
  unfold MomW
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (abs_coord_le_sqrt' ϖ z 0) _)
    (pow_le_pow_left₀ (abs_nonneg _) (abs_coord_le_sqrt' ϖ z 1) _) (by positivity)
    (by positivity)

/-- `⟨ϖz⟩^{-n} |w_β(z)| ≤ 1` for `|β| ≤ n`. -/
theorem weight_mul_momW_le (ϖ : ℝ) {n : ℕ} {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ n) (z : Vec 2) :
    cutoffBracket ϖ z ^ (-(n : ℝ) / 2) * |MomW ϖ β z| ≤ 1 := by
  have hc1 := cutoffBracket_one_le ϖ z
  have hc0 : 0 < cutoffBracket ϖ z := zero_lt_one.trans_le hc1
  have hs1 : 1 ≤ Real.sqrt (cutoffBracket ϖ z) := Real.one_le_sqrt.2 hc1
  have h1 : |MomW ϖ β z| ≤ cutoffBracket ϖ z ^ ((n : ℝ) / 2) := by
    refine (abs_momW_le_sqrt ϖ β z).trans ?_
    refine (pow_le_pow_right₀ hs1 hβ).trans (le_of_eq ?_)
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hc0.le]
    ring_nf
  calc cutoffBracket ϖ z ^ (-(n : ℝ) / 2) * |MomW ϖ β z|
      ≤ cutoffBracket ϖ z ^ (-(n : ℝ) / 2) * cutoffBracket ϖ z ^ ((n : ℝ) / 2) :=
        mul_le_mul_of_nonneg_left h1 (weight_nonneg' ϖ _ z)
    _ = 1 := by
        rw [← Real.rpow_add hc0]
        ring_nf
        exact Real.rpow_zero _

/-- The monomial on a ball. -/
theorem abs_momW_le_ball (ϖ : ℝ) (β : ℕ × ℕ) {R : ℝ} {z : Vec 2}
    (hz : z ∈ Metric.closedBall (0 : Vec 2) R) :
    |MomW ϖ β z| ≤ (|ϖ| * R) ^ (β.1 + β.2) := by
  have hzR : ‖z‖ ≤ R := by simpa using hz
  have hc : ∀ i, |ϖ * z i| ≤ |ϖ| * R := fun i => by
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Real.norm_eq_abs (z i) ▸ norm_le_pi_norm z i).trans hzR)
      (abs_nonneg ϖ)
  unfold MomW
  rw [abs_mul, abs_pow, abs_pow, pow_add]
  exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) (hc 0) _)
    (pow_le_pow_left₀ (abs_nonneg _) (hc 1) _) (by positivity)
    (pow_nonneg ((abs_nonneg _).trans (hc 0)) _)

end Weights

section Ball

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, CompleteSpace (h i)]

/-- The constant of the ball estimate. -/
def BallConst (μ : Vec 2 → ℝ) (hμs : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (hμ : ContDiff ℝ (⊤ : ℕ∞) μ) (ϖ : ℝ) (n L : ℕ) : ℝ :=
  CutConst L * (TestConst (seamRealCutoffSchwartz μ (Real.pi / 2) hμs hμ) ϖ ϖ⁻¹ n L + 1)

/-- **The moments of the low pass on a ball**, uniformly in the radius. -/
theorem lowPass_ball_le (μ : Vec 2 → ℝ) (hμ : ContDiff ℝ (⊤ : ℕ∞) μ)
    (hμs : ∀ ξ, Real.pi / 2 ≤ Real.sqrt (vecDot ξ ξ) → μ ξ = 0)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (n L : ℕ) {ϖ : ℝ} (hϖ : 0 < ϖ)
    (G : ∀ x, Vec 2 → h x) (hG : ∀ x, MemLp (G x) 2 volume)
    {β : ℕ × ℕ} (hβ : β.1 + β.2 ≤ n) (R : ℝ) :
    familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm
        ((Metric.closedBall (0 : Vec 2) R).indicator
          (fun z => MomW ϖ β z • fourierCutoff μ (G x) z)) 2 volume) ≤
      ENNReal.ofReal (BallConst μ hμs hμ ϖ n L) * negJetNorm π n L ϖ ϖ⁻¹ G := by
  set B := Metric.closedBall (0 : Vec 2) R with hB
  have hBm : MeasurableSet B := Metric.isClosed_closedBall.measurableSet
  set k := seamRealCutoffSchwartz μ (Real.pi / 2) hμs hμ with hk
  set F : ∀ x, Vec 2 → h x := fun x => fourierCutoff μ (G x) with hFd
  set w := MomW ϖ β with hw
  have hwc : Continuous w := MomW_continuous ϖ β
  have hF2 : ∀ x, MemLp (F x) 2 volume := fun x =>
    fourierCutoff_memLp_of_memLp μ _ hμs hμ (hG x)
  set A : ℝ := (|ϖ| * |R|) ^ (β.1 + β.2) with hA
  have hA0 : 0 ≤ A := by positivity
  have hwB : ∀ z ∈ B, |w z| ≤ A := fun z hz =>
    (abs_momW_le_ball ϖ β hz).trans (pow_le_pow_left₀ (by
      have : 0 ≤ ‖z‖ := norm_nonneg z
      have h' : ‖z‖ ≤ R := by simpa [hB] using hz
      exact mul_nonneg (abs_nonneg ϖ) (this.trans h')) (mul_le_mul_of_nonneg_left
        (le_abs_self R) (abs_nonneg ϖ)) _)
  set u : ∀ x, Vec 2 → h x := fun x => B.indicator (fun z => w z • F x z) with hud
  set χ : ∀ x, Vec 2 → h x := fun x z => w z • u x z with hχd
  have hum : ∀ x, AEStronglyMeasurable (u x) volume := fun x =>
    (hwc.aestronglyMeasurable.smul (hF2 x).aestronglyMeasurable).indicator hBm
  have hχm : ∀ x, AEStronglyMeasurable (χ x) volume := fun x =>
    hwc.aestronglyMeasurable.smul (hum x)
  have hu_le : ∀ x z, ‖u x z‖ ≤ A * ‖B.indicator (F x) z‖ := by
    intro x z
    by_cases hz : z ∈ B
    · simp only [hud, Set.indicator_of_mem hz, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hwB z hz) (norm_nonneg _)
    · simp only [hud, Set.indicator_of_notMem hz, norm_zero, mul_zero, le_refl]
  have hχ_le : ∀ x z, ‖χ x z‖ ≤ A * ‖u x z‖ := by
    intro x z
    by_cases hz : z ∈ B
    · simp only [hχd, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hwB z hz) (norm_nonneg _)
    · simp only [hχd, hud, Set.indicator_of_notMem hz, smul_zero, norm_zero, mul_zero, le_refl]
  have hFB2 : ∀ x, MemLp (B.indicator (F x)) 2 volume := fun x => (hF2 x).indicator hBm
  have hFB1 : ∀ x, Integrable (B.indicator (F x)) volume := by
    intro x
    have : IsFiniteMeasure (volume.restrict B) :=
      isFiniteMeasure_restrict.2 (measure_closedBall_lt_top (x := (0 : Vec 2)) (r := R)).ne
    exact IntegrableOn.integrable_indicator (((hF2 x).restrict B).integrable one_le_two) hBm
  have hu2 : ∀ x, MemLp (u x) 2 volume := fun x =>
    ((hFB2 x).const_smul A).of_le (hum x) (Eventually.of_forall fun z => by
      show ‖u x z‖ ≤ ‖A • B.indicator (F x) z‖
      rw [norm_smul A, Real.norm_eq_abs, abs_of_nonneg hA0]
      exact hu_le x z)
  have hu1 : ∀ x, Integrable (u x) volume := fun x =>
    ((hFB1 x).norm.const_mul A).mono' (hum x) (Eventually.of_forall fun z => hu_le x z)
  have hχ2 : ∀ x, MemLp (χ x) 2 volume := fun x =>
    ((hu2 x).const_smul A).of_le (hχm x) (Eventually.of_forall fun z => by
      show ‖χ x z‖ ≤ ‖A • u x z‖
      rw [norm_smul A, Real.norm_eq_abs, abs_of_nonneg hA0]
      exact hχ_le x z)
  have hχ1 : ∀ x, Integrable (χ x) volume := fun x =>
    ((hu1 x).norm.const_mul A).mono' (hχm x) (Eventually.of_forall fun z => hχ_le x z)
  -- the pairing is the squared norm
  have hpt : ∀ x z, inner ℝ (F x z) (χ x z) = ‖u x z‖ ^ 2 := by
    intro x z
    by_cases hz : z ∈ B
    · simp only [hχd, hud, Set.indicator_of_mem hz, real_inner_smul_right, norm_smul,
        Real.norm_eq_abs, mul_pow, sq_abs, real_inner_self_eq_norm_sq]
      ring
    · simp only [hχd, hud, Set.indicator_of_notMem hz, smul_zero, inner_zero_right, norm_zero]
      norm_num
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hc
  set X : ι → ℝ≥0∞ := fun x => eLpNorm (u x) 2 volume with hX
  set Y := familyNorm c X with hY
  have hXsq : ∀ x, X x ^ 2 = ENNReal.ofReal (∫ z, ‖u x z‖ ^ 2) := by
    intro x
    have hi := (hu2 x).integrable_norm_rpow two_ne_zero ENNReal.ofNat_ne_top
    simp only [ENNReal.toReal_ofNat, Real.rpow_two] at hi
    show eLpNorm (u x) 2 volume ^ 2 = ENNReal.ofReal (∫ z, ‖u x z‖ ^ 2)
    rw [ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall fun z => sq_nonneg _),
      eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top (hum x),
      eLpNorm'_eq_lintegral_enorm]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hYsq : Y ^ 2 = ∑ x, c x * X x ^ 2 := by
    rw [hY, familyNorm_sq]
  set P : ℝ := ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (G x z) (schwartzConvolution k (χ x) z) with hPd
  have hconv : ∀ x, schwartzConvolution k (χ x) = fourierCutoff μ (χ x) := fun x =>
    (Discard.fourierCutoff_eq_conv μ _ hμs hμ (χ x)).symm
  have hPeq : P = ∑ x, (π x)⁻¹ * ∫ z, ‖u x z‖ ^ 2 := by
    rw [hPd]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hconv x, ← integral_inner_fourierCutoff_comm μ _ hμs hμ (hG x) (hχ2 x)]
    congr 1
    exact integral_congr_ae (Eventually.of_forall fun z => hpt x z)
  have hP0 : 0 ≤ P := by
    rw [hPeq]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (inv_nonneg.2 (hπ x).le)
      (integral_nonneg fun z => sq_nonneg _)
  have hPY : ENNReal.ofReal P = Y ^ 2 := by
    rw [hYsq, hPeq, ENNReal.ofReal_sum_of_nonneg fun x _ => mul_nonneg (inv_nonneg.2 (hπ x).le)
      (integral_nonneg fun z => sq_nonneg _)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [ENNReal.ofReal_mul (inv_nonneg.2 (hπ x).le), hXsq x]
  -- the test norm
  set TC := TestConst k ϖ ϖ⁻¹ n L with hTC
  have hTC0 : 0 ≤ TC := TestConst_nonneg k ϖ (inv_nonneg.2 hϖ.le) n L
  have htest : weightedJetNorm π (-((n : ℕ) : ℝ)) L ϖ ϖ⁻¹
      (fun x _ w' z => orderedDerivative w' (schwartzConvolution k (χ x)) z) ≤
      ENNReal.ofReal TC * Y := by
    refine (weightedJetNorm_conv_le π k ϖ (inv_nonneg.2 hϖ.le) n L χ hχ1).trans ?_
    refine mul_le_mul' le_rfl (familyNorm_mono c fun x => ?_)
    show eLpNorm (fun z => cutoffBracket ϖ z ^ (-(n : ℝ) / 2) * ‖χ x z‖) 2 volume ≤
      eLpNorm (u x) 2 volume
    refine eLpNorm_mono (f := fun z => cutoffBracket ϖ z ^ (-(n : ℝ) / 2) * ‖χ x z‖)
      ((weight_continuous' ϖ (-(n : ℝ))).aestronglyMeasurable.mul (hχm x).norm) fun z => ?_
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (weight_nonneg' ϖ _ z) (norm_nonneg _))]
    simp only [hχd, norm_smul, Real.norm_eq_abs]
    calc cutoffBracket ϖ z ^ (-(n : ℝ) / 2) * (|w z| * ‖u x z‖)
        = (cutoffBracket ϖ z ^ (-(n : ℝ) / 2) * |w z|) * ‖u x z‖ := by ring
      _ ≤ 1 * ‖u x z‖ := mul_le_mul_of_nonneg_right (weight_mul_momW_le ϖ hβ z)
          (norm_nonneg _)
      _ = ‖u x z‖ := one_mul _
  -- conclusion
  have hYfin : Y ≠ ⊤ := by
    rw [hY, familyNorm]
    refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) ?_
    refine (ENNReal.sum_lt_top.2 fun x _ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (ENNReal.pow_lt_top (hu2 x).eLpNorm_lt_top)).ne
  by_cases hY0 : Y = 0
  · rw [hY0]
    exact zero_le
  set T : ℝ := (TC + 1) * Y.toReal with hT
  have hYr : 0 < Y.toReal := ENNReal.toReal_pos hY0 hYfin
  have hTpos : 0 < T := mul_pos (by linarith) hYr
  have htest' : weightedJetNorm π (-((n : ℕ) : ℝ)) L ϖ ϖ⁻¹
      (fun x _ w' z => orderedDerivative w' (schwartzConvolution k (χ x)) z) ≤
      ENNReal.ofReal T := by
    refine htest.trans ?_
    rw [hT, ENNReal.ofReal_mul (by linarith), ENNReal.ofReal_toReal hYfin]
    exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by linarith)) le_rfl
  have hE := pair_le_of_test π (n : ℝ) L ϖ (inv_pos.2 hϖ) G
    (fun x => schwartzConvolution k (χ x))
    (fun x => schwartzConvolution_contDiff k (χ x) (hχ1 x))
    (fun x => integrable_inner_of_memLp (hG x) (by
      rw [hconv x]
      exact fourierCutoff_memLp_of_memLp μ _ hμs hμ (hχ2 x))) hTpos htest'
  rw [← hPd, abs_of_nonneg hP0, hPY] at hE
  -- `Y² ≤ c (TC + 1) Y · N`, so `Y ≤ c (TC + 1) N`
  have hE' : Y * Y ≤ (ENNReal.ofReal (BallConst μ hμs hμ ϖ n L) * negJetNorm π n L ϖ ϖ⁻¹ G) * Y := by
    rw [← sq]
    refine hE.trans (le_of_eq ?_)
    rw [hT, BallConst, ← hk, ← hTC, ← mul_assoc, ENNReal.ofReal_mul (by
      have := CutConst_pos L
      positivity), ENNReal.ofReal_toReal hYfin]
    ring
  exact (ENNReal.mul_le_mul_iff_left hY0 hYfin).1 hE'

end Ball

section Limit

/-- The squared `L²` norm is the supremum of the squared norms on the balls `B_n`. -/
theorem eLpNorm_sq_eq_iSup_ball {E : Type*} [NormedAddCommGroup E] {f : Vec 2 → E}
    (hf : AEStronglyMeasurable f volume) :
    eLpNorm f 2 volume ^ 2 =
      ⨆ k : ℕ, eLpNorm ((Metric.closedBall (0 : Vec 2) k).indicator f) 2 volume ^ 2 := by
  have hsq : ∀ g : Vec 2 → E, AEStronglyMeasurable g volume →
      eLpNorm g 2 volume ^ 2 = ∫⁻ z, ‖g z‖ₑ ^ 2 := by
    intro g hg
    rw [eLpNorm_eq_eLpNorm' two_ne_zero ENNReal.ofNat_ne_top hg, eLpNorm'_eq_lintegral_enorm]
    simp only [ENNReal.toReal_ofNat, ENNReal.rpow_two]
    rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
    norm_num
  have hB : ∀ k : ℕ, MeasurableSet (Metric.closedBall (0 : Vec 2) k) := fun k =>
    Metric.isClosed_closedBall.measurableSet
  rw [hsq f hf]
  simp_rw [hsq _ (hf.indicator (hB _))]
  have hind : ∀ k : ℕ, ∫⁻ z, ‖(Metric.closedBall (0 : Vec 2) k).indicator f z‖ₑ ^ 2 =
      (volume.withDensity fun z => ‖f z‖ₑ ^ 2) (Metric.closedBall (0 : Vec 2) k) := by
    intro k
    rw [withDensity_apply _ (hB k), ← lintegral_indicator (hB k)]
    refine lintegral_congr fun z => ?_
    by_cases hz : z ∈ Metric.closedBall (0 : Vec 2) k
    · simp only [Set.indicator_of_mem hz]
    · simp only [Set.indicator_of_notMem hz, enorm_zero, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, zero_pow]
  simp_rw [hind]
  have hmono : Monotone fun k : ℕ => Metric.closedBall (0 : Vec 2) k := fun a b hab =>
    Metric.closedBall_subset_closedBall (by exact_mod_cast hab)
  rw [← hmono.measure_iUnion, Metric.iUnion_closedBall_nat, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]

end Limit

section Main

/-- **The low-pass moments.** -/
theorem seamLowPassMoment : SeamLowPassMomentStatement.{u, v} := by
  intro n L μ hμ _ _ hμs ι _ h _ _ _ _ _ _ π hπ ϖ hϖ _ G hG hN
  unfold momentNorm
  refine ENNReal.sum_lt_top.2 fun β hβ => ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  have hβn : β.1 + β.2 ≤ n := (Finset.mem_filter.1 hβ).2
  refine ENNReal.rpow_lt_top_of_nonneg (by norm_num) (ENNReal.sum_lt_top.2 fun x _ => ?_).ne
  set K := ENNReal.ofReal (BallConst μ hμs hμ ϖ n L) * negJetNorm π n L ϖ ϖ⁻¹ G with hKd
  have hK : K < ⊤ := ENNReal.mul_lt_top ENNReal.ofReal_lt_top hN
  have hF2 : MemLp (fourierCutoff μ (G x)) 2 volume :=
    fourierCutoff_memLp_of_memLp μ _ hμs hμ (hG x)
  have hmeas : AEStronglyMeasurable (fun z => MomW ϖ β z • fourierCutoff μ (G x) z) volume :=
    (MomW_continuous ϖ β).aestronglyMeasurable.smul hF2.aestronglyMeasurable
  have hball : ∀ R : ℕ, ENNReal.ofReal ((π x)⁻¹) * eLpNorm
      ((Metric.closedBall (0 : Vec 2) R).indicator
        (fun z => MomW ϖ β z • fourierCutoff μ (G x) z)) 2 volume ^ 2 ≤ K ^ 2 := by
    intro R
    have h1 := lowPass_ball_le μ hμ hμs π hπ n L hϖ G hG hβn R
    refine le_trans ?_ (pow_le_pow_left₀ zero_le h1 2)
    rw [familyNorm_sq]
    exact Finset.single_le_sum (f := fun x => ENNReal.ofReal ((π x)⁻¹) * eLpNorm
      ((Metric.closedBall (0 : Vec 2) R).indicator
        (fun z => MomW ϖ β z • fourierCutoff μ (G x) z)) 2 volume ^ 2)
      (fun _ _ => zero_le) (Finset.mem_univ x)
  have hsup : ENNReal.ofReal ((π x)⁻¹) *
      eLpNorm (fun z => MomW ϖ β z • fourierCutoff μ (G x) z) 2 volume ^ 2 ≤ K ^ 2 := by
    rw [eLpNorm_sq_eq_iSup_ball hmeas, ENNReal.mul_iSup]
    exact iSup_le hball
  exact hsup.trans_lt (ENNReal.pow_lt_top hK)

end Main

end AVRegularity.CycleWords.Seam
end
end

section
/-! # The test of the duality for the negative datum

For a smooth even multiplier `m ≥ 0` of compact support with `|ξ|^{2l} m ≤ 1` for `l ≤ k`, and the
moment-weighted datum `G_x = (ϖ^{|β|}/β!) y^β φ_x`, with the components `g_{x,e} = ⟨b_e, G_x⟩`:
`∑_x π_x⁻¹ ∑_e (2π)⁻² ∫ m |ĝ_{x,e}|² ≤ (C ‖φ‖_{-n,k})²`.
The test is `T_x = q_{β,R} · (m(D) G_x)`; it pairs with `φ` to `∑ π⁻¹ ⟨G_x, m(D)G_x⟩`.
-/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleWords.Assembly AVRegularity.CycleWords.Discard
open scoped ENNReal

namespace AVRegularity.CycleWords.Seam.NegLowBand

open AVRegularity.CycleWords.Seam.YoungKernel AVRegularity.CycleWords.Seam

universe u v

theorem integrable_of_memLp_compact {E : Type*} [NormedAddCommGroup E] {f : Vec 2 → E}
    (hf : MemLp f 2 volume) (hc : HasCompactSupport f) : Integrable f volume :=
  ((hf.locallyIntegrable (by norm_num)).integrableOn_isCompact hc.isCompact).integrable_of_forall_notMem_eq_zero
    fun x hx => image_eq_zero_of_notMem_tsupport hx

/-- The scale-and-weight multiplier of the moment `β`. -/
def qq (ϖ : ℝ) (β : ℕ × ℕ) (y : Vec 2) : ℝ :=
  (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) * momentWeight β y

/-- The scaled scalar component of the moment `β` of a datum. -/
def gsc {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] (ϖ : ℝ) (β : ℕ × ℕ)
    (φ : Vec 2 → E) (e : E) (y : Vec 2) : ℝ :=
  (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)) *
    (momentWeight β y * inner ℝ e (φ y))

theorem qq_continuous (ϖ : ℝ) (β : ℕ × ℕ) : Continuous (qq ϖ β) := by
  unfold qq momentWeight
  fun_prop

theorem qfun_eq (ϖ : ℝ) (β : ℕ × ℕ) (R : ℝ) (z : Vec 2) :
    qfun ϖ β R z = qq ϖ β z * chiR R z := by
  unfold qfun qq momentWeight
  ring

section Vec

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The moment-weighted datum as an `E`-valued function. -/
def gvec (ϖ : ℝ) (β : ℕ × ℕ) (φ : Vec 2 → E) (y : Vec 2) : E := qq ϖ β y • φ y

theorem inner_gvec (ϖ : ℝ) (β : ℕ × ℕ) (φ : Vec 2 → E) (e : E) (y : Vec 2) :
    inner ℝ e (gvec ϖ β φ y) = gsc ϖ β φ e y := by
  unfold gvec gsc qq
  rw [inner_smul_right]
  ring

theorem gvec_memLp (ϖ : ℝ) (β : ℕ × ℕ) {φ : Vec 2 → E} (hφm : StronglyMeasurable φ)
    (hφc : HasCompactSupport φ) (hφ2 : MemLp φ 2 volume) : MemLp (gvec ϖ β φ) 2 volume := by
  obtain ⟨R0, hR0, hR⟩ := exists_support_radius hφc
  refine hφ2.of_le_mul (c := |ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)| *
    R0 ^ (β.1 + β.2)) ((((qq_continuous ϖ β).stronglyMeasurable).smul hφm).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun y => ?_)
  unfold gvec
  by_cases hy : R0 < ‖y‖
  · rw [hR y hy]; simp
  · rw [not_lt] at hy
    rw [norm_smul, Real.norm_eq_abs]
    unfold qq momentWeight
    rw [abs_mul]
    have h0 : |y 0| ≤ R0 := (coord_le_norm 0 y).trans hy
    have h1 : |y 1| ≤ R0 := (coord_le_norm 1 y).trans hy
    have hmw : |y 0 ^ β.1 * y 1 ^ β.2| ≤ R0 ^ (β.1 + β.2) := by
      rw [abs_mul, abs_pow, abs_pow, pow_add]
      exact mul_le_mul (pow_le_pow_left₀ (abs_nonneg _) h0 _) (pow_le_pow_left₀ (abs_nonneg _) h1 _)
        (by positivity) (by positivity)
    calc |ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)| *
          |y 0 ^ β.1 * y 1 ^ β.2| * ‖φ y‖
        ≤ |ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ)| * R0 ^ (β.1 + β.2) *
          ‖φ y‖ := by
          have := abs_nonneg (ϖ ^ (β.1 + β.2) / ((β.1.factorial * β.2.factorial : ℕ) : ℝ))
          gcongr

theorem gvec_hasCompactSupport (ϖ : ℝ) (β : ℕ × ℕ) {φ : Vec 2 → E} (hφc : HasCompactSupport φ) :
    HasCompactSupport (gvec ϖ β φ) :=
  hφc.smul_left

theorem gsc_integrable (ϖ : ℝ) (β : ℕ × ℕ) {φ : Vec 2 → E} (hφm : StronglyMeasurable φ)
    (hφc : HasCompactSupport φ) (hφ2 : MemLp φ 2 volume) (e : E) :
    Integrable (gsc ϖ β φ e) volume := by
  have h1 := integrable_of_memLp_compact (gvec_memLp ϖ β hφm hφc hφ2)
    (gvec_hasCompactSupport ϖ β hφc)
  have := (innerSL ℝ e).integrable_comp h1
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp only [innerSL_apply_apply]
  exact inner_gvec ϖ β φ e y

theorem inner_integrable {φ : Vec 2 → E} (hφc : HasCompactSupport φ) (hφ2 : MemLp φ 2 volume)
    (e : E) : Integrable (fun y => inner ℝ e (φ y)) volume := by
  have := (innerSL ℝ e).integrable_comp (integrable_of_memLp_compact hφ2 hφc)
  simpa [innerSL_apply_apply] using this

theorem inner_hasCompactSupport {φ : Vec 2 → E} (hφc : HasCompactSupport φ) (e : E) :
    HasCompactSupport (fun y => inner ℝ e (φ y)) :=
  hφc.comp_left (g := fun v => inner ℝ e v) (by simp)

theorem inner_memLp {φ : Vec 2 → E} (hφc : HasCompactSupport φ) (hφ2 : MemLp φ 2 volume) {e : E}
    (he : ‖e‖ = 1) : MemLp (fun y => inner ℝ e (φ y)) 2 volume := by
  refine hφ2.of_le (inner_integrable hφc hφ2 e).aestronglyMeasurable
    (Filter.Eventually.of_forall fun y => ?_)
  rw [Real.norm_eq_abs]
  refine (abs_real_inner_le_norm _ _).trans ?_
  rw [he, one_mul]

end Vec

end AVRegularity.CycleWords.Seam.NegLowBand
end
end
