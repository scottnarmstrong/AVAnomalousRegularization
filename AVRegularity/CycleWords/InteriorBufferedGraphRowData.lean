-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.ConstructedScalarFibreDataRepresentatives
import AVRegularity.CycleWords.InteriorPulseRawAdjointFastPeriodicDecay
import AVRegularity.CycleWords.InteriorPulseReflectedActualWeakAllNativeOrders
public import AVRegularity.CycleWords.ConstructedScalarFibreConstants
public import AVRegularity.Weighted.WordNativeSolutionPack
import AVRegularity.CycleWords.GeometryErrorPieceMassBudget
public import AVRegularity.CycleWords.InteriorPulseReflectedTracePolynomialSmoothing
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! The actual smooth scalar fibre data under explicit numerical choices of constants. -/

theorem interiorPulseSmoothFibreScalarData_with_representatives
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    (ρ : ℝ≥0) (hρ : 0 < ρ)
    (hband : fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) < fibreCoefficientMajorantRadius Cw)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (K : ScalarConstants)
    (hKξ : K.ξ0 = constructedScalarCommonRadius Cw (ρ : ℝ))
    (hKCg : K.Cg = constructedScalarGraphPrice Cw)
    (hKCj : ∀ J, K.Cj J = constructedScalarJetPrice J
      (fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))) Cw (ρ : ℝ))
    (hKcj : ∀ J, K.cj J = 3 * Real.pi ^ 2)
    (hKQj : ∀ J, K.Qj J = 2 * J) (t₀ S : ℝ) :
    ∃ d : FibreScalarData K (ν / ocMeanFlux α q Λ ζ m ν) G
      (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) t₀ S,
      (∀ p t a, d.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
        fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t a) ∧
      d.lam = fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ∧
      (∀ p t, d.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
        fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) ∧
      ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < K.ξ0 → ∀ t,
        AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet d.r ξ) t) ∧
        AVenhance.IsZ2Periodic (fibreSeriesFun d.ell ξ t) := by
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let r₀ := fibreCoefficientFamily η Cw hη G hG hv hw
  let lam := fibreCoefficientSymbol η G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) r₀
  let R₀ := fibreNorm (fun _ : Fin 2 => ((ρ : ℝ) : ℂ))
  have hδ : 0 < K.ξ0 := by
    rw [hKξ]
    exact constructedScalarCommonRadius_pos hCw hρ
  have hrad := fibreCoefficientMajorantRadius_pos hCw
  have hδR : K.ξ0 ≤ fibreCoefficientMajorantRadius Cw / 16 := by
    rw [hKξ]
    have h := min_le_left (fibreCoefficientMajorantRadius Cw / 2048) ((ρ : ℝ) / 4)
    change min _ _ ≤ _
    linarith
  have hδold : K.ξ0 ≤ fibreCoefficientMajorantRadius Cw := by linarith
  have hCg : 0 ≤ fibreCoefficientGraphBound Cw := by
    unfold fibreCoefficientGraphBound
    positivity
  have hR₀ : 0 ≤ R₀ := fibreNorm_nonneg _
  have hρR₀ : (ρ : ℝ) ≤ R₀ := by
    have h := fibreNorm_coordinate_le (fun _ : Fin 2 => ((ρ : ℝ) : ℂ)) 0
    simpa only [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ρ.coe_nonneg] using h
  have hδρ : K.ξ0 ≤ (ρ : ℝ) := by
    rw [hKξ]
    have h := min_le_right (fibreCoefficientMajorantRadius Cw / 2048) ((ρ : ℝ) / 4)
    change min _ _ ≤ _
    linarith [ρ.coe_nonneg]
  obtain ⟨r, ell, hgraph, her, heell, hjets⟩ :=
    interiorPulseCanonicalGraphRow_smooth_scalar_jets hΛ hζ hν hr y₀ hslot hv V hb G hG
      Cw hCw hw hη0 hη hm ρ hρ hband
  have herv : ∀ p t, cellValue (r p) t =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (r₀ p) t := fun p t => her p t (valueIndex2 1)
  have hs (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) :=
    constructedScalarCommonDisc_bounds hCw hρ ξ (hξ.le.trans_eq hKξ)
  have hxR (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) : fibreNorm ξ ≤ R₀ :=
    hξ.le.trans (hδρ.trans hρR₀)
  have hxθ (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ < K.ξ0) (i : Fin 2) :
      ‖(Real.sqrt η : ℂ) * ξ i‖ ≤ R₀ :=
    (normalizedFrequency_coordinate_le hη ξ i).trans (hxR ξ hξ)
  refine ⟨{
    r := r
    lam := lam
    ell := ell
    graph := ?_
    row_summable := ?_
    row_mean := ?_
    row_taylor := ?_
    real_ratio := ?_
    graph_jets := ?_
    row_jets := ?_
    fast_decay := ?_
    fast_smoothing := ?_
    adjoint_decay := ?_
    adjoint_smoothing := ?_ }, her, rfl, heell, ?_⟩
  · apply isFibreGraph_radius_restriction hgraph hδ hδold hCg
    rw [hKCg]
    exact constructedScalarGraphPrice_graph Cw
  · intro ξ hξ
    exact constructedScalarRow_summable η Cw hη hCw G hG hv hw ell heell ξ
      (hξ.le.trans hδR)
  · intro ξ hξ t
    obtain ⟨hi, hn⟩ := constructedScalarGraphRow_normalization η Cw hη hCw G hG hv hw
      r her ell heell ξ (hξ.le.trans hδR) t
    refine ⟨hi, hn, ?_⟩
    rw [hKCg]
    exact constructedScalarRow_sub_one_bound η Cw hη hCw G hG hv hw ell heell ξ
      (hξ.le.trans hδR) t
  · intro n ξ t
    rw [hKCg]
    exact constructedScalarRow_taylor_bound η Cw hη hCw G hG hv hw ell heell hδ hδR n ξ t
  · intro ξ hreal hξ s t hst
    rw [hKCg]
    exact constructedScalarGraph_real_ratio η Cw hη hCw G hG hv hw r her hη0 hm V hb
      ξ hreal (hξ.le.trans hδold) hst
  · intro J ξ _ hξ t
    have hj := hjets ξ (hξ.le.trans_eq hKξ) t
    refine ⟨hj.1.of_le (by simp), ?_⟩
    rw [hKCj J, hKQj J]
    exact (hj.2.2.2.2 J).1
  · intro J ξ _ hξ t
    have hj := hjets ξ (hξ.le.trans_eq hKξ) t
    refine ⟨hj.2.2.1.of_le (by simp), ?_⟩
    rw [hKCj J, hKQj J]
    exact (hj.2.2.2.2 J).2
  · intro J ξ _ hξ a b _ hab _ D hD g₀ hg₀ hp₀ hi
    have h := interiorPulseSmoothFast_all_time_periodic_decay J hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD g₀ hg₀ hp₀ hi (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁
  · intro J ξ _ hξ a b _ hab _ D hD
    have h := interiorPulseSmoothFast_rough_smoothing J hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁
  · intro J ξ _ hξ a b _ hab _ D hD g₀ hg₀ hp₀ hi
    have h := interiorPulseSmoothAdjointFast_all_time_periodic_decay J hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD g₀ hg₀ hp₀ hi (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁
  · intro J ξ _ hξ a b _ hab _ D hD
    have h := interiorPulseSmoothAdjointFast_rough_smoothing J hΛ hζ hν hr y₀ hslot hv V hb
      G hG Cw hCw hw ξ R₀ hR₀ (hxR ξ hξ) (hxθ ξ hξ) hη0 hη hm hg hgsmall
      (hs ξ hξ).1 (hs ξ hξ).2.2.2.2 hab D hD (ρ : ℝ) r ell herv heell
    obtain ⟨g₁, hg₁, hp₁, he₁, hb₁⟩ := h
    refine ⟨g₁, hg₁.of_le (by simp), hp₁, he₁, ?_⟩
    rw [hKCj J, hKQj J, hKcj J]
    exact hb₁

  · intro ξ hξ t
    have hj := hjets ξ (hξ.le.trans_eq hKξ) t
    exact ⟨hj.2.1, hj.2.2.2.1⟩

/-! Full scalar fibre data with numerical constants fixed only by the scaled drift bound. -/

theorem interiorPulseSmoothFibreScalarData_representatives
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) {slot : ℤ} (hslot : Odd slot) (hv : IsCellDrift (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot))
    (V : ℝ) (hb : ∀ t x, ∑ j, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (seed : ScalarConstants) (t₀ S : ℝ) :
    ∃ d : FibreScalarData (constructedScalarFibreConstants seed Cw hCw)
      (ν / ocMeanFlux α q Λ ζ m ν) G (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) t₀ S,
      (∀ p t a, d.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
        fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t a) ∧
      d.lam = fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorSinglePulseDrift α q Λ ζ m ν y₀ slot) (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw) ∧
      (∀ p t, d.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
        fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hv hw p t) ∧
      ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < (constructedScalarFibreConstants seed Cw hCw).ξ0 → ∀ t,
        AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet d.r ξ) t) ∧
        AVenhance.IsZ2Periodic (fibreSeriesFun d.ell ξ t) := by
  apply interiorPulseSmoothFibreScalarData_with_representatives hΛ hζ hν hr y₀ hslot hv V hb G hG Cw hCw
    hw hη0 hη hm (constructedScalarNativeRadius Cw hCw)
    (constructedScalarNativeRadius_pos Cw hCw) (constructedScalarNativeRadius_band Cw hCw)
    hg hgsmall (constructedScalarFibreConstants seed Cw hCw)
  · exact (constructedScalarCommonRadius_native Cw hCw).symm
  · rfl
  · intro J
    rfl
  · intro J
    rfl
  · intro J
    rfl

/-! Full scalar fibre data with numerical constants fixed only by the scaled drift bound. -/

theorem interiorOrientationExtensions_fibre_data_representatives
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (a b : ℝ) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (seed : ScalarConstants) (t₀ S : ℝ) :
    ∀ p, ∃ hvp : IsCellDrift (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p),
      ∃ hwp : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
        Real.sqrt (∑ i, interiorOrientationExtensions α q Λ ζ m ν y₀ a b p t x i ^ 2) ≤ Cw,
      ∃ d : FibreScalarData (constructedScalarFibreConstants seed Cw hCw)
        (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p) t₀ S,
      (∀ k t a, d.r k t a =ᵐ[volume.restrict AVenhance.unitCube]
        fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hvp hwp k t a) ∧
      d.lam = fibreCoefficientSymbol (ν / ocMeanFlux α q Λ ζ m ν) G
        (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p)
        (fibreCoefficientFamily (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hvp hwp) ∧
      (∀ k t, d.ell k t =ᵐ[volume.restrict AVenhance.unitCube]
        fibreAdjointRowCoefficients (ν / ocMeanFlux α q Λ ζ m ν) Cw hη G hG hvp hwp k t) ∧
      ∀ ξ : Fin 2 → ℂ, fibreNorm ξ < (constructedScalarFibreConstants seed Cw hCw).ξ0 → ∀ t,
        AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet d.r ξ) t) ∧
        AVenhance.IsZ2Periodic (fibreSeriesFun d.ell ξ t) := by
  intro p
  let n := interiorActivePulseRegionIndex (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
    (ocCellDrift α q Λ ζ m ν y₀) p
  have hk : Odd (2 * n + 1) := ⟨n, by ring⟩
  let hvp := interiorSinglePulseDrift_isCellDrift hΛ hζ ν y₀ hk hv
  let hwp := interiorSinglePulseDrift_scaled_bound hΛ hζ ν y₀ hk _ Cw hCw hw
  refine ⟨hvp, hwp, ?_⟩
  exact interiorPulseSmoothFibreScalarData_representatives hΛ hζ hν hr y₀ hk
    hvp V (interiorSinglePulseDrift_bound hΛ hζ ν y₀ hk V hb) G hG Cw hCw hwp
    hη0 hη (fun t j => interiorSinglePulseDrift_mean_zero hΛ ν y₀ hk t j)
    hg hgsmall seed t₀ S

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Set
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Finite initial polynomial budgets propagate along a given chronological word chain. -/

open AVRegularity.Weighted

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChain_capped_successor_l2_duhamel (hD : 2 ≤ D)
    (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (letters : Fin N → CycleLetter ι h D) (J H : ℕ)
    (a b : ℝ) (hab : a ≤ b)
    (hL : ∀ j, IsCycleLetter π (letters j) (Icc a b ×ˢ Set.univ) J H)
    (κ : Fin (N + 1) → ι → ℕ) (K : ℕ) (d : Fin N → ℕ)
    (hd : ∀ j, (letters j).order = d j) (hreserve : (K + ∑ j, d j) ≤ J)
    (hc : ∀ j x y (o : Finset.Icc 2 D), (letters j).edge x y o ≠ [] →
      κ j.succ x + o.1 ≤ κ j.castSucc y + 2)
    (X0 : Vec 2) (δ : ℝ)
    (hm : ∀ j x u o (k : Fin ((letters j).edge x u o).length), ∀ wd X z,
      Measurable (fun t => (((letters j).edge x u o).get k).coeff wd t X z))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (hvs : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (strain r ϖ : ℝ) (ha : 0 ≤ strain) (hr : 0 < r) (hϖ : 0 < ϖ)
    (hrh : r ≤ 1 / 2) (hsmall : strain * r ^ 2 ≤ 1 / 8)
    (hjets : ∀ l, 1 ≤ l → l ≤ (K + ∑ j, d j) → ∀ t x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤ strain * (l.factorial : ℝ))
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (tw S : ℝ) (Cw : ℕ → ℝ)
    (W : ∀ n, ChartWeights (fun t _ => G t) v tw S ϖ 0 n Cw)
    (hwa : tw ≤ a) (hwb : b ≤ tw + S)
    (f : ∀ x, PlaneHk Set.univ (κ 0 x) (h x))
    (U : ∀ j x, ℝ → PlaneHk Set.univ (κ j x) (h x))
    (Uw : ∀ j x, ℝ → PlaneHk Set.univ (κ j x + 1) (h x))
    (hsol : IsPlaneChain (wordChainData G letters X0 δ) κ a b v f (fun _ _ _ => 0) U Uw)
    (hf : ∀ x n, weightedFactorialNormSq n ϖ 0 r
      (cappedWordSlots κ K d 0 x)
      (truncatePlaneHk (cappedWordSlots_le_original κ K d 0 x) (f x)) ≠ ⊤)
    (M : ℝ) (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2) (j : Fin N) (x : ι) :
    let κc := cappedWordSlots κ K d
    let fc : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κc p.1 p.2) (h p.2) :=
      fun p => truncatePlaneHk (cappedWordSlots_le_original κ K d p.1 p.2)
        (wordLevelDatum κ f p.1 p.2)
    let uc : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κc p.1 p.2) (h p.2) :=
      fun p t => truncatePlaneHk (cappedWordSlots_le_original κ K d p.1 p.2) (U p.1 p.2 t)
    let wc : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κc p.1 p.2 + 1) (h p.2) :=
      fun p t => truncatePlaneHk (Nat.succ_le_succ (cappedWordSlots_le_original κ K d p.1 p.2))
        (Uw p.1 p.2 t)
    ∃ F : ℝ → PlaneFluxL2 (h x), MemLp F 2 (volume.restrict (Icc a b)) ∧
      (∀ᵐ t ∂volume.restrict (Icc a b), ∀ k, F t k =ᵐ[volume]
        fun z => wordChainPreviousFlux letters X0 δ κc (fun p => wc p t) (j.succ, x) t z k) ∧
      ∀ (e : h x) (g : Lp ℝ 2 (volume : Measure (Vec 2))),
      let B := planeBlochBackwardRealField hab G hG v hv M hb g
      inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κc j.succ x) (uc (j.succ, x) b))) g =
        inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κc j.succ x) (fc (j.succ, x))))
          (planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) B (-a))) -
        ∫ t in a..b, inner ℝ (planeFluxFiberCoordinateCLM e (F t))
          (planeH1GradientOperator (cellEnergyPlaneRealH1State (neg_le_neg hab) B (-t))) := by
  classical
  have he := wordChain_capped_previous_gradient_moments hD π hπ letters J H a b hab
    hL κ K d hd hreserve hc X0 δ hm v hv hvs strain r ϖ ha hr hϖ hrh hsmall hjets
    G hG tw S Cw W hwa hwb 0 f U Uw hsol hf
  have hcsol := wordChainFrom_capped hD G letters κ K d hL hd hc X0 δ a b v
    (fun j x => wordLevelDatum κ f j x) (fun _ _ _ => 0) U Uw hsol
  simp only [map_zero] at hcsol
  exact wordChainSuccessor_l2_duhamel hD G hG letters X0 δ (cappedWordSlots κ K d)
    a b hab v hv M hb
    (fun p => truncatePlaneHk (cappedWordSlots_le_original κ K d p.1 p.2)
      (wordLevelDatum κ f p.1 p.2))
    (fun p t => truncatePlaneHk (cappedWordSlots_le_original κ K d p.1 p.2) (U p.1 p.2 t))
    (fun p t => truncatePlaneHk (Nat.succ_le_succ (cappedWordSlots_le_original κ K d p.1 p.2))
      (Uw p.1 p.2 t)) hcsol π hπ j x J H (hL j) (hm j x) ϖ r hϖ hr (he j)

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Actual and indexed pulse fibre data with all-order graph and row replacement and symbol comparison;
the actual symbol is the literal coefficient symbol. -/

theorem interiorBufferedGraphRowData
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (a b D : ℝ) (marks : Fin 2 → Finset ℝ)
    (hL : 0 < ocEll q Λ m ν ^ 2) (hD0 : 0 ≤ D)
    (hD : D ≤ (ocTau α q Λ m / ocEll q Λ m ν ^ 2) / 4)
    (hleftT : Ico a (a + D) ⊆ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
      (ocCellDrift α q Λ ζ m ν y₀))
    (hrightT : Ioc (b - D) b ⊆ interiorTrimmedQuiet (ocTau α q Λ m / ocEll q Λ m ν ^ 2)
      (ocCellDrift α q Λ ζ m ν y₀))
    (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
    (V : ℝ) (hb : ∀ t x, ∑ j, ocCellDrift α q Λ ζ m ν y₀ t x j ^ 2 ≤ V ^ 2)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (Cw : ℝ) (hCw : 0 ≤ Cw)
    (hw : ∀ t x, Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ Cw)
    (hη0 : 0 ≤ ν / ocMeanFlux α q Λ ζ m ν)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1)
    (hm : ∀ t (j : Fin 2), cellMean (fun x => (ocCellDrift α q Λ ζ m ν y₀ t x j : ℂ)) = 0)
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (seed : ScalarConstants) (t₀ S : ℝ) :
    let η := ν / ocMeanFlux α q Λ ζ m ν
    let K := scalarBufferedComparisonConstants (constructedScalarFibreConstants seed Cw hCw)
    let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
      (ocCellDrift α q Λ ζ m ν y₀) marks
    ∃ actual : FibreScalarData K η G (ocCellDrift α q Λ ζ m ν y₀) t₀ S,
    (∀ (hη' : η ≤ 1) (hw' : ∀ t x, Real.sqrt η *
        Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ K.Cw),
      actual.lam = fibreCoefficientSymbol η G (ocCellDrift α q Λ ζ m ν y₀)
        (fibreCoefficientFamily η K.Cw hη' G hG hv hw')) ∧
    ∃ extlocal : ∀ p : Fin reg.P, FibreScalarData K η G
      (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p) t₀ S,
      (∀ p j ξ, (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
        ∀ t ∈ Icc (reg.lo p) (reg.hi p + reg.buffer),
          cellSobolevNorm j (fun x => cellValue (fibreSeriesJet actual.r ξ) t x -
            cellValue (fibreSeriesJet (extlocal p).r ξ) t x) ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ *
            Real.exp (-(K.cj j) * reg.buffer))) ∧
      (∀ p j ξ, (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
        ∀ t ∈ Icc (reg.lo p - reg.buffer) (reg.hi p),
          cellSobolevNorm j (fun x => fibreSeriesFun actual.ell ξ t x -
            fibreSeriesFun (extlocal p).ell ξ t x) ≤
          ENNReal.ofReal (K.Cj j * peFactor η ^ K.Qj j * fibreNorm ξ *
            Real.exp (-(K.cj j) * reg.buffer))) ∧
      ∀ p ξ, (∀ i, (ξ i).im = 0) → fibreNorm ξ < K.ξ0 →
        ∀ t ∈ Icc (reg.lo p) (reg.hi p + reg.buffer),
          ‖fibreSeriesC actual.lam ξ t - fibreSeriesC (extlocal p).lam ξ t‖ ≤
            K.Cj 0 * peFactor η ^ K.Qj 0 * fibreNorm ξ ^ 2 *
              Real.exp (-(K.cj 0) * reg.buffer) := by
  classical
  have hτ0 : 0 ≤ ocTau α q Λ m / ocEll q Λ m ν ^ 2 :=
    (div_pos (AVRegularity.Construction.Stream.ocTau_pos hΛ) hL).le
  have hleft : ∀ t ∈ Ico a (a + D), ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0 :=
    fun t ht => interiorTrimmedQuiet_drift hτ0 (hleftT ht)
  have hright : ∀ t ∈ Ioc (b - D) b, ∀ z, ocCellDrift α q Λ ζ m ν y₀ t z = 0 :=
    fun t ht => interiorTrimmedQuiet_drift hτ0 (hrightT ht)
  let η := ν / ocMeanFlux α q Λ ζ m ν
  let K₀ := constructedScalarFibreConstants seed Cw hCw
  let K := scalarBufferedComparisonConstants K₀
  let reg := interiorBufferedBlockRegions (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D
    (ocCellDrift α q Λ ζ m ν y₀) marks
  have hpos := constructedScalarFibreConstants_positive seed Cw hCw
  have hC (j : ℕ) : 0 ≤ K₀.Cj j := (hpos.2.2.2 j).1.le
  have hrate (j : ℕ) : Real.pi ^ 2 / 4 ≤ K₀.cj j := by
    change Real.pi ^ 2 / 4 ≤ 3 * Real.pi ^ 2
    linarith only [sq_nonneg Real.pi]
  obtain ⟨actual₀, her, hlam, heell, hper⟩ := constructedSmoothFibreScalarData_representatives
    hΛ hζ hν hr y₀ hv V hb G hG Cw hCw hw hη0 hη hm hg hgsmall seed t₀ S
  have hext := interiorOrientationExtensions_fibre_data_representatives hΛ hζ hν hr
    y₀ a b hv V hb G hG Cw hCw hw hη0 hη hg hgsmall seed t₀ S
  choose hvp hwp ext₀ heR heLam heEll hePer using hext
  let actual := fibreScalarDataWithBufferedConstants actual₀ hpos.1 hCw hpos.2.1.le hC hrate
  let extlocal := fun p => fibreScalarDataWithBufferedConstants (ext₀ p)
    hpos.1 hCw hpos.2.1.le hC hrate
  have hagree := interiorOrientationExtensions_agree hΛ hζ ν y₀ hL a b D marks hD hleft hright
  have hnonempty := interiorBufferedBlockRegions_nonempty
    (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b D (ocCellDrift α q Λ ζ m ν y₀) marks hleftT hrightT
  have hmeanext (p : Fin reg.P) :=
    ((interiorOrientationExtensions_drift hΛ hζ ν y₀ a b η Cw hCw hv hw) p).2.1
  have hboundext (p : Fin reg.P) : ∀ t x,
      ∑ i, interiorOrientationExtensions α q Λ ζ m ν y₀ a b p t x i ^ 2 ≤ V ^ 2 := by
    let n := interiorActivePulseRegionIndex (ocTau α q Λ m / ocEll q Λ m ν ^ 2) a b
      (ocCellDrift α q Λ ζ m ν y₀) p
    have hk : Odd (2 * n + 1) := ⟨n, by ring⟩
    exact interiorSinglePulseDrift_bound hΛ hζ ν y₀ hk V hb
  have hquiet := interiorOrientationExtensions_quiet_left hΛ hζ ν y₀ hL a b D marks
    hD hleftT hrightT
  dsimp only
  refine ⟨actual, fun _ _ => hlam, extlocal, ?_, ?_, ?_⟩
  · intro p j ξ hreal hξ t ht
    exact fibreScalarData_buffered_graph_uniform_constants η Cw hη0 hη hCw G hG hg hgsmall
      (ocCellDrift α q Λ ζ m ν y₀) (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p)
      hv (hvp p) hm (hmeanext p) hw (hwp p) V hb (hboundext p) ξ
      (reg.lo p) (reg.hi p) D (hnonempty p) hD0
      (fun t ht => funext (hagree p t ht)) actual₀ (ext₀ p) hC (fun _ => rfl)
      hreal rfl hξ her (heR p)
      (fun t => (hper ξ (hξ.trans_le (min_le_left _ _)) t).1)
      (fun t => (hePer p ξ (hξ.trans_le (min_le_left _ _)) t).1) t ht j
  · intro p j ξ hreal hξ t ht
    exact fibreScalarData_buffered_row_uniform_constants η Cw hη0 hη hCw G hG hg hgsmall
      (ocCellDrift α q Λ ζ m ν y₀) (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p)
      hv (hvp p) hm (hmeanext p) hw (hwp p) V hb (hboundext p) ξ
      (reg.lo p) (reg.hi p) D (hnonempty p) hD0
      (fun t ht => funext (hagree p t ht)) (hquiet p) actual₀ (ext₀ p) hC (fun _ => rfl)
      hreal rfl hξ heell (heEll p)
      (fun t => (hper ξ (hξ.trans_le (min_le_left _ _)) t).2)
      (fun t => (hePer p ξ (hξ.trans_le (min_le_left _ _)) t).2) t ht j
  · intro p ξ _ hξ t ht
    exact fibreScalarData_buffered_symbol_uniform_constants η Cw hη0 hη hCw G hG hg hgsmall
      (ocCellDrift α q Λ ζ m ν y₀) (interiorOrientationExtensions α q Λ ζ m ν y₀ a b p)
      hv (hvp p) hm (hmeanext p) hw (hwp p) V hb (hboundext p) ξ
      (reg.lo p) (reg.hi p) D (hnonempty p) hD0
      (fun t ht => funext (hagree p t ht)) actual₀ (ext₀ p) rfl hξ hlam (heLam p) t ht

end AVRegularity.CycleWords
end
