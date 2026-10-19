-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.InteriorPulseReflectedActualWeakAllNativeOrders
import AVRegularity.CycleWords.InteriorPulseActualWeakNativeShortPropagation
import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
import AVRegularity.CycleWords.CellComplexH1Separability
public import AVRegularity.CycleDamping.ConstructedCanonicalGraph
public import AVRegularity.CycleWords.InteriorPulseReflectedTracePolynomialSmoothing
public import AVRegularity.CycleWords.FibreGraphNativeSeries
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The quiet left buffer controls the forward error in the actual row overlap. -/

theorem canonicalGraph_reverse_correction_buffered_product_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    (hquiet : 0 < buffer → ∀ t ∈ Icc (lo - buffer) lo, ∀ x, w t x = 0) :
    let D := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ
    let E := fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ
    let B := fibreAdjointGraphRaw η Cw hη G hG hw hsw ξ
    ∀ t ∈ Icc (lo - buffer) hi,
      ‖cellRawTrace B (-t)‖ * ‖cellRawTrace D t - cellRawTrace E t‖ ≤
      (2 * fibreWordCorrectionBound Cw ^ 2 * fibreNorm ξ ^ 2) *
        Real.exp (-(Real.pi ^ 2 / 4) * buffer) := by
  let Cr := fibreWordCorrectionBound Cw
  let f := fibreNorm ξ
  have hCr : 0 ≤ Cr := (fibreWordBounds_nonneg hCw).2
  have hf : 0 ≤ f := fibreNorm_nonneg ξ
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hξsmall : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024 :=
    (hξ.trans (fibreWordRadius_le_graph Cw)).trans (min_le_left _ _)
  have hnξ : fibreNorm (fun j => -ξ j) ≤ fibreCoefficientMajorantRadius Cw := by
    rw [fibreNorm_neg]
    linarith only [hξsmall, hR]
  have hglobal := fibreCoefficientFamily_graph_class_correction_bound η Cw hη hCw
    (fun s => G (-s)) (cellMetric_timeReverse hG) (cellDrift_timeReverse hw)
    (cellDrift_timeReverse_scaled_bound hsw) (fun j => -ξ j) hnξ
  have hab : lo - buffer ≤ hi + buffer := by linarith only [hlohi, hbuffer]
  have hforward := canonicalGraph_common_drift_window_norm_difference_decay η Cw hη0 hη
    hCw G hG hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ hab hvw
  have hbuffered := canonicalGraph_buffered_norm_difference_bound η Cw hη0 hη hCw
    G hG hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ
    lo hi buffer hlohi hbuffer hvw
  dsimp only
  intro t ht
  have hB : ‖cellRawTrace (fibreAdjointGraphRaw η Cw hη G hG hw hsw ξ) (-t)‖ ≤ Cr * f := by
    simpa only [fibreNorm_neg, Cr, f, fibreWordCorrectionBound, fibreAdjointGraphRaw]
      using hglobal (-t)
  by_cases htl : lo ≤ t
  · have hd := hbuffered t ⟨htl, by linarith only [ht.2, hbuffer]⟩
    have hp := mul_le_mul hB hd (norm_nonneg _) (mul_nonneg hCr hf)
    apply hp.trans_eq
    dsimp only [Cr, f]
    ring
  · have hbefore : t ≤ lo := (lt_of_not_ge htl).le
    have hquiet' : ∀ s ∈ Icc t (t + (lo - t)), ∀ x, w s x = 0 := by
      intro s hs x
      exact hquiet (by linarith only [ht.1, lt_of_not_ge htl]) s
        ⟨ht.1.trans hs.1, by linarith only [hs.2]⟩ x
    have hq := canonicalAdjointGraph_quiet_future_norm_bound η Cw hη hCw G hG hg hgsmall
      hw hsw ξ hξsmall t (lo - t) (sub_nonneg.mpr hbefore) hquiet'
    have hti : t ∈ Icc (lo - buffer) (hi + buffer) :=
      ⟨ht.1, by linarith only [ht.2, hbuffer]⟩
    have hd := hforward t hti
    have hd' : ‖cellRawTrace (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hv hsv) ξ) t -
        cellRawTrace (fibreSeriesJet (fibreCoefficientFamily η Cw hη G hG hw hsw) ξ) t‖ ≤
        (2 * Cr * f) * Real.exp (-(Real.pi ^ 2 / 4) * (t - (lo - buffer))) := by
      simpa only [Cr, f, mul_comm] using hd
    have hp := complementaryExponentialBuffers (Real.pi ^ 2 / 4) (2 * Real.pi ^ 2)
      (t - (lo - buffer)) (lo - t) buffer (2 * Cr * f) (Cr * f)
      _ _ (by positivity) (by linarith only [sq_nonneg Real.pi])
      (sub_nonneg.mpr hbefore) (by ring_nf; exact le_refl buffer)
      (by positivity) (mul_nonneg hCr hf) (norm_nonneg _) hd' hq
    rw [mul_comm] at hp
    apply hp.trans_eq
    dsimp only [Cr, f]
    ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Each actual or frozen scalar chart satisfies the full-radius weighted energy estimate. -/

theorem geometryPiece_lower_energy (n Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧
    ∀ {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
      [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
      [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      (π : ι → ℝ) (_hπ : ∀ x, 0 < π x) (Kslot : ι → ℕ) (_hK : ∀ x, Kslot x ≤ Kmax)
      {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (_hΛ : 1 ≤ Λ) (_hζ : IsFastProfile ζ)
      {Φ : ℕ → ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream (Φ (m - 1)))
      {ν B T ta ρs g g0 a B₀ lam Cb CT : ℝ} {qJ : ℕ} (_hqJ : Kmax + 1 ≤ qJ)
      {l₀ : ℤ} {P : ℕ} {y₀ : Vec 2}
      (_cov : IsGeometryCover α q Λ m ζ Φ hφ ν B T ta ρs g g0 a B₀ lam Cb CT qJ Kmax CG l₀ P y₀)
      (_hg0 : g0 ≤ 1 / 4) (i : Fin P)
      (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
      (_hG : G = ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
          (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) ∨
        G = fun t _ => ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ + i) ν
          (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i) t 0)
      (_W : ChartWeights G (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
        (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
        (ocEpsilon q Λ m / Real.sqrt (B * T)) 0 n Cw)
      (D : ℕ) (_hD : 2 ≤ D)
      (f : ∀ x, PlaneHk Set.univ (Kslot x) (h x))
      (F : ∀ x, ℝ → PlaneHk Set.univ (Kslot x) (PiLp 2 (fun _ : Fin 2 => h x)))
      (_hF : ∀ x, (∫⁻ t in Set.Icc (ocPieceStart α q Λ m ν ta (l₀ + i))
        (ocPieceEnd α q Λ m ν ta T (l₀ + i)), ENNReal.ofReal (‖F x t‖ ^ 2)) < ⊤)
      (u : ∀ (_ : Fin 1) x, ℝ → PlaneHk Set.univ (Kslot x) (h x))
      (w : ∀ (_ : Fin 1) x, ℝ → PlaneHk Set.univ (Kslot x + 1) (h x))
      (_hsln : IsPlaneChainFrom (geometryScalarData D G) (fun _ x => Kslot x)
        (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i))
        (ocCellDrift α q Λ ζ m ν (ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i))
        (fun _ x => f x) (fun _ x => F x) u w),
      geometryEnergyNorm π Kslot n (ocEpsilon q Λ m / Real.sqrt (B * T)) 0
        (ρs / ocEpsilon q Λ m) (ocPieceStart α q Λ m ν ta (l₀ + i))
        (ocPieceEnd α q Λ m ν ta T (l₀ + i)) (fun x => u 0 x) (fun x => w 0 x) ≤
      ENNReal.ofReal C * (geometryDataNorm π Kslot n (ocEpsilon q Λ m / Real.sqrt (B * T)) 0
        (ρs / ocEpsilon q Λ m) f + geometryFluxNorm π Kslot n
        (ocEpsilon q Λ m / Real.sqrt (B * T)) 0 (ρs / ocEpsilon q Λ m)
        (ocPieceStart α q Λ m ν ta (l₀ + i)) (ocPieceEnd α q Λ m ν ta T (l₀ + i)) F) := by
  obtain ⟨C, hC, henergy⟩ := weighted_energy_plane_lower_apriori n Kmax CG Cw
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ π hπ Kslot hK α q Λ m ζ hΛ hζ Φ hφ
    ν B T ta ρs g g0 a B₀ lam Cb CT qJ hqJ l₀ P y₀ cov hg0 i G hG W D hD f F hF u w hsln
  let yc := ocCellCentre α q Λ m (Φ (m - 1)) hφ l₀ y₀ i
  let left := ocPieceStart α q Λ m ν ta (l₀ + i)
  let right := ocPieceEnd α q Λ m ν ta T (l₀ + i)
  have H := geometryCover_piece_scalar_inputs Kmax CG hΛ hζ hφ hqJ cov hg0 i G hG
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hell : 0 < ocEll q Λ m ν ^ 2 := by
    unfold ocEll
    exact sq_pos_of_pos (div_pos he (Real.sqrt_pos.mpr cov.pos.1))
  -- The cover controls the metric on its window only: run the estimate for the clamped metric.
  let Gc := metricClamp (ta / ocEll q Λ m ν ^ 2) ((ta + T) / ocEll q Λ m ν ^ 2) G
  have hWc : ∀ t ∈ Set.Icc (ta / ocEll q Λ m ν ^ 2) (ta / ocEll q Λ m ν ^ 2 + T / ocEll q Λ m ν ^ 2),
      Gc t = G t := fun t ht => metricClamp_of_mem G (by rwa [add_div])
  have hsub := ocPiece_interval_subset α q Λ m ν ta T (l₀ + i) hell
  apply henergy π hπ Kslot hK left right H.time
    (ρs / ocEpsilon q Λ m) (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1))
    H.radius H.delta H.scale (ocCellDrift α q Λ ζ m ν yc)
    H.drift_bounded H.drift_measurable H.drift_smooth H.drift_divergence
    a B₀ lam H.strain H.drift_constant H.drift_length H.drift_jets H.drift_scale H.drift_small
    Gc g H.metric_size H.metric_small H.metric_measurable H.metric_symmetric H.metric_near
    H.metric_smooth H.metric_jets
    (ta / ocEll q Λ m ν ^ 2) (T / ocEll q Λ m ν ^ 2)
    (ocEpsilon q Λ m / Real.sqrt (B * T)) 0
    (ocPieceStart_global_lower α q Λ m ν ta (l₀ + i) hell)
    (by simpa only [add_div] using ocPieceEnd_global_upper α q Λ m ν ta T (l₀ + i) hell)
    (chartWeightsOfEqOn W hWc) f F hF (fun x => u 0 x) (fun x => w 0 x)
  exact isPlaneChainFrom_geometryScalarData_congr (fun t ht => metricClamp_of_mem G (hsub ht))
    (geometryScalarSolution_singleton_order_two D hD G Kslot left right
      (ocCellDrift α q Λ ζ m ν yc) f F u w hsln)

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CycleDamping
namespace AVRegularity.CycleWords

/-! The actual canonical graph used for the interior Gaussian has the prescribed phase
jet scaling, with constants fixed before the band, metric, interval and frequency. -/

theorem constructedCanonical_phase_jets
    (η : ℝ) (hη0 : 0 ≤ η) (hη : η ≤ 1)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ constructedGraphBudget)
    (S : ℝ) (hS : 1 ≤ S) (s₀ s t : ℝ) (hs : s₀ ≤ s) (hst : s ≤ t) (ht : t ≤ s₀ + S)
    (n : ℕ) (j : Fin n → Fin 2) (hn : 1 ≤ n) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < constructedGraphRadius / 2) :
    let r := fibreCoefficientFamily η constructedGraphBudget hη G hG hv hw
    let lam := canonicalSymbol η G v r
    ‖iteratedFDeriv ℂ n (fun ξ' : Fin 2 → ℂ => ∫ τ in s..t, fibreSeriesC lam ξ' τ) ξ
      (fun i => Pi.single (j i) (1 : ℂ))‖ ≤
      fibrePhaseJetConstant constructedGraphBudget n * Real.sqrt S ^ n *
        (if n = 1 then Real.sqrt S * fibreNorm ξ else 1) := by
  exact fibreCoefficientFamily_phase_word_bound η constructedGraphBudget hη0 hη
    constructedGraphBudget_pos.le G hG hv hw S hS s₀ s t hs hst ht n j hn ξ hξ

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Buffered zero-order graph and quadratic symbol replacement from actual common-drift evolution. -/

theorem fibreScalarData_buffered_graph_all_order_replacement (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    {K : ScalarConstants} {t₀ S : ℝ}
    (d : FibreScalarData K η G v t₀ S) (e : FibreScalarData K η G w t₀ S)
    (hC : ∀ j, 0 ≤ K.Cj j) (hQ : ∀ j, K.Qj j = 2 * j)
    (hreal : ∀ i, (ξ i).im = 0) (hξK : fibreNorm ξ < K.ξ0)
    (her : ∀ p t a, d.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
      fibreCoefficientFamily η Cw hη G hG hv hsv p t a)
    (hes : ∀ p t a, e.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
      fibreCoefficientFamily η Cw hη G hG hw hsw p t a)
    (hpd : ∀ t, AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet d.r ξ) t))
    (hpe : ∀ t, AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet e.r ξ) t)) :
    ∀ t ∈ Icc lo (hi + buffer), ∀ j,
      cellSobolevNorm j (fun x => cellValue (fibreSeriesJet d.r ξ) t x -
        cellValue (fibreSeriesJet e.r ξ) t x) ≤ ENNReal.ofReal
      (smoothPeriodicGapPrice (fun k => 2 * K.Cj k) (2 * fibreWordCorrectionBound Cw) j *
        peFactor η ^ (2 * j) * fibreNorm ξ *
        Real.exp (-((Real.pi ^ 2 / 4) / (2 : ℝ) ^ j) * buffer)) := by
  intro t ht
  let f := fun x => cellValue (fibreSeriesJet d.r ξ) t x - cellValue (fibreSeriesJet e.r ξ) t x
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := contDiff_infty.mpr (fun j =>
    (d.graph_jets j ξ hreal hξK t).1.sub (e.graph_jets j ξ hreal hξK t).1)
  have hper : AVenhance.IsZ2Periodic f := by
    intro n x
    change cellValue (fibreSeriesJet d.r ξ) t (x + AVenhance.latticeShift n) -
      cellValue (fibreSeriesJet e.r ξ) t (x + AVenhance.latticeShift n) = _
    rw [hpd t n x, hpe t n x]
  have hhigh (j : ℕ) : cellSobolevNorm j f ≤
      ENNReal.ofReal ((2 * K.Cj j) * peFactor η ^ (2 * j) * fibreNorm ξ) := by
    have he := fibreScalarData_graph_difference_bound d e j ξ hreal hξK t
    rw [hQ j] at he
    have hA : 0 ≤ K.Cj j * peFactor η ^ (2 * j) * fibreNorm ξ :=
      mul_nonneg (mul_nonneg (hC j) (by unfold peFactor; positivity)) (fibreNorm_nonneg ξ)
    rw [← ENNReal.ofReal_add hA hA] at he
    convert he using 1
    congr 1
    ring
  have hzero : cellL2Norm f ≤ ENNReal.ofReal
      ((2 * fibreWordCorrectionBound Cw) * fibreNorm ξ *
        Real.exp (-(Real.pi ^ 2 / 4) * buffer)) := by
    rw [cellL2Norm_fibreSeries_difference_congr d.r _ e.r _ her hes ξ t]
    have he := canonicalGraph_buffered_literal_L2_difference_bound η Cw hη0 hη hCw G hG
      hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ lo hi buffer hlohi hbuffer hvw t ht
    convert he using 1
    congr 1
    ring
  exact smoothPeriodic_polynomial_gap_hierarchy f hf hper (fun j => 2 * K.Cj j)
    (2 * fibreWordCorrectionBound Cw) (peFactor η) (fibreNorm ξ) (Real.pi ^ 2 / 4) buffer
    (fun j => mul_nonneg (by norm_num) (hC j))
    (mul_nonneg (by norm_num) (fibreWordBounds_nonneg hCw).2)
    (by unfold peFactor; positivity) (fibreNorm_nonneg ξ) hhigh hzero

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Buffered zero-order graph and quadratic symbol replacement from actual common-drift evolution. -/

theorem fibreScalarData_buffered_symbol_uniform_constants (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    {K : ScalarConstants} {t₀ S : ℝ}
    (d : FibreScalarData K η G v t₀ S) (e : FibreScalarData K η G w t₀ S)
    (hKCw : K.Cw = Cw) (hξK : fibreNorm ξ < (scalarBufferedComparisonConstants K).ξ0)
    (hlam : d.lam = fibreCoefficientSymbol η G v (fibreCoefficientFamily η Cw hη G hG hv hsv))
    (hmu : e.lam = fibreCoefficientSymbol η G w (fibreCoefficientFamily η Cw hη G hG hw hsw)) :
    ∀ t ∈ Icc lo (hi + buffer),
      ‖fibreSeriesC d.lam ξ t - fibreSeriesC e.lam ξ t‖ ≤
      (scalarBufferedComparisonConstants K).Cj 0 *
        peFactor η ^ (scalarBufferedComparisonConstants K).Qj 0 * fibreNorm ξ ^ 2 *
        Real.exp (-((scalarBufferedComparisonConstants K).cj 0) * buffer) := by
  have hξword : fibreNorm ξ ≤ fibreWordRadius Cw := by
    have he : fibreNorm ξ ≤ fibreWordRadius K.Cw := hξK.le.trans (min_le_right _ _)
    simpa only [hKCw] using he
  have he := canonicalGraph_buffered_symbol_difference_bound η Cw hη0 hη hCw G hG
    hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξword lo hi buffer hlohi hbuffer hvw
  intro t ht
  rw [hlam, hmu]
  apply (he t ht).trans
  change (2 * Cw * fibreWordCorrectionBound Cw) * fibreNorm ξ ^ 2 *
      Real.exp (-(Real.pi ^ 2 / 4) * buffer) ≤
    scalarBufferedGraphPrice K 0 * peFactor η ^ K.Qj 0 * fibreNorm ξ ^ 2 *
      Real.exp (-((Real.pi ^ 2 / 4) / (2 : ℝ) ^ 0) * buffer)
  rw [pow_zero, div_one]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg (fibreNorm ξ))
  have hprice : 2 * Cw * fibreWordCorrectionBound Cw ≤ scalarBufferedGraphPrice K 0 := by
    unfold scalarBufferedGraphPrice
    rw [hKCw]
    exact (le_max_right _ _).trans (le_max_right _ _)
  have hnonneg : 0 ≤ scalarBufferedGraphPrice K 0 :=
    (mul_nonneg (mul_nonneg (by norm_num) hCw) (fibreWordBounds_nonneg hCw).2).trans hprice
  simpa only [mul_one] using mul_le_mul hprice (one_le_pow₀ (one_le_peFactor η))
    (by norm_num : (0 : ℝ) ≤ 1) hnonneg

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open Homogenization Metric AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
open scoped NNReal AVRegularity.CycleWords.NativeComplex
namespace AVRegularity.CycleWords

/-! Native lifts of the original analytic graph correction preserve its exact zero-frequency value. -/

theorem fibreGraph_native_smooth_zero_of_witnesses
    {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (hgraph : IsFibreGraph η G v ξ₀ Cg r lam) (hξ0 : 0 < ξ₀)
    (R : ℝ≥0) (hR : 0 < R)
    (hband : fibreNorm (fun _ : Fin 2 => ((R : ℝ) : ℂ)) < ξ₀)
    (t : ℝ) (q : ℕ) (M : ℝ) (hM : 0 ≤ M)
    (hex : ∀ ξ ∈ ball (0 : Fin 2 → ℂ) (R : ℝ),
      ∃ U : TorusHk q ℂ,
        torusHkValueCLM U = ∑' p, fibreMonomial ξ p •
          fibreGraphCoefficientClass hgraph R hR hband p t ∧ ‖U‖ ≤ M) :
    ∃ F : (Fin 2 → ℂ) → TorusHk q ℂ,
      (∀ ξ ∈ ball (0 : Fin 2 → ℂ) (R : ℝ),
        torusHkValueCLM (F ξ) = ∑' p, fibreMonomial ξ p •
          fibreGraphCoefficientClass hgraph R hR hband p t ∧ ‖F ξ‖ ≤ M) ∧
      ContDiffOn ℂ (⊤ : ℕ∞) F (ball 0 (R : ℝ)) ∧ F 0 = 0 := by
  have hzband : fibreNorm (0 : Fin 2 → ℂ) < ξ₀ := by simpa [fibreNorm] using hξ0
  have htrace : cellRawTrace (fibreSeriesJet r 0) t = 0 := by
    have hg := hgraph.2.1 0 hzband
    have he : cellEnergyNorm Set.univ (fibreSeriesJet r 0) = 0 := by
      apply le_antisymm _ zero_le
      simpa only [fibreNorm, Pi.zero_apply, norm_zero, zero_pow (by decide : 2 ≠ 0),
        Finset.sum_const_zero, Real.sqrt_zero, mul_zero, ENNReal.ofReal_zero] using hg.2.2.2.2
    have hn := cellRawTrace_norm_le_energy (fibreSeriesJet r 0) hg.2.2.1.1 hg.2.2.1.2.2 t
    rw [he, ENNReal.toReal_zero] at hn
    exact norm_eq_zero.mp (le_antisymm hn (norm_nonneg _))
  have hseries := fibreGraphTrace_eq_nativeSeries hgraph R hR hband 0 hzband
    (by simp) t
  exact torusHigher_native_smooth_zero_choice q _ R M hR hM
    (fibreGraphNativeSeries_analyticOnNhd hgraph R hR hband t)
    (hseries.symm.trans htrace) hex

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Buffered zero-order graph and quadratic symbol replacement from actual common-drift evolution. -/

theorem fibreScalarData_buffered_graph_uniform_constants (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    {K : ScalarConstants} {t₀ S : ℝ}
    (d : FibreScalarData K η G v t₀ S) (e : FibreScalarData K η G w t₀ S)
    (hC : ∀ j, 0 ≤ K.Cj j) (hQ : ∀ j, K.Qj j = 2 * j)
    (hreal : ∀ i, (ξ i).im = 0) (hKCw : K.Cw = Cw)
    (hξK : fibreNorm ξ < (scalarBufferedComparisonConstants K).ξ0)
    (her : ∀ p t a, d.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
      fibreCoefficientFamily η Cw hη G hG hv hsv p t a)
    (hes : ∀ p t a, e.r p t a =ᵐ[volume.restrict AVenhance.unitCube]
      fibreCoefficientFamily η Cw hη G hG hw hsw p t a)
    (hpd : ∀ t, AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet d.r ξ) t))
    (hpe : ∀ t, AVenhance.IsZ2Periodic (cellValue (fibreSeriesJet e.r ξ) t)) :
    ∀ t ∈ Icc lo (hi + buffer), ∀ j,
      cellSobolevNorm j (fun x => cellValue (fibreSeriesJet d.r ξ) t x -
        cellValue (fibreSeriesJet e.r ξ) t x) ≤ ENNReal.ofReal
      ((scalarBufferedComparisonConstants K).Cj j *
        peFactor η ^ (scalarBufferedComparisonConstants K).Qj j * fibreNorm ξ *
        Real.exp (-((scalarBufferedComparisonConstants K).cj j) * buffer)) := by
  have hξold : fibreNorm ξ < K.ξ0 := hξK.trans_le (min_le_left _ _)
  have hξword : fibreNorm ξ ≤ fibreWordRadius Cw := by
    have he : fibreNorm ξ ≤ fibreWordRadius K.Cw := hξK.le.trans (min_le_right _ _)
    simpa only [hKCw] using he
  have he := fibreScalarData_buffered_graph_all_order_replacement η Cw hη0 hη hCw G hG
    hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξword lo hi buffer hlohi hbuffer hvw
    d e hC hQ hreal hξold her hes hpd hpe
  intro t ht j
  apply (he t ht j).trans
  apply ENNReal.ofReal_le_ofReal
  change smoothPeriodicGapPrice (fun k => 2 * K.Cj k) (2 * fibreWordCorrectionBound Cw) j *
      peFactor η ^ (2 * j) * fibreNorm ξ *
      Real.exp (-((Real.pi ^ 2 / 4) / (2 : ℝ) ^ j) * buffer) ≤
    scalarBufferedGraphPrice K j * peFactor η ^ K.Qj j * fibreNorm ξ *
      Real.exp (-((Real.pi ^ 2 / 4) / (2 : ℝ) ^ j) * buffer)
  rw [hQ j]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (fibreNorm_nonneg ξ)
  apply mul_le_mul_of_nonneg_right _ (by unfold peFactor; positivity)
  unfold scalarBufferedGraphPrice
  rw [hKCw]
  exact (le_max_left _ _).trans (le_max_right _ _)

end AVRegularity.CycleWords
end
end

section
public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CycleDamping
namespace AVRegularity.CycleWords

/-! The canonical band symbol (the literal coefficient family at the budget
`constructedGraphBudget`) has the full and every finite Gaussian bound, with a frequency radius
fixed before the band, metric and admissible interval. -/

theorem bandChain_scalar_gaussian {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∃ g₀ ξmax c : ℝ, 0 < g₀ ∧ 0 < ξmax ∧ 0 < c ∧
      ∀ Λ : ℕ, Λ₀ ≤ Λ → ∀ (M : ℕ) (κ : ℕ → ℝ), IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ ν B : ℝ, κ m = ν → κ (m - 1) = B →
      ∀ (y₀ : Vec 2) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (g : ℝ)
      (hG : IsCellMetric (fun t _ => G t)), 0 ≤ g → g ≤ g₀ →
      IsMetricNearIdentity (fun t _ => G t) g → ∀ Θ θ ta T : ℝ,
      0 ≤ Θ → IsOCAdmissibleInterval α q Λ ζ m ν B Θ θ ta T →
      ∀ (hη : ν / B ≤ 1) (hv : IsCellDrift (ocCellDrift α q Λ ζ m ν y₀))
        (hw : ∀ t x, Real.sqrt (ν / B) *
          Real.sqrt (∑ i, ocCellDrift α q Λ ζ m ν y₀ t x i ^ 2) ≤ constructedGraphBudget),
      ∀ ξ : Fin 2 → ℂ, (∀ i, (ξ i).im = 0) → fibreNorm ξ ≤ ξmax →
        (∫ t in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
          fibreSeriesC (fibreCoefficientSymbol (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
            (fibreCoefficientFamily (ν / B) constructedGraphBudget hη G hG hv hw)) ξ t).re ≤
            -c * (T / ocEll q Λ m ν ^ 2) * fibreNorm ξ ^ 2 ∧
        ∀ N : ℕ, 2 ≤ N →
          (∫ t in (ta / ocEll q Λ m ν ^ 2)..((ta + T) / ocEll q Λ m ν ^ 2),
            ∑ n ∈ Finset.range (N + 1), fibreHomogeneous
              (fibreCoefficientSymbol (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
                (fibreCoefficientFamily (ν / B) constructedGraphBudget hη G hG hv hw)) ξ n t).re ≤
              -c * (T / ocEll q Λ m ν ^ 2) * fibreNorm ξ ^ 2 := by
  obtain ⟨L, hL, g₀, hg₀, hquad⟩ := bandChain_canonical_quadratic_damping hα₀ hα₁ hs₀ hs₁ hq hζ
  let c₀ := (1 - Real.exp (-2)) / 288
  have hc₀ : 0 < c₀ := div_pos
    (sub_pos.mpr (Real.exp_lt_one_iff.mpr (by norm_num))) (by norm_num)
  let A := 2 * constructedGraphBound * (2 / constructedGraphRadius) ^ 3
  have hA : 0 < A := by
    dsimp only [A]
    exact mul_pos (mul_pos (by norm_num) constructedGraphBound_pos)
      (pow_pos (div_pos (by norm_num) constructedGraphRadius_pos) _)
  let ξmax := min (constructedGraphRadius / 4) (c₀ / (4 * A))
  have hξmax : 0 < ξmax := lt_min
    (div_pos constructedGraphRadius_pos (by norm_num))
    (div_pos hc₀ (mul_pos (by norm_num) hA))
  refine ⟨L, hL, g₀, ξmax, c₀ / 2,
    hg₀, hξmax, div_pos hc₀ (by norm_num), ?_⟩
  intro Λ hΛ M κ hκ m hm hmM ν B hνeq hBeq y₀ G g hG hg hgg hnear Θ θ ta T hΘ hadm hη hv hw
  have hΛ1 : 1 ≤ Λ := by omega
  have hν : 0 < ν := hνeq ▸ CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hBmean : B = ocMeanFlux α q Λ ζ m ν := by
    rw [← hBeq, hκ.2 m (by omega) hmM, hνeq]
  have hB : 0 < B := by
    rw [hBmean]
    exact hν.trans_le (CycleReference.meanFlux_ge_input hΛ1 hζ hν)
  let r := fibreCoefficientFamily (ν / B) constructedGraphBudget hη G hG hv hw
  let lam := canonicalSymbol (ν / B) G (ocCellDrift α q Λ ζ m ν y₀) r
  have hgraph : IsFibreGraph (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
      constructedGraphRadius constructedGraphBound r lam :=
    Graph.fibreCoefficientFamily_isFibreGraph (ν / B) constructedGraphBudget
      (div_pos hν hB).le hη constructedGraphBudget_pos.le G hG hv hw
  have hlam : ∀ p, AEStronglyMeasurable (lam p) volume :=
    canonicalSymbol_aestronglyMeasurable _ _ hη G hG hv hw
  intro ξ hreal hξ
  have hlamEq : fibreCoefficientSymbol (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
      (fibreCoefficientFamily (ν / B) constructedGraphBudget hη G hG hv hw) =
      canonicalSymbol (ν / B) G (ocCellDrift α q Λ ζ m ν y₀)
        (fibreCoefficientFamily (ν / B) constructedGraphBudget hη G hG hv hw) := rfl
  rw [hlamEq]
  have hquarter := hξ.trans (min_le_left (constructedGraphRadius / 4) (c₀ / (4 * A)))
  have hsmall : A * fibreNorm ξ ≤ c₀ / 4 := by
    have hh := mul_le_mul_of_nonneg_left
      (hξ.trans (min_le_right (constructedGraphRadius / 4) (c₀ / (4 * A)))) hA.le
    exact hh.trans_eq (by field_simp [ne_of_gt hA])
  have hS : 0 ≤ T / ocEll q Λ m ν ^ 2 := hΘ.trans hadm.2.1
  have hab : ta / ocEll q Λ m ν ^ 2 ≤ (ta + T) / ocEll q Λ m ν ^ 2 := by
    rw [← sub_nonneg]
    convert hS using 1
    ring
  have hquadξ := hquad Λ hΛ M κ hκ m hm hmM ν B hνeq hBeq y₀ G g hG hg hgg hnear
    constructedGraphBudget hη hv hw Θ θ ta T hΘ hadm ξ hreal
  have hdif : (ta + T) / ocEll q Λ m ν ^ 2 - ta / ocEll q Λ m ν ^ 2 = T / ocEll q Λ m ν ^ 2 := by ring
  have he := low_full_finite_damping_of_graph hG hv hgraph constructedGraphRadius_pos
    constructedGraphBound_pos.le hlam ξ hquarter _ _ c₀ hab hsmall (by simpa only [hdif] using hquadξ)
  simpa only [hdif] using he

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Complete left-buffered L2 replacement for the actual normalized canonical rows. -/

theorem canonicalRow_buffered_norm_difference_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    (hquiet : 0 < buffer → ∀ t ∈ Icc (lo - buffer) lo, ∀ x, w t x = 0) :
    ∀ t ∈ Icc (lo - buffer) hi,
      ‖cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hsv) ξ) t -
        cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hw hsw) ξ) t‖ ≤
        (20 * fibreWordCorrectionBound Cw + 16 * fibreWordCorrectionBound Cw ^ 2) *
          fibreNorm ξ * Real.exp (-(Real.pi ^ 2 / 4) * buffer) := by
  have hreverse := canonicalAdjointGraph_buffered_norm_difference_bound η Cw hη0 hη hCw
    G hG hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ
    lo hi buffer hlohi hbuffer hvw
  have hproduct := canonicalGraph_reverse_correction_buffered_product_bound η Cw hη0 hη hCw
    G hG hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ
    lo hi buffer hlohi hbuffer hvw hquiet
  have hf0 := fibreNorm_nonneg ξ
  have hf1 := (fibreWord_frequency_small hCw ξ hξ).1
  have hfsq : fibreNorm ξ ^ 2 ≤ fibreNorm ξ := by
    calc
      _ = fibreNorm ξ * fibreNorm ξ := pow_two _
      _ ≤ 1 * fibreNorm ξ := mul_le_mul_of_nonneg_right hf1 hf0
      _ = _ := one_mul _
  intro t ht
  have hrow := canonicalRow_difference_bound η Cw hη hCw G hG v w hv hw hsv hsw ξ hξ t
  have hp := add_le_add
    (mul_le_mul_of_nonneg_left (hreverse t ht) (by norm_num : (0 : ℝ) ≤ 10))
    (mul_le_mul_of_nonneg_left (hproduct t ht) (by norm_num : (0 : ℝ) ≤ 8))
  have hrow' : ‖cellSourceSlice (fibreSeriesFun
      (fibreAdjointRowCoefficients η Cw hη G hG hv hsv) ξ) t -
      cellSourceSlice (fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hw hsw) ξ) t‖ ≤ 10 * (Real.exp (-(Real.pi ^ 2 / 4) * buffer) *
      (2 * fibreWordCorrectionBound Cw * fibreNorm ξ)) +
      8 * ((2 * fibreWordCorrectionBound Cw ^ 2 * fibreNorm ξ ^ 2) *
        Real.exp (-(Real.pi ^ 2 / 4) * buffer)) := by
    apply hrow.trans
    convert hp using 1
    ring
  apply hrow'.trans
  have hpow := mul_le_mul_of_nonneg_left hfsq
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 16)
      (sq_nonneg (fibreWordCorrectionBound Cw)))
      (Real.exp_pos (-(Real.pi ^ 2 / 4) * buffer)).le)
  convert add_le_add_left hpow
    (20 * fibreWordCorrectionBound Cw * fibreNorm ξ *
      Real.exp (-(Real.pi ^ 2 / 4) * buffer)) using 1 <;> ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The actual word component has the backward Bloch formula for its preceding-letter source. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChain_component_duhamel (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (M : ℝ)
    (hb : ∀ t x, ∑ k, v t x k ^ 2 ≤ M ^ 2)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι)
    (V : ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hVl : MemLp V 2 (volume.restrict (Icc a b)))
    (hV : ∀ᵐ t ∂volume.restrict (Icc a b), planeValue (V t) =ᵐ[volume]
      wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) i t)
    (e : h i.2) (g : Lp ℝ 2 (volume : Measure (Vec 2))) :
    let B := planeBlochBackwardRealField hab G hG v hv M hb g
    inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (U i b))) g =
      inner ℝ (planeFiberCoordinateCLM e (planeHkValueOperator (κ i.1 i.2) (f i)))
        (planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab) B (-a))) -
      ∫ r in a..b, inner ℝ (planeFluxValueOperator (κ i.1 i.2)
        (mapPlaneHk (planeFiberFluxCoordinate e) (V r)))
        (planeH1GradientOperator (cellEnergyPlaneRealH1State (neg_le_neg hab) B (-r))) := by
  obtain ⟨C, hCpos, hC⟩ := cellDriftTorusSymbol_bound v hv
  obtain ⟨C', hC'pos, hC'⟩ := cellDriftTorusSymbol_bound _ (cellDrift_neg hv)
  obtain ⟨Cr, hCrpos, hCr⟩ := cellDriftTorusSymbol_bound _ (cellDrift_timeReverse hv)
  have hvm : ∀ t k, Measurable (fun x => v t x k) := fun t k =>
    (measurable_pi_apply k).comp (hv.1.comp (measurable_const.prodMk measurable_id))
  have hvb : ∀ t k x, ‖v t x k‖ ≤ C := by
    intro t k x
    have he := hC t k (torusQuotient x)
    rw [cellDriftTorusSymbol_plane v hv, Complex.norm_real] at he
    exact he
  have hs := wordChain_scalar_component_redistribution hD G letters X0 δ κ a b v
    hvm C hvb f U Uw hsol i V hV
  have hs2 := geometryScalarSolution_order_two D hD (fun t _ => G t)
    (fun _ _ => κ i.1 i.2) a b v (fun _ _ => f i) (fun _ _ => V)
    (fun _ _ => U i) (fun _ _ => Uw i) hs
  exact planeScalarCoordinateForced_duhamel (h := fun _ : Unit => h i.2)
    a b hab (fun _ _ => κ i.1 i.2) G hG v hv M hb C hCpos hC C' hC'pos hC'
    Cr hCrpos hCr (fun _ => f i) (fun _ => V) (fun _ => hVl)
    (fun _ => U i) (fun _ => Uw i) hs2 (0, ()) e g

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Literal L2 comparison of actual canonical adjoint rows on the full replacement window. -/

theorem canonicalRow_buffered_literal_L2_difference_bound (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    (hquiet : 0 < buffer → ∀ t ∈ Icc (lo - buffer) lo, ∀ x, w t x = 0) :
    ∀ t ∈ Icc (lo - buffer) hi,
      cellL2Norm (fun x =>
        fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hv hsv) ξ t x -
        fibreSeriesFun (fibreAdjointRowCoefficients η Cw hη G hG hw hsw) ξ t x) ≤
        ENNReal.ofReal ((20 * fibreWordCorrectionBound Cw + 16 * fibreWordCorrectionBound Cw ^ 2) *
          fibreNorm ξ * Real.exp (-(Real.pi ^ 2 / 4) * buffer)) := by
  have hR := fibreCoefficientMajorantRadius_pos hCw
  have hrsmall : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 1024 :=
    (hξ.trans (fibreWordRadius_le_graph Cw)).trans (min_le_left _ _)
  have hξ16 : fibreNorm ξ ≤ fibreCoefficientMajorantRadius Cw / 16 := by
    linarith only [hrsmall, hR]
  have he := canonicalRow_buffered_norm_difference_bound η Cw hη0 hη hCw G hG hg hgsmall
    v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ lo hi buffer hlohi hbuffer hvw hquiet
  intro t ht
  rw [cellL2Norm_difference_of_source_slices _ _ t
    (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hv hsv ξ hξ16 t).1
    (fibreAdjointRowCoefficients_series_memLp_bound η Cw hη hCw G hG hw hsw ξ hξ16 t).1]
  exact ENNReal.ofReal_le_ofReal (he t ht)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A priori weighted energy for the literal native geometry error. -/

theorem geometryError_component_lower_apriori (q Kmax : ℕ) (CG Cw : ℕ → ℝ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
    (_hD : 2 ≤ D) (J Ks : ℕ) (K : ι → ℕ) (_hK : ∀ u, K u ≤ Kmax) (_hdesc : F.IsDescending K) (p : P) (c : Ctx p)
    (a b s δ : ℝ) (X0 phase : Vec 2)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (ρ ϖ g strain B lam : ℝ)
    (_HC : ScalarCoefficientInputs Kmax CG a b ρ δ v strain B lam G g)
    (tw S : ℝ) (_htw : tw ≤ a) (_htb : b ≤ tw + S)
    (_W : ChartWeights G v tw S ϖ 0 q Cw)
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (U : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Uw : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (fZ : ∀ (_ : Fin (J + 1)) x, PlaneHk Set.univ (K x) (h x))
    (Z : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Zw : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (V : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (_hsol : IsPlaneChainFrom (geometryActualData G (F.cellFiber s phase p c) X0 δ)
      (fun _ x => K x) a b v (fun _ x => f x) (fun _ _ _ => 0)
      (fun _ x => U x) (fun _ x => Uw x))
    (_hZ : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 δ)
      (fun _ x => K x) a b v fZ (fun _ _ _ => 0) Z Zw)
    (_hVm : ∀ x, MemLp (V x) 2 (volume.restrict (Set.Icc a b)))
    (_hV : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V x t) =ᵐ[volume]
      geometryErrorSourceFlux F J Ks K p c G s δ X0 phase (fun u => Uw u t - ∑ j, Zw j u t)
        (fun j u => Zw j u t) x t) ,
    ∀ x, nativeComponentEnergy q ϖ ρ a b
      (nativeErrorCurve (U x) (fun j => Z j x)) (nativeErrorCurve (Uw x) (fun j => Zw j x)) ≤
      ENNReal.ofReal A * (weightedFactorialNormSq q ϖ 0 ρ (K x)
        (nativeErrorDatum (f x) (fun j => fZ j x)) +
        16 * ∫⁻ t in Set.Icc a b, weightedFactorialNormSq q ϖ 0 ρ (K x) (V x t)) := by
  obtain ⟨A, hA, henergy⟩ := scalarNative_component_apriori_uniform q Kmax CG Cw
  refine ⟨A, hA, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F hD J Ks K hK hdesc p c a b s δ X0 phase v G
    ρ ϖ g strain B lam HC tw S htw htb W f U Uw fZ Z Zw V hsol hZ hVm hV x
  obtain ⟨Mv, hMv, hvc, hvb, hGc, hGb⟩ := scalarCoefficientInputs_spatial_bounds HC
  have hs := geometryError_scalar_component_redistribution F hD J Ks K hdesc p c
    a b s δ X0 phase v G Mv (5 / 4) hMv (by norm_num) hvc hvb hGc hGb
    f U Uw fZ Z Zw V hsol hZ hV x
  have hs2 := geometryScalarSolution_order_two D hD (h := fun _ : Unit => h x)
    G (fun _ _ => K x) a b v (fun _ _ => nativeErrorDatum (f x) (fun j => fZ j x))
    (fun _ _ => V x) (fun _ _ => nativeErrorCurve (U x) (fun j => Z j x))
    (fun _ _ => nativeErrorCurve (Uw x) (fun j => Zw j x)) hs
  exact henergy (K x) (hK x) a b ρ δ ϖ g strain B lam v G HC tw S htw htb W
    (nativeErrorDatum (f x) (fun j => fZ j x)) (V x)
    (nativeErrorCurve (U x) (fun j => Z j x)) (nativeErrorCurve (Uw x) (fun j => Zw j x)) (hVm x) hs2

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! All-order literal row replacement from actual future forgetting and normalization stability. -/

theorem fibreScalarData_buffered_row_all_order_replacement (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ) (hξ : fibreNorm ξ ≤ fibreWordRadius Cw)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    (hquiet : 0 < buffer → ∀ t ∈ Icc (lo - buffer) lo, ∀ x, w t x = 0)
    {K : ScalarConstants} {t₀ S : ℝ}
    (d : FibreScalarData K η G v t₀ S) (e : FibreScalarData K η G w t₀ S)
    (hC : ∀ j, 0 ≤ K.Cj j) (hQ : ∀ j, K.Qj j = 2 * j)
    (hreal : ∀ i, (ξ i).im = 0) (hξK : fibreNorm ξ < K.ξ0)
    (her : ∀ p t, d.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients η Cw hη G hG hv hsv p t)
    (hes : ∀ p t, e.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients η Cw hη G hG hw hsw p t)
    (hpd : ∀ t, AVenhance.IsZ2Periodic (fibreSeriesFun d.ell ξ t))
    (hpe : ∀ t, AVenhance.IsZ2Periodic (fibreSeriesFun e.ell ξ t)) :
    ∀ t ∈ Icc (lo - buffer) hi, ∀ j,
      cellSobolevNorm j (fun x => fibreSeriesFun d.ell ξ t x -
        fibreSeriesFun e.ell ξ t x) ≤ ENNReal.ofReal
      (smoothPeriodicGapPrice (fun k => 2 * K.Cj k) (20 * fibreWordCorrectionBound Cw + 16 * fibreWordCorrectionBound Cw ^ 2) j *
        peFactor η ^ (2 * j) * fibreNorm ξ *
        Real.exp (-((Real.pi ^ 2 / 4) / (2 : ℝ) ^ j) * buffer)) := by
  intro t ht
  let f := fun x => fibreSeriesFun d.ell ξ t x - fibreSeriesFun e.ell ξ t x
  have heq : f = (fun x => fibreSeriesFun d.ell ξ t x - 1) -
      (fun x => fibreSeriesFun e.ell ξ t x - 1) := by
    funext x
    dsimp only [f, Pi.sub_apply]
    ring
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [heq]
    exact contDiff_infty.mpr (fun j =>
      (d.row_jets j ξ hreal hξK t).1.sub (e.row_jets j ξ hreal hξK t).1)
  have hper : AVenhance.IsZ2Periodic f := by
    intro n x
    change fibreSeriesFun d.ell ξ t (x + AVenhance.latticeShift n) -
      fibreSeriesFun e.ell ξ t (x + AVenhance.latticeShift n) = _
    rw [hpd t n x, hpe t n x]
  have hhigh (j : ℕ) : cellSobolevNorm j f ≤
      ENNReal.ofReal ((2 * K.Cj j) * peFactor η ^ (2 * j) * fibreNorm ξ) := by
    have he := fibreScalarData_row_difference_bound d e j ξ hreal hξK t
    rw [hQ j] at he
    have hA : 0 ≤ K.Cj j * peFactor η ^ (2 * j) * fibreNorm ξ :=
      mul_nonneg (mul_nonneg (hC j) (by unfold peFactor; positivity)) (fibreNorm_nonneg ξ)
    rw [← ENNReal.ofReal_add hA hA] at he
    convert he using 1
    congr 1
    ring
  have hzero : cellL2Norm f ≤ ENNReal.ofReal
      ((20 * fibreWordCorrectionBound Cw + 16 * fibreWordCorrectionBound Cw ^ 2) * fibreNorm ξ *
        Real.exp (-(Real.pi ^ 2 / 4) * buffer)) := by
    rw [cellL2Norm_fibreRow_difference_congr d.ell _ e.ell _ her hes ξ t]
    have he := canonicalRow_buffered_literal_L2_difference_bound η Cw hη0 hη hCw G hG
      hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξ lo hi buffer hlohi hbuffer hvw hquiet t ht
    exact he
  exact smoothPeriodic_polynomial_gap_hierarchy f hf hper (fun j => 2 * K.Cj j)
    (20 * fibreWordCorrectionBound Cw + 16 * fibreWordCorrectionBound Cw ^ 2) (peFactor η) (fibreNorm ξ) (Real.pi ^ 2 / 4) buffer
    (fun j => mul_nonneg (by norm_num) (hC j))
    (by have hCr := (fibreWordBounds_nonneg hCw).2; positivity)
    (by unfold peFactor; positivity) (fibreNorm_nonneg ξ) hhigh hzero

/-! Buffered zero-order graph and quadratic symbol replacement from actual common-drift evolution. -/

theorem fibreScalarData_buffered_row_uniform_constants (η Cw : ℝ)
    (hη0 : 0 ≤ η) (hη : η ≤ 1) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {g : ℝ} (hg : IsMetricNearIdentity (fun t _ => G t) g) (hgsmall : g ≤ 1 / 16)
    (v w : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (hw : IsCellDrift w)
    (hmv : ∀ t (j : Fin 2), cellMean (fun x => (v t x j : ℂ)) = 0)
    (hmw : ∀ t (j : Fin 2), cellMean (fun x => (w t x j : ℂ)) = 0)
    (hsv : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (hsw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, w t x i ^ 2) ≤ Cw)
    (V : ℝ) (hbv : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hbw : ∀ t x, ∑ i, w t x i ^ 2 ≤ V ^ 2)
    (ξ : Fin 2 → ℂ)
    (lo hi buffer : ℝ) (hlohi : lo ≤ hi) (hbuffer : 0 ≤ buffer)
    (hvw : ∀ t ∈ Icc (lo - buffer) (hi + buffer), w t = v t)
    (hquiet : 0 < buffer → ∀ t ∈ Icc (lo - buffer) lo, ∀ x, w t x = 0)
    {K : ScalarConstants} {t₀ S : ℝ}
    (d : FibreScalarData K η G v t₀ S) (e : FibreScalarData K η G w t₀ S)
    (hC : ∀ j, 0 ≤ K.Cj j) (hQ : ∀ j, K.Qj j = 2 * j)
    (hreal : ∀ i, (ξ i).im = 0) (hKCw : K.Cw = Cw)
    (hξK : fibreNorm ξ < (scalarBufferedComparisonConstants K).ξ0)
    (her : ∀ p t, d.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients η Cw hη G hG hv hsv p t)
    (hes : ∀ p t, e.ell p t =ᵐ[volume.restrict AVenhance.unitCube]
      fibreAdjointRowCoefficients η Cw hη G hG hw hsw p t)
    (hpd : ∀ t, AVenhance.IsZ2Periodic (fibreSeriesFun d.ell ξ t))
    (hpe : ∀ t, AVenhance.IsZ2Periodic (fibreSeriesFun e.ell ξ t)) :
    ∀ t ∈ Icc (lo - buffer) hi, ∀ j,
      cellSobolevNorm j (fun x => fibreSeriesFun d.ell ξ t x -
        fibreSeriesFun e.ell ξ t x) ≤ ENNReal.ofReal
      ((scalarBufferedComparisonConstants K).Cj j *
        peFactor η ^ (scalarBufferedComparisonConstants K).Qj j * fibreNorm ξ *
        Real.exp (-((scalarBufferedComparisonConstants K).cj j) * buffer)) := by
  have hξold : fibreNorm ξ < K.ξ0 := hξK.trans_le (min_le_left _ _)
  have hξword : fibreNorm ξ ≤ fibreWordRadius Cw := by
    have he : fibreNorm ξ ≤ fibreWordRadius K.Cw := hξK.le.trans (min_le_right _ _)
    simpa only [hKCw] using he
  have he := fibreScalarData_buffered_row_all_order_replacement η Cw hη0 hη hCw G hG
    hg hgsmall v w hv hw hmv hmw hsv hsw V hbv hbw ξ hξword lo hi buffer hlohi hbuffer hvw hquiet
    d e hC hQ hreal hξold her hes hpd hpe
  intro t ht j
  apply (he t ht j).trans
  apply ENNReal.ofReal_le_ofReal
  change smoothPeriodicGapPrice (fun k => 2 * K.Cj k) (20 * fibreWordCorrectionBound Cw + 16 * fibreWordCorrectionBound Cw ^ 2) j *
      peFactor η ^ (2 * j) * fibreNorm ξ *
      Real.exp (-((Real.pi ^ 2 / 4) / (2 : ℝ) ^ j) * buffer) ≤
    scalarBufferedGraphPrice K j * peFactor η ^ K.Qj j * fibreNorm ξ *
      Real.exp (-((Real.pi ^ 2 / 4) / (2 : ℝ) ^ j) * buffer)
  rw [hQ j]
  apply mul_le_mul_of_nonneg_right _ (Real.exp_pos _).le
  apply mul_le_mul_of_nonneg_right _ (fibreNorm_nonneg ξ)
  apply mul_le_mul_of_nonneg_right _ (by unfold peFactor; positivity)
  unfold scalarBufferedGraphPrice
  rw [hKCw]
  exact (le_max_right _ _).trans (le_max_left _ _)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A uniform mass estimate for the actual geometry error on one piece. -/

theorem geometryError_piece_mass_budget_uniform (Hdepth n Kmax : ℕ) (CG Cw Cmol : ℕ → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
      [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
      [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
      [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
      {D : ℕ} {P : Type*} {Ctx : P → Type*}, ∀ (F : ChartedFamily ι h D P Ctx)
    (_hD : 2 ≤ D) (_hdepth : F.HasDepthAtMost Hdepth) (J Ks : ℕ)
    (π : ι → ℝ) (_hπ : ∀ u, 0 < π u) (K : ι → ℕ) (_hK : ∀ u, K u ≤ Kmax)
    (_hdesc : F.IsDescending K) (dom : F.Domain) (ν e E ρ : ℝ)
    (_hν : 0 < ν) (_he : 0 < e) (_hE : 0 < E) (_hρ : 0 < ρ)
    (Jmol : ℕ) (b₀ : ι → ι → ℝ)
    (_henv : IsMolecularEnvelope F π K dom ν e E ρ Cmol Jmol b₀) (_hmeas : F.IsTimeMeasurable)
    (_hb₀ : ∀ v u, 0 ≤ b₀ v u) (_hrow : ∀ v, ∑ u, b₀ v u ≤ 1) (_hcol : ∀ u, ∑ v, b₀ v u ≤ 1)
    (p : P) (c : Ctx p) (a b s ϖ g : ℝ) (_hs : s ≠ 0) (_hϖ : 0 < ϖ) (X0 phase : Vec 2)
    (_hwindow : ∀ t ∈ Set.Icc a b, ∀ Y : Vec 2, (s * t, Y) ∈ dom p c)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (strain B lam : ℝ)
    (_HC : ScalarCoefficientInputs Kmax CG a b (ρ / e) (e / E) v strain B lam G g)
    (tw S : ℝ) (_htw : tw ≤ a) (_htb : b ≤ tw + S)
    (_W : ChartWeights G v tw S ϖ 0 n Cw)
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (U : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Uw : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (fZ : ∀ (_ : Fin (J + 1)) x, PlaneHk Set.univ (K x) (h x))
    (Z : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x) (h x))
    (Zw : ∀ (_ : Fin (J + 1)) x, ℝ → PlaneHk Set.univ (K x + 1) (h x))
    (R : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (_hsol : IsPlaneChainFrom (geometryActualData G (F.cellFiber s phase p c) X0 (e / E))
      (fun _ x => K x) a b v (fun _ x => f x) (fun _ _ _ => 0)
      (fun _ x => U x) (fun _ x => Uw x))
    (_hZ : IsPlaneChainFrom (geometryResponseData J Ks G 0 (F.cellFiber s phase p c) X0 (e / E))
      (fun _ x => K x) a b v fZ (fun _ _ _ => 0) Z Zw)
    (_hR : ∀ x, MemLp (R x) 2 (volume.restrict (Set.Icc a b)))
    (_hRv : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (R x t) =ᵐ[volume]
      geometryErrorRemainderFlux F J Ks K p c G s (e / E) X0 phase (fun j u => Zw j u t) x t),
    (∑ x, ENNReal.ofReal ((π x)⁻¹) * nativeComponentEnergy n ϖ (ρ / e) a b
      (nativeErrorCurve (U x) (fun j => Z j x)) (nativeErrorCurve (Uw x) (fun j => Zw j x))) ≤
      ENNReal.ofReal C *
        ((∑ x, ENNReal.ofReal ((π x)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K x)
          (nativeErrorDatum (f x) (fun j => fZ j x))) +
         ∑ x, ENNReal.ofReal ((π x)⁻¹) * ∫⁻ t in Set.Icc a b,
           weightedFactorialNormSq n ϖ 0 (ρ / e) (K x) (R x t)) := by
  obtain ⟨A, hA, henergy⟩ := geometryError_component_lower_apriori n Kmax CG Cw
  let θ := originalSourceGraphConstant Kmax (Cmol 0)
  have hθ : 0 ≤ θ := originalSourceGraphConstant_nonneg Kmax (Cmol 0)
  let Bprice := 1 + A + A * (32 * θ * (1 + θ)) + A * 32
  have hS : 0 ≤ 32 * θ * (1 + θ) := by positivity
  have hB : 1 ≤ Bprice := by dsimp [Bprice]; nlinarith [mul_nonneg hA hS]
  have hAB : A ≤ Bprice := by dsimp [Bprice]; nlinarith [mul_nonneg hA hS]
  have hSB : A * (32 * θ * (1 + θ)) ≤ Bprice := by dsimp [Bprice]; nlinarith
  have hMB : A * 32 ≤ Bprice := by dsimp [Bprice]; nlinarith [mul_nonneg hA hS]
  let C := (1 + Bprice) ^ Hdepth * Bprice
  have hC : 1 ≤ C := by
    have hP : 1 ≤ (1 + Bprice) ^ Hdepth := one_le_pow₀ (by linarith)
    simpa only [C, one_mul] using mul_le_mul hP hB zero_le_one (zero_le_one.trans hP)
  refine ⟨C, hC, ?_⟩
  intro ι _ h _ _ _ _ _ _ D P Ctx F hD hdepth J Ks π hπ K hK hdesc dom ν e E ρ hν he hE hρ
    Jmol b₀ henv hmeas hb₀ hrow hcol p c a b s ϖ g hs hϖ X0 phase hwindow v G
    strain B lam HC tw S htw htb W f U Uw fZ Z Zw R hsol hZ hR hRv
  let Ue := fun x => nativeErrorCurve (U x) (fun j => Z j x)
  let Uwe := fun x => nativeErrorCurve (Uw x) (fun j => Zw j x)
  have hUwe (x : ι) : MemLp (Uwe x) 2 (volume.restrict (Set.Icc a b)) :=
    nativeTime_sub_sum_memLp _ (Uw x) (fun j => Zw j x) (hsol.2.1 (0, x)) (fun j => hZ.2.1 (j, x))
  obtain ⟨V, hV, hVv, hVb⟩ := originalSource_with_native_remainder_exists F π hπ K Kmax hK hdesc dom
    ν e E ρ hν he hE hρ Cmol Jmol b₀ henv hmeas hb₀ hrow hcol p c s a b ϖ hs hϖ X0 phase
    hwindow Uwe hUwe R hR
    (fun x t => geometryErrorRemainderFlux F J Ks K p c G s (e / E) X0 phase (fun j u => Zw j u t) x t) hRv
  have hv : ∀ x, ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V x t) =ᵐ[volume]
      geometryErrorSourceFlux F J Ks K p c G s (e / E) X0 phase
        (fun u => Uw u t - ∑ j, Zw j u t) (fun j u => Zw j u t) x t := hVv
  have heq := henergy F hD J Ks K hK hdesc p c a b s (e / E) X0 phase v G
    (ρ / e) ϖ g strain B lam HC tw S htw htb W f U Uw fZ Z Zw V hsol hZ hV hv
  let price := fun v u => Real.sqrt (π u / π v) *
    (∑ α : OriginalSourceIndex F v u, originalSourcePrice F K Kmax dom ν e E ρ v u α)
  have hp (v u : ι) : 0 ≤ price v u := mul_nonneg (Real.sqrt_nonneg _)
    (Finset.sum_nonneg (fun α _ => originalSourcePrice_nonneg F K Kmax dom ν e E ρ hν.le hρ.le v u α))
  obtain ⟨hn, _, hc, hsupport⟩ := originalSource_normalized_graph_budget F Hdepth hdepth π K Kmax hK
    dom ν e E ρ hν hE hρ Cmol Jmol b₀ henv hb₀ hrow hcol
  have hcE (u : ι) : (∑ v, ENNReal.ofReal (normalizedFiniteGraph θ price v u)) ≤ 1 := by
    rw [← ENNReal.ofReal_sum_of_nonneg (fun v _ => hn v u)]
    exact (ENNReal.ofReal_le_ofReal (hc u)).trans_eq (by simp)
  have hsE (v u : ι) (hne : ENNReal.ofReal (normalizedFiniteGraph θ price v u) ≠ 0) :
      familyDepthRank F Hdepth u < familyDepthRank F Hdepth v := by
    apply hsupport v u
    intro hz
    exact hne (by rw [hz]; simp)
  have hb := forcedGraph_mass_budget Hdepth (familyDepthRank F Hdepth) (familyDepthRank_le F Hdepth)
    (fun v => (π v)⁻¹) (fun v => inv_nonneg.mpr (hπ v).le) price hp A θ Bprice hA hθ
    (le_trans zero_le_one hB) hAB hSB hMB hcE hsE
    (fun x => nativeComponentEnergy n ϖ (ρ / e) a b (Ue x) (Uwe x))
    (fun x => weightedFactorialNormSq n ϖ 0 (ρ / e) (K x) (nativeErrorDatum (f x) (fun j => fZ j x)))
    (fun x => ∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 (ρ / e) (K x) (V x t))
    (fun x => ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq n ϖ 0 (ρ / e) (K x) (Uwe x t))
    (fun x => ENNReal.ofReal ((π x)⁻¹) * ∫⁻ t in Set.Icc a b,
      weightedFactorialNormSq n ϖ 0 (ρ / e) (K x) (R x t))
    (fun _ => le_add_left le_rfl) heq (hVb n)
  have hcoef : (1 + ENNReal.ofReal Bprice) ^ Hdepth * ENNReal.ofReal Bprice = ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_one, ← ENNReal.ofReal_add zero_le_one (le_trans zero_le_one hB),
      ← ENNReal.ofReal_pow (by linarith : 0 ≤ 1 + Bprice), ← ENNReal.ofReal_mul (by positivity)]
  simpa only [hcoef, Ue, Uwe] using hb

end AVRegularity.CycleWords
end
end
