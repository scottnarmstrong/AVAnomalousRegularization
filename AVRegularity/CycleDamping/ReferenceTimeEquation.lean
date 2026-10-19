-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
import AVRegularity.CycleDamping.CellShiftedGap
public import AVRegularity.Statements.Construction.OcA
import AVRegularity.CoupledEnergy.Galerkin.PlainVariationalEnergy
import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
public import AVRegularity.Statements.Intermediate.CycleEvolution.OcCellDrift
public import AVRegularity.CycleEvolution.CellMetricJetFluxDerivative
import AVRegularity.CycleReference.CorrectorMeanGeometry
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.OcBandChain
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.CycleReference.CoreFlux
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.CycleReference.ChartTestTransport
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
open AVenhance.Infra.Classical
namespace AVRegularity.CycleDamping

/-! Exact scalar linearity of the classical order-one raw jet. -/

theorem cellSmoothScalarJet_const_mul (c : ℝ) (q : Vec 2 → ℝ)
    (hq : Differentiable ℝ q) :
    CycleEvolution.cellSmoothScalarJet (fun x => c * q x) =
      c • CycleEvolution.cellSmoothScalarJet q := by
  funext a x
  rcases a with ⟨j, w⟩
  fin_cases j
  · rfl
  · change fderiv ℝ (fun x => c * q x) x (basisVec (w 0)) =
      c * fderiv ℝ q x (basisVec (w 0))
    rw [fderiv_const_mul (hq x)]
    simp only [smul_apply, smul_eq_mul]

end AVRegularity.CycleDamping
end

section
namespace AVRegularity.CycleDamping

/-! The actual switching error is bounded by the cell memory ratio. -/

theorem switch_error_le_memory_ratio {α q : ℝ} {Λ m : ℕ} {ν : ℝ}
    (hΛ : 1 ≤ Λ) :
    ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
      Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) ≤
      ocEll q Λ m ν ^ 2 / ocTau α q Λ m := by
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have he : 0 ≤ ocEll q Λ m ν ^ 2 / ocTau α q Λ m := div_nonneg (sq_nonneg _) hτ.le
  have hx : -(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (sq_nonneg _)) hτ.le)
      (mul_nonneg (by norm_num) (sq_nonneg _))
  have h := mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hx) he
  simpa only [mul_one] using h

/-! Uniform relaxation on every interior band-chain level. -/

theorem bandChain_relaxation_large {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (R : ℝ) (hR : 0 < R) :
    ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ Λ : ℕ, Λ₀ ≤ Λ →
      ∀ M : ℕ, ∀ κ : ℕ → ℝ, IsOCBandChain α q Λ ζ M κ →
      ∀ m : ℕ, 2 ≤ m → m ≤ M →
        R ≤ ocMu q Λ m (κ m) * ocTau α q Λ m := by
  have hp : 0 < 4 * Real.pi ^ 2 := by positivity
  obtain ⟨L, hL, hb⟩ := bandChain_memory_ratio_small hα₀ hα₁ hs₀ hs₁ hq hζ
    (4 * Real.pi ^ 2 / R) (div_pos hp hR)
  refine ⟨L, hL, ?_⟩
  intro Λ hΛ M κ hκ m hm hmM
  have hΛ1 : 1 ≤ Λ := by omega
  have hν := CycleReference.bandChain_pos hΛ1 hζ hκ hmM
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ1
  have hsmall := hb Λ hΛ M κ hκ m hm hmM
  have hratio := (div_le_div_iff₀ hτ hR).mp hsmall
  have hrate := ocMu_cell_rate (q := q) (m := m) hΛ1 hν
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ1
  have hlen : 0 < ocEll q Λ m (κ m) ^ 2 := by
    rw [CycleReference.ocEll_sq_eq hν]
    positivity
  rw [← hrate] at hratio
  have hf : ocEll q Λ m (κ m) ^ 2 * R ≤
      ocEll q Λ m (κ m) ^ 2 * (ocMu q Λ m (κ m) * ocTau α q Λ m) := by
    calc
      _ = ocEll q Λ m (κ m) ^ 2 * R := rfl
      _ ≤ (ocMu q Λ m (κ m) * ocEll q Λ m (κ m) ^ 2) * ocTau α q Λ m := hratio
      _ = _ := by ring
  exact (mul_le_mul_iff_right₀ hlen).mp hf

/-! The normalized corrector amplitude is controlled by the enhanced reference diffusivity. -/

/-- Exact square of the dimensionless shear amplitude. -/
theorem corrector_amplitude_sq {α q : ℝ} {Λ m : ℕ} {ν B : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hB : 0 < B) :
    (Real.sqrt (ν / B) * ocA α q Λ m * ocEll q Λ m ν ^ 2) ^ 2 =
      2 * ocHStar α q Λ m ν / B := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  rw [mul_pow, mul_pow, Real.sq_sqrt (div_pos hν hB).le,
    CycleReference.ocEll_sq_eq hν, ocA, ocHStar]
  rw [Real.rpow_sub he, Real.rpow_two]
  have hp : (ocEpsilon q Λ m ^ (1 + α)) ^ 2 =
      ocEpsilon q Λ m ^ (2 * (1 + α)) := by
    rw [← Real.rpow_mul_natCast he.le]
    congr 1
    ring
  rw [div_pow, hp]
  field_simp

/-- Mean enhancement bounds the normalized corrector amplitude independently of contrast. -/
theorem corrector_amplitude_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m) :
    Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocA α q Λ m * ocEll q Λ m ν ^ 2 ≤
      Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)) := by
  let c := (1 - Real.exp (-2)) / 96
  let B := ocMeanFlux α q Λ ζ m ν
  have hc : 0 < c := CycleReference.core_coercivity_constant_range.1
  have hlo := (CycleReference.refFlux_mean_core_bounds hΛ hζ hν hrelax).1
  have hH : 0 < ocHStar α q Λ m ν := by
    unfold ocHStar
    have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    positivity
  have hB : 0 < B := (mul_pos hc (add_pos hν hH)).trans_le hlo
  have hHB : ocHStar α q Λ m ν / B ≤ 1 / c := by
    apply (div_le_div_iff₀ hB hc).2
    change ocHStar α q Λ m ν * c ≤ 1 * B
    change c * (ν + ocHStar α q Λ m ν) ≤ B at hlo
    nlinarith only [hlo, mul_pos hc hν]
  have hs := corrector_amplitude_sq (α := α) (q := q) (m := m) hΛ hν hB
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hn : 0 ≤ Real.sqrt (ν / B) * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
    unfold ocA
    positivity
  change _ ≤ Real.sqrt (2 / c)
  apply (Real.le_sqrt hn (div_nonneg (by norm_num) hc.le)).2
  rw [hs]
  calc
    2 * ocHStar α q Λ m ν / B = 2 * (ocHStar α q Λ m ν / B) := by ring
    _ ≤ 2 * (1 / c) := mul_le_mul_of_nonneg_left hHB (by norm_num)
    _ = 2 / c := by ring

/-! Small molecular contrast forces a uniform lower bound on the weighted shear amplitude. -/

theorem corrector_amplitude_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1 / 2) :
    1 ≤ Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
  let B := ocMeanFlux α q Λ ζ m ν
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hc := CycleReference.core_coercivity_constant_range.1
  have hH : 0 < ocHStar α q Λ m ν := by unfold ocHStar; positivity
  have hbounds := CycleReference.refFlux_mean_core_bounds hΛ hζ hν hrelax
  have hB : 0 < B := (mul_pos hc (add_pos hν hH)).trans_le hbounds.1
  have hνB : ν ≤ B / 2 := by
    apply (div_le_iff₀ hB).mp at hη
    linarith only [hη]
  have hHB : B / 2 ≤ ocHStar α q Λ m ν := by
    linarith only [hνB, hbounds.2]
  have hratio : 1 ≤ 2 * ocHStar α q Λ m ν / B := by
    apply (le_div_iff₀ hB).mpr
    linarith only [hHB]
  have hs := corrector_amplitude_sq (α := α) (q := q) (m := m) hΛ hν hB
  have hn : 0 ≤ Real.sqrt (ν / B) * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
    unfold ocA
    positivity
  change 1 ≤ Real.sqrt (ν / B) * ocA α q Λ m * ocEll q Λ m ν ^ 2
  nlinarith only [hratio, hs, hn]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CycleDamping

/-! Weak cell integration by parts using the committed Fourier projection calculus. -/

theorem projected_derivative_pairing (j : Fin 2) (u z : TorusHk 1 ℂ) (N : ℕ) :
    inner ℝ (cellDerivativeCLM j (galerkinProj N u)) (torusHkValueCLM (galerkinProj N z)) =
      -inner ℝ (torusHkValueCLM (galerkinProj N u)) (cellDerivativeCLM j (galerkinProj N z)) := by
  let q := smoothFourierJet (L := 1) N u (valueIndex2 1)
  let r := smoothFourierJet (L := 1) N z (valueIndex2 1)
  have hi := periodic_hilbert_partial_ibp q r ((smoothFourierJet_contDiff N u _).of_le (by simp))
    ((smoothFourierJet_contDiff N z _).of_le (by simp)) (smoothFourierJet_periodic N u _)
    (smoothFourierJet_periodic N z _) j
  rw [L2.inner_def, L2.inner_def]
  have hl : (∫ x in AVenhance.unitCube,
      inner ℝ (cellDerivativeCLM j (galerkinProj N u) x)
        (torusHkValueCLM (galerkinProj N z) x)) =
      ∫ x in AVenhance.unitCube, inner ℝ (fderiv ℝ q x (basisVec j)) (r x) := by
    apply integral_congr_ae
    filter_upwards [galerkinProj_jet_ae_smooth N u ⟨⟨1, by decide⟩, fun _ => j⟩,
      galerkinProj_jet_ae_smooth N z (valueIndex2 1)] with x hu hz
    change cellDerivativeCLM j (galerkinProj N u) x = _ at hu
    change torusHkValueCLM (galerkinProj N z) x = _ at hz
    rw [hu, hz]
    have hd := smoothFourierJet_fderiv (L := 1) N u (0 : Fin 1) Fin.elim0 j x
    change fderiv ℝ q x (basisVec j) = _ at hd
    rw [hd]
    congr 1
  have hr : (∫ x in AVenhance.unitCube,
      inner ℝ (torusHkValueCLM (galerkinProj N u) x)
        (cellDerivativeCLM j (galerkinProj N z) x)) =
      ∫ x in AVenhance.unitCube, inner ℝ (q x) (fderiv ℝ r x (basisVec j)) := by
    apply integral_congr_ae
    filter_upwards [galerkinProj_jet_ae_smooth N u (valueIndex2 1),
      galerkinProj_jet_ae_smooth N z ⟨⟨1, by decide⟩, fun _ => j⟩] with x hu hz
    change torusHkValueCLM (galerkinProj N u) x = _ at hu
    change cellDerivativeCLM j (galerkinProj N z) x = _ at hz
    rw [hu, hz]
    have hd := smoothFourierJet_fderiv (L := 1) N z (0 : Fin 1) Fin.elim0 j x
    change fderiv ℝ r x (basisVec j) = _ at hd
    rw [hd]
    congr 1
  rw [hl, hr]
  exact hi

theorem weak_derivative_pairing (j : Fin 2) (u z : TorusHk 1 ℂ) :
    inner ℝ (cellDerivativeCLM j u) (torusHkValueCLM z) =
      -inner ℝ (torusHkValueCLM u) (cellDerivativeCLM j z) := by
  have hu := galerkinProj_tendsto u
  have hz := galerkinProj_tendsto z
  have hl := ((cellDerivativeCLM j).continuous.continuousAt.tendsto.comp hu).inner (𝕜 := ℝ)
    (torusHkValueCLM.continuous.continuousAt.tendsto.comp hz)
  have hr := ((torusHkValueCLM).continuous.continuousAt.tendsto.comp hu).inner (𝕜 := ℝ)
    ((cellDerivativeCLM j).continuous.continuousAt.tendsto.comp hz) |>.neg
  have he : (fun N => inner ℝ (cellDerivativeCLM j (galerkinProj N u))
      (torusHkValueCLM (galerkinProj N z))) =
      (fun N => -inner ℝ (torusHkValueCLM (galerkinProj N u))
        (cellDerivativeCLM j (galerkinProj N z))) := by
    funext N
    exact projected_derivative_pairing j u z N
  change Tendsto (fun N => inner ℝ (cellDerivativeCLM j (galerkinProj N u))
    (torusHkValueCLM (galerkinProj N z))) atTop
    (𝓝 (inner ℝ (cellDerivativeCLM j u) (torusHkValueCLM z))) at hl
  rw [he] at hl
  exact tendsto_nhds_unique hl hr

theorem scalar_derivative_class (c : ℂ) (z : TorusHk 1 ℂ) (j : Fin 2) :
    cellDerivativeCLM j (cellH1Scalar c z) = cellScalarCLM c (cellDerivativeCLM j z) := by
  apply Lp.ext
  exact (cellH1Scalar_jet_ae c z ⟨⟨1, by decide⟩, fun _ => j⟩).trans
    (cellScalarCLM_ae c (cellDerivativeCLM j z)).symm

theorem weak_complex_derivative_pairing (j : Fin 2) (u z : TorusHk 1 ℂ) :
    cellComplexPair (cellDerivativeCLM j u) (torusHkValueCLM z) =
      -cellComplexPair (torusHkValueCLM u) (cellDerivativeCLM j z) := by
  apply Complex.ext
  · rw [Complex.neg_re, cellComplexPair_re, cellComplexPair_re]
    exact weak_derivative_pairing j u z
  · rw [Complex.neg_im, cellComplexPair_im, cellComplexPair_im,
      ← cellH1Scalar_value, weak_derivative_pairing j u (cellH1Scalar Complex.I z),
      scalar_derivative_class]

end AVRegularity.CycleDamping
end

section
namespace AVRegularity.CycleDamping

/-! A positive lower coupling bound on the selected complete-core orientation. -/

theorem constructed_shear_coupling_lower {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (hη : ν / ocMeanFlux α q Λ ζ m ν ≤ 1 / 2)
    (ξ ξlo : ℝ) (hξ : ξlo / 2 ≤ |ξ|) :
    Real.pi * ξlo ≤ |(2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2) *
      (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ξ)| := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hA : 0 ≤ 2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
    unfold ocA
    positivity
  have hl := corrector_amplitude_lower hΛ hζ hν hrelax hη
  have hmul := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hl (by positivity : 0 ≤ 2 * Real.pi)) (abs_nonneg ξ)
  have hxi := mul_le_mul_of_nonneg_left hξ (by positivity : 0 ≤ 2 * Real.pi)
  rw [abs_mul, abs_of_nonneg hA, abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
  nlinarith only [hmul, hxi]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleDamping

/-! Time measurability follows from the actual graph equation and metric, without a coefficient assumption. -/

theorem fibreQuad_time_measurable {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hG : IsCellMetric (fun t _ => G t)) (ξ : Fin 2 → ℂ) :
    Measurable (fun t => fibreQuad (G t) ξ) := by
  unfold fibreQuad
  apply Finset.measurable_sum
  intro i _
  apply Finset.measurable_sum
  intro j _
  have hm : Measurable (fun t => G t i j) :=
    (CycleEvolution.cellMetric_entry_measurable hG i j).comp
      (measurable_id.prodMk (measurable_const (a := (0 : Vec 2))))
  exact (measurable_const.mul (Complex.continuous_ofReal.measurable.comp hm)).mul_const (ξ j)

theorem graph_symbol_aestronglyMeasurable {η ξ₀ Cg : ℝ}
    {G : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {r : ℕ × ℕ → ℝ → RawJet2 1 ℂ} {lam : ℕ × ℕ → ℝ → ℂ}
    (hG : IsCellMetric (fun t _ => G t)) (hv : IsCellDrift v)
    (h : IsFibreGraph η G v ξ₀ Cg r lam) (ξ : Fin 2 → ℂ)
    (hξ : fibreNorm ξ < ξ₀) :
    AEStronglyMeasurable (fibreSeriesC lam ξ) volume := by
  have hi := (h.2.1 ξ hξ).2.2.1
  have hp : AEStronglyMeasurable (fun p : ℝ × Vec 2 =>
      CycleEvolution.fibreDriftCoupling η v ξ p.1 p.2 *
        cellValue (fibreSeriesJet r ξ) p.1 p.2)
      ((volume.restrict Set.univ).prod (volume.restrict AVenhance.unitCube)) :=
    (CycleEvolution.fibreDriftCoupling_measurable η hv ξ).aestronglyMeasurable.mul
      (hi.1.2.2.2.1 (valueIndex2 1))
  have hm := CycleEvolution.cellMean_aestronglyMeasurable (I := Set.univ)
    (f := fun t x => CycleEvolution.fibreDriftCoupling η v ξ t x *
      cellValue (fibreSeriesJet r ξ) t x) hp
  have hq : AEStronglyMeasurable (fun t => fibreQuad (G t) ξ) (volume.restrict Set.univ) :=
    (fibreQuad_time_measurable hG ξ).aestronglyMeasurable
  have hs : AEStronglyMeasurable (fun t => -(η : ℂ) * fibreQuad (G t) ξ -
      Complex.I * cellMean (fun x => CycleEvolution.fibreDriftCoupling η v ξ t x *
        cellValue (fibreSeriesJet r ξ) t x)) (volume.restrict Set.univ) :=
    (aestronglyMeasurable_const.mul hq).sub (aestronglyMeasurable_const.mul hm)
  have he : AEStronglyMeasurable (fibreSeriesC lam ξ) (volume.restrict Set.univ) := by
    apply hs.congr
    exact Filter.Eventually.of_forall (fun t => ((h.2.1 ξ hξ).2.2.2.1 t).symm)
  simpa only [Measure.restrict_univ] using he

end AVRegularity.CycleDamping
end

section
open Homogenization
namespace AVRegularity.CycleDamping

/-! The glued reference corrector with the normalization and sign of the true cell corrector. -/

/-- The reference corrector in the cell coordinates centered at `y₀`. -/
def cellReferenceValue (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B : ℝ) (y₀ : Vec 2) (t : ℝ) (z : Vec 2) : Vec 2 :=
  -(Real.sqrt (ν / B) / ocEpsilon q Λ m) •
    ocRefCorrector α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t)
      (y₀ + ocEpsilon q Λ m • z)

/-- The product normalization turns cell drift times corrector into physical velocity times
corrector divided by `B`. -/
theorem reference_product_normalization {q : ℝ} {Λ m : ℕ} {ν B : ℝ}
    (hΛ : 1 ≤ Λ) (hν : 0 < ν) (hB : 0 < B) :
    (Real.sqrt (ν / B) * ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
      (Real.sqrt (ν / B) / ocEpsilon q Λ m) = 1 / B := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  rw [CycleReference.ocEll_sq_eq hν]
  calc
    _ = (Real.sqrt (ν / B)) ^ 2 * (ocEpsilon q Λ m ^ 2 / ν) /
        ocEpsilon q Λ m ^ 2 := by ring
    _ = _ := by rw [Real.sq_sqrt (div_pos hν hB).le]; field_simp

end AVRegularity.CycleDamping
end

section
open MeasureTheory Set Filter Topology
open AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Genuine fixed-test complex moment curves are absolutely continuous. -/

theorem complex_time_of_primitive {a b : ℝ} (hab : a ≤ b) (f df : ℝ → ℂ)
    (hdf : IntervalIntegrable df volume a b)
    (he : ∀ t ∈ Icc a b, f t = f a + ∫ s in a..t, df s) :
    StrongTimeRegularity a b f df := by
  apply complex_time_from_components
  · apply scalarStrongTime_of_primitive hab _ _
      (intervalIntegrable_iff.mpr (Complex.reCLM.integrable_comp (intervalIntegrable_iff.mp hdf)))
    intro t ht
    have hr := congrArg Complex.re (he t ht)
    have hi : IntervalIntegrable df volume a t := hdf.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2)
    have hm := Complex.reCLM.intervalIntegral_comp_comm hi
    change (∫ s in a..t, (df s).re) = (∫ s in a..t, df s).re at hm
    rw [Complex.add_re, ← hm] at hr
    exact hr
  · apply scalarStrongTime_of_primitive hab _ _
      (intervalIntegrable_iff.mpr (Complex.imCLM.integrable_comp (intervalIntegrable_iff.mp hdf)))
    intro t ht
    have hr := congrArg Complex.im (he t ht)
    have hi : IntervalIntegrable df volume a t := hdf.mono_set (by
      rw [uIcc_of_le hab, uIcc_of_le ht.1]
      exact Icc_subset_Icc le_rfl ht.2)
    have hm := Complex.imCLM.intervalIntegral_comp_comm hi
    change (∫ s in a..t, (df s).im) = (∫ s in a..t, df s).im at hm
    rw [Complex.add_im, ← hm] at hr
    exact hr

theorem weak_complex_test_strongTime {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → ComplexCellL2} {slice g : ℝ → TorusHk 1 ℂ}
    (h : CellWeakHilbertCurve a b u slice g) (z : TorusHk 1 ℂ) :
    StrongTimeRegularity a b (fun t => cellComplexPair (u t) (torusHkValueCLM z))
      (fun t => cellDualComplexPair (g t) z) := by
  have hp := cellDualComplexPair_intervalIntegrable ⟨le_rfl, hab⟩ ⟨hab, le_rfl⟩ hab g h.dual z
  apply complex_time_of_primitive hab _ _ hp
  intro t ht
  have he := h.complex_increment a ⟨le_rfl, hab⟩ t ht ht.1 z
  exact (eq_add_of_sub_eq he).trans (add_comm _ _)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Removing the cell mean on the actual H¹ quotient. -/

theorem cellDerivative_mean_zero (j : Fin 2) (u : TorusHk 1 ℂ) :
    cellMean (cellDerivativeCLM j u) = 0 := by
  rw [← cellComplexPair_one, ← cellH1One_value,
    weak_complex_derivative_pairing, cellH1One_derivative, cellComplexPair_zero_right, neg_zero]

theorem cellScalar_constant (c d : ℂ) :
    cellScalarCLM c (cellConstantCLM d) = cellConstantCLM (c * d) := by
  apply Lp.ext
  filter_upwards [cellScalarCLM_ae c (cellConstantCLM d), cellConstantCLM_ae d,
    cellConstantCLM_ae (c * d)] with x hs hd hcd
  rw [hs, hd, hcd]

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! The actual physical switching residual in cell coordinates. -/

/-- The centered reference-corrector residual after scaling physical time and space. -/
def cellSwitchResidual (α q : ℝ) (Λ : ℕ) (ζ : ℝ → ℝ) (m : ℕ)
    (ν B : ℝ) (y₀ : Vec 2) (t : ℝ) (z : Vec 2) : Vec 2 :=
  -(Real.sqrt (ν / B) * ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
    (∑' k : {k : ℤ // Odd k},
      deriv (ocCutoff α q Λ m k.1) (ocEll q Λ m ν ^ 2 * t) •
        ocPulseCorrector α q Λ ζ m ν k.1 (ocEll q Λ m ν ^ 2 * t)
          (y₀ + ocEpsilon q Λ m • z))

/-- Euclidean length respects scalar multiplication in the `Vec 2` carrier. -/
theorem sqrt_vecNormSq_smul (c : ℝ) (z : Vec 2) :
    Real.sqrt (vecNormSq (c • z)) = |c| * Real.sqrt (vecNormSq z) := by
  have he : vecNormSq (c • z) = c ^ 2 * vecNormSq z := by
    simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.smul_apply, smul_eq_mul]
    ring
  rw [he, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq_eq_abs]

/-- The switching source has the precise cell-time exponential, with its amplitude exposed. -/
theorem cellSwitchResidual_bound {α q : ℝ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, ∀ Λ : ℕ, 1 ≤ Λ → ∀ m : ℕ, ∀ ν B : ℝ, 0 < ν → 0 < B →
      ∀ y₀ : Vec 2, ∀ t : ℝ, ∀ z : Vec 2,
      Real.sqrt (vecNormSq (cellSwitchResidual α q Λ ζ m ν B y₀ t z)) ≤
        C / (4 * Real.pi ^ 2) *
          (Real.sqrt (ν / B) * ocA α q Λ m * ocEll q Λ m ν ^ 2) *
          (ocEll q Λ m ν ^ 2 / ocTau α q Λ m) *
          Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) := by
  obtain ⟨C, hC⟩ := CycleReference.switching_residual_bound (α := α) (q := q) hζ
  refine ⟨C, ?_⟩
  intro Λ hΛ m ν B hν hB y₀ t z
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have hb := hC Λ hΛ m ν hν (ocEll q Λ m ν ^ 2 * t)
    (y₀ + ocEpsilon q Λ m • z)
  have hs := mul_le_mul_of_nonneg_left hb
    (show 0 ≤ Real.sqrt (ν / B) * ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m by positivity)
  unfold cellSwitchResidual
  rw [sqrt_vecNormSq_smul, abs_neg, abs_of_nonneg (by positivity)]
  refine hs.trans_eq ?_
  rw [ocMu_switch_exponent hΛ hν, CycleReference.ocEll_sq_eq hν, ocMu]
  field_simp

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! Mean removal commutes with shifted gradients on the genuine cell quotient. -/

theorem cellMean_scalar (c : ℂ) (u : ComplexCellL2) :
    cellMean (cellScalarCLM c u) = c * cellMean u := by
  change (∫ x in AVenhance.unitCube, cellScalarCLM c u x) = _
  rw [integral_congr_ae (cellScalarCLM_ae c u), integral_const_mul]
  rfl

theorem cellShiftedDerivative_mean (θ : Fin 2 → ℂ) (u : TorusHk 1 ℂ) (j : Fin 2) :
    cellMean (cellShiftedDerivativeCLM θ j u) = Complex.I * θ j * cellMean (torusHkValueCLM u) := by
  rw [← cellMeanCLM_apply]
  change cellMeanCLM (cellDerivativeCLM j u + cellScalarCLM (Complex.I * θ j) (torusHkValueCLM u)) = _
  rw [map_add, cellMeanCLM_apply, cellMeanCLM_apply, cellDerivative_mean_zero,
    cellMean_scalar, zero_add]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleDamping

/-! The actual Riesz derivative identifies the complex homogeneous generator. -/

theorem dual_complex_generator (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ)
    (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    cellDualComplexPair (cellDualDerivative C hG V hv hb t u S F) z =
      cellComplexGenerator C hG V hv hb t u z + cellComplexSource C.θ S F z := by
  apply Complex.ext
  · rw [cellDualComplexPair_re, Complex.add_re, cellComplexGenerator_re,
      cellComplexSource_re, cellDualDerivative_pairing]
  · rw [cellDualComplexPair_im, Complex.add_im, cellComplexGenerator_im,
      cellComplexSource_im, cellDualDerivative_pairing]

theorem homogeneous_dual_complex_generator (C : CellCoefficients) (hG : IsCellMetric C.G)
    (V : ℝ) (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u z : TorusHk 1 ℂ) :
    cellDualComplexPair (cellDualDerivative C hG V hv hb t u 0 0) z =
      cellComplexGenerator C hG V hv hb t u z := by
  rw [dual_complex_generator]
  simp only [cellComplexSource, cellComplexPair_zero_left, Pi.zero_apply,
    Finset.sum_const_zero, sub_self, add_zero]

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Exact flux of the normalized glued reference corrector, including ramps and quiet gaps. -/

/-- The reference tensor agrees with `J/B` at every cell time and every cell center. -/
theorem cell_reference_flux {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    (y₀ : Vec 2) (t : ℝ) (i j : Fin 2) :
    (ν / B) * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
      (∫ z in unitCube, (Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z i) *
        cellReferenceValue α q Λ ζ m ν B y₀ t z j) =
        ocRefFlux α q Λ ζ m ν (ocEll q Λ m ν ^ 2 * t) i j / B := by
  classical
  let u := ocEll q Λ m ν ^ 2 * t
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k u ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    have hnorm := reference_product_normalization (q := q) (m := m) hΛ hν hB
    have he : (fun z : Vec 2 =>
        (Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z i) *
          cellReferenceValue α q Λ ζ m ν B y₀ t z j) =
        fun z => (ocPulse α q Λ ζ m k u * ocPulseMemory α q Λ ζ m ν k u / B) *
          (ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) i *
            ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) j) := by
      funext z
      simp only [ocCellDrift, cellReferenceValue]
      change Real.sqrt (ν / B) *
        ((ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) •
          streamVel (ocPulseStream α q Λ ζ m) u (y₀ + ocEpsilon q Λ m • z)) i *
        (-(Real.sqrt (ν / B) / ocEpsilon q Λ m) •
          ocRefCorrector α q Λ ζ m ν u (y₀ + ocEpsilon q Λ m • z)) j = _
      simp only [CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
        CycleReference.ocRefCorrector_eq_active hΛ hζ hk hp,
        ocPulseCorrector, Pi.smul_apply, smul_eq_mul]
      calc
        _ = ((Real.sqrt (ν / B) * ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
            (Real.sqrt (ν / B) / ocEpsilon q Λ m)) *
            (ocPulse α q Λ ζ m k u * ocPulseMemory α q Λ ζ m ν k u) *
            (ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) i *
              ocShearVel α q Λ m k (y₀ + ocEpsilon q Λ m • z) j) := by ring
        _ = _ := by rw [hnorm]; ring
    rw [he, integral_const_mul, cell_shear_covariance hΛ hν ⟨k, hk⟩ y₀ i j]
    unfold ocRefFlux
    rw [CycleReference.pulseMatrixSum_eq_at_active hΛ hζ ν u ⟨k, hk⟩ hp]
    simp only [Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
    ring
  · have hz (k : ℤ) (hk : Odd k) : ocPulse α q Λ ζ m k u = 0 := by
      by_contra hne
      exact hp ⟨k, hk, hne⟩
    have hv (z : Vec 2) : ocCellDrift α q Λ ζ m ν y₀ t z = 0 := by
      unfold ocCellDrift
      rw [CycleReference.pulseStreamVel_eq_zero_of_quiet hz]
      exact smul_zero _
    simp only [hv, Pi.zero_apply, mul_zero, zero_mul, integral_zero, add_zero]
    unfold ocRefFlux
    rw [CycleReference.pulseMatrixSum_eq_zero_of_quiet ν u (fun k => hz k.1 k.2)]
    simp only [smul_zero, add_zero, Matrix.smul_apply, smul_eq_mul]
    ring

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleDamping

/-! Actual time differentiability of the glued reference corrector. -/

theorem refCorrector_differentiableAt {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν t : ℝ) (y : Vec 2) (j : Fin 2) :
    DifferentiableAt ℝ (fun s => ocRefCorrector α q Λ ζ m ν s y j) t := by
  classical
  obtain ⟨S, hS⟩ := CycleReference.refCorrector_locally_finite (ζ := ζ) hΛ ν t
  have heq : (fun s => ocRefCorrector α q Λ ζ m ν s y j) =ᶠ[𝓝 t]
      (fun s => ∑ k ∈ S, ocCutoff α q Λ m k.1 s *
        ocPulseCorrector α q Λ ζ m ν k.1 s y j) := by
    filter_upwards [hS] with s hs
    rw [hs]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply DifferentiableAt.congr_of_eventuallyEq _ heq
  apply DifferentiableAt.fun_sum
  intro k hk
  exact ((CycleReference.ocCutoff_contDiff hΛ k.1).differentiable (by simp) t).mul
    (CycleReference.pulseCorrector_hasDerivAt hΛ hζ ν k.1 t y j).differentiableAt

theorem cellReferenceValue_hasDerivAt {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν B t : ℝ) (y₀ z : Vec 2) (j : Fin 2) :
    HasDerivAt (fun s => cellReferenceValue α q Λ ζ m ν B y₀ s z j)
      (-(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
        deriv (fun u => ocRefCorrector α q Λ ζ m ν u
          (y₀ + ocEpsilon q Λ m • z) j) (ocEll q Λ m ν ^ 2 * t) *
        ocEll q Λ m ν ^ 2) t := by
  have hd := (refCorrector_differentiableAt (α := α) (q := q) (m := m) hΛ hζ ν (ocEll q Λ m ν ^ 2 * t)
    (y₀ + ocEpsilon q Λ m • z) j).hasDerivAt
  have hc := hd.comp t ((hasDerivAt_id t).const_mul (ocEll q Λ m ν ^ 2))
  simpa only [cellReferenceValue, Pi.smul_apply, smul_eq_mul, mul_assoc,
    Function.comp_apply, mul_one] using
    hc.const_mul (-(Real.sqrt (ν / B) / ocEpsilon q Λ m))

/-! Joint continuity of the actual locally finite glued corrector. -/

theorem pulseCorrector_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k) (ν : ℝ) (j : Fin 2) :
    Continuous (fun p : ℝ × Vec 2 => ocPulseCorrector α q Λ ζ m ν k p.1 p.2 j) := by
  have hM : Continuous (ocPulseMemory α q Λ ζ m ν k) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (CycleReference.ocPulseMemory_hasDerivAt hΛ hζ ν k t).continuousAt)
  have hv : Continuous (fun y : Vec 2 => ocShearVel α q Λ m k y j) := by
    rcases CycleReference.odd_int_mod_four hk with h1 | h3
    · simp only [CycleReference.ocShearVel_horizontal h1]
      fin_cases j <;> norm_num <;> fun_prop
    · simp only [CycleReference.ocShearVel_vertical h3]
      fin_cases j <;> norm_num <;> fun_prop
  change Continuous (fun p : ℝ × Vec 2 =>
    -(ocPulseMemory α q Λ ζ m ν k p.1) * ocShearVel α q Λ m k p.2 j)
  exact (hM.comp continuous_fst).neg.mul (hv.comp continuous_snd)

theorem refCorrector_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (j : Fin 2) :
    Continuous (fun p : ℝ × Vec 2 => ocRefCorrector α q Λ ζ m ν p.1 p.2 j) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨S, hS⟩ := CycleReference.refCorrector_locally_finite
    (α := α) (q := q) (m := m) (ζ := ζ) hΛ ν p.1
  have he : (fun r : ℝ × Vec 2 => ocRefCorrector α q Λ ζ m ν r.1 r.2 j) =ᶠ[𝓝 p]
      (fun r => ∑ k ∈ S, ocCutoff α q Λ m k.1 r.1 *
        ocPulseCorrector α q Λ ζ m ν k.1 r.1 r.2 j) := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hS] with r hr
    rw [hr]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply ContinuousAt.congr_of_eventuallyEq _ he
  apply Continuous.continuousAt
  apply continuous_finsetSum
  intro k hk
  exact ((CycleReference.ocCutoff_contDiff hΛ k.1).continuous.comp continuous_fst).mul
    (pulseCorrector_joint_continuous hΛ hζ k.2 ν j)

end AVRegularity.CycleDamping
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleDamping

/-! Divergence-free transport annihilates the actual constant complex test. -/

theorem cellDriftForm_constant_right
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ)
    (u z : TorusHk 1 ℂ) (hz : ∀ j, cellDerivativeCLM j z = 0) :
    cellDriftForm v V hv.1 hb t u z = 0 := by
  let B := cellDriftForm v V hv.1 hb t
  have he := cellDriftForm_energy_zero hv V hb t (u + z)
  have hu := cellDriftForm_energy_zero hv V hb t u
  have hz0 (w : TorusHk 1 ℂ) : B z w = 0 := by
    change (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM ⟨0, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j z))
      (torusHkValueCLM w)) = 0
    simp only [hz, map_zero, inner_zero_left, Finset.sum_const_zero]
  change B (u + z) (u + z) = 0 at he
  simp only [map_add, add_apply, hz0] at he
  change B u u = 0 at hu
  change B u z = 0
  linarith only [he, hu]

theorem cellDrift_complex_constant_zero
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2) (t : ℝ) (u : TorusHk 1 ℂ) :
    (∑ j : Fin 2, cellComplexPair
      (cellDriftEntryCLM ⟨G, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u))
      (cellConstantCLM 1)) = 0 := by
  apply Complex.ext
  · have he := cellDriftForm_constant_right v hv V hb t u cellH1One cellH1One_derivative
    change (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM ⟨G, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u))
      (torusHkValueCLM cellH1One)) = 0 at he
    simpa only [Fin.sum_univ_two, Complex.add_re, cellComplexPair_re, cellH1One_value,
      Complex.zero_re] using he
  · have he := cellDriftForm_constant_right v hv V hb t u (cellH1Scalar Complex.I cellH1One)
      (fun j => by rw [scalar_derivative_class, cellH1One_derivative, map_zero])
    change (∑ j : Fin 2, inner ℝ
      (cellDriftEntryCLM ⟨G, v, 0, 0⟩ V hv.1 hb t j (cellDerivativeCLM j u))
      (torusHkValueCLM (cellH1Scalar Complex.I cellH1One))) = 0 at he
    simpa only [Fin.sum_univ_two, Complex.add_im, cellComplexPair_im, cellH1Scalar_value,
      cellH1One_value, Complex.zero_im] using he

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! A template-dependent switching residual bound uniform in the contrast. -/

/-- The normalized switching defect is bounded by a fixed constant times `d_sw`. -/
theorem cellSwitchResidual_uniform_bound {α q : ℝ} {ζ : ℝ → ℝ}
    (hζ : IsFastProfile ζ) :
    ∃ C : ℝ, 0 < C ∧ ∀ Λ : ℕ, 1 ≤ Λ → ∀ m : ℕ, ∀ ν : ℝ, 0 < ν →
      6 ≤ ocMu q Λ m ν * ocTau α q Λ m →
      ∀ y₀ : Vec 2, ∀ t : ℝ, ∀ z : Vec 2,
      Real.sqrt (vecNormSq (cellSwitchResidual α q Λ ζ m ν
        (ocMeanFlux α q Λ ζ m ν) y₀ t z)) ≤
        C * (ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
          Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2))) := by
  obtain ⟨C, hC⟩ := cellSwitchResidual_bound (α := α) (q := q) hζ
  let K := Real.sqrt (2 / ((1 - Real.exp (-2)) / 96))
  let D := (|C| + 1) / (4 * Real.pi ^ 2) * K + 1
  have hD : 0 < D := by dsimp [D, K]; positivity
  refine ⟨D, hD, ?_⟩
  intro Λ hΛ m ν hν hrelax y₀ t z
  have hB : 0 < ocMeanFlux α q Λ ζ m ν :=
    hν.trans_le (CycleReference.meanFlux_ge_input hΛ hζ hν)
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hτ := AVRegularity.Construction.Stream.ocTau_pos (α := α) (q := q) (m := m) hΛ
  have ha := corrector_amplitude_bound (α := α) (q := q) (m := m) hΛ hζ hν hrelax
  have hb := hC Λ hΛ m ν _ hν hB y₀ t z
  calc
    _ ≤ _ := hb
    _ ≤ (|C| + 1) / (4 * Real.pi ^ 2) *
        (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocA α q Λ m * ocEll q Λ m ν ^ 2) *
        (ocEll q Λ m ν ^ 2 / ocTau α q Λ m) *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) := by
      unfold ocA
      gcongr
      exact (le_abs_self C).trans (by linarith)
    _ ≤ (|C| + 1) / (4 * Real.pi ^ 2) * K *
        (ocEll q Λ m ν ^ 2 / ocTau α q Λ m) *
        Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) := by
      gcongr
    _ ≤ _ := by
      dsimp [D]
      have hn : 0 ≤ ocEll q Λ m ν ^ 2 / ocTau α q Λ m *
          Real.exp (-(Real.pi ^ 2) * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) := by positivity
      nlinarith only [hn]

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance Filter Topology
namespace AVRegularity.CycleDamping

/-! Joint continuity of the actual constructed pulse velocity and rescaled cell drift. -/

theorem pulseShearSum_eq_active {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k)
    {t : ℝ} (hp : ocPulse α q Λ ζ m k t ≠ 0) (y : Vec 2) (i : Fin 2) :
    (∑' l : {l : ℤ // Odd l}, ocPulse α q Λ ζ m l.1 t * ocShearVel α q Λ m l.1 y i) =
      ocPulse α q Λ ζ m k t * ocShearVel α q Λ m k y i := by
  classical
  let slot : {l : ℤ // Odd l} := ⟨k, hk⟩
  apply tsum_eq_single slot
  intro l hl
  have hz : ocPulse α q Λ ζ m l.1 t = 0 := by
    by_contra hn
    exact hl (Subtype.ext (CycleReference.odd_pulse_support_unique hΛ hζ
      hk l.2 hp hn).symm)
  rw [hz, zero_mul]

theorem pulseStreamVel_component_tsum {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (t : ℝ) (y : Vec 2) (i : Fin 2) :
    streamVel (ocPulseStream α q Λ ζ m) t y i =
      ∑' k : {k : ℤ // Odd k}, ocPulse α q Λ ζ m k.1 t * ocShearVel α q Λ m k.1 y i := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k t ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    rw [CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp]
    simp only [Pi.smul_apply, smul_eq_mul]
    exact (pulseShearSum_eq_active hΛ hζ hk hp y i).symm
  · have hz : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k t = 0 := by
      intro k hk
      by_contra hn
      exact hp ⟨k, hk, hn⟩
    rw [CycleReference.pulseStreamVel_eq_zero_of_quiet hz]
    simp only [Pi.zero_apply]
    symm
    calc
      _ = ∑' _k : {k : ℤ // Odd k}, (0 : ℝ) := by
        apply tsum_congr
        intro k
        rw [hz k.1 k.2, zero_mul]
      _ = 0 := tsum_zero

theorem pulseStreamVel_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (i : Fin 2) :
    Continuous (fun p : ℝ × Vec 2 => streamVel (ocPulseStream α q Λ ζ m) p.1 p.2 i) := by
  classical
  apply continuous_iff_continuousAt.mpr
  intro p
  obtain ⟨S, hS⟩ := CycleReference.cutoff_locally_finite
    (α := α) (q := q) (m := m) hΛ p.1
  have he : (fun r : ℝ × Vec 2 => streamVel (ocPulseStream α q Λ ζ m) r.1 r.2 i) =ᶠ[𝓝 p]
      (fun r => ∑ k ∈ S, ocPulse α q Λ ζ m k.1 r.1 * ocShearVel α q Λ m k.1 r.2 i) := by
    filter_upwards [continuous_fst.continuousAt.tendsto.eventually hS] with r hr
    rw [pulseStreamVel_component_tsum hΛ hζ]
    apply tsum_eq_sum
    intro k hk
    have hz : ocPulse α q Λ ζ m k.1 r.1 = 0 := by
      by_contra hn
      have h1 := CycleReference.ocCutoff_eq_one_of_pulse_ne_zero hΛ hζ hn
      rw [hr k hk] at h1
      exact zero_ne_one h1
    rw [hz, zero_mul]
  apply ContinuousAt.congr_of_eventuallyEq _ he
  apply Continuous.continuousAt
  apply continuous_finsetSum
  intro k hk
  have hv : Continuous (fun y : Vec 2 => ocShearVel α q Λ m k.1 y i) := by
    rcases CycleReference.odd_int_mod_four k.2 with h1 | h3
    · simp only [CycleReference.ocShearVel_horizontal h1]
      fin_cases i <;> norm_num <;> fun_prop
    · simp only [CycleReference.ocShearVel_vertical h3]
      fin_cases i <;> norm_num <;> fun_prop
  exact ((CycleReference.ocPulse_continuous hζ k.1).comp continuous_fst).mul
    (hv.comp continuous_snd)

theorem ocCellDrift_joint_continuous {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) :
    Continuous (fun p : ℝ × Vec 2 => ocCellDrift α q Λ ζ m ν y₀ p.1 p.2) := by
  apply continuous_pi
  intro i
  have hc := pulseStreamVel_joint_continuous (α := α) (q := q) (m := m) hΛ hζ i
  have ha : Continuous (fun p : ℝ × Vec 2 =>
      (ocEll q Λ m ν ^ 2 * p.1, y₀ + ocEpsilon q Λ m • p.2)) := by fun_prop
  simpa only [ocCellDrift, Pi.smul_apply, smul_eq_mul, Function.comp_def, Pi.mul_def] using
    continuous_const.mul (hc.comp ha)

end AVRegularity.CycleDamping
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleDamping

/-! Uniform pointwise reference-corrector size, including quiet margins and quiet gaps. -/

theorem refCorrector_value_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (t : ℝ) (y : Vec 2) :
    Real.sqrt (vecNormSq (ocRefCorrector α q Λ ζ m ν t y)) ≤
      2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m / ocMu q Λ m ν := by
  have hμ := CycleReference.ocMu_pos (q := q) (m := m) hΛ hν
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have ha : 0 < ocA α q Λ m := by unfold ocA; positivity
  classical
  by_cases hex : ∃ k : {k : ℤ // Odd k},
      ocCutoff α q Λ m k.1 t • ocPulseCorrector α q Λ ζ m ν k.1 t y ≠ 0
  · obtain ⟨k, hk⟩ := hex
    rw [reference_corrector_single hΛ hζ ν t y k hk]
    have hb := CycleReference.pulseCorrector_scaled_norm_le (α := α) (q := q) (m := m) hΛ hζ hν k.1 k.2 t
      (ocCutoff α q Λ m k.1 t) y
    have hM := CycleReference.ocPulseMemory_range (α := α) (q := q) (m := m) hΛ hζ ν hν k.1 t
    have hc : 0 ≤ ocCutoff α q Λ m k.1 t := Real.smoothTransition.nonneg _
    have hc1 : ocCutoff α q Λ m k.1 t ≤ 1 := Real.smoothTransition.le_one _
    rw [abs_of_nonneg hc] at hb
    apply hb.trans
    apply (le_div_iff₀ hμ).2
    have hcm : ocCutoff α q Λ m k.1 t * ocPulseMemory α q Λ ζ m ν k.1 t ≤
        ocPulseMemory α q Λ ζ m ν k.1 t :=
      (mul_le_mul_of_nonneg_right hc1 hM.1).trans_eq (one_mul _)
    have hcmμ := mul_le_mul_of_nonneg_left hcm hμ.le
    have hfinal := mul_le_mul_of_nonneg_right (hcmμ.trans hM.2) (show
      0 ≤ 2 * Real.pi * ocA α q Λ m * ocEpsilon q Λ m by positivity)
    nlinarith only [hfinal]
  · have hz : ocRefCorrector α q Λ ζ m ν t y = 0 := by
      unfold ocRefCorrector
      have hzero (k : {k : ℤ // Odd k}) : ocCutoff α q Λ m k.1 t •
          ocPulseCorrector α q Λ ζ m ν k.1 t y = 0 :=
        not_ne_iff.mp (fun hk => hex ⟨k, hk⟩)
      simp only [hzero, tsum_zero]
    rw [hz]
    simp only [vecNormSq, vecDot, Fin.sum_univ_two, Pi.zero_apply, zero_mul,
      add_zero, Real.sqrt_zero]
    positivity

theorem cellReferenceValue_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B : ℝ} (hν : 0 < ν)
    (t : ℝ) (y₀ z : Vec 2) :
    Real.sqrt (vecNormSq (cellReferenceValue α q Λ ζ m ν B y₀ t z)) ≤
      Real.sqrt (ν / B) * ocA α q Λ m * ocEll q Λ m ν ^ 2 / (2 * Real.pi) := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have hμ := CycleReference.ocMu_pos (q := q) (m := m) hΛ hν
  have hs := Real.sqrt_nonneg (ν / B)
  have hr := ocMu_cell_rate (q := q) (m := m) hΛ hν
  have hL : ocEll q Λ m ν ^ 2 = 4 * Real.pi ^ 2 / ocMu q Λ m ν := by
    apply (eq_div_iff hμ.ne').2
    simpa only [mul_comm] using hr
  unfold cellReferenceValue
  rw [sqrt_vecNormSq_smul, abs_neg, abs_of_nonneg (div_nonneg hs he.le)]
  have hb := mul_le_mul_of_nonneg_left
    (refCorrector_value_bound (α := α) (q := q) (m := m) hΛ hζ hν (ocEll q Λ m ν ^ 2 * t)
      (y₀ + ocEpsilon q Λ m • z)) (div_nonneg hs he.le)
  apply hb.trans_eq
  rw [hL]
  field_simp
  ring

theorem cellReferenceValue_uniform_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (hrelax : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (t : ℝ) (y₀ z : Vec 2) :
    Real.sqrt (vecNormSq (cellReferenceValue α q Λ ζ m ν
      (ocMeanFlux α q Λ ζ m ν) y₀ t z)) ≤
      Real.sqrt (2 / ((1 - Real.exp (-2)) / 96)) / (2 * Real.pi) :=
  (cellReferenceValue_bound hΛ hζ hν t y₀ z).trans
    (div_le_div_of_nonneg_right (corrector_amplitude_bound hΛ hζ hν hrelax)
      (mul_pos (by norm_num) Real.pi_pos).le)

/-! The exact normalized time equation, before weak spatial integration by parts. -/

theorem cellReferenceValue_time_equation {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν : ℝ} (hν : 0 < ν)
    (B t : ℝ) (y₀ z : Vec 2) (j : Fin 2) :
    deriv (fun s => cellReferenceValue α q Λ ζ m ν B y₀ s z j) t +
      4 * Real.pi ^ 2 * cellReferenceValue α q Λ ζ m ν B y₀ t z j =
        Real.sqrt (ν / B) * ocCellDrift α q Λ ζ m ν y₀ t z j +
          cellSwitchResidual α q Λ ζ m ν B y₀ t z j := by
  let u := ocEll q Λ m ν ^ 2 * t
  let y := y₀ + ocEpsilon q Λ m • z
  have heq := CycleReference.refCorrector_equation (α := α) (q := q) (m := m) hΛ hζ ν u y j
  rw [CycleReference.refCorrector_laplacian hΛ,
    CycleReference.pulseStream_transport_refCorrector_zero hΛ hζ, add_zero] at heq
  have hr := ocMu_cell_rate (q := q) (m := m) hΛ hν
  have hr' : ν * (2 * Real.pi * (ocEpsilon q Λ m)⁻¹) ^ 2 *
      ocEll q Λ m ν ^ 2 = 4 * Real.pi ^ 2 := by
    simp only [ocMu, div_eq_mul_inv] at hr
    convert hr using 1
    ring
  classical
  obtain ⟨S, hS⟩ := CycleReference.cutoff_locally_finite (α := α) (q := q) (m := m) hΛ u
  have hz (k : {k : ℤ // Odd k}) (hk : k ∉ S) :
      deriv (ocCutoff α q Λ m k.1) u = 0 := by
    have he : ocCutoff α q Λ m k.1 =ᶠ[nhds u] fun _ => 0 := by
      filter_upwards [hS] with s hs
      exact hs k hk
    rw [he.deriv_eq]
    exact deriv_const _ _
  have hvsum : (∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) u •
      ocPulseCorrector α q Λ ζ m ν k.1 u y) =
      ∑ k ∈ S, deriv (ocCutoff α q Λ m k.1) u •
        ocPulseCorrector α q Λ ζ m ν k.1 u y := by
    apply tsum_eq_sum
    intro k hk
    rw [hz k hk, zero_smul]
  have hssum : (∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) u *
      ocPulseCorrector α q Λ ζ m ν k.1 u y j) =
      ∑ k ∈ S, deriv (ocCutoff α q Λ m k.1) u *
        ocPulseCorrector α q Λ ζ m ν k.1 u y j := by
    apply tsum_eq_sum
    intro k hk
    rw [hz k hk, zero_mul]
  have hcomponent : (∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) u •
      ocPulseCorrector α q Λ ζ m ν k.1 u y) j =
      ∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) u *
        ocPulseCorrector α q Λ ζ m ν k.1 u y j := by
    rw [hvsum, hssum]
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  rw [(cellReferenceValue_hasDerivAt (α := α) (q := q) (m := m) hΛ hζ ν B t y₀ z j).deriv]
  simp only [cellReferenceValue, ocCellDrift, cellSwitchResidual, Pi.smul_apply,
    smul_eq_mul]
  change -(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
      deriv (fun s => ocRefCorrector α q Λ ζ m ν s y j) u * ocEll q Λ m ν ^ 2 +
      4 * Real.pi ^ 2 * (-(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
        ocRefCorrector α q Λ ζ m ν u y j) =
      Real.sqrt (ν / B) * (ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
        streamVel (ocPulseStream α q Λ ζ m) u y j) +
      -(Real.sqrt (ν / B) * ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m) *
        (∑' k : {k : ℤ // Odd k}, deriv (ocCutoff α q Λ m k.1) u •
          ocPulseCorrector α q Λ ζ m ν k.1 u y) j
  rw [hcomponent]
  linear_combination -(Real.sqrt (ν / B) / ocEpsilon q Λ m) *
    ocEll q Λ m ν ^ 2 * heq +
    (Real.sqrt (ν / B) / ocEpsilon q Λ m) *
    ocRefCorrector α q Λ ζ m ν u y j * hr'

end AVRegularity.CycleDamping
end
