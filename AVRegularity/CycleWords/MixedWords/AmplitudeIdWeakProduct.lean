-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.MixedWords.AmplitudeIdCellEnergy
import AVRegularity.CycleJoint.NativePiolaJetRowEquality

/-! The weak product commutator behind the actual moment fibre equation. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane
open AVRegularity.CycleJointProofs
namespace AVRegularity.CycleWords.Assembly

open Filter AVRegularity.CoupledEnergyPlane.Fourier
open scoped Topology

section OrderedPairing
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

private theorem amplitudeId_tendsto_orderedWord_readout {K m : ℕ} (hm : m ≤ K)
    (U : PlaneHk Set.univ K E) (w : DerivativeWord2 m) :
    Tendsto (fun N => hilbertWordOperator N w (univToPlane (U.val (valueIndex2 K))))
      atTop (𝓝 (univToPlane (U.val ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩))) := by
  have h := (univToPlane.continuous.tendsto
    (U.val ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩)).comp
      (tendsto_hilbertBandHk_component K U ⟨⟨m, Nat.lt_succ_of_le hm⟩, w⟩)
  simpa only [Function.comp_def, hilbertBandHk_component, univToPlane_planeToUniv,
    hilbertWordOperator] using h

private theorem amplitudeId_planeHk_ordered_jet_pairing {K L m : ℕ} (hmK : m ≤ K) (hmL : m ≤ L)
    (U : PlaneHk Set.univ K E) (Z : PlaneHk Set.univ L E) (w : DerivativeWord2 m) :
    inner ℝ (univToPlane (U.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩))
      (univToPlane (Z.val (valueIndex2 L))) =
      (-1 : ℝ) ^ m * inner ℝ (univToPlane (U.val (valueIndex2 K)))
        (univToPlane (Z.val ⟨⟨m, Nat.lt_succ_of_le hmL⟩, w⟩)) := by
  have hl := (amplitudeId_tendsto_orderedWord_readout hmK U w).inner (𝕜 := ℝ)
    (tendsto_const_nhds (x := univToPlane (Z.val (valueIndex2 L))))
  have hr := (tendsto_const_nhds (x := (-1 : ℝ) ^ m)).mul
    ((tendsto_const_nhds (x := univToPlane (U.val (valueIndex2 K)))).inner (𝕜 := ℝ)
      (amplitudeId_tendsto_orderedWord_readout hmL Z w))
  exact tendsto_nhds_unique hl
    (hr.congr (fun N => (hilbertWord_ordered_inner N w _ _).symm))

end OrderedPairing

/-- The moment forcing is exactly the product commutator, up to a weak spatial divergence. -/
theorem amplitudeId_moment_rhs_algebra
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (v dm du S : Fin 2 → ℝ) (H : Fin 2 → Fin 2 → ℝ)
    (m u : ℝ) (p ψ : ℂ) (dψ : Fin 2 → ℂ) :
    -(∑ i : Fin 2, ∑ k : Fin 2, (G i k : ℂ) *
        (p * ((m * du i + dm i * u : ℝ) : ℂ)) * dψ k) -
      (∑ i : Fin 2, (v i : ℂ) * (p * ((m * du i + dm i * u : ℝ) : ℂ)) * ψ) +
      p * (((∑ i : Fin 2, ∑ k : Fin 2, G i k * H i k) +
        ∑ i : Fin 2, v i * dm i) * u - ∑ i : Fin 2, dm i * S i : ℝ) * ψ -
      (∑ i : Fin 2, p * ((m * S i -
        (∑ k : Fin 2, (G i k + G k i) * dm k) * u : ℝ) : ℂ) * dψ i) =
    -(∑ i : Fin 2, ∑ k : Fin 2, (G i k : ℂ) * (du i : ℂ) *
        (p * ((m : ℂ) * dψ k + (dm k : ℂ) * ψ))) -
      (∑ i : Fin 2, (v i : ℂ) * (du i : ℂ) * (p * (m : ℂ) * ψ)) -
      (∑ i : Fin 2, (S i : ℂ) * (p * ((m : ℂ) * dψ i + (dm i : ℂ) * ψ))) +
      ∑ i : Fin 2, ∑ k : Fin 2, (G i k : ℂ) * p *
        ((du i : ℂ) * (dm k : ℂ) * ψ +
          (u : ℂ) * ((H k i : ℂ) * ψ + (dm k : ℂ) * dψ i)) := by
  have hs : G 1 0 = G 0 1 := hG.apply 0 1
  simp only [Fin.sum_univ_two, hs]
  push_cast
  ring

/-- A real projection of a complex spatial pairing is its genuine native Hilbert pairing. -/
theorem amplitudeId_plane_bilinear_projection
    (f : Lp ℝ 2 (volume : Measure (Vec 2))) (Z : PlaneHk Set.univ 1 ℂ)
    (a : JetIndex2 1) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, (f y : ℂ) * Z.toFunction.jet a y) =
      inner ℝ f (univToPlane ((mapPlaneHk L Z).val a)) := by
  have hz : MemLp (Z.toFunction.jet a) 2 volume := by
    simpa only [Measure.restrict_univ] using Z.toFunction.memL2 a
  have hi : Integrable (fun y => (f y : ℂ) * Z.toFunction.jet a y) volume :=
    (Lp.memLp f).ofReal.integrable_mul hz
  rw [← L.integral_comp_comm hi, L2.inner_def]
  have hread : univToPlane ((mapPlaneHk L Z).val a) =ᵐ[volume]
      fun y => L (Z.toFunction.jet a y) :=
    (univToPlane_ae _).trans (planeHkMapRawReadout L Z a)
  apply integral_congr_ae
  filter_upwards [hread] with y hy
  rw [hy, Real.inner_apply]
  have h := L.map_smul (f y) (Z.toFunction.jet a y)
  simpa only [Complex.real_smul, smul_eq_mul, mul_comm] using h

/-- Complex bilinear plane tests satisfy the actual weak integration-by-parts identity. -/
theorem amplitudeId_plane_bilinear_first_pair
    (U : PlaneHk Set.univ 1 ℝ) (Z : PlaneHk Set.univ 1 ℂ) (i : Fin 2) :
    (∫ y, ((U.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y : ℝ) : ℂ) *
      Z.toFunction.jet (valueIndex2 1) y) =
      -(∫ y, ((U.toFunction.jet (valueIndex2 1) y : ℝ) : ℂ) *
        Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) := by
  let a : JetIndex2 1 := ⟨⟨1, by decide⟩, fun _ => i⟩
  let o : JetIndex2 1 := valueIndex2 1
  have hU (b : JetIndex2 1) : MemLp (U.toFunction.jet b) 2 volume := by
    simpa only [Measure.restrict_univ] using U.toFunction.memL2 b
  have hZ (b : JetIndex2 1) : MemLp (Z.toFunction.jet b) 2 volume := by
    simpa only [Measure.restrict_univ] using Z.toFunction.memL2 b
  have hleft : Integrable (fun y => (U.toFunction.jet a y : ℂ) * Z.toFunction.jet o y) volume :=
    (hU a).ofReal.integrable_mul (hZ o)
  have hright : Integrable (fun y => (U.toFunction.jet o y : ℂ) * Z.toFunction.jet a y) volume :=
    (hU o).ofReal.integrable_mul (hZ a)
  have hreal (L : ℂ →L[ℝ] ℝ) :
      (∫ y, U.toFunction.jet a y * L (Z.toFunction.jet o y)) =
        -(∫ y, U.toFunction.jet o y * L (Z.toFunction.jet a y)) := by
    let ZL := mapPlaneHk L Z
    have h := amplitudeId_planeHk_ordered_jet_pairing (K := 1) (L := 1) (m := 1)
      le_rfl le_rfl U ZL (fun _ => i)
    simp only [pow_one, neg_mul, one_mul, L2.inner_def] at h
    have hu (b : JetIndex2 1) :
        univToPlane (U.val b) =ᵐ[volume] U.toFunction.jet b := univToPlane_ae _
    have hz (b : JetIndex2 1) : univToPlane (ZL.val b) =ᵐ[volume]
        fun y => L (Z.toFunction.jet b y) :=
      (univToPlane_ae _).trans (planeHkMapRawReadout L Z b)
    calc
      _ = ∫ y, inner ℝ (univToPlane (U.val a) y) (univToPlane (ZL.val o) y) := by
        apply integral_congr_ae
        filter_upwards [hu a, hz o] with y huy hzy
        rw [huy, hzy, Real.inner_apply]
      _ = -(∫ y, inner ℝ (univToPlane (U.val o) y) (univToPlane (ZL.val a) y)) := h
      _ = _ := by
        congr 1
        apply integral_congr_ae
        filter_upwards [hu o, hz a] with y huy hzy
        rw [huy, hzy, Real.inner_apply]
  apply Complex.ext
  · rw [Complex.neg_re]
    change Complex.reCLM (∫ y, (U.toFunction.jet a y : ℂ) * Z.toFunction.jet o y) =
      -Complex.reCLM (∫ y, (U.toFunction.jet o y : ℂ) * Z.toFunction.jet a y)
    rw [← Complex.reCLM.integral_comp_comm hleft, ← Complex.reCLM.integral_comp_comm hright]
    simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.reCLM_apply] using hreal Complex.reCLM
  · rw [Complex.neg_im]
    change Complex.imCLM (∫ y, (U.toFunction.jet a y : ℂ) * Z.toFunction.jet o y) =
      -Complex.imCLM (∫ y, (U.toFunction.jet o y : ℂ) * Z.toFunction.jet a y)
    rw [← Complex.imCLM.integral_comp_comm hleft, ← Complex.imCLM.integral_comp_comm hright]
    simpa only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero, Complex.imCLM_apply] using hreal Complex.imCLM

/-- A real native weak curve admits every complex H1 bilinear test, with its actual dual. -/
theorem amplitudeId_plane_complex_increment {a b : ℝ}
    {u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 ℝ}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (Z : PlaneHk Set.univ 1 ℂ) :
    (∫ y, (u t y : ℂ) * Z.toFunction.jet (valueIndex2 1) y) -
      (∫ y, (u s y : ℂ) * Z.toFunction.jet (valueIndex2 1) y) =
      ∫ r in s..t, (inner ℝ (dual r) (mapPlaneHk Complex.reCLM Z) : ℂ) +
        Complex.I * (inner ℝ (dual r) (mapPlaneHk Complex.imCLM Z) : ℂ) := by
  have hint (L : ℂ →L[ℝ] ℝ) : IntervalIntegrable
      (fun r => inner ℝ (dual r) (mapPlaneHk L Z)) volume s t :=
    planeWeakPair_intervalIntegrable hs ht hst dual h.dual_mem (mapPlaneHk L Z)
  have hre := h.increment s hs t ht hst (mapPlaneHk Complex.reCLM Z)
  have him := h.increment s hs t ht hst (mapPlaneHk Complex.imCLM Z)
  have hcast (L : ℂ →L[ℝ] ℝ) : IntervalIntegrable
      (fun r => (inner ℝ (dual r) (mapPlaneHk L Z) : ℂ)) volume s t :=
    ⟨Complex.ofRealCLM.integrable_comp (hint L).1,
      Complex.ofRealCLM.integrable_comp (hint L).2⟩
  have hiRe := hcast Complex.reCLM
  have hiIm := (hcast Complex.imCLM).const_mul Complex.I
  rw [intervalIntegral.integral_add hiRe hiIm,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
    intervalIntegral.integral_ofReal]
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero]
    exact (congrArg₂ (fun x y : ℝ => x - y)
      (amplitudeId_plane_bilinear_projection (u t) Z (valueIndex2 1) Complex.reCLM)
      (amplitudeId_plane_bilinear_projection (u s) Z (valueIndex2 1) Complex.reCLM)).trans hre
  · simp only [Complex.sub_im, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add]
    exact (congrArg₂ (fun x y : ℝ => x - y)
      (amplitudeId_plane_bilinear_projection (u t) Z (valueIndex2 1) Complex.imCLM)
      (amplitudeId_plane_bilinear_projection (u s) Z (valueIndex2 1) Complex.imCLM)).trans him

/-- The literal complex bilinear spatial side of the real divergence-forced plane equation. -/
def amplitudeId_planeWeakRhs (G : Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → Vec 2)
    (W : PlaneHk Set.univ 1 ℝ) (S : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (Z : PlaneHk Set.univ 1 ℂ) (y : Vec 2) : ℂ :=
  -(∑ i : Fin 2, ∑ k : Fin 2,
      ((G i k * planeH1GradientOperator W i y : ℝ) : ℂ) *
        Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => k⟩ y) -
    (∑ i : Fin 2, ((v y i * planeH1GradientOperator W i y : ℝ) : ℂ) *
      Z.toFunction.jet (valueIndex2 1) y) -
    ∑ i : Fin 2, (S i y : ℂ) * Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y

/-- Bounded drift and native L2 fields make every term of the complex weak side integrable. -/
theorem amplitudeId_planeWeakRhs_integrable
    (G : Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (W : PlaneHk Set.univ 1 ℝ) (S : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (Z : PlaneHk Set.univ 1 ℂ) (t : ℝ) :
    Integrable (amplitudeId_planeWeakRhs G (v t) W S Z) volume := by
  obtain ⟨V, hb⟩ := hv.2.1
  have hZ (a : JetIndex2 1) : MemLp (Z.toFunction.jet a) 2 volume := by
    simpa only [Measure.restrict_univ] using Z.toFunction.memL2 a
  have hdu (i : Fin 2) : MemLp (fun y => v t y i * planeH1GradientOperator W i y) 2 volume := by
    have hm : Measurable (fun y => v t y i) :=
      (measurable_pi_apply i).comp (hv.1.comp (measurable_const.prodMk measurable_id))
    apply (Lp.memLp (planeH1GradientOperator W i)).of_le_mul
      (hm.aestronglyMeasurable.mul (Lp.memLp _).aestronglyMeasurable)
    exact Filter.Eventually.of_forall (fun y => by
      change ‖v t y i * planeH1GradientOperator W i y‖ ≤ |V| * ‖planeH1GradientOperator W i y‖
      rw [norm_mul, Real.norm_eq_abs (v t y i)]
      exact mul_le_mul_of_nonneg_right (CycleEvolution.cellDrift_entry_bound hb t y i) (norm_nonneg _))
  exact ((integrable_finsetSum Finset.univ (fun i _ =>
    integrable_finsetSum Finset.univ (fun k _ =>
      ((Lp.memLp (planeH1GradientOperator W i)).const_mul (G i k)).ofReal.integrable_mul
        (hZ ⟨⟨1, by decide⟩, fun _ => k⟩)))).neg.sub
    (integrable_finsetSum Finset.univ (fun i _ => (hdu i).ofReal.integrable_mul
      (hZ (valueIndex2 1))))).sub
    (integrable_finsetSum Finset.univ (fun i _ => (Lp.memLp (S i)).ofReal.integrable_mul
      (hZ ⟨⟨1, by decide⟩, fun _ => i⟩)))

private theorem amplitudeId_real_coefficient_projection (L : ℂ →L[ℝ] ℝ) (a : ℝ) (z : ℂ) :
    L ((a : ℂ) * z) = a * L z := by
  simpa only [Complex.real_smul, smul_eq_mul] using L.map_smul a z

/-- The complex spatial expression projects to exactly the native real generator and source. -/
theorem amplitudeId_planeWeakRhs_projection
    (G : Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (t C : ℝ) (hC : ∀ i y, ‖cellDriftTorusSymbol v t i y‖ ≤ C)
    (W : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ)
    (Z : PlaneHk Set.univ 1 ℂ) (L : ℂ →L[ℝ] ℝ) :
    L (∫ y, amplitudeId_planeWeakRhs G (v t) W S Z y) =
      inner ℝ (planeRealBlochGeneratorDual G v hv t C hC W + planeSourceDual 0 S)
        (mapPlaneHk L Z) := by
  rw [← L.integral_comp_comm (amplitudeId_planeWeakRhs_integrable G v hv W S Z t),
    planeRealBlochNativeFlux_pair]
  have hmap (a : JetIndex2 1) :
      univToPlane ((mapPlaneHk L Z).val a) =ᵐ[volume] fun y => L (Z.toFunction.jet a y) :=
    (univToPlane_ae _).trans (planeHkMapRawReadout L Z a)
  apply integral_congr_ae
  filter_upwards [hmap (valueIndex2 1),
    ae_all_iff.mpr (fun i : Fin 2 => hmap ⟨⟨1, by decide⟩, fun _ => i⟩)] with y hy hd
  simp only [amplitudeId_planeWeakRhs, map_sub, map_neg, map_sum,
    amplitudeId_real_coefficient_projection, planeRealBlochSpatialRhs,
    planeRealH1TestGradient, planeH1GradientOperator_apply,
    CoupledEnergyPlane.Fourier.planeHkValueOperator_apply,
    hy, hd, Real.inner_apply]
  simp only [Fin.sum_univ_two]
  ring

/-- The actual forced plane weak curve has the literal complex spatial increment. -/
theorem amplitudeId_plane_forced_increment {a b : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (C : ℝ) (hC : ∀ r i y, ‖cellDriftTorusSymbol v r i y‖ ≤ C)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (W : ℝ → PlaneHk Set.univ 1 ℝ) (S : ℝ → PlaneFluxL2 ℝ)
    (h : PlaneWeakHilbertCurve a b u W (fun r =>
      planeRealBlochGeneratorDual (G r) v hv r C (hC r) (W r) + planeSourceDual 0 (S r)))
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (Z : PlaneHk Set.univ 1 ℂ) :
    (∫ y, (u t y : ℂ) * Z.toFunction.jet (valueIndex2 1) y) -
      (∫ y, (u s y : ℂ) * Z.toFunction.jet (valueIndex2 1) y) =
      ∫ r in s..t, ∫ y, amplitudeId_planeWeakRhs (G r) (v r) (W r) (S r) Z y := by
  have hi := amplitudeId_plane_complex_increment h hs ht hst Z
  refine hi.trans (intervalIntegral.integral_congr (fun r _ => ?_))
  have hre := amplitudeId_planeWeakRhs_projection (G r) v hv r C (hC r) (W r) (S r) Z Complex.reCLM
  have him := amplitudeId_planeWeakRhs_projection (G r) v hv r C (hC r) (W r) (S r) Z Complex.imCLM
  apply Complex.ext
  · simpa only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero, Complex.reCLM_apply] using hre.symm
  · simpa only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, Complex.imCLM_apply] using him.symm

/-- A compact smooth scalar coefficient gives a genuine localized complex H1 test. -/
def amplitudeId_scalarLocalTest (Z : TorusHk 1 ℂ) (c : Vec 2 → ℂ)
    (hc : ContDiff ℝ (1 : ℕ) c) (hcompact : HasCompactSupport c) : PlaneHk Set.univ 1 ℂ :=
  CycleJointProofs.localizeTorusCarrier Z
    (fun y => ContinuousLinearMap.mul ℝ ℂ (c y))
    ((ContinuousLinearMap.mul ℝ ℂ).contDiff.comp hc)
    (hcompact.comp_left (ContinuousLinearMap.map_zero _))

/-- The localized native test has the literal value and the literal Leibniz first derivative. -/
theorem amplitudeId_scalarLocalTest_readout (Z : TorusHk 1 ℂ) (c : Vec 2 → ℂ)
    (hc : ContDiff ℝ (1 : ℕ) c) (hcompact : HasCompactSupport c) :
    ((amplitudeId_scalarLocalTest Z c hc hcompact).toFunction.jet (valueIndex2 1) =ᵐ[volume]
      fun y => c y * Z.toFunction.jet (valueIndex2 1) y) ∧
    ∀ i : Fin 2, (amplitudeId_scalarLocalTest Z c hc hcompact).toFunction.jet
      ⟨⟨1, by decide⟩, fun _ => i⟩ =ᵐ[volume] fun y =>
        c y * Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y +
          fderiv ℝ c y (basisVec i) * Z.toFunction.jet (valueIndex2 1) y := by
  let C := fun y => ContinuousLinearMap.mul ℝ ℂ (c y)
  have hC := (ContinuousLinearMap.mul ℝ ℂ).contDiff.comp hc
  have hcomp := hcompact.comp_left (ContinuousLinearMap.map_zero (ContinuousLinearMap.mul ℝ ℂ))
  constructor
  · exact CycleJointProofs.localizeTorusCarrier_value_ae Z C hC hcomp
  · intro i
    have hd (y : Vec 2) : fderiv ℝ C y =
        (ContinuousLinearMap.mul ℝ ℂ).comp (fderiv ℝ c y) :=
      ((ContinuousLinearMap.mul ℝ ℂ).hasFDerivAt.comp y
        (hc.differentiable (by norm_num)).differentiableAt.hasFDerivAt).fderiv
    filter_upwards [CycleJointProofs.localizeTorusCarrier_jet_ae Z C hC hcomp
      ⟨⟨1, by decide⟩, fun _ => i⟩] with y hy
    change (CycleJointProofs.localizeTorusCarrier Z C hC hcomp).toFunction.jet
      ⟨⟨1, by decide⟩, fun _ => i⟩ y = _
    rw [hy, CycleJointProofs.multiplicationRawJet_first, hd]
    rfl

/-- The compact coefficient used to test a phase-weighted scalar plane value. -/
def amplitudeId_weightedTestCoefficient (θ : Vec 2) (m q : Vec 2 → ℝ) (y : Vec 2) : ℂ :=
  (q y : ℂ) * Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (m y : ℂ)

/-- Smooth real weights and cutoffs give a smooth compact complex testing coefficient. -/
theorem amplitudeId_weightedTestCoefficient_regular (θ : Vec 2) (m q : Vec 2 → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hcompact : HasCompactSupport q) :
    ContDiff ℝ (⊤ : ℕ∞) (amplitudeId_weightedTestCoefficient θ m q) ∧
      HasCompactSupport (amplitudeId_weightedTestCoefficient θ m q) := by
  refine ⟨((Complex.ofRealCLM.contDiff.comp hq).mul (amplitudeId_phase_contDiff θ)).mul
    (Complex.ofRealCLM.contDiff.comp hm), ?_⟩
  exact ((hcompact.comp_left Complex.ofReal_zero).mul_right).mul_right

/-- The actual derivative of the testing coefficient includes the radian covariant shift. -/
theorem amplitudeId_weightedTestCoefficient_fderiv (θ : Vec 2) (m q : Vec 2 → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (y : Vec 2) (i : Fin 2) :
    fderiv ℝ (amplitudeId_weightedTestCoefficient θ m q) y (basisVec i) =
      Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (((fderiv ℝ m y (basisVec i) * q y + m y * fderiv ℝ q y (basisVec i) : ℝ) : ℂ) -
          Complex.I * (θ i : ℂ) * (m y : ℂ) * (q y : ℂ)) := by
  have hm' := (hm.differentiable (by simp)).differentiableAt (x := y)
  have hq' := (hq.differentiable (by simp)).differentiableAt (x := y)
  have hp' := ((amplitudeId_phase_contDiff θ).differentiable (by simp)).differentiableAt (x := y)
  have hmc : DifferentiableAt ℝ (fun z => (m z : ℂ)) y :=
    Complex.ofRealCLM.differentiableAt.comp y hm'
  have hqc : DifferentiableAt ℝ (fun z => (q z : ℂ)) y :=
    Complex.ofRealCLM.differentiableAt.comp y hq'
  have hd (f : Vec 2 → ℝ) (hf : DifferentiableAt ℝ f y) :
      fderiv ℝ (fun z => (f z : ℂ)) y = Complex.ofRealCLM.comp (fderiv ℝ f y) :=
    (Complex.ofRealCLM.hasFDerivAt.comp y hf.hasFDerivAt).fderiv
  unfold amplitudeId_weightedTestCoefficient
  have hout := fderiv_fun_mul (hqc.mul hp') hmc
  simp only [Pi.mul_apply] at hout
  rw [hout, fderiv_mul hqc hp', hd q hq', hd m hm']
  simp only [smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply,
    add_apply, smul_eq_mul, amplitudeId_phase_fderiv, Complex.ofReal_add, Complex.ofReal_mul]
  ring

/-- The compactly tested covariant equation of a phase-weighted real moment. -/
def amplitudeId_momentWeakRhs (G : Matrix (Fin 2) (Fin 2) ℝ) (v : Vec 2 → Vec 2)
    (θ : Vec 2) (m : Vec 2 → ℝ) (W : PlaneHk Set.univ 1 ℝ)
    (S : PlaneFluxL2 ℝ) (Z : TorusHk 1 ℂ) (q : Vec 2 → ℝ) (y : Vec 2) : ℂ :=
  let p := Complex.exp (-(Complex.I * (vecDot θ y : ℂ)))
  let u := W.toFunction.jet (valueIndex2 1) y
  let du := fun i => planeH1GradientOperator W i y
  let dm := fun i => fderiv ℝ m y (basisVec i)
  let H := fun i k => fderiv ℝ (fun z => fderiv ℝ m z (basisVec i)) y (basisVec k)
  let ψ := (q y : ℂ) * Z.toFunction.jet (valueIndex2 1) y
  let dψ := fun i => (q y : ℂ) * Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y +
    ((fderiv ℝ q y (basisVec i) : ℂ) - Complex.I * (θ i : ℂ) * (q y : ℂ)) *
      Z.toFunction.jet (valueIndex2 1) y
  show ℂ from
  -(∑ i : Fin 2, ∑ k : Fin 2, (G i k : ℂ) *
      (p * ((m y * du i + dm i * u : ℝ) : ℂ)) * dψ k) -
    (∑ i : Fin 2, (v y i : ℂ) * (p * ((m y * du i + dm i * u : ℝ) : ℂ)) * ψ) +
    p * (((∑ i : Fin 2, ∑ k : Fin 2, G i k * H i k) +
      ∑ i : Fin 2, v y i * dm i) * u - ∑ i : Fin 2, dm i * S i y : ℝ) * ψ -
    (∑ i : Fin 2, p * ((m y * S i y -
      (∑ k : Fin 2, (G i k + G k i) * dm k) * u : ℝ) : ℂ) * dψ i)

/-- The compact moment equation follows by the native weak product rule and spatial IBP. -/
theorem amplitudeId_localized_moment_rhs
    (G : Matrix (Fin 2) (Fin 2) ℝ) (hG : G.IsSymm)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (t : ℝ)
    (θ : Vec 2) (m q : Vec 2 → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hcompact : HasCompactSupport q)
    (W : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ) (Z : TorusHk 1 ℂ) :
    let hc := amplitudeId_weightedTestCoefficient_regular θ m q hm hq hcompact
    let T := amplitudeId_scalarLocalTest Z (amplitudeId_weightedTestCoefficient θ m q)
      (hc.1.of_le (by simp)) hc.2
    Integrable (amplitudeId_momentWeakRhs G (v t) θ m W S Z q) volume ∧
      (∫ y, amplitudeId_momentWeakRhs G (v t) θ m W S Z q y) =
        ∫ y, amplitudeId_planeWeakRhs G (v t) W S T y := by
  classical
  dsimp only
  let dm := fun i : Fin 2 => fun y => fderiv ℝ m y (basisVec i)
  have hdm (i : Fin 2) : ContDiff ℝ (⊤ : ℕ∞) (dm i) :=
    (hm.fderiv_right (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const
  let c := amplitudeId_weightedTestCoefficient θ m q
  have hc := amplitudeId_weightedTestCoefficient_regular θ m q hm hq hcompact
  let T := amplitudeId_scalarLocalTest Z c (hc.1.of_le (by simp)) hc.2
  let ca := fun i => amplitudeId_weightedTestCoefficient θ (dm i) q
  have hca (i : Fin 2) := amplitudeId_weightedTestCoefficient_regular θ (dm i) q (hdm i) hq hcompact
  let A := fun i => amplitudeId_scalarLocalTest Z (ca i) ((hca i).1.of_le (by simp)) (hca i).2
  let o : JetIndex2 1 := valueIndex2 1
  let a := fun i : Fin 2 => (⟨⟨1, by decide⟩, fun _ => i⟩ : JetIndex2 1)
  let Q := fun i k y => (W.toFunction.jet (a i) y : ℂ) * (A k).toFunction.jet o y +
    (W.toFunction.jet o y : ℂ) * (A k).toFunction.jet (a i) y
  have hu (b : JetIndex2 1) : MemLp (W.toFunction.jet b) 2 volume := by
    simpa only [Measure.restrict_univ] using W.toFunction.memL2 b
  have ha (k : Fin 2) (b : JetIndex2 1) : MemLp ((A k).toFunction.jet b) 2 volume := by
    simpa only [Measure.restrict_univ] using (A k).toFunction.memL2 b
  have hQi (i k : Fin 2) : Integrable (Q i k) volume :=
    ((hu (a i)).ofReal.integrable_mul (ha k o)).add
      ((hu o).ofReal.integrable_mul (ha k (a i)))
  have hQzero (i k : Fin 2) : (∫ y, Q i k y) = 0 := by
    have hl : Integrable (fun y => (W.toFunction.jet (a i) y : ℂ) * (A k).toFunction.jet o y) volume :=
      (hu (a i)).ofReal.integrable_mul (ha k o)
    have hr : Integrable (fun y => (W.toFunction.jet o y : ℂ) * (A k).toFunction.jet (a i) y) volume :=
      (hu o).ofReal.integrable_mul (ha k (a i))
    dsimp only [Q]
    rw [integral_add hl hr, amplitudeId_plane_bilinear_first_pair]
    exact neg_add_cancel _
  have hT := amplitudeId_scalarLocalTest_readout Z c (hc.1.of_le (by simp)) hc.2
  have hA (k : Fin 2) := amplitudeId_scalarLocalTest_readout Z (ca k)
    ((hca k).1.of_le (by simp)) (hca k).2
  have hdu (i : Fin 2) : planeH1GradientOperator W i =ᵐ[volume] W.toFunction.jet (a i) :=
    univToPlane_ae _
  have hpoint : amplitudeId_momentWeakRhs G (v t) θ m W S Z q =ᵐ[volume]
      fun y => amplitudeId_planeWeakRhs G (v t) W S T y +
        ∑ i : Fin 2, ∑ k : Fin 2, (G i k : ℂ) * Q i k y := by
    filter_upwards [hT.1, ae_all_iff.mpr hT.2,
      ae_all_iff.mpr (fun k => (hA k).1),
      ae_all_iff.mpr (fun k => ae_all_iff.mpr (hA k).2), ae_all_iff.mpr hdu]
      with y htv htd hav had hduy
    let p := Complex.exp (-(Complex.I * (vecDot θ y : ℂ)))
    let ψ := (q y : ℂ) * Z.toFunction.jet o y
    let dψ := fun i => (q y : ℂ) * Z.toFunction.jet (a i) y +
      ((fderiv ℝ q y (basisVec i) : ℂ) - Complex.I * (θ i : ℂ) * (q y : ℂ)) *
        Z.toFunction.jet o y
    have htv' : T.toFunction.jet o y = p * (m y : ℂ) * ψ := by
      rw [htv]
      dsimp only [c, amplitudeId_weightedTestCoefficient, p, ψ, o]
      ring
    have htd' (i : Fin 2) : T.toFunction.jet (a i) y =
        p * ((m y : ℂ) * dψ i + (dm i y : ℂ) * ψ) := by
      rw [htd i, amplitudeId_weightedTestCoefficient_fderiv θ m q hm hq]
      dsimp only [c, amplitudeId_weightedTestCoefficient, p, ψ, dψ, dm, a, o]
      push_cast
      ring
    have hav' (k : Fin 2) : (A k).toFunction.jet o y = p * (dm k y : ℂ) * ψ := by
      rw [hav k]
      dsimp only [ca, amplitudeId_weightedTestCoefficient, p, ψ, o]
      ring
    have had' (k i : Fin 2) : (A k).toFunction.jet (a i) y = p *
        ((fderiv ℝ (dm k) y (basisVec i) : ℂ) * ψ + (dm k y : ℂ) * dψ i) := by
      rw [had k i, amplitudeId_weightedTestCoefficient_fderiv θ (dm k) q (hdm k) hq]
      dsimp only [ca, amplitudeId_weightedTestCoefficient, p, ψ, dψ, a, o]
      push_cast
      ring
    have h := amplitudeId_moment_rhs_algebra G hG (v t y) (fun i => dm i y)
      (fun i => W.toFunction.jet (a i) y) (fun i => S i y)
      (fun i k => fderiv ℝ (dm i) y (basisVec k)) (m y) (W.toFunction.jet o y) p ψ dψ
    change _ = _ at h
    dsimp only [amplitudeId_momentWeakRhs, amplitudeId_planeWeakRhs, Q]
    simp only [Fin.sum_univ_two] at h ⊢
    rw [hduy 0, hduy 1, htv', htd' 0, htd' 1, hav' 0, hav' 1,
      had' 0 0, had' 0 1, had' 1 0, had' 1 1]
    convert h using 1
    dsimp only [dm, p, ψ, dψ, a, o]
    push_cast
    ring
  have hdiv : Integrable (fun y => ∑ i : Fin 2, ∑ k : Fin 2, (G i k : ℂ) * Q i k y) volume :=
    integrable_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun k _ => (hQi i k).const_mul _))
  have hbase := amplitudeId_planeWeakRhs_integrable G v hv W S T t
  refine ⟨(hbase.add hdiv).congr hpoint.symm, ?_⟩
  rw [integral_congr_ae hpoint, integral_add hbase hdiv,
    integral_finsetSum Finset.univ (fun i _ =>
      integrable_finsetSum Finset.univ (fun k _ => (hQi i k).const_mul _))]
  simp_rw [integral_finsetSum Finset.univ (fun k _ => (hQi _ k).const_mul _),
    integral_const_mul, hQzero]
  simp only [mul_zero, Finset.sum_const_zero, add_zero]
  rfl

/-- The literal moment curve satisfies the compact covariant time increment. -/
theorem amplitudeId_localized_moment_increment {a b : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ r, (G r).IsSymm)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (C : ℝ) (hC : ∀ r i y, ‖cellDriftTorusSymbol v r i y‖ ≤ C)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (W : ℝ → PlaneHk Set.univ 1 ℝ) (S : ℝ → PlaneFluxL2 ℝ)
    (h : PlaneWeakHilbertCurve a b u W (fun r =>
      planeRealBlochGeneratorDual (G r) v hv r C (hC r) (W r) + planeSourceDual 0 (S r)))
    (θ : Vec 2) (m q : Vec 2 → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hcompact : HasCompactSupport q) (Z : TorusHk 1 ℂ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    (∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (m y * u t y : ℝ) *
        (q y : ℂ) * Z.toFunction.jet (valueIndex2 1) y) -
      (∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (m y * u s y : ℝ) *
        (q y : ℂ) * Z.toFunction.jet (valueIndex2 1) y) =
      ∫ r in s..t, ∫ y, amplitudeId_momentWeakRhs (G r) (v r) θ m (W r) (S r) Z q y := by
  let hc := amplitudeId_weightedTestCoefficient_regular θ m q hm hq hcompact
  let T := amplitudeId_scalarLocalTest Z (amplitudeId_weightedTestCoefficient θ m q)
    (hc.1.of_le (by simp)) hc.2
  have he := amplitudeId_plane_forced_increment G v hv C hC u W S h hs ht hst T
  have hr := (amplitudeId_scalarLocalTest_readout Z
    (amplitudeId_weightedTestCoefficient θ m q) (hc.1.of_le (by simp)) hc.2).1
  have hval (r : ℝ) : (∫ y, (u r y : ℂ) * T.toFunction.jet (valueIndex2 1) y) =
      ∫ y, Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) * (m y * u r y : ℝ) *
        (q y : ℂ) * Z.toFunction.jet (valueIndex2 1) y := by
    apply integral_congr_ae
    filter_upwards [hr] with y hy
    rw [hy]
    dsimp only [amplitudeId_weightedTestCoefficient]
    push_cast
    ring
  rw [hval t, hval s] at he
  refine he.trans (intervalIntegral.integral_congr (fun r _ => ?_))
  exact (amplitudeId_localized_moment_rhs (G r) (hG r) v hv r θ m q hm hq hcompact
    (W r) (S r) Z).2.symm

/-- The localized moment increment has a genuinely integrable temporal right side. -/
theorem amplitudeId_localized_moment_time_integrable {a b : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : ∀ r, (G r).IsSymm)
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v)
    (C : ℝ) (hC : ∀ r i y, ‖cellDriftTorusSymbol v r i y‖ ≤ C)
    (u : ℝ → Lp ℝ 2 (volume : Measure (Vec 2)))
    (W : ℝ → PlaneHk Set.univ 1 ℝ) (S : ℝ → PlaneFluxL2 ℝ)
    (h : PlaneWeakHilbertCurve a b u W (fun r =>
      planeRealBlochGeneratorDual (G r) v hv r C (hC r) (W r) + planeSourceDual 0 (S r)))
    (θ : Vec 2) (m q : Vec 2 → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hq : ContDiff ℝ (⊤ : ℕ∞) q)
    (hcompact : HasCompactSupport q) (Z : TorusHk 1 ℂ)
    {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b) (hst : s ≤ t) :
    IntervalIntegrable (fun r => ∫ y,
      amplitudeId_momentWeakRhs (G r) (v r) θ m (W r) (S r) Z q y) volume s t := by
  let hc := amplitudeId_weightedTestCoefficient_regular θ m q hm hq hcompact
  let T := amplitudeId_scalarLocalTest Z (amplitudeId_weightedTestCoefficient θ m q)
    (hc.1.of_le (by simp)) hc.2
  let d := fun r => planeRealBlochGeneratorDual (G r) v hv r C (hC r) (W r) + planeSourceDual 0 (S r)
  have hi (L : ℂ →L[ℝ] ℝ) := planeWeakPair_intervalIntegrable hs ht hst d h.dual_mem
    (mapPlaneHk L T)
  have hri := intervalIntegrable_iff.mpr
    (Complex.ofRealCLM.integrable_comp (intervalIntegrable_iff.mp (hi Complex.reCLM)))
  have him := intervalIntegrable_iff.mpr
    (Complex.ofRealCLM.integrable_comp (intervalIntegrable_iff.mp (hi Complex.imCLM)))
  apply (hri.add (him.const_mul Complex.I)).congr_ae
  apply Filter.Eventually.of_forall
  intro r
  dsimp only
  rw [(amplitudeId_localized_moment_rhs (G r) (hG r) v hv r θ m q hm hq hcompact
    (W r) (S r) Z).2]
  have hre := amplitudeId_planeWeakRhs_projection (G r) v hv r C (hC r) (W r) (S r) T Complex.reCLM
  have him := amplitudeId_planeWeakRhs_projection (G r) v hv r C (hC r) (W r) (S r) T Complex.imCLM
  apply Complex.ext
  · simpa only [Complex.ofRealCLM_apply, d, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero, add_zero, Complex.reCLM_apply] using hre.symm
  · simpa only [Complex.ofRealCLM_apply, d, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add, Complex.imCLM_apply] using him.symm

/-- The literal covariant first derivative of the phase-weighted moment. -/
def amplitudeId_momentPlaneGradient (θ : Vec 2) (β : ℕ × ℕ)
    (W : PlaneHk Set.univ 1 ℝ) (i : Fin 2) (y : Vec 2) : ℂ :=
  Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    (momentWeight β y * planeH1GradientOperator W i y +
      momentWeightGrad β y i * W.toFunction.jet (valueIndex2 1) y : ℝ)

/-- The actual scalar moment commutator, before periodization. -/
def amplitudeId_momentPlaneSource (G : Matrix (Fin 2) (Fin 2) ℝ)
    (v : Vec 2 → Vec 2) (θ : Vec 2) (β : ℕ × ℕ)
    (W : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ) (y : Vec 2) : ℂ :=
  Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    ((momentWeightLap G β y + ∑ i, v y i * momentWeightGrad β y i) *
      W.toFunction.jet (valueIndex2 1) y - ∑ i, momentWeightGrad β y i * S i y : ℝ)

/-- The actual divergence moment commutator, before periodization. -/
def amplitudeId_momentPlaneFlux (G : Matrix (Fin 2) (Fin 2) ℝ)
    (θ : Vec 2) (β : ℕ × ℕ) (W : PlaneHk Set.univ 1 ℝ) (S : PlaneFluxL2 ℝ)
    (i : Fin 2) (y : Vec 2) : ℂ :=
  Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    (momentWeight β y * S i y - (∑ k, (G i k + G k i) * momentWeightGrad β y k) *
      W.toFunction.jet (valueIndex2 1) y : ℝ)

/-- Moving the frequency shift into the source gives an ordinary source/flux balance,
with exactly the literal moment commutators. -/
theorem amplitudeId_moment_rhs_balance
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (θ : Vec 2) (β : ℕ × ℕ) (W : ℝ → PlaneHk Set.univ 1 ℝ)
    (S : ℝ → PlaneFluxL2 ℝ) (Z : TorusHk 1 ℂ) (q : Vec 2 → ℝ) (r : ℝ) (y : Vec 2) :
    let B := fun i t => amplitudeId_momentPlaneGradient θ β (W t) i
    let F := fun i t => amplitudeId_momentPlaneFlux (G t) θ β (W t) (S t) i
    let R := fun t => amplitudeId_momentPlaneSource (G t) (v t) θ β (W t) (S t)
    amplitudeId_momentWeakRhs (G r) (v r) θ (momentWeight β) (W r) (S r) Z q y =
      amplitudeId_covariantSource G v θ B F R r y * (q y : ℂ) *
        Z.toFunction.jet (valueIndex2 1) y -
      ∑ i : Fin 2, amplitudeId_covariantFlux G B F i r y *
        ((q y : ℂ) * Z.toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y +
          (fderiv ℝ q y (basisVec i) : ℂ) * Z.toFunction.jet (valueIndex2 1) y) := by
  dsimp only [amplitudeId_momentWeakRhs]
  simp_rw [amplitudeId_moment_fderiv]
  rw [amplitudeId_moment_laplacian]
  dsimp only [amplitudeId_covariantSource, amplitudeId_covariantFlux,
    amplitudeId_momentPlaneGradient, amplitudeId_momentPlaneSource, amplitudeId_momentPlaneFlux]
  simp only [Fin.sum_univ_two]
  push_cast
  ring

/-- Plane almost-everywhere equality passes through every integer image simultaneously. -/
theorem amplitudeId_latticePeriodization_congr {f g : Vec 2 → ℂ}
    (he : f =ᵐ[volume] g) : latticePeriodization f =ᵐ[volume] latticePeriodization g := by
  have hs : ∀ᵐ y ∂volume, ∀ n : Fin 2 → ℤ,
      f (y + AVenhance.latticeShift n) = g (y + AVenhance.latticeShift n) :=
    ae_all_iff.mpr (fun n =>
      (measurePreserving_add_right volume (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp he)
  filter_upwards [hs] with y hy
  exact tsum_congr hy

/-- Native radial curves periodize to native periodic curves with a global literal readout. -/
theorem amplitudeId_radial_cell_curve (μ : Measure ℝ) (f : ℝ → Vec 2 → ℂ)
    (P : AmplitudeIdPlaneRadialCurve μ f) :
    ∃ U : ℝ → TorusHk 0 ℂ, MemLp U 2 μ ∧ ∀ᵐ t ∂μ,
      (U t).toFunction.jet (valueIndex2 0) =ᵐ[volume] latticePeriodization (f t) := by
  obtain ⟨M, hM, hbudget⟩ := P.budget
  have hm : ∀ᵐ t ∂μ, HasRadialPlaneMoments (P.value t) 0 := by
    filter_upwards [hbudget] with t ht
    intro a
    rw [zeroJetIndex_eq a]
    simp only [sub_zero]
    exact lt_of_le_of_lt ht.2 ENNReal.ofReal_lt_top
  have hb : ∀ᵐ t ∂μ, ∀ a : JetIndex2 0, eLpNorm
      (fun y => (1 + ‖y - (0 : Vec 2)‖) ^ 4 • (P.value t).toFunction.jet a y) 2 volume ≤
        ENNReal.ofReal ‖M t‖ := by
    filter_upwards [hbudget] with t ht
    intro a
    simpa only [zeroJetIndex_eq a, sub_zero] using ht.2
  obtain ⟨U, hU, hread⟩ := exists_periodized_radial_carrier_time_memLp μ P.value P.mem 0 hm M hM hb
  refine ⟨U, hU, ?_⟩
  filter_upwards [hread, P.readout] with t ht hp
  exact (periodizedCarrier_rawJet_ae (P.value t) (U t) (valueIndex2 0) (ht _)).trans
    (amplitudeId_latticePeriodization_congr hp)

/-- Every radial native time curve has an absolutely convergent literal lattice series. -/
theorem AmplitudeIdPlaneRadialCurve.summable {μ : Measure ℝ} {f : ℝ → Vec 2 → ℂ}
    (P : AmplitudeIdPlaneRadialCurve μ f) :
    ∀ᵐ t ∂μ, ∀ᵐ y ∂volume.restrict AVenhance.unitCube,
      Summable (fun n : Fin 2 → ℤ => ‖f t (y + AVenhance.latticeShift n)‖) := by
  obtain ⟨M, _, hb⟩ := P.budget
  filter_upwards [hb, P.readout] with t ht hread
  have hm : HasRadialPlaneMoments (P.value t) 0 := by
    intro a
    rw [memLp_iff]
    simpa only [zeroJetIndex_eq a, sub_zero] using
      (lt_of_le_of_lt ht.2 ENNReal.ofReal_lt_top : eLpNorm
        (fun y => (1 + ‖y‖) ^ 4 • (P.value t).toFunction.jet (valueIndex2 0) y) 2 volume < ⊤)
  have hs := radialCarrier_image_enorm_tsum_lt_top (P.value t) 0 hm (valueIndex2 0)
  have he (n : Fin 2 → ℤ) :
      eLpNorm (fun y => (P.value t).toFunction.jet (valueIndex2 0) (y + AVenhance.latticeShift n)) 2
        (volume.restrict AVenhance.unitCube) =
      ‖planeImageJetCLM AVenhance.unitCube (AVenhance.latticeShift n) (valueIndex2 0) (P.value t)‖ₑ := by
    rw [← eLpNorm_congr_ae (planeImageJetCLM_ae AVenhance.unitCube (AVenhance.latticeShift n)
      (valueIndex2 0) (P.value t))]
    exact (Lp.enorm_def _).symm
  have hsum := (CycleEvolution.cellLpSeries_memLp_bound (volume.restrict AVenhance.unitCube)
    (fun n y => (P.value t).toFunction.jet (valueIndex2 0) (y + AVenhance.latticeShift n))
    (by simpa only [he] using hs)).2.2
  have hlat := ae_all_iff.mpr (fun n : Fin 2 → ℤ =>
    ((measurePreserving_add_right volume (AVenhance.latticeShift n)).quasiMeasurePreserving.ae_eq_comp
      hread).restrict (s := AVenhance.unitCube))
  filter_upwards [hsum, hlat] with y hy hl
  exact hy.congr (fun n => congrArg norm (hl n))

/-- Absolutely convergent lattice sums commute with finite periodic complex multipliers. -/
theorem amplitudeId_lattice_finite_sum {J : Type*} [Fintype J]
    (c f : J → Vec 2 → ℂ) (y : Vec 2)
    (hc : ∀ j (n : Fin 2 → ℤ), c j (y + AVenhance.latticeShift n) = c j y)
    (hf : ∀ j, Summable (fun n : Fin 2 → ℤ => f j (y + AVenhance.latticeShift n))) :
    latticePeriodization (fun x => ∑ j, c j x * f j x) y =
      ∑ j, c j y * latticePeriodization (f j) y := by
  classical
  change (∑' n : Fin 2 → ℤ, ∑ j, c j (y + AVenhance.latticeShift n) *
    f j (y + AVenhance.latticeShift n)) = _
  simp_rw [hc]
  rw [Summable.tsum_finsetSum (fun j _ => (hf j).mul_left (c j y))]
  simp only [tsum_mul_left, latticePeriodization]

/-- The periodization of a finite periodic-coefficient combination has its literal cell readout. -/
theorem amplitudeId_periodized_combination_readout {J : Type*} [Fintype J]
    (μ : Measure ℝ) (f : J → ℝ → Vec 2 → ℂ)
    (P : ∀ j, AmplitudeIdPlaneRadialCurve μ (f j))
    (c : J → ℝ → Vec 2 → ℂ) (hp : ∀ j t, AVenhance.IsZ2Periodic (c j t))
    (R : J → ℝ → Vec 2 → ℂ)
    (hR : ∀ j, ∀ᵐ t ∂μ, R j t =ᵐ[volume.restrict AVenhance.unitCube] latticePeriodization (f j t))
    (U : ℝ → Vec 2 → ℂ)
    (hU : ∀ᵐ t ∂μ, U t =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization (fun y => ∑ j, c j t y * f j t y)) :
    ∀ᵐ t ∂μ, U t =ᵐ[volume.restrict AVenhance.unitCube] fun y => ∑ j, c j t y * R j t y := by
  classical
  filter_upwards [hU, ae_all_iff.mpr (fun j => (P j).summable), ae_all_iff.mpr hR]
    with t ht hs hr
  filter_upwards [ht, ae_all_iff.mpr hs, ae_all_iff.mpr hr] with y hy hsy hry
  rw [hy, amplitudeId_lattice_finite_sum (fun j => c j t) (fun j => f j t) y
    (fun j n => hp j t n y) (fun j => Summable.of_norm (f := _) (hsy j))]
  exact Finset.sum_congr rfl (fun j _ => congrArg (fun z => c j t y * z) (hry j).symm)

section CellGradientReadout
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The periodic moment jet has exactly the periodized covariant plane gradient. -/
theorem amplitudeId_cell_covariant_gradient_readout
    (μ : Measure ℝ) (U : ℝ → PlaneHk Set.univ 1 E) (hU : MemLp U 2 μ)
    (ϖ r : ℝ) (hϖ : 0 < ϖ) (hr : 0 < r)
    (he : ∀ n : ℕ, (∫⁻ t, weightedFactorialNormSq n ϖ 0 r 1 (U t) ∂μ) ≠ ⊤)
    (θ : Vec 2) (β : ℕ × ℕ) (e : E) (W : ℝ → TorusHk 1 ℂ)
    (hW : ∀ᵐ t ∂μ, ∀ a, (W t).val a =ᵐ[volume.restrict AVenhance.unitCube]
      periodizeRawJet (multiplicationRawJet (amplitudeId_momentCoefficient θ β e) (U t).toFunction.jet) a) :
    ∀ᵐ t ∂μ, ∀ i : Fin 2,
      (fun y => (W t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y +
        Complex.I * (θ i : ℂ) * (W t).toFunction.jet (valueIndex2 1) y) =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (momentWeight β y * inner ℝ e ((U t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) +
          momentWeightGrad β y i * inner ℝ e ((U t).toFunction.jet (valueIndex2 1) y) : ℝ)) := by
  classical
  have hM (γ : ℕ × ℕ) (a : JetIndex2 1) :=
    (amplitudeId_native_moment_time_readout μ U hU ϖ r hϖ hr he θ γ e a).2
  filter_upwards [hW, ae_all_iff.mpr (fun γ => ae_all_iff.mpr (hM γ))] with t hwt hmt
  intro i
  let V := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    (momentWeight β y * inner ℝ e ((U t).toFunction.jet (valueIndex2 1) y) : ℝ)
  let D := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    (momentWeight β y * inner ℝ e ((U t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y) : ℝ)
  let L := fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
    (momentWeight (amplitudeId_lowerMoment β i) y *
      inner ℝ e ((U t).toFunction.jet (valueIndex2 1) y) : ℝ)
  let c : ℂ := amplitudeId_momentMultiplicity β i
  have hfirst := amplitudeId_periodized_first_of_summable (U t) θ β e i
    ((hmt β (valueIndex2 1)).2.mono (fun _ h => Summable.of_norm (f := _) h))
    ((hmt β ⟨⟨1, by decide⟩, fun _ => i⟩).2.mono (fun _ h => Summable.of_norm (f := _) h))
    ((hmt (amplitudeId_lowerMoment β i) (valueIndex2 1)).2.mono
      (fun _ h => Summable.of_norm (f := _) h))
  have hgrad := ((periodicJetRepresentative_ae (W t).val ⟨⟨1, by decide⟩, fun _ => i⟩).trans
    (hwt ⟨⟨1, by decide⟩, fun _ => i⟩)).trans hfirst
  have hUvalue : planeValue (U t) = (U t).toFunction.jet (valueIndex2 1) := by
    rw [planeValue_eq_stored]
    rfl
  have hvalue : (W t).toFunction.jet (valueIndex2 1) =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization V := by
    apply ((periodicJetRepresentative_ae (W t).val _).trans (hwt _)).trans
    exact Filter.Eventually.of_forall (fun y => tsum_congr (fun n => by
      simpa only [V, hUvalue] using amplitudeId_moment_jet_value (U t) θ β e (y + AVenhance.latticeShift n)))
  filter_upwards [hgrad, hvalue, (hmt β ⟨⟨1, by decide⟩, fun _ => i⟩).2,
    (hmt (amplitudeId_lowerMoment β i) (valueIndex2 1)).2] with y hgy hvy hDy hLy
  have hB : latticePeriodization (fun x => Complex.exp (-(Complex.I * (vecDot θ x : ℂ))) *
      (momentWeight β x * inner ℝ e ((U t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) +
        momentWeightGrad β x i * inner ℝ e ((U t).toFunction.jet (valueIndex2 1) x) : ℝ)) y =
      latticePeriodization D y + c * latticePeriodization L y := by
    have hpoint (x : Vec 2) : Complex.exp (-(Complex.I * (vecDot θ x : ℂ))) *
        (momentWeight β x * inner ℝ e ((U t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ x) +
          momentWeightGrad β x i * inner ℝ e ((U t).toFunction.jet (valueIndex2 1) x) : ℝ) =
        D x + c * L x := by
      rw [amplitudeId_momentWeightGrad_lower]
      dsimp only [D, L, c]
      push_cast
      ring
    change (∑' n : Fin 2 → ℤ, _) = _
    simp_rw [hpoint]
    rw [(Summable.of_norm (f := fun n => D (y + AVenhance.latticeShift n)) hDy).tsum_add
      ((Summable.of_norm (f := fun n => L (y + AVenhance.latticeShift n)) hLy).mul_left c), tsum_mul_left]
    rfl
  change (W t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y = _ at hgy
  rw [hB, hgy, hvy]
  change latticePeriodization D y + c * latticePeriodization L y -
    Complex.I * (θ i : ℂ) * latticePeriodization V y +
    Complex.I * (θ i : ℂ) * latticePeriodization V y = _
  ring

end CellGradientReadout

section WordCellReadout
open AVRegularity.CoupledEnergy.Galerkin
universe u v
variable {ι : Type u} [Fintype ι] {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D Nw : ℕ} {K : ScalarConstants} {g₁ : ℝ}

/-- The continuous moment Bloch trace is the value class of its native periodic energy state. -/
theorem AmplitudeIdWordCellData.agrees
    {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {j : Fin (Nw + 1)} {x : ι} {e : h x} {θ : Vec 2} {β : ℕ × ℕ}
    (A : AmplitudeIdWordCellData F j x e θ β) :
    ∀ᵐ t ∂volume.restrict (Icc F.a F.b), A.value t = torusHkValueCLM (A.state t) := by
  let U := fun t => truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t)
  filter_upwards [A.state_readout, F.solution.2.2.1 (j, x), ae_restrict_mem measurableSet_Icc]
    with t hwt ht htime
  have hv : planeValue (U t) = planeValue (F.u j x t) := by
    calc
      _ = planeValue (F.w j x t) := planeJetOrder_truncate
        (show 1 ≤ F.κ j x + 1 by omega) (Nat.zero_le _) (F.w j x t) _
      _ = planeValue (truncatePlaneHk (Nat.le_succ (F.κ j x)) (F.w j x t)) :=
        (planeJetOrder_truncate (Nat.le_succ (F.κ j x)) (Nat.zero_le _) (F.w j x t) _).symm
      _ = _ := congrArg planeValue ht
  have hp : periodizeRawJet (multiplicationRawJet (amplitudeId_momentCoefficient θ β e)
      (U t).toFunction.jet) (valueIndex2 1) =ᵐ[volume.restrict AVenhance.unitCube]
      planeBlochC θ (fun y => momentWeight β y * inner ℝ e (planeValue (F.u j x t) y)) := by
    exact Filter.Eventually.of_forall (fun y => tsum_congr (fun n => by
      rw [amplitudeId_moment_jet_value, hv]
      rfl))
  exact Lp.ext ((A.trace t htime).trans ((hwt (valueIndex2 1)).trans hp).symm)

/-- The state covariant gradient is the periodization of the actual native plane coordinate. -/
theorem AmplitudeIdWordCellData.covariant_readout
    {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {j : Fin (Nw + 1)} {x : ι} {e : h x} {θ : Vec 2} {β : ℕ × ℕ}
    (A : AmplitudeIdWordCellData F j x e θ β) :
    ∀ᵐ t ∂volume.restrict (Icc F.a F.b), ∀ i : Fin 2,
      (fun y => (A.state t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ y +
        Complex.I * (θ i : ℂ) * (A.state t).toFunction.jet (valueIndex2 1) y) =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization (amplitudeId_momentPlaneGradient θ β (amplitudeId_wordCoordinateSlice F j x e t) i) := by
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  let U := fun t => truncatePlaneHk (show 1 ≤ F.κ j x + 1 by omega) (F.w j x t)
  have hc := amplitudeId_cell_covariant_gradient_readout (volume.restrict (Icc F.a F.b))
    U A.plane_mem F.ϖ A.radius hϖ A.radius_pos A.plane_energy θ β e A.state A.state_readout
  filter_upwards [hc] with t ht
  intro i
  apply (ht i).trans
  apply (amplitudeId_latticePeriodization_congr ?_).restrict
  have hg : planeH1GradientOperator (amplitudeId_wordCoordinateSlice F j x e t) i =ᵐ[volume]
      (amplitudeId_wordCoordinateSlice F j x e t).toFunction.jet ⟨⟨1, by decide⟩, fun _ => i⟩ :=
    univToPlane_ae _
  filter_upwards [amplitudeId_wordCoordinate_truncated_readout F j x e t (valueIndex2 1),
    amplitudeId_wordCoordinate_truncated_readout F j x e t ⟨⟨1, by decide⟩, fun _ => i⟩, hg]
    with y hv hd hg
  dsimp only [amplitudeId_momentPlaneGradient]
  rw [hg, hv, hd]

/-- The cell forcing classes read the source and flux of the actual native coordinate equation. -/
theorem AmplitudeIdWordCellData.forcing_readouts
    {F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁}
    {j : Fin (Nw + 1)} {x : ι} {e : h x} {θ : Vec 2} {β : ℕ × ℕ}
    (A : AmplitudeIdWordCellData F j x e θ β)
    (V : ℝ → PlaneHk Set.univ (F.κ j x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hV : ∀ᵐ t ∂volume.restrict (Icc F.a F.b), planeValue (V t) =ᵐ[volume]
      fun y => wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
        (fun p => F.w p.1 p.2 t) (j, x) t y) :
    let W := amplitudeId_wordCoordinateSlice F j x e
    let S := fun t => planeFluxFiberCoordinateCLM e (planeFluxValueOperator (F.κ j x) (V t))
    ∀ᵐ t ∂volume.restrict (Icc F.a F.b),
      (A.scalar t =ᵐ[volume.restrict AVenhance.unitCube]
        latticePeriodization (amplitudeId_momentPlaneSource (F.G t) (F.v t) θ β (W t) (S t))) ∧
      ∀ i, A.flux i t =ᵐ[volume.restrict AVenhance.unitCube]
        latticePeriodization (amplitudeId_momentPlaneFlux (F.G t) θ β (W t) (S t) i) := by
  dsimp only
  let W := amplitudeId_wordCoordinateSlice F j x e
  let S := fun t => planeFluxFiberCoordinateCLM e (planeFluxValueOperator (F.κ j x) (V t))
  filter_upwards [hV, F.solution.2.2.1 (j, x), A.scalar_readout, ae_all_iff.mpr A.flux_readout]
    with t hvt ht hR hQ
  have hval : planeValue (F.w j x t) = planeValue (F.u j x t) := by
    calc
      _ = planeValue (truncatePlaneHk (Nat.le_succ (F.κ j x)) (F.w j x t)) :=
        (planeJetOrder_truncate (Nat.le_succ (F.κ j x)) (Nat.zero_le _) (F.w j x t) _).symm
      _ = _ := congrArg planeValue ht
  have hw : (W t).toFunction.jet (valueIndex2 1) =ᵐ[volume]
      fun y => inner ℝ e (planeValue (F.u j x t) y) := by
    have h := (amplitudeId_wordCoordinate_readouts F j x e t).2 (valueIndex2 1)
    change (W t).toFunction.jet (valueIndex2 1) =ᵐ[volume]
      (fun y => inner ℝ e (planeValue (F.w j x t) y)) at h
    simpa only [hval] using h
  have hs (i : Fin 2) : S t i =ᵐ[volume]
      fun y => inner ℝ e (wordChainPreviousFlux F.letters F.X₀ (F.ϖ * F.ηg) F.κ
        (fun p => F.w p.1 p.2 t) (j, x) t y i) := by
    filter_upwards [planeFluxFiberCoordinateCLM_ae e (planeFluxValueOperator (F.κ j x) (V t)) i,
      planeFluxValueOperator_ae (F.κ j x) (V t) i, hvt] with y hc hv hy
    change S t i y = _
    rw [hc, hv]
    exact congrArg (inner ℝ e) (congrArg (fun z : PiLp 2 (fun _ : Fin 2 => h x) => z i) hy)
  have hpR : amplitudeId_momentPlaneSource (F.G t) (F.v t) θ β (W t) (S t) =ᵐ[volume]
      fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (amplitudeId_wordMomentScalar F j x e β t y : ℂ) := by
    filter_upwards [hw, ae_all_iff.mpr hs] with y hwy hsy
    simp only [amplitudeId_momentPlaneSource, amplitudeId_wordMomentScalar, hwy, hsy]
  have hpF (i : Fin 2) : amplitudeId_momentPlaneFlux (F.G t) θ β (W t) (S t) i =ᵐ[volume]
      fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
        (amplitudeId_wordMomentFlux F j x e β i t y : ℂ) := by
    filter_upwards [hw, hs i] with y hwy hsy
    simp only [amplitudeId_momentPlaneFlux, amplitudeId_wordMomentFlux, hwy, hsy]
  exact ⟨hR.trans ((amplitudeId_latticePeriodization_congr hpR).restrict).symm,
    fun i => (hQ i).trans ((amplitudeId_latticePeriodization_congr (hpF i)).restrict).symm⟩

/-- Every endpoint phase-moment has a genuine radial plane L2 carrier. -/
theorem amplitudeId_word_endpoint_carrier
    (F : AmplitudeIdFrame (ι := ι) (h := h) (D := D) (Nw := Nw) K g₁)
    (j : Fin (Nw + 1)) (x : ι) (e : h x) (θ : Vec 2) (β : ℕ × ℕ)
    (t : ℝ) (ht : t ∈ Icc F.a F.b) :
    ∃ X : PlaneHk Set.univ 0 ℂ,
      X.toFunction.jet (valueIndex2 0) =ᵐ[volume]
        (fun y => Complex.exp (-(Complex.I * (vecDot θ y : ℂ))) *
          (momentWeight β y * inner ℝ e (planeValue (F.u j x t) y) : ℝ)) ∧
      MemLp (fun y => (1 + ‖y‖) ^ 4 • X.toFunction.jet (valueIndex2 0) y) 2 volume := by
  have hϖ : 0 < F.ϖ := by
    rw [F.piece.hϖ]
    exact Real.sqrt_pos.mpr (div_pos F.piece.hη (lt_of_lt_of_le zero_lt_one F.piece.hS))
  obtain ⟨r, _, he⟩ := amplitudeId_full_polynomial_budgets F
  have hm (n : ℕ) : (∫⁻ y, ENNReal.ofReal
      ((1 + F.ϖ ^ 2 * (y 0 ^ 2 + y 1 ^ 2)) ^ n * ‖planeValue (F.u j x t) y‖ ^ 2)) < ⊤ := by
    obtain ⟨C, _, hb⟩ := (he n j x).1
    exact ((amplitudeId_weighted_value_le (F.u j x t) n F.ϖ r).trans (hb t ht)).trans_lt
      ENNReal.ofReal_lt_top
  have hmeas : AEStronglyMeasurable (planeValue (F.u j x t)) volume :=
    (planeJetOrder_memLp (Nat.zero_le _) (F.u j x t) _).aestronglyMeasurable
  exact amplitudeId_radial_plane_carrier _
    (amplitudeId_scalar_radial_memLp _ hmeas F.ϖ hϖ hm θ β e)

end WordCellReadout

/-- Periodic coefficients commute with the native radial source and flux periodizations. -/
theorem amplitudeId_covariant_cell_readouts
    (μ : Measure ℝ) (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t, AVenhance.IsZ2Periodic (v t)) (θ : Vec 2)
    (B F : Fin 2 → ℝ → Vec 2 → ℂ) (R : ℝ → Vec 2 → ℂ)
    (PB : ∀ i, AmplitudeIdPlaneRadialCurve μ (B i))
    (PF : ∀ i, AmplitudeIdPlaneRadialCurve μ (F i))
    (PR : AmplitudeIdPlaneRadialCurve μ R)
    (PQ : ∀ i, AmplitudeIdPlaneRadialCurve μ (amplitudeId_covariantFlux G B F i))
    (Bc Fc : Fin 2 → ℝ → Vec 2 → ℂ) (Rc : ℝ → Vec 2 → ℂ)
    (hB : ∀ i, ∀ᵐ t ∂μ, Bc i t =ᵐ[volume.restrict AVenhance.unitCube] latticePeriodization (B i t))
    (hF : ∀ i, ∀ᵐ t ∂μ, Fc i t =ᵐ[volume.restrict AVenhance.unitCube] latticePeriodization (F i t))
    (hR : ∀ᵐ t ∂μ, Rc t =ᵐ[volume.restrict AVenhance.unitCube] latticePeriodization (R t))
    (Qc : Fin 2 → ℝ → Vec 2 → ℂ) (Hc : ℝ → Vec 2 → ℂ)
    (hQ : ∀ i, ∀ᵐ t ∂μ, Qc i t =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization (amplitudeId_covariantFlux G B F i t))
    (hH : ∀ᵐ t ∂μ, Hc t =ᵐ[volume.restrict AVenhance.unitCube]
      latticePeriodization (amplitudeId_covariantSource G v θ B F R t)) :
    (∀ i, ∀ᵐ t ∂μ, Qc i t =ᵐ[volume.restrict AVenhance.unitCube]
      amplitudeId_covariantFlux G Bc Fc i t) ∧
    (∀ᵐ t ∂μ, Hc t =ᵐ[volume.restrict AVenhance.unitCube]
      amplitudeId_covariantSource G v θ Bc Fc Rc t) := by
  classical
  have hqc (i : Fin 2) : ∀ᵐ t ∂μ, Qc i t =ᵐ[volume.restrict AVenhance.unitCube]
      amplitudeId_covariantFlux G Bc Fc i t := by
    let f : Unit ⊕ Fin 2 → ℝ → Vec 2 → ℂ := Sum.elim (fun _ => F i) B
    let P : ∀ j, AmplitudeIdPlaneRadialCurve μ (f j) := Sum.rec (fun _ => PF i) PB
    let c : Unit ⊕ Fin 2 → ℝ → Vec 2 → ℂ :=
      Sum.elim (fun _ _ _ => 1) (fun k t _ => (G t k i : ℂ))
    let r : Unit ⊕ Fin 2 → ℝ → Vec 2 → ℂ := Sum.elim (fun _ => Fc i) Bc
    have hp (j : Unit ⊕ Fin 2) (t : ℝ) : AVenhance.IsZ2Periodic (c j t) := by
      cases j <;> intro n y <;> rfl
    have hr (j : Unit ⊕ Fin 2) : ∀ᵐ t ∂μ, r j t =ᵐ[volume.restrict AVenhance.unitCube]
        latticePeriodization (f j t) := by
      cases j with
      | inl _ => exact hF i
      | inr k => exact hB k
    have he (t : ℝ) (y : Vec 2) : (∑ j, c j t y * f j t y) =
        amplitudeId_covariantFlux G B F i t y := by
      simp only [Fintype.sum_sum_type, Fintype.sum_unique, c, f, Sum.elim_inl,
        Sum.elim_inr, one_mul, amplitudeId_covariantFlux]
    have hh := amplitudeId_periodized_combination_readout μ f P c hp r hr (Qc i)
      (by simpa only [he] using hQ i)
    change ∀ᵐ t ∂μ, Qc i t =ᵐ[volume.restrict AVenhance.unitCube]
      (fun y => Fc i t y + ∑ k, (G t k i : ℂ) * Bc k t y)
    simpa only [Fintype.sum_sum_type, Fintype.sum_unique, c, r, Sum.elim_inl,
      Sum.elim_inr, one_mul] using hh
  refine ⟨hqc, ?_⟩
  let f : Unit ⊕ (Fin 2 ⊕ Fin 2) → ℝ → Vec 2 → ℂ :=
    Sum.elim (fun _ => R) (Sum.elim B (amplitudeId_covariantFlux G B F))
  let P : ∀ j, AmplitudeIdPlaneRadialCurve μ (f j) := Sum.rec (fun _ => PR) (Sum.rec PB PQ)
  let c : Unit ⊕ (Fin 2 ⊕ Fin 2) → ℝ → Vec 2 → ℂ :=
    Sum.elim (fun _ _ _ => 1) (Sum.elim (fun i t y => -(v t y i : ℂ))
      (fun i _ _ => Complex.I * (θ i : ℂ)))
  let r : Unit ⊕ (Fin 2 ⊕ Fin 2) → ℝ → Vec 2 → ℂ :=
    Sum.elim (fun _ => Rc) (Sum.elim Bc Qc)
  have hp (j : Unit ⊕ (Fin 2 ⊕ Fin 2)) (t : ℝ) : AVenhance.IsZ2Periodic (c j t) := by
    rcases j with _ | (i | i)
    · intro n y; rfl
    · intro n y
      change -(v t (y + AVenhance.latticeShift n) i : ℂ) = -(v t y i : ℂ)
      rw [hv t n y]
    · intro n y; rfl
  have hr (j : Unit ⊕ (Fin 2 ⊕ Fin 2)) : ∀ᵐ t ∂μ,
      r j t =ᵐ[volume.restrict AVenhance.unitCube] latticePeriodization (f j t) := by
    rcases j with _ | (i | i)
    · exact hR
    · exact hB i
    · exact hQ i
  have he (t : ℝ) (y : Vec 2) : (∑ j, c j t y * f j t y) =
      amplitudeId_covariantSource G v θ B F R t y := by
    simp only [Fintype.sum_sum_type, Fintype.sum_unique, c, f, Sum.elim_inl,
      Sum.elim_inr, one_mul, amplitudeId_covariantSource, add_assoc]
  have hh := amplitudeId_periodized_combination_readout μ f P c hp r hr Hc
    (by simpa only [he] using hH)
  filter_upwards [hh, ae_all_iff.mpr hqc] with t ht hqt
  filter_upwards [ht, ae_all_iff.mpr hqt] with y hy hqy
  simpa only [Fintype.sum_sum_type, Fintype.sum_unique, c, r, Sum.elim_inl,
    Sum.elim_inr, one_mul, amplitudeId_covariantSource, hqy, add_assoc] using hy

end AVRegularity.CycleWords.Assembly
