-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Weighted.BoundedWeightRoot
import AVRegularity.CoupledEnergyPlane.Variational.ResidualValueSource
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! Window-only metric hypotheses supply the true clamped Sobolev flux class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem intervalMetricGradientCarrier_memLp {K : ℕ} {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGm : Measurable (fun p : Set.Icc a b × Vec 2 => G p.1 p.2))
    (hG : ∀ t ∈ Set.Icc a b, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc a b, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hw : MemLp w 2 (volume.restrict (Set.Icc a b))) :
    MemLp (fun t => planeMetricGradientCarrier (E := E)
      (planeIntervalCoefficient a b hab G t)
      (hG _ (Set.projIcc a b hab t).property) M
      (hb _ (Set.projIcc a b hab t).property) (w t))
      2 (volume.restrict (Set.Icc a b)) :=
  planeMetricGradientCarrier_memLp _ (planeIntervalCoefficient a b hab G)
    (planeIntervalCoefficient_measurable a b hab G hGm)
    (fun t => hG _ (Set.projIcc a b hab t).property) M
    (fun t => hb _ (Set.projIcc a b hab t).property) w hw

end AVRegularity.Weighted
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The scalar chain gives the exact metric weak time increment. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The exact scalar coupled weak solution supplies metric increments between any two window times. -/
theorem scalarChainTrace_increment
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (v : ℝ → Vec 2 → Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (F : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (PiLp 2 (fun _ : Fin 2 => h p.2)))
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun p : Fin 1 × ι => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w)
    (i : Fin 1 × ι) {s t : ℝ} (hs : s ∈ Icc a b) (ht : t ∈ Icc a b)
    (φ : PlaneHk Set.univ 1 (h i.2)) :
    inner ℝ (coupledPlaneL2Trace u i t) (planeHkValueOperator (E := h i.2) 1 φ) -
      inner ℝ (coupledPlaneL2Trace u i s) (planeHkValueOperator (E := h i.2) 1 φ) =
      ∫ r in s..t, ∫ x, planeScalarRawRhs (κ i.1 i.2) (v r) (G r) (w i r) (F i r) φ x := by
  rw [coupledPlaneL2Trace_inner, coupledPlaneL2Trace_inner]
  have he := coupledWeakIdentity_fixed_increment (volume.restrict Set.univ) hab v
    (fun r => (u i r).toFunction.jet (valueIndex2 (κ i.1 i.2)))
    ((f i).toFunction.jet (valueIndex2 (κ i.1 i.2)))
    (φ.toFunction.jet (valueIndex2 1))
    (fun k => φ.toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r k => (w i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ => k⟩)
    (fun r => scalarChainFlux G κ (fun p => w p r) i r)
    (fun r => (F i r).toFunction.jet (valueIndex2 (κ i.1 i.2)))
    (fun r => (0 : PlaneHk Set.univ (κ i.1 i.2) (h i.2)).toFunction.jet
      (valueIndex2 (κ i.1 i.2)))
    (fun r hr => hsln.2.2.2.2 i r hr φ) hs ht
  simp only [Measure.restrict_univ] at he
  rw [he]
  apply intervalIntegral.integral_congr
  intro r _
  apply integral_congr_ae
  apply Filter.Eventually.of_forall
  intro x
  simp only [planeWeakSpatialRhs, one_mul, planeScalarRawRhs]
  simp_rw [scalarChainFlux_eq]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Variational AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! Separate actual differentiated transport into its principal action and value source. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def planeDriftCommutatorTerm {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (D : RawJet2 (K + 1) E)
    (w : DerivativeWord2 j) (x : Vec 2) : E :=
  ∑ m : PositionMask j, if 1 ≤ maskLeftLength j m then driftMaskTerm hj v D m w x else 0

theorem driftMask_sum_split {K j : ℕ} (hj : j ≤ K)
    (D : RawJet2 (K + 1) E) (v : Vec 2 → Vec 2)
    (w : DerivativeWord2 j) (x : Vec 2) :
    (∑ m : PositionMask j, driftMaskTerm hj v D m w x) =
      (∑ k : Fin 2, v x k • D ⟨⟨j + 1, by omega⟩, Fin.snoc w k⟩ x) +
      planeDriftCommutatorTerm hj v D w x := by
  rw [← driftMaskTerm_principal_sum hj D v w x]
  unfold planeDriftCommutatorTerm
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hm : maskLeftLength j m = 0
  · simp [hm]
  · have hp : 1 ≤ maskLeftLength j m := by omega
    simp [hm, hp]

variable [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeTransportCarrier_principal_commutator_ae {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (p : PlaneHk Set.univ (K + 1) E) (j : Fin (K + 1)) (w : DerivativeWord2 j.val) :
    (planeTransportCarrier hK v hv V hbv a B lam hjets p).val ⟨j, w⟩
      =ᵐ[volume.restrict Set.univ] fun x =>
        (∑ k : Fin 2, v x k • p.toFunction.jet
          ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, Fin.snoc w k⟩ x) +
          planeDriftCommutatorTerm (Nat.le_of_lt_succ j.isLt) v p.toFunction.jet w x := by
  filter_upwards [planeTransportCarrier_jet_masks_ae hK v hv V hbv a B lam hjets p j w]
    with x hx
  exact hx.trans (driftMask_sum_split (Nat.le_of_lt_succ j.isLt) p.toFunction.jet v w x)

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! Transfer finite readout moments to the actual raw weak-jet representatives. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

omit [FiniteDimensional ℝ E] in
theorem planeJetReadout_ae_raw {K : ℕ} (U : PlaneHk Set.univ K E) (α : JetIndex2 K) :
    planeJetReadoutOperator K α U =ᵐ[volume] U.toFunction.jet α :=
  univToPlane_ae (U.val α)

omit [FiniteDimensional ℝ E] in
theorem weighted_raw_jet_memLp_of_energy {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (U : PlaneHk Set.univ K E) (α : JetIndex2 K)
    (he : chartScalarEnergy (fun x => q x ^ 2) (planeJetReadoutOperator K α U) ≠ ⊤) :
    MemLp (fun x => q x • U.toFunction.jet α x) 2 (volume.restrict Set.univ) := by
  have hm := weighted_plane_memLp_of_chartEnergy_ne_top q hq (planeJetReadoutOperator K α U) he
  have hae : (fun x => q x • planeJetReadoutOperator K α U x) =ᵐ[volume]
      fun x => q x • U.toFunction.jet α x :=
    (planeJetReadout_ae_raw U α).mono (fun x hx => congrArg (fun e => q x • e) hx)
  simpa only [Measure.restrict_univ] using hm.ae_eq hae

theorem multiplyGrowingPlaneHk_readout_ae {K : ℕ} (U : PlaneHk Set.univ K E)
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (q : Vec 2 → ℝ) (hq : ∀ x, 0 ≤ q x)
    (hw : ∀ α, MemLp (fun x => q x • U.toFunction.jet α x) 2 (volume.restrict Set.univ))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l * q x)
    (α : JetIndex2 K) :
    planeJetReadoutOperator K α (multiplyGrowingPlaneHk U C hC q hq hw A hA hb) =ᵐ[volume]
      multiplicationRawJet C U.toFunction.jet α := by
  have hh := PlaneHkFunction.toHk_toFunction_ae
    (⟨multiplicationRawJet C U.toFunction.jet,
      multiplicationRawJet_memL2_growing C hC U.toFunction.jet U.toFunction.memL2 q hq hw A hA hb,
      multiplicationRawJet_hasOrderedWeakJetOn hC U.toFunction.hasWeakJet
        (jet_scalar_locallyIntegrable U.toFunction.memL2)⟩ : PlaneHkFunction Set.univ K F) α
  simp only [Measure.restrict_univ] at hh
  exact (planeJetReadout_ae_raw _ α).trans hh

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The spatial estimate for the actual compact clipped-weight scalar energy test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarDual_clipped_compact_estimate
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B g : ℝ) (hB : 0 < B)
    (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hvb : ∀ x, ‖v t x‖ ≤ M) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => (χ x ^ 2 * clipWeight B (W.W m t x)) • planeHkValueOperator (E := E) 1 u x) :
    let q := fun x => clipWeight B (W.W m t x)
    let U := planeHkValueOperator (E := E) 1 u
    let du := planeH1GradientOperator (E := E) u
    2 * inner ℝ (planeWeakDualRepresentative
      (planeScalarTransport (v t) (fun k => (contDiff_pi.mp hv k).continuous) hM
        (fun k x => (by simpa only [← Real.norm_eq_abs] using
          (norm_le_pi_norm (v t x) k).trans (hvb x))))
      (planeScalarDiffusion (G t) (fun k j => (hG k j).continuous) (by norm_num : (0 : ℝ) ≤ 5 / 4)
        (fun k j x => nearIdentity_entry_abs_le G g hg4 hGnear t x (hGs x) k j)) u F) z +
    (∫ x, χ x ^ 2 * deriv (fun s => clipWeight B (W.W m s x)) t * ‖U x‖ ^ 2) +
    (∫ x, χ x ^ 2 * q x * ‖(WithLp.toLp 2 (fun i => du i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
    18 * W.lam m * (∫ x, χ x ^ 2 * q x * ‖U x‖ ^ 2) +
    8 * (∫ x, q x * ‖(WithLp.toLp 2 (fun i => F i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
    (4096 * η ^ 2 + 16 * M * η) * (∫ x, q x * ‖U x‖ ^ 2) := by
  let q := fun x => clipWeight B (W.W m t x)
  let Φ := fun i x => clipWeightDeriv B (W.W m t x) * W.Phi m t x i
  let dt := fun x => deriv (fun s => clipWeight B (W.W m s x)) t
  let U := planeHkValueOperator (E := E) 1 u
  let du := planeH1GradientOperator (E := E) u
  obtain ⟨hq, hΦ, hdt⟩ := chartWeights_clipped_spatial_regularity W m hm t B hB
  have hvcomp k x : |v t x k| ≤ M := by
    simpa only [← Real.norm_eq_abs] using (norm_le_pi_norm (v t x) k).trans (hvb x)
  have hGb k j x : |G t x k j| ≤ 5 / 4 :=
    nearIdentity_entry_abs_le G g hg4 hGnear t x (hGs x) k j
  obtain ⟨hidentity, hL⟩ := planeScalarDual_cutoff_production_identity (v t) hv hM hvcomp (G t)
    hG hGs (by norm_num : (0 : ℝ) ≤ 5 / 4) hGb q χ hq hχ hsχ Φ hΦ dt hdt u z F hz
  let L := fun x => cutoffFluxProduction (G t) (v t) q χ Φ dt x
    (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)
  let e := fun x => χ x ^ 2 * q x * ‖U x‖ ^ 2
  let f := fun x => q x * ‖(WithLp.toLp 2 (fun i => F i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2
  let mass := fun x => q x * ‖U x‖ ^ 2
  have he : Integrable e volume := by
    apply compact_scalar_normSq_integrable U _ ((hχ.continuous.pow 2).mul hq.continuous)
    convert (hsχ.mul_right (f' := χ)).mul_right (f' := q) using 1
    funext x
    exact congrArg (fun r => r * q x) (pow_two (χ x))
  have hqb : ∀ᵐ x ∂volume, ‖q x‖ ≤ B := Filter.Eventually.of_forall (fun x => by
    rw [Real.norm_of_nonneg (clipWeight_pos hB (W.pos m hm t x)).le]
    exact clipWeight_le_bound hB (W.pos m hm t x))
  have hf : Integrable f volume := bounded_scalar_finiteLp_normSq_integrable F q
    hq.continuous.aestronglyMeasurable hqb
  have hmass : Integrable mass volume := bounded_scalar_Lp_normSq_integrable U q
    hq.continuous.aestronglyMeasurable hqb
  have hpoint : ∀ᵐ x ∂volume, L x ≤ (18 * W.lam m) * e x + 8 * f x +
      (4096 * η ^ 2 + 16 * M * η) * mass x := Filter.Eventually.of_forall (fun x => by
    have hh := chartWeights_clipped_cutoff_energy_pointwise W m hm t ht B g hB hg4 hGnear
      hv hdiv hGs hG χ (hχ.differentiable (by norm_num)) x hM hη
      (hχ0 x) (hχ1 x) (hvb x) (hdχ x)
      (WithLp.toLp 2 (fun i => du i x)) (WithLp.toLp 2 (fun i => F i x)) (U x)
    dsimp only [L, e, f, mass]
    nlinarith only [hh])
  have hbudget := integral_three_term_bound L e f mass (18 * W.lam m) 8
    (4096 * η ^ 2 + 16 * M * η) hL he hf hmass hpoint
  rw [← hidentity] at hbudget
  exact hbudget

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! An everywhere-defined curve of genuine growing-coefficient Sobolev products. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]

def growingPlaneHkCurve {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (U : ℝ → PlaneHk Set.univ K E) (t : ℝ) : PlaneHk Set.univ K F :=
  if he : ∀ α, chartScalarEnergy (fun x => q x ^ 2) (planeJetReadoutOperator K α (U t)) ≠ ⊤ then
    multiplyGrowingPlaneHk (U t) (C t) (hC t) q hq0
      (fun α => weighted_raw_jet_memLp_of_energy q hq (U t) α (he α)) A hA (fun l => hb l t)
  else 0

theorem growingPlaneHkCurve_readout_ae {K : ℕ}
    (q : Vec 2 → ℝ) (hq : Continuous q) (hq0 : ∀ x, 0 ≤ q x)
    (C : ℝ → Vec 2 → E →L[ℝ] F) (hC : ∀ t, ContDiff ℝ (K : ℕ) (C t))
    (A : Fin (K + 1) → ℝ) (hA : ∀ l, 0 ≤ A l)
    (hb : ∀ l t x, ‖coefficientDerivativeArray (C t) l.val x‖ ≤ A l * q x)
    (U : ℝ → PlaneHk Set.univ K E) (t : ℝ)
    (he : ∀ α, chartScalarEnergy (fun x => q x ^ 2) (planeJetReadoutOperator K α (U t)) ≠ ⊤)
    (α : JetIndex2 K) :
    planeJetReadoutOperator K α (growingPlaneHkCurve q hq hq0 C hC A hA hb U t) =ᵐ[volume]
      multiplicationRawJet (C t) (U t).toFunction.jet α := by
  rw [growingPlaneHkCurve, dite_eq_left he]
  exact multiplyGrowingPlaneHk_readout_ae _ _ _ _ _ _ _ _ _ α

end AVRegularity.Weighted
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Every given scalar chain energy solution has the actual weak Hilbert time curve. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The scalar solution's drift, metric and forcing construct its weak Hilbert dual. -/
theorem scalarChain_planeWeakHilbertCurve
    (a b : ℝ) (hab : a ≤ b) (κ : Fin 1 → ι → ℕ)
    (v : ℝ → Vec 2 → Vec 2) (hvc : ∀ t ∈ Icc a b, Continuous (v t))
    (hvm : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (M : ℝ) (hvb : ∀ t ∈ Icc a b, ∀ z, ‖v t z‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hGc : ∀ t ∈ Icc a b, ∀ k j, Continuous (fun z => G t z k j))
    (hGm : Measurable (fun p : Icc a b × Vec 2 => G p.1 p.2))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hG : IsMetricNearIdentity G g)
    (hsym : ∀ t ∈ Icc a b, ∀ z, (G t z).IsSymm)
    (f : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (F : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (PiLp 2 (fun _ : Fin 2 => h p.2)))
    (hF : ∀ p, MemLp (F p) 2 (volume.restrict (Icc a b)))
    (u : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (w : ∀ p : Fin 1 × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsln : IsCoupledWeakSolutionPlane 1 a b v 2 (fun p : Fin 1 × ι => κ p.1 p.2)
      (planeChainCoefficient (geometryScalarData (h := h) 2 G) κ) f F
      (fun _ _ => 0) u w) (i : Fin 1 × ι) :
    PlaneWeakHilbertCurve a b (coupledPlaneL2Trace u i) (coupledPlaneH1Slice w i)
      (fun t => planeWeakDualRepresentative
        (planeIntervalTransport a b hab v hvc M hvb t)
        (planeIntervalDiffusion a b hab G hGc g hg4 hG hsym t)
        (coupledPlaneH1Slice w i t) (planeFluxValueOperator (E := h i.2) (κ i.1 i.2) (F i t))) := by
  apply coupledWeakSolution_planeWeakHilbertCurve hsln i
  · exact planeIntervalDual_memLp a b hab v hvc hvm M hvb G hGc hGm g hg4 hG hsym
      (coupledPlaneH1Slice w i) (κ i.1 i.2) (F i)
      (coupledWeakSolution_h1_trace_data hsln i).2.1 (hF i)
  · intro s hs t ht hst φ
    rw [scalarChainTrace_increment a b hab κ v G f F u w hsln i hs ht φ]
    apply intervalIntegral.integral_congr
    intro r hr
    have hrab : r ∈ Icc a b :=
      Icc_subset_Icc hs.1 ht.2 (by simpa only [uIcc_of_le hst] using hr)
    have hp := planeScalarDual_pair_eq_raw (κ i.1 i.2)
      (planeIntervalCoefficient a b hab v r)
      (planeIntervalVelocity_continuous a b hab v hvc r) (le_max_right M 0)
      (planeIntervalVelocity_bound a b hab v M hvb r)
      (planeIntervalCoefficient a b hab G r)
      (planeIntervalMetric_continuous a b hab G hGc r) (by norm_num : (0 : ℝ) ≤ 5 / 4)
      (planeIntervalMetric_bound a b hab G g hg4 hG hsym r) (w i r) (F i r) φ
    change (∫ x, planeScalarRawRhs (κ i.1 i.2) (v r) (G r) (w i r) (F i r) φ x) = _
    have heq : (∫ x, planeScalarRawRhs (κ i.1 i.2)
        (planeIntervalCoefficient a b hab v r) (planeIntervalCoefficient a b hab G r)
        (w i r) (F i r) φ x) =
        ∫ x, planeScalarRawRhs (κ i.1 i.2) (v r) (G r) (w i r) (F i r) φ x := by
      rw [planeIntervalCoefficient_of_mem a b hab v r hrab,
        planeIntervalCoefficient_of_mem a b hab G r hrab]
    exact heq.symm.trans hp.symm

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The spatial estimate for the actual compact clipped-weight scalar energy test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeScalarDual_clipped_value_estimate
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (t : ℝ) (ht : t ∈ Icc t₀ (t₀ + S)) (B g : ℝ) (hB : 0 < B)
    (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hv : ContDiff ℝ 1 (v t))
    (hdiv : ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (hGs : ∀ x, (G t x).IsSymm)
    (hG : ∀ i j : Fin 2, ContDiff ℝ 1 (fun x => G t x i j))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    {M η : ℝ} (hM : 0 ≤ M) (hη : 0 ≤ η)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (hvb : ∀ x, ‖v t x‖ ≤ M) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (u z : PlaneHk Set.univ 1 E) (F : PlaneFluxL2 E)
    (H : Lp E 2 (volume : Measure (Vec 2)))
    (hz : planeHkValueOperator (E := E) 1 z =ᵐ[volume]
      fun x => (χ x ^ 2 * clipWeight B (W.W m t x)) • planeHkValueOperator (E := E) 1 u x) :
    let q := fun x => clipWeight B (W.W m t x)
    let U := planeHkValueOperator (E := E) 1 u
    let du := planeH1GradientOperator (E := E) u
    2 * inner ℝ (planeValueForcedDual
      (planeScalarTransport (v t) (fun k => (contDiff_pi.mp hv k).continuous) hM
        (fun k x => (by simpa only [← Real.norm_eq_abs] using
          (norm_le_pi_norm (v t x) k).trans (hvb x))))
      (planeScalarDiffusion (G t) (fun k j => (hG k j).continuous) (by norm_num : (0 : ℝ) ≤ 5 / 4)
        (fun k j x => nearIdentity_entry_abs_le G g hg4 hGnear t x (hGs x) k j)) u F H) z +
    (∫ x, χ x ^ 2 * deriv (fun s => clipWeight B (W.W m s x)) t * ‖U x‖ ^ 2) +
    (∫ x, χ x ^ 2 * q x * ‖(WithLp.toLp 2 (fun i => du i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
    18 * W.lam m * (∫ x, χ x ^ 2 * q x * ‖U x‖ ^ 2) +
    8 * (∫ x, q x * ‖(WithLp.toLp 2 (fun i => F i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
    (4096 * η ^ 2 + 16 * M * η) * (∫ x, q x * ‖U x‖ ^ 2) +
      2 * (∫ x, (χ x ^ 2 * q x) * (‖H x‖ * ‖U x‖)) := by
  have hs := planeScalarDual_clipped_compact_estimate W m hm t ht B g hB hg4 hGnear
    hv hdiv hGs hG χ hχ hsχ hM hη hχ0 hχ1 hvb hdχ u z F hz
  obtain ⟨hq, _, _⟩ := chartWeights_clipped_spatial_regularity W m hm t B hB
  let q := fun x => χ x ^ 2 * clipWeight B (W.W m t x)
  have hq0 x : 0 ≤ q x := mul_nonneg (sq_nonneg _) (clipWeight_pos hB (W.pos m hm t x)).le
  have hqb x : ‖q x‖ ≤ B := by
    rw [Real.norm_of_nonneg (hq0 x)]
    have hc : χ x ^ 2 ≤ 1 := by nlinarith only [hχ0 x, hχ1 x]
    calc
      q x ≤ 1 * clipWeight B (W.W m t x) :=
        mul_le_mul_of_nonneg_right hc (clipWeight_pos hB (W.pos m hm t x)).le
      _ ≤ B := by rw [one_mul]; exact clipWeight_le_bound hB (W.pos m hm t x)
  have hqp : AEStronglyMeasurable q volume :=
    ((hχ.continuous.pow 2).mul hq.continuous).aestronglyMeasurable
  have hp := planeValueForcing_weighted_pair_abs_le H
    (planeHkValueOperator (E := E) 1 u) z q hqp
    (Filter.Eventually.of_forall hqb) (Filter.Eventually.of_forall hq0) hz
  rw [ContinuousLinearMap.adjoint_inner_left] at hp
  have hp' := (le_abs_self (inner ℝ H (planeHkValueOperator (E := E) 1 z))).trans hp
  dsimp only
  rw [planeValueForcedDual_pair, mul_add]
  dsimp only [q] at hp'
  linarith only [hs, hp']

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The stored metric flux is the word's principal diffusion plus its actual commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeWordMetricCommutator {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (hGc : ∀ k a, Continuous (fun x => G x k a))
    (C : ℝ) (hC : 0 ≤ C) (hGb : ∀ k a x, |G x k a| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) : PlaneFluxL2 E :=
  planeJetFluxOperator K α (planeMetricGradientCarrier G hG M hb W) -
    planeScalarDiffusion G hGc hC hGb
      (planeH1GradientOperator (planeWordH1SliceOperator K α W))

theorem planeWordMetricCommutator_ae {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (hGc : ∀ k a, Continuous (fun x => G x k a))
    (C : ℝ) (hC : 0 ≤ C) (hGb : ∀ k a x, |G x k a| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) (k : Fin 2) :
    planeWordMetricCommutator G hG M hb hGc C hC hGb W α k =ᵐ[volume]
      fun x => metricCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        G W.toFunction.jet α.2 x k := by
  let A := planeJetFluxOperator K α (planeMetricGradientCarrier G hG M hb W)
  let B := planeScalarDiffusion G hGc hC hGb
    (planeH1GradientOperator (planeWordH1SliceOperator K α W))
  have hgrad : ∀ᵐ x ∂volume, ∀ a : Fin 2,
      planeH1GradientOperator (planeWordH1SliceOperator K α W) a x =
        W.toFunction.jet ⟨⟨α.1.val + 1, Nat.succ_lt_succ α.1.isLt⟩, Fin.snoc α.2 a⟩ x := by
    apply ae_all_iff.mpr
    intro a
    rw [planeWordH1Slice_gradient]
    exact univToPlane_ae _
  have hm := planeMetricGradientCarrier_principal_commutator_ae G hG M hb W α.1 α.2
  simp only [Measure.restrict_univ] at hm
  change A k - B k =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub (A k) (B k),
    planeJetFluxOperator_ae α (planeMetricGradientCarrier G hG M hb W) k,
    planeScalarDiffusion_ae G hGc hC hGb
      (planeH1GradientOperator (planeWordH1SliceOperator K α W)) k, hm, hgrad]
    with x hx hA hB hM hg
  rw [hx]
  dsimp only [A, B, Pi.sub_apply]
  rw [hA, hM, hB]
  simp only [PiLp.add_apply, finiteMetricFlux]
  simp_rw [hg]
  simp

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Weighted

/-! The actual Sobolev transport carrier inherits time square integrability. -/

variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance transportIntegrableAdd (K : ℕ) : AddCommGroup (PlaneHk Set.univ K E) := inferInstance
local instance transportIntegrableTopAdd (K : ℕ) : IsTopologicalAddGroup (PlaneHk Set.univ K E) := inferInstance

theorem planeTransportCarrier_memLp (μ : Measure T) {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : T → Vec 2 → Vec 2) (hvm : Measurable (Function.uncurry v))
    (hv : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V a B lam : ℝ) (hbv : ∀ t x, ‖v t x‖ ≤ V)
    (hB : ∀ l : Fin (K + 1), 0 ≤ driftEnvelope V a B lam l.val)
    (hjets : ∀ t l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (w : T → PlaneHk Set.univ (K + 1) E) (hw : MemLp w 2 μ) :
    MemLp (fun t => planeTransportCarrier hK (v t) (hv t) V (hbv t)
      a B lam (hjets t) (w t)) 2 μ := by
  let U := hw.toLp w
  let Q := planeTransportTimeCLM μ hK v hvm hv V a B lam hbv hB hjets U
  have he : Q =ᵐ[μ] fun t => planeTransportCarrier hK (v t) (hv t) V (hbv t)
      a B lam (hjets t) (w t) := by
    filter_upwards [planeTransportTimeCLM_ae μ hK v hvm hv V a B lam hbv hB hjets U,
      hw.coeFn_toLp] with t ht hu
    rw [ht, hu]
  exact (memLp_congr_ae he).mp (Lp.memLp Q)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The actual clipped chart energy with a spatial cutoff has its exact time production. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_clipped_compact_energy_time {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk Set.univ 1 E} (h : PlaneWeakHilbertCurve a b u slice dual)
    (w : ℝ × Vec 2 → ℝ) (hw : ContDiff ℝ 2 w) (hp : ∀ p, 0 < w p)
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (L : ℝ) (hL : 0 < L) :
    ∃ B : ℝ → PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E,
      (∀ t ∈ Icc a b, ∀ z, planeHkValueOperator (E := E) 1 (B t z) =ᵐ[volume]
        fun x => (χ x ^ 2 * clipWeight L (w (t,x))) • planeHkValueOperator (E := E) 1 z x) ∧
      AVRegularity.CycleEvolution.StrongTimeRegularity a b
        (fun t => ∫ x, χ x ^ 2 * clipWeight L (w (t,x)) * ‖u t x‖ ^ 2)
        (fun t => 2 * inner ℝ (dual t) (B t (slice t)) +
          ∫ x, χ x ^ 2 * deriv (fun s => clipWeight L (w (s,x))) t * ‖u t x‖ ^ 2) := by
  obtain ⟨τ, hτ, hsτ, _hbτ, hτ1⟩ := exists_compact_time_cutoff a b
  have hτ2 : ContDiff ℝ 2 τ := hτ.of_le (by simp)
  let f := compactChartWeightRoot τ χ L w
  have hf : ContDiff ℝ 2 f := compactChartWeightRoot_contDiff τ hτ2 χ hχ L hL w hw hp
  have hsf : HasCompactSupport f := compactChartWeightRoot_hasCompactSupport τ hsτ χ hsχ L w
  obtain ⟨B, hB, htime⟩ := planeWeak_compact_weighted_energy_strongTime hab h f hf hsf
  have hsq t (ht : t ∈ Icc a b) x : f (t,x) ^ 2 = χ x ^ 2 * clipWeight L (w (t,x)) := by
    rw [compactChartWeightRoot_sq τ χ L hL w hp, (hτ1 t ht).1]
    simp
  have hdt t (ht : t ∈ Icc a b) x :
      2 * f (t,x) * fderiv ℝ f (t,x) (1,0) =
        χ x ^ 2 * deriv (fun s => clipWeight L (w (s,x))) t :=
    compactChartWeightRoot_time_production τ hτ2 χ hχ L hL w hw hp t x
      (hτ1 t ht).1 (hτ1 t ht).2
  refine ⟨B, ?_, strongTime_congr_on_window hab htime ?_ ?_⟩
  · intro t ht z
    simpa only [hsq t ht] using hB t z
  · intro t ht
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x =>
      congrArg (fun r => r * ‖u t x‖ ^ 2) (hsq t ht x))
  · intro t ht
    congr 1
    rw [← integral_const_mul]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun x => by
      calc
        2 * (f (t,x) * fderiv ℝ f (t,x) (1,0) * ‖u t x‖ ^ 2) =
            (2 * f (t,x) * fderiv ℝ f (t,x) (1,0)) * ‖u t x‖ ^ 2 := by ring
        _ = _ := by rw [hdt t ht x])

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The stored metric flux is the word's principal diffusion plus its actual commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarMetricCarrier_word_residual {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (hGc : ∀ k a, Continuous (fun x => G x k a))
    (C : ℝ) (hC : 0 ≤ C) (hGb : ∀ k a x, |G x k a| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) :
    planeJetFluxOperator K α (planeMetricGradientCarrier G hG M hb W + F) -
      planeScalarDiffusion G hGc hC hGb
        (planeH1GradientOperator (planeWordH1SliceOperator K α W)) =
      planeWordMetricCommutator G hG M hb hGc C hC hGb W α + planeJetFluxOperator K α F := by
  rw [map_add]
  unfold planeWordMetricCommutator
  abel

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The retained weighted factorial production is time integrable for the actual Sobolev lift. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem rawWeightedGradient_time_integrable {K : ℕ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) (μ : Measure ℝ)
    (W : ℝ → PlaneHk Set.univ (K + 1) E) (hW : MemLp W 2 μ) :
    Integrable (fun t => rawWeightedGradientEnergy ρ
      (fun x => clipWeight B (C.W m t x)) (W t).toFunction.jet) μ := by
  have hi (α : JetIndex2 K) : Integrable (fun t =>
      ∫ x, clipWeight B (C.W m t x) *
        ‖(WithLp.toLp 2 (fun k : Fin 2 =>
          planeH1GradientOperator (planeWordH1SliceOperator K α (W t)) k x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) μ := by
    have hg := (planeH1GradientOperator (E := E)).comp_memLp'
      ((planeWordH1SliceOperator (E := E) K α).comp_memLp' hW)
    exact chartWeights_clipped_finite_time_integrable (E := E) C m hm B hB μ _ hg
  have hsum := integrable_finsetSum (Finset.univ : Finset (JetIndex2 K))
    (fun α _ => (hi α).const_mul (factorialWeight ρ α.1.val))
  apply hsum.congr
  exact Filter.Eventually.of_forall (fun t => planeStoredWord_gradient_energy ρ _ (W t))

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! No commutator source occurs at the original undifferentiated equation. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem metricCommutatorTerm_order_zero {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (D : RawJet2 (K + 1) E)
    (w : DerivativeWord2 0) (x : Vec 2) :
    metricCommutatorTerm (Nat.zero_le K) G D w x = 0 := by
  unfold metricCommutatorTerm
  apply Finset.sum_eq_zero
  intro m _
  have hm : maskLeftLength 0 m = 0 := Nat.eq_zero_of_le_zero (maskLeftLength_le 0 m)
  simp [hm]

theorem planeDriftCommutatorTerm_order_zero {K : ℕ}
    (v : Vec 2 → Vec 2) (D : RawJet2 (K + 1) E)
    (w : DerivativeWord2 0) (x : Vec 2) :
    planeDriftCommutatorTerm (Nat.zero_le K) v D w x = 0 := by
  unfold planeDriftCommutatorTerm
  apply Finset.sum_eq_zero
  intro m _
  have hm : maskLeftLength 0 m = 0 := Nat.eq_zero_of_le_zero (maskLeftLength_le 0 m)
  simp [hm]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The stored transport is the word's transport plus its genuine value commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def planeWordDriftCommutator {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hvc : ∀ k, Continuous (fun x => v x k))
    (C : ℝ) (hC : 0 ≤ C) (hvb : ∀ k x, |v x k| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) : Lp E 2 (volume : Measure (Vec 2)) :=
  planeJetReadoutOperator K α (planeTransportCarrier hK v hv V hbv a B lam hjets W) -
    planeScalarTransport v hvc hC hvb
      (planeH1GradientOperator (planeWordH1SliceOperator K α W))

theorem planeWordDriftCommutator_ae {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hvc : ∀ k, Continuous (fun x => v x k))
    (C : ℝ) (hC : 0 ≤ C) (hvb : ∀ k x, |v x k| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) :
    planeWordDriftCommutator hK v hv V hbv a B lam hjets hvc C hC hvb W α =ᵐ[volume]
      fun x => planeDriftCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        v W.toFunction.jet α.2 x := by
  let A := planeJetReadoutOperator K α (planeTransportCarrier hK v hv V hbv a B lam hjets W)
  let Q := planeScalarTransport v hvc hC hvb
    (planeH1GradientOperator (planeWordH1SliceOperator K α W))
  have hgrad : ∀ᵐ x ∂volume, ∀ k : Fin 2,
      planeH1GradientOperator (planeWordH1SliceOperator K α W) k x =
        W.toFunction.jet ⟨⟨α.1.val + 1, Nat.succ_lt_succ α.1.isLt⟩, Fin.snoc α.2 k⟩ x := by
    apply ae_all_iff.mpr
    intro k
    rw [planeWordH1Slice_gradient]
    exact univToPlane_ae _
  have hm := planeTransportCarrier_principal_commutator_ae hK v hv V hbv a B lam hjets W α.1 α.2
  simp only [Measure.restrict_univ] at hm
  change A - Q =ᵐ[volume] _
  filter_upwards [Lp.coeFn_sub A Q,
    univToPlane_ae ((planeTransportCarrier hK v hv V hbv a B lam hjets W).val α),
    planeScalarTransport_ae v hvc hC hvb
      (planeH1GradientOperator (planeWordH1SliceOperator K α W)), hm, hgrad]
    with x hx hA hB hM hg
  rw [hx]
  dsimp only [A, Q, Pi.sub_apply]
  rw [planeJetReadoutOperator_apply, hA, hM, hB]
  simp_rw [hg]
  simp

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution
namespace AVRegularity.Weighted

/-! The stored metric flux is the word's principal diffusion plus its actual commutator. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarMetricCarrier_word_residual_ae {K : ℕ}
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k a, ContDiff ℝ (K : ℕ) (fun x => G x k a))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ (l : Fin (K + 1)) x k a,
      ‖iteratedFDeriv ℝ l.val (fun y => G y k a) x‖ ≤ M l)
    (hGc : ∀ k a, Continuous (fun x => G x k a))
    (C : ℝ) (hC : 0 ≤ C) (hGb : ∀ k a x, |G x k a| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K)
    (F : PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (k : Fin 2) :
    (planeJetFluxOperator K α (planeMetricGradientCarrier G hG M hb W + F) -
      planeScalarDiffusion G hGc hC hGb
        (planeH1GradientOperator (planeWordH1SliceOperator K α W))) k =ᵐ[volume]
      fun x => metricCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        G W.toFunction.jet α.2 x k + F.val α x k := by
  rw [scalarMetricCarrier_word_residual]
  change (planeWordMetricCommutator G hG M hb hGc C hC hGb W α k +
    planeJetFluxOperator K α F k) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_add
    (planeWordMetricCommutator G hG M hb hGc C hC hGb W α k)
    (planeJetFluxOperator K α F k),
    planeWordMetricCommutator_ae G hG M hb hGc C hC hGb W α k,
    planeJetFluxOperator_ae α F k] with x ha hc hf
  exact ha.trans (congrArg₂ HAdd.hAdd hc hf)

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! Exact clipped weighted time production with the genuine value commutator term. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_clipped_value_energy_time {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice : ℝ → PlaneHk Set.univ 1 E}
    (T : ℝ → PlaneFluxL2 E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)))
    (D : ℝ → PlaneFluxL2 E →L[ℝ] PlaneFluxL2 E)
    (F : ℝ → PlaneFluxL2 E) (g : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (h : PlaneWeakHilbertCurve a b u slice
      (fun t => planeValueForcedDual (T t) (D t) (slice t) (F t) (g t)))
    (w : ℝ × Vec 2 → ℝ) (hw : ContDiff ℝ 2 w) (hp : ∀ p, 0 < w p)
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (L : ℝ) (hL : 0 < L) :
    ∃ B : ℝ → PlaneHk Set.univ 1 E →L[ℝ] PlaneHk Set.univ 1 E,
      (∀ t ∈ Icc a b, ∀ z, planeHkValueOperator (E := E) 1 (B t z) =ᵐ[volume]
        fun x => (χ x ^ 2 * clipWeight L (w (t,x))) • planeHkValueOperator (E := E) 1 z x) ∧
      AVRegularity.CycleEvolution.StrongTimeRegularity a b
        (fun t => ∫ x, χ x ^ 2 * clipWeight L (w (t,x)) * ‖u t x‖ ^ 2)
        (fun t => 2 * inner ℝ (planeWeakDualRepresentative (T t) (D t) (slice t) (F t))
            (B t (slice t)) +
          2 * (∫ x, (χ x ^ 2 * clipWeight L (w (t,x))) *
            inner ℝ (g t x) (planeHkValueOperator (E := E) 1 (slice t) x)) +
          ∫ x, χ x ^ 2 * deriv (fun s => clipWeight L (w (s,x))) t * ‖u t x‖ ^ 2) := by
  obtain ⟨B, hB, htime⟩ := planeWeak_clipped_compact_energy_time hab h w hw hp χ hχ hsχ L hL
  refine ⟨B, hB, strongTime_congr_on_window hab htime (fun _ _ => rfl) ?_⟩
  intro t ht
  rw [planeValueForcedDual_pair, mul_add]
  have hpair := planeValueForcing_pair_of_value (g t) (B t (slice t))
    (planeHkValueOperator (E := E) 1 (slice t))
    (fun x => χ x ^ 2 * clipWeight L (w (t,x))) (hB t ht (slice t))
  rw [ContinuousLinearMap.adjoint_inner_left] at hpair
  rw [hpair]

end AVRegularity.Weighted
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.Weighted

/-! The stored transport is the word's transport plus its genuine value commutator. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarDriftCarrier_word_residual {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hvc : ∀ k, Continuous (fun x => v x k))
    (C : ℝ) (hC : 0 ≤ C) (hvb : ∀ k x, |v x k| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) :
    planeJetReadoutOperator K α (-planeTransportCarrier hK v hv V hbv a B lam hjets W) +
      planeScalarTransport v hvc hC hvb
        (planeH1GradientOperator (planeWordH1SliceOperator K α W)) =
      -planeWordDriftCommutator hK v hv V hbv a B lam hjets hvc C hC hvb W α := by
  rw [map_neg]
  unfold planeWordDriftCommutator
  abel
end

/-! The stored transport is the word's transport plus its genuine value commutator. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem scalarDriftCarrier_word_residual_ae {K Kmax : ℕ} (hK : K ≤ Kmax)
    (v : Vec 2 → Vec 2) (hv : ContDiff ℝ (⊤ : ℕ∞) v)
    (V : ℝ) (hbv : ∀ x, ‖v x‖ ≤ V) (a B lam : ℝ)
    (hjets : ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient v) l x‖ ≤
        a * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hvc : ∀ k, Continuous (fun x => v x k))
    (C : ℝ) (hC : 0 ≤ C) (hvb : ∀ k x, |v x k| ≤ C)
    (W : PlaneHk Set.univ (K + 1) E) (α : JetIndex2 K) :
    (planeJetReadoutOperator K α (-planeTransportCarrier hK v hv V hbv a B lam hjets W) +
      planeScalarTransport v hvc hC hvb
        (planeH1GradientOperator (planeWordH1SliceOperator K α W))) =ᵐ[volume]
      fun x => -planeDriftCommutatorTerm (Nat.le_of_lt_succ α.1.isLt)
        v W.toFunction.jet α.2 x := by
  rw [scalarDriftCarrier_word_residual]
  filter_upwards [Lp.coeFn_neg (planeWordDriftCommutator hK v hv V hbv a B lam hjets
    hvc C hC hvb W α),
    planeWordDriftCommutator_ae hK v hv V hbv a B lam hjets hvc C hC hvb W α]
    with x hn hc
  exact hn.trans (congrArg Neg.neg hc)
end

end AVRegularity.Weighted
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! The summed stored-word dissipation is the true factorial production on a time window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeStoredWord_gradient_interval_energy {K : ℕ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (ρ a b : ℝ) (hab : a ≤ b)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (hW : MemLp W 2 (volume.restrict (Set.Icc a b))) :
    (∑ α : JetIndex2 K, factorialWeight ρ α.1.val *
      (∫ t in a..b, ∫ x, clipWeight B (C.W m t x) *
        ‖(WithLp.toLp 2 (fun k : Fin 2 =>
          planeH1GradientOperator (planeWordH1SliceOperator K α (W t)) k x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2)) =
      ∫ t in a..b, rawWeightedGradientEnergy ρ
        (fun x => clipWeight B (C.W m t x)) (W t).toFunction.jet := by
  have hi (α : JetIndex2 K) : IntervalIntegrable (fun t =>
      ∫ x, clipWeight B (C.W m t x) *
        ‖(WithLp.toLp 2 (fun k : Fin 2 =>
          planeH1GradientOperator (planeWordH1SliceOperator K α (W t)) k x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) volume a b := by
    have hg := (planeH1GradientOperator (E := E)).comp_memLp'
      ((planeWordH1SliceOperator (E := E) K α).comp_memLp' hW)
    exact intervalIntegrable_of_integrable_Icc hab
      (chartWeights_clipped_finite_time_integrable (E := E) C m hm B hB _ _ hg)
  rw [intervalIntegral_weighted_sum a b _ _ hi]
  apply intervalIntegral.integral_congr
  intro t _
  exact planeStoredWord_gradient_energy ρ _ (W t)
end

/-! Actual Sobolev flux data give time-integrable clipped factorial energy. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem rawWeightedFlux_time_integrable {K : ℕ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {v : ℝ → Vec 2 → Vec 2}
    {t₀ S ϖ : ℝ} {zc : Vec 2} {N : ℕ} {Cw : ℕ → ℝ}
    (C : ChartWeights G v t₀ S ϖ zc N Cw) (m : ℕ) (hm : m ≤ N)
    (B : ℝ) (hB : 0 < B) (ρ : ℝ) (μ : Measure ℝ)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E))) (hF : MemLp F 2 μ) :
    Integrable (fun t => rawWeightedFactorialEnergy ρ
      (fun x => clipWeight B (C.W m t x)) (F t).toFunction.jet) μ := by
  have hi (α : JetIndex2 K) : Integrable (fun t =>
      ∫ x, clipWeight B (C.W m t x) *
        ‖(WithLp.toLp 2 (fun k : Fin 2 => planeJetFluxOperator K α (F t) k x) :
          PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) μ := by
    have hf := (planeJetFluxOperator (E := E) K α).comp_memLp' hF
    exact chartWeights_clipped_finite_time_integrable (E := E) C m hm B hB μ _ hf
  have hsum := integrable_finsetSum (Finset.univ : Finset (JetIndex2 K))
    (fun α _ => (hi α).const_mul (factorialWeight ρ α.1.val))
  apply hsum.congr
  exact Filter.Eventually.of_forall (fun t => planeStoredWord_flux_energy ρ _ (F t))
end

end AVRegularity.Weighted
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.Weighted

/-! A testing weight multiplies the complete commutator source without producing new derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem planeDriftCommutatorTerm_scaledRawJet {K j : ℕ} (hj : j ≤ K)
    (v : Vec 2 → Vec 2) (s : Vec 2 → ℝ) (D : RawJet2 (K + 1) E)
    (w : DerivativeWord2 j) (x : Vec 2) :
    planeDriftCommutatorTerm hj v (scaledRawJet s D) w x =
      s x • planeDriftCommutatorTerm hj v D w x := by
  unfold planeDriftCommutatorTerm
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs
  · exact driftMaskTerm_scaledRawJet hj v s D m w x
  · exact (smul_zero _).symm

theorem metricCommutatorTerm_scaledRawJet {K j : ℕ} (hj : j ≤ K)
    (G : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (s : Vec 2 → ℝ)
    (D : RawJet2 (K + 1) E) (w : DerivativeWord2 j) (x : Vec 2) :
    metricCommutatorTerm hj G (scaledRawJet s D) w x =
      s x • metricCommutatorTerm hj G D w x := by
  unfold metricCommutatorTerm
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  split_ifs
  · exact metricMaskTerm_scaledRawJet hj G s D m w x
  · exact (smul_zero _).symm

end AVRegularity.Weighted
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.Weighted

/-! The actual scalar weak time curve satisfies the clipped compact energy growth inequality. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeak_clipped_value_energy_growth
    (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Icc a b, ContDiff ℝ 1 (v t))
    (hdiv : ∀ t ∈ Icc a b, ∀ x, ∑ j : Fin 2, fderiv ℝ (v t) x (basisVec j) j = 0)
    (M : ℝ) (hM : 0 ≤ M) (hvb : ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ M)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Icc a b, ∀ k j, ContDiff ℝ 1 (fun x => G t x k j))
    (g : ℝ) (hg4 : g ≤ 1 / 4) (hGnear : IsMetricNearIdentity G g)
    (hGs : ∀ t ∈ Icc a b, ∀ x, (G t x).IsSymm)
    (t₀ S ϖ : ℝ) (zc : Vec 2) (N m : ℕ) (Cw : ℕ → ℝ)
    (W : ChartWeights G v t₀ S ϖ zc N Cw) (hm : m ≤ N)
    (ha : t₀ ≤ a) (hb : b ≤ t₀ + S)
    (u : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (slice : ℝ → PlaneHk Set.univ 1 E) (F : ℝ → PlaneFluxL2 E)
    (H : ℝ → Lp E 2 (volume : Measure (Vec 2)))
    (h : PlaneWeakHilbertCurve a b u slice
      (fun t => planeValueForcedDual
        (planeIntervalTransport a b hab v (fun t ht => (hv t ht).continuous) M hvb t)
        (planeIntervalDiffusion a b hab G (fun t ht k j => (hG t ht k j).continuous)
          g hg4 hGnear hGs t) (slice t) (F t) (H t)))
    (χ : Vec 2 → ℝ) (hχ : ContDiff ℝ 2 χ) (hsχ : HasCompactSupport χ)
    (hχ0 : ∀ x, 0 ≤ χ x) (hχ1 : ∀ x, χ x ≤ 1)
    (η : ℝ) (hη : 0 ≤ η) (hdχ : ∀ x, ‖fderiv ℝ χ x‖ ≤ η)
    (B : ℝ) (hB : 0 < B) :
    ∃ P : ℝ → ℝ,
      AVRegularity.CycleEvolution.StrongTimeRegularity a b
        (fun t => ∫ x, χ x ^ 2 * clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) P ∧
      (∀ᵐ t ∂volume.restrict (Icc a b),
        P t + (∫ x, χ x ^ 2 * clipWeight B (W.W m t x) *
          ‖(WithLp.toLp 2 (fun i => planeH1GradientOperator (E := E) (slice t) i x) :
            PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) ≤
        18 * W.lam m * (∫ x, χ x ^ 2 * clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
        8 * (∫ x, clipWeight B (W.W m t x) *
          ‖(WithLp.toLp 2 (fun i => F t i x) : PiLp 2 (fun _ : Fin 2 => E))‖ ^ 2) +
        (4096 * η ^ 2 + 16 * M * η) * (∫ x, clipWeight B (W.W m t x) * ‖u t x‖ ^ 2) +
        2 * (∫ x, (χ x ^ 2 * clipWeight B (W.W m t x)) * (‖H t x‖ * ‖u t x‖))) := by
  obtain ⟨A, hA, htime⟩ := planeWeak_clipped_value_energy_time hab _ _ F H h
    (fun p => W.W m p.1 p.2) (W.smooth m hm).1
    (fun p => W.pos m hm p.1 p.2) χ hχ hsχ B hB
  refine ⟨_, htime, ?_⟩
  filter_upwards [h.agrees, ae_restrict_mem measurableSet_Icc] with t hut ht
  have htW : t ∈ Icc t₀ (t₀ + S) := ⟨ha.trans ht.1, ht.2.trans hb⟩
  have hs := planeScalarDual_clipped_value_estimate W m hm t htW B g hB hg4 hGnear
    (hv t ht) (hdiv t ht) (hGs t ht) (hG t ht) χ hχ hsχ hM hη hχ0 hχ1
    (hvb t ht) hdχ (slice t) (A t (slice t)) (F t) (H t) (hA t ht (slice t))
  have hvcomp k x : |v t x k| ≤ M := by
    simpa only [← Real.norm_eq_abs] using (norm_le_pi_norm (v t x) k).trans (hvb t ht x)
  have hGb k j x : |G t x k j| ≤ 5 / 4 :=
    nearIdentity_entry_abs_le G g hg4 hGnear t x (hGs t ht x) k j
  have hT := planeIntervalTransport_eq_of_mem (E := E) a b hab v
    (fun t ht => (hv t ht).continuous) M hM hvb t ht
    (fun k => (contDiff_pi.mp (hv t ht) k).continuous) hvcomp
  have hD := planeIntervalDiffusion_eq_of_mem (E := E) a b hab G
    (fun t ht k j => (hG t ht k j).continuous) g hg4 hGnear hGs t ht
    (fun k j => (hG t ht k j).continuous) hGb
  rw [hut, hT, hD]
  dsimp only at hs
  rw [planeValueForcedDual_pair, mul_add] at hs
  have hp := planeValueForcing_pair_of_value (H t) (A t (slice t))
    (planeHkValueOperator (E := E) 1 (slice t))
    (fun x => χ x ^ 2 * clipWeight B (W.W m t x)) (hA t ht (slice t))
  rw [ContinuousLinearMap.adjoint_inner_left] at hp
  rw [hp] at hs
  exact hs

end AVRegularity.Weighted
end
end
