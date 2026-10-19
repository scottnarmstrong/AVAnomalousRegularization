-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.JetUpTo
import AVRegularity.CycleComparison.Reconstruction.PulseTail
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofCovMeanJetSteps
public import AVRegularity.Construction.Preservation.Residual.FluxCancellation.Core
import AVRegularity.Construction.Preservation.Residual.FluxCancellation.ProofHilbertLiftArraysSetting
import AVRegularity.CycleComparison.Reconstruction.FrozenMeasure
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
public import AVRegularity.Construction.Preservation.FullLift.NativeLiftedFieldCovarianceEnergy
import AVRegularity.Construction.Preservation.FullLift.UniformNativeNormalizedJointBounds
import AVRegularity.CycleComparison.ActualMeans.KernelRegular
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Construction.Preservation.FullLift.NativePulseTimeDissipation
import AVenhance.Infra.Construction.StreamAdmissible

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy AVRegularity.CycleComparison.Coarse
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.Construction.Residual.Presentation

/-! Measurable physical coefficient operators on the time window. The ordinary graph norm
bound follows from the proved factorial row bound and is used only for integrability.
Coefficient values are jointly measurable; no time continuity premise is introduced.
Outside the window the operator is zero, so an empty window causes no extension problem. -/

private theorem covTruncCoefficient_factorial_upper {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K : ℕ} (ρ : ℝ) (U : TorusHk K E) :
    Real.sqrt (factorialNormSq ρ U.val) ≤ Real.sqrt (factorialWeightMax ρ K) * ‖U‖ := by
  have hmax : 0 ≤ factorialWeightMax ρ K :=
    (factorialWeight_nonneg ρ 0).trans (factorialWeight_le_max ρ (0 : Fin (K + 1)))
  have hbound := Real.sqrt_le_sqrt (factorialNormSq_upper ρ U.val)
  have hnorm : ‖U.val‖ = ‖U‖ := rfl
  simpa only [Real.sqrt_mul hmax, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _), hnorm] using hbound

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {K R : ℕ} {a b ρ Cb : ℝ} {π : ι → ℝ}
  {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}

namespace CovTruncCoefficientData
variable (P : CovTruncCoefficientData K R a b ρ Cb π input target)

/-- Extend the genuine window operator by zero. -/
def op (hρ : 0 < ρ) (t : ℝ) :
    (∀ v, TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v))) →L[ℝ]
      (∀ v, TorusHk K (PiLp 2 (fun _ : Fin 2 => h v))) := by
  classical
  exact if ht : t ∈ Set.Icc a b then P.opOnWindow hρ t ht else 0

/-- One output component has the ordinary graph-norm bound supplied by its factorial row. -/
theorem opOnWindow_component_norm (hρ : 0 < ρ) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (U : ∀ v, TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v))) (v : ι) :
    ‖P.opOnWindow hρ t ht U v‖ ≤
      ((Real.sqrt (factorialWeightMax ρ (K + R)) / Real.sqrt (factorialWeightMin ρ K)) *
        ∑ u, P.price v u) * ‖U‖ := by
  have hi (u : ι) : Real.sqrt (factorialNormSq ρ (U u).val) ≤
      Real.sqrt (factorialWeightMax ρ (K + R)) * ‖U‖ :=
    (covTruncCoefficient_factorial_upper ρ (U u)).trans
      (mul_le_mul_of_nonneg_left (norm_le_pi_norm U u) (Real.sqrt_nonneg _))
  have hs : Real.sqrt (factorialNormSq ρ (P.opOnWindow hρ t ht U v).val) ≤
      (∑ u, P.price v u) * (Real.sqrt (factorialWeightMax ρ (K + R)) * ‖U‖) := by
    refine (P.opOnWindow_factorial_le hρ t ht U v).trans ?_
    rw [Finset.sum_mul]
    exact Finset.sum_le_sum fun u _ => mul_le_mul_of_nonneg_left (hi u) (P.price_nonneg v u)
  have hn := (jetNorm_le_factorialRoot ρ hρ (P.opOnWindow hρ t ht U v).val).trans
    (div_le_div_of_nonneg_right hs (Real.sqrt_nonneg _))
  change ‖P.opOnWindow hρ t ht U v‖ ≤ _ at hn
  exact hn.trans_eq (by ring)

/-- The ordinary operator norm is uniformly finite on the window. Its constant may depend
on the finite component set, unlike the mass-weighted price. -/
theorem op_norm_bound (hρ : 0 < ρ) : ∃ Cn : ℝ, ∀ t ∈ Set.Icc a b, ‖P.op hρ t‖ ≤ Cn := by
  classical
  let S := ∑ v, ∑ u, P.price v u
  let D := Real.sqrt (factorialWeightMax ρ (K + R)) / Real.sqrt (factorialWeightMin ρ K)
  have hS : 0 ≤ S := Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun u _ => P.price_nonneg v u
  have hD : 0 ≤ D := div_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine ⟨D * S, fun t ht => ?_⟩
  rw [op, dite_eq_left ht]
  apply (P.opOnWindow hρ t ht).opNorm_le_bound (mul_nonneg hD hS)
  intro U
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg (mul_nonneg hD hS) (norm_nonneg U))).mpr
  intro v
  refine (P.opOnWindow_component_norm hρ t ht U v).trans ?_
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (fun w _ => Finset.sum_nonneg fun u _ => P.price_nonneg w u) (Finset.mem_univ v)) hD)
    (norm_nonneg U)

/-- A single block has measurable action on every measurable input trajectory. -/
theorem term_aestronglyMeasurable (hρ : 0 < ρ) (v u : ι) (r : Fin (R + 1))
    (U : ℝ → TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h u)))
    (hU : AEStronglyMeasurable U (volume.restrict (Set.Icc a b))) :
    AEStronglyMeasurable (fun t => if ht : t ∈ Set.Icc a b then
      P.termCLM hρ v u r t ht (U t) else 0) (volume.restrict (Set.Icc a b)) := by
  classical
  let W := hU.mk U
  have hW : StronglyMeasurable W := hU.stronglyMeasurable_mk
  let T : Set.Icc a b → TorusHk K
      (PiLp 2 (fun _ : DerivativeWord2 r.val => PiLp 2 (fun _ : Fin 2 => h u))) :=
    fun t => torusKernelDerivativeTensorCLM (E := PiLp 2 (fun _ : Fin 2 => h u)) K r.val
      (truncateTorusHk (E := PiLp 2 (fun _ : Fin 2 => h u)) (Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) K) (W t))
  have hT : StronglyMeasurable T :=
    (torusKernelDerivativeTensorCLM (E := PiLp 2 (fun _ : Fin 2 => h u)) K r.val).continuous.comp_stronglyMeasurable
      ((truncateTorusHk (E := PiLp 2 (fun _ : Fin 2 => h u)) (Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) K)).continuous.comp_stronglyMeasurable
        (hW.comp_measurable measurable_subtype_coe))
  have hb : StronglyMeasurable (fun t : Set.Icc a b =>
      P.termCLM hρ v u r t t.2 (W t)) := by
    have hmul := torusMultiplier_time_stronglyMeasurable ρ hρ
      (fun t : Set.Icc a b => P.coeff v u r t) (P.measurable v u r)
      (fun t => P.smooth v u r t t.2) (fun t => P.periodic v u r t t.2)
      (P.jetBound v u r) (fun t => P.jetBound_bounds hρ v u r t t.2) T hT
    have he : (fun t : Set.Icc a b => P.termCLM hρ v u r t t.2 (W t)) =
        fun t => (T t).mulCoefficient (P.coeff v u r t) (P.smooth v u r t t.2)
          (P.periodic v u r t t.2) (P.jetBound_bounds hρ v u r t t.2) := by
      funext t
      rw [P.termCLM_apply]
      simp only [T, torusKernelDerivativeTensorCLM_apply]
    rw [he]
    exact hmul
  have hext : StronglyMeasurable (fun t => if ht : t ∈ Set.Icc a b then
      P.termCLM hρ v u r t ht (W t) else 0) := by
    apply stronglyMeasurable_of_restrict_of_restrict_compl (s := Set.Icc a b) measurableSet_Icc
    · have he : (Set.Icc a b).domRestrict (fun t => if ht : t ∈ Set.Icc a b then
          P.termCLM hρ v u r t ht (W t) else 0) =
          fun t : Set.Icc a b => P.termCLM hρ v u r t t.2 (W t) := by
        funext t
        change (if ht : (t : ℝ) ∈ Set.Icc a b then
          P.termCLM hρ v u r t ht (W t) else 0) = _
        rw [dite_eq_left t.2]
      rw [he]
      exact hb
    · have he : (Set.Icc a b)ᶜ.domRestrict (fun t => if ht : t ∈ Set.Icc a b then
          P.termCLM hρ v u r t ht (W t) else 0) = fun _ => 0 := by
        funext t
        simp only [Set.domRestrict, dite_eq_right t.2]
      rw [he]
      exact stronglyMeasurable_const
  refine hext.aestronglyMeasurable.congr ?_
  filter_upwards [hU.ae_eq_mk] with t htW
  by_cases ht : t ∈ Set.Icc a b
  · simp only [dite_eq_left ht, htW, W]
  · simp only [dite_eq_right ht]

/-- The finite matrix of blocks has measurable action, without a time-continuity premise. -/
theorem op_aestronglyMeasurable (hρ : 0 < ρ)
    (U : ∀ v, ℝ → TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h v)))
    (hU : ∀ v, AEStronglyMeasurable (U v) (volume.restrict (Set.Icc a b))) (v : ι) :
    AEStronglyMeasurable (fun t => P.op hρ t (fun u => U u t) v)
      (volume.restrict (Set.Icc a b)) := by
  classical
  have hm := Finset.aestronglyMeasurable_fun_sum Finset.univ fun u _ =>
    Finset.aestronglyMeasurable_fun_sum Finset.univ fun r _ =>
      P.term_aestronglyMeasurable hρ v u r (U u) (hU u)
  refine hm.congr (Filter.Eventually.of_forall fun t => ?_)
  by_cases ht : t ∈ Set.Icc a b
  · simp only [dite_eq_left ht, op, P.opOnWindow_apply]
  · simp only [dite_eq_right ht, op, Finset.sum_const_zero]
    rfl

/-- Physical coefficient data supplies the exact operator ingredient used by the cell-mean operator. -/
def toFluxOperator (hρ : 0 < ρ) (hπ : ∀ v, 0 < π v) :
    CovTruncFluxOperator (K + R) K (Set.Icc a b) ρ π Cb input target where
  op := P.op hρ
  norm_bound := P.op_norm_bound hρ
  measurable_apply := P.op_aestronglyMeasurable hρ
  weighted_bound := fun t ht U => by
    simp only [op, dite_eq_left ht]
    exact P.opOnWindow_mass_bound hρ hπ t ht U
  realizes := fun U hU v t ht => by
    simp only [op, dite_eq_left ht]
    exact P.opOnWindow_value_ae hρ t ht (fun u => U u t) (fun u => hU u t ht) v

end CovTruncCoefficientData

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift AVRegularity.CycleComparison.Reconstruction
namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

/-! # The physical lift of a pulse is `C^J` from the lift sequence alone

`pulsePhysicalLift_contDiff` needs a lift setting. For the qualitative regularity of the lifted
field of the terminal context only the box smoothness of the coefficients of the lift sequence is
needed (the pattern of `pulseMeanFluxEuler_contDiff`): the label lift is the finite sum of
`ε^n` times the sampled coefficients applied to word derivatives of the coarse field
(`contDiff_liftSum`), and the physical lift is its composition with the label map.

Degenerate cases: `J = 0` (continuity); `N = 0`; an empty index type (the field is `0`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]

omit [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] in
/-- **The physical lift of a pulse is `C^J`** if the coefficients are box smooth of order `(J, J)`
at the pulse clock, the chart and the coarse field are `C^{N+J}` and the label map is `C^J`. -/
theorem pulsePhysicalLift_contDiff' (c ρ e εc : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) {J : ℕ} (hc : c ≠ 0)
    (hbox : ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m) (v u : ι),
      IsBoxSmooth J J (fun X z => Cc hh n m α (c⁻¹ * t) X z v u))
    (hχ : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (chart t)) (hψ : ContDiff ℝ (J : ℕ∞) (label t))
    (ha : ContDiff ℝ ((N + J : ℕ) : ℕ∞) (a t)) :
    ContDiff ℝ (J : ℕ∞) (pulsePhysicalLift c ρ e εc N H Cc chart label a t) := by
  rw [pulsePhysicalLift_eq_comp]
  refine (contDiff_pi.2 fun v => ?_).comp hψ
  have hg := contDiff_chartFrame a chart hc ha hχ ρ
  have he : (fun y' : Vec 2 => labelLift Cc N H εc
      (fun s X => a (c * s) (chart (c * s) (ρ • X))) ρ e c t y' v) = fun y' : Vec 2 =>
      ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), εc ^ n •
        ∑ q : LiftActionIndex ι n, Cc hh n q.1.val q.2.1 (c⁻¹ * t) (ρ⁻¹ • y') (e⁻¹ • y') v
          q.2.2 (orderedDerivative q.2.1
            ((fun s X => a (c * s) (chart (c * s) (ρ • X))) (c⁻¹ * t)) (ρ⁻¹ • y') q.2.2) :=
    funext fun y' => labelLift_coeff_sum Cc N H εc
      (fun s X => a (c * s) (chart (c * s) (ρ • X))) ρ e c t y' v
  rw [he]
  exact contDiff_liftSum Cc N H εc ρ e (c⁻¹ * t) v
    (fun hh hhh n _ q => CoarseFluxDiff.contDiff_sample (hbox hh hhh n q.1.val q.2.1 v q.2.2)
      le_rfl le_rfl ρ e) hg

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
end

section
open Homogenization AVRegularity.Sobolev AVRegularity
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **The glued mean flux is `C^s` in space, without a `SplitInput`**.

A version of `menuGluedMeanFlux_contDiff` that takes the
four stage facts it uses (`1 ≤ Λ`, fast profile, band chain, `1 ≤ Dm`) and the lift sequence
(`hin.lift`) as hypotheses instead of the record `SplitInput`, which a terminal context does not
have. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **The glued mean flux is `C^s` in space** (the stage facts as hypotheses). -/
theorem covTruncReg_gluedMeanFlux_contDiff (Mn : SuccMenu)
    (G : GenStage D hr Dm b j₀) (depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hord : 1 ≤ Dm)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D G.level k (nativeChain G.level k)
          (Mn.lenFactor * liftLength D G.level)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        Mn.sX Mn.sZ (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Mn.N depth
        (CcT k))
    (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ)
    (rs ns : Finset ℕ) (hrs : ∀ r ∈ rs, r ≤ depth)
    (hE : (∃ r ∈ rs, r ≠ 0) → ActualFluxJointSmooth G)
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (ha : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (a t)) (v : CompIn G.comps) :
    ContDiff ℝ (s : ℕ∞) (fun x => menuGluedMeanFlux Mn G G.level rs ns CcT a t x v) := by
  have hcc := EntryWeakProofs.weakData_cellScaleSq_pos D hbase hprof hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hbase
  unfold menuGluedMeanFlux
  refine ContDiff.sum fun k _ => ContDiff.sum fun r hr => ContDiff.sum fun n _ => ?_
  by_cases hodd : Odd k
  · simp only [hodd, dite_true]
    by_cases hcut : ocCutoff D.α D.q D.Λ G.level k t = 0
    · simp only [hcut, zero_smul]
      exact contDiff_const
    · refine ContDiff.const_smul _ ?_
      have ht' := clock_mem_window D G.level k t hτ hcc hcut
      have hwin := AVRegularity.Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
      obtain ⟨_, _, hz3, _, _, hbox, _⟩ := hlift k hodd
      refine pulseMeanFluxEuler_contDiff _ _ _ n r _ _ _ _ _ t v s Mn.N depth hcc.ne'
        hord (hrs r hr) hz3 ?_ ?_ ?_ ?_ ha ?_ ?_
      · exact fun hh' hH n' m α v u => (hbox hh' hH n' m α v u _ ht').1.mono hsX hsZ
      · intro k' j
        exact (EntryWeakProofs.familyLiftData_metric_entry_smooth D G.level k _
          (by simp [nativeChain]) _ _ _ k' j).of_le (by exact_mod_cast le_top)
      · intro k'
        exact (ocPulseCellDrift_contDiff D.α D.q D.Λ D.ζ G.level (D.kap G.level) hodd _ k').of_le
          (by exact_mod_cast le_top)
      · intro hr0
        exact fiber_edge_boxSmooth G (hE ⟨r, hr, hr0⟩) k hodd _ _ t hcc.ne' hwin s
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
          (D.slotAnchor G.level k)).of_le (by exact_mod_cast le_top)
      · exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
          (D.slotAnchor G.level k) t).of_le (by exact_mod_cast le_top)
  · simp only [hodd, dite_false]
    exact contDiff_const

end AVRegularity.Construction.Residual.Presentation
end

section
open Homogenization AVRegularity.Sobolev AVRegularity AVenhance
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
namespace AVRegularity.Construction.Residual.Presentation

/-! **`G` is `C^s` in space at a general order `s`, without a `SplitInput`**.

`temporal_comm_contDiff` has the order `2p` hard-coded; `covTruncReg_comm_contDiff` redoes it
at an order `s` (the stream velocity is smooth, the field is `C^{s+2p}`). The three terms of
`menuGFlux = (comm - diag) - mean` are then `C^s` for a field `C^{s+Dm+N+2p}`. -/

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The commutator part of `G` is `C^s` for a `C^{s+2p}` field. -/
theorem covTruncReg_comm_contDiff (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p s K : ℕ) (hK : s + 2 * p ≤ K) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) :
    ContDiff ℝ (s : ℕ∞) (fun x => ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
      ∑ a' ∈ Finset.range l, (covOperator Hc)^[a'] (commFluxE bv Hc
        ((covOperator Hc)^[l - 1 - a'] f)) x) := by
  refine ContDiff.sum fun l hl => ContDiff.const_smul _ (ContDiff.sum fun a' ha' => ?_)
  have hl' := Finset.mem_Icc.mp hl
  have ha'' := Finset.mem_range.mp ha'
  have h1 : ContDiff ℝ ((s + 2 * a' + 1 : ℕ) : ℕ∞) ((covOperator Hc)^[l - 1 - a'] f) :=
    AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc (l - 1 - a')
      (s + 2 * a' + 1) f (hf.of_le (by exact_mod_cast (by omega :
        s + 2 * a' + 1 + 2 * (l - 1 - a') ≤ K)))
  have h2 := commFluxE_contDiff bv hbv Hc (s + 2 * a') h1
  exact AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc a' s
    _ h2

end Operators

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

omit [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] in
/-- **`menuGFlux` is `C^s` in space** for a field `C^{s+Dm+N+2p}`, with the stage facts as
hypotheses. -/
theorem covTruncReg_menuGFlux_contDiff (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (m N p depth : ℕ) (hm : G.level = m) (hN : N = Mn.N) (hp : p = Mn.p)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (hbase : 1 ≤ D.Λ) (hprof : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hord : 1 ≤ Dm)
    (hlift : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D m k (nativeChain m k)
          (Mn.lenFactor * liftLength D m)
          (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
        Mn.sX Mn.sZ (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) Mn.N depth
        (CcT k))
    (hdepth : 1 ≤ depth → ActualFluxJointSmooth G)
    (s : ℕ) (hsX : s + Dm ≤ Mn.sX) (hsZ : s + Dm ≤ Mn.sZ) (K : ℕ)
    (hK : s + Dm + N + 2 * p ≤ K)
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ)
    (hg : ∀ v, ContDiff ℝ (K : ℕ∞) (fun x => aZ t x v)) (v : CompIn G.comps) :
    ContDiff ℝ (s : ℕ∞) (fun y => menuGFlux Mn G m N p depth CcT aZ v t y) := by
  subst hm hN hp
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (G.level - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have ha : ContDiff ℝ ((s + Dm + Mn.N : ℕ) : ℕ∞) (menuCovPRep Mn D G.level Mn.p aZ t) := by
    refine contDiff_pi.mpr fun w => ?_
    exact covPolyP_contDiff _ Mn.p _ ((hg w).of_le (by exact_mod_cast (by omega :
      s + Dm + Mn.N + 2 * Mn.p ≤ K)))
  have hga : ContDiff ℝ ((s + 1 : ℕ) : ℕ∞) (fun y => menuCovPRep Mn D G.level Mn.p aZ t y v) :=
    covPolyP_contDiff _ Mn.p _ ((hg v).of_le (by exact_mod_cast (by omega :
      s + 1 + 2 * Mn.p ≤ K)))
  unfold menuGFlux menuTemporalFlux menuDiagFluxPhys menuMeanFluxE
  refine ContDiff.sub (ContDiff.sub ?_ (ContDiff.sub ?_ ?_)) ?_
  · exact covTruncReg_comm_contDiff _ hbv _ Mn.p s K (by omega) (hg v)
  · exact covTruncReg_gluedMeanFlux_contDiff Mn G depth CcT hbase hprof hband hord hlift s hsX hsZ
      {0} (Finset.Icc 2 (Mn.N + 1)) (fun r hr => by simp at hr; omega)
      (fun ⟨r, hr, hr0⟩ => absurd (Finset.mem_singleton.mp hr) hr0)
      (menuCovPRep Mn D G.level Mn.p aZ) t ha v
  · refine contDiff_pi.mpr fun j => ContDiff.sum fun l _ => ContDiff.smul contDiff_const ?_
    exact gradE_contDiff s hga l
  · exact covTruncReg_gluedMeanFlux_contDiff Mn G depth CcT hbase hprof hband hord hlift s hsX hsZ
      (Finset.Icc 1 depth) (Finset.Icc 2 (Mn.N + Dm)) (fun r hr => (Finset.mem_Icc.mp hr).2)
      (fun ⟨r, hr, hr0⟩ => hdepth (by have := Finset.mem_Icc.mp hr; omega))
      (menuCovPRep Mn D G.level Mn.p aZ) t ha v

end AVRegularity.Construction.Residual.Presentation
end
end
end

section
@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev AVRegularity AVenhance
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
namespace AVRegularity.Construction.Residual.Presentation

/-! **Periodicity of `G`**.

The commutator part, the gradient part of the diagonal term and `P_p` of a periodic `C^K` field
are `ℤ²`-periodic. The glued mean-flux terms are periodic only if the lift is periodic in the slow
variable (`CovTruncGluedPeriodic`: the one hypothesis not supplied by the terminal context);
`covTruncReg_menuGFlux_periodic` reduces the periodicity of `G` to it. -/

section Operators

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The covariance operator of a periodic `C^2` field is periodic. -/
theorem covTruncReg_covOperator_periodic (Hc : Matrix (Fin 2) (Fin 2) ℝ) {f : Vec 2 → E}
    (hf : ContDiff ℝ 2 f) (hp : IsZ2Periodic f) : IsZ2Periodic (covOperator Hc f) := by
  have hd1 : IsZ2Periodic (fderiv ℝ f) := fderiv_isZ2Periodic (hf.differentiable (by norm_num)) hp
  have hj : ∀ j, IsZ2Periodic (fun y => fderiv ℝ f y (basisVec j)) := fun j n x =>
    congrArg (fun A => A (basisVec j)) (hd1 n x)
  have hdj : ∀ j, Differentiable ℝ (fun y => fderiv ℝ f y (basisVec j)) := fun j =>
    ((hf.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const).differentiable
      one_ne_zero
  intro n x
  simp only [covOperator]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [fderiv_isZ2Periodic (hdj j) (hj j) n x]

/-- Iterates of the covariance operator on a periodic `C^K` field are periodic (`2l + 2 ≤ K`). -/
theorem covTruncReg_iter_periodic (Hc : Matrix (Fin 2) (Fin 2) ℝ) (K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : IsZ2Periodic f) (l : ℕ) :
    2 * l + 2 ≤ K → IsZ2Periodic ((covOperator Hc)^[l] f) := by
  induction l with
  | zero => intro _; simpa using hp
  | succ l ih =>
    intro hl
    rw [Function.iterate_succ_apply']
    have hprev := ih (by omega)
    have h2 : ContDiff ℝ ((2 : ℕ) : ℕ∞) ((covOperator Hc)^[l] f) :=
      AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc l 2 f
        (hf.of_le (by exact_mod_cast (by omega : 2 + 2 * l ≤ K)))
    have h2' : ContDiff ℝ 2 ((covOperator Hc)^[l] f) := by exact_mod_cast h2
    exact covTruncReg_covOperator_periodic (f := (covOperator Hc)^[l] f) Hc h2' hprev

/-- `P_p` of a periodic `C^K` field is periodic (`2p + 2 ≤ K`). -/
theorem covTruncReg_covPolyP_periodic (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (K : ℕ∞) f) (hp : IsZ2Periodic f) (hK : 2 * p + 2 ≤ K) :
    IsZ2Periodic (covPolyP Hc p f) := by
  intro n x
  simp only [covPolyP, Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  have hl' : l ≤ p := Nat.lt_succ_iff.mp (Finset.mem_range.mp hl)
  rw [covTruncReg_iter_periodic Hc K hf hp l (by omega) n x]

/-- The gradient of a periodic differentiable field is periodic. -/
theorem covTruncReg_gradE_periodic {g : Vec 2 → E} (hg : Differentiable ℝ g)
    (hp : IsZ2Periodic g) (l : Fin 2) : IsZ2Periodic (fun x => gradE g x l) := by
  intro n x
  have := fderiv_isZ2Periodic hg hp n x
  simp only [gradE]
  exact congrArg (fun A => A (basisVec l)) this

/-- `commFluxE` of a periodic `C^1` field along a periodic smooth velocity is periodic. -/
theorem covTruncReg_commFluxE_periodic (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (hpb : IsZ2Periodic bv) (Hc : Matrix (Fin 2) (Fin 2) ℝ) {g : Vec 2 → E}
    (hg : ContDiff ℝ 1 g) (hp : IsZ2Periodic g) : IsZ2Periodic (commFluxE bv Hc g) := by
  intro n x
  have hJ := fderiv_isZ2Periodic (hbv.differentiable (by simp)) hpb n x
  have hJm : jacMatrix bv (x + latticeShift n) = jacMatrix bv x := by
    simp only [jacMatrix, hJ]
  have hgr : ∀ l, gradE g (x + latticeShift n) l = gradE g x l := fun l =>
    covTruncReg_gradE_periodic (hg.differentiable one_ne_zero) hp l n x
  have hJm' : jacMatrix bv (x + fun i => (n i : ℝ)) = jacMatrix bv x := hJm
  have hgr' : ∀ l, gradE g (x + fun i => (n i : ℝ)) l = gradE g x l := hgr
  funext j
  simp only [commFluxE, hJm, hgr]

/-- One term of the commutator part of `G` is periodic. -/
theorem covTruncReg_commTerm_periodic (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (hpb : IsZ2Periodic bv) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K l a' : ℕ) (hK : 2 * p + 3 ≤ K)
    (hl : l ≤ p) (ha : a' < l) {f : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f)
    (hp : IsZ2Periodic f) :
    IsZ2Periodic ((covOperator Hc)^[a'] (commFluxE bv Hc ((covOperator Hc)^[l - 1 - a'] f))) := by
  have h1 : ContDiff ℝ ((2 * a' + 3 : ℕ) : ℕ∞) ((covOperator Hc)^[l - 1 - a'] f) :=
    AVRegularity.Construction.Preservation.FullLift.covOperator_iterate_contDiff Hc (l - 1 - a')
      (2 * a' + 3) f (hf.of_le (by exact_mod_cast (by omega :
        2 * a' + 3 + 2 * (l - 1 - a') ≤ K)))
  have hpg : IsZ2Periodic ((covOperator Hc)^[l - 1 - a'] f) :=
    covTruncReg_iter_periodic Hc K hf hp _ (by omega)
  have h2 := commFluxE_contDiff bv hbv Hc (2 * a' + 2) h1
  have h1' : ContDiff ℝ 1 ((covOperator Hc)^[l - 1 - a'] f) := by
    exact h1.of_le (by exact_mod_cast (by omega : 1 ≤ 2 * a' + 3))
  exact covTruncReg_iter_periodic Hc (2 * a' + 2) h2
    (covTruncReg_commFluxE_periodic bv hbv hpb Hc h1' hpg) a' (by omega)

/-- The commutator part of `G` is periodic for a periodic `C^K` field, `2p + 3 ≤ K`. -/
theorem covTruncReg_comm_periodic (bv : Vec 2 → Vec 2) (hbv : ContDiff ℝ (⊤ : ℕ∞) bv)
    (hpb : IsZ2Periodic bv) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p K : ℕ) (hK : 2 * p + 3 ≤ K)
    {f : Vec 2 → E} (hf : ContDiff ℝ (K : ℕ∞) f) (hp : IsZ2Periodic f) :
    IsZ2Periodic (∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) •
      ∑ a' ∈ Finset.range l, (covOperator Hc)^[a'] (commFluxE bv Hc
        ((covOperator Hc)^[l - 1 - a'] f))) := by
  intro n x
  simp only [Finset.sum_apply, Pi.smul_apply]
  refine Finset.sum_congr rfl fun l hl => ?_
  congr 1
  refine Finset.sum_congr rfl fun a' ha' => ?_
  exact covTruncReg_commTerm_periodic bv hbv hpb Hc p K l a' hK (Finset.mem_Icc.mp hl).2
    (Finset.mem_range.mp ha') hf hp n x

end Operators

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **Periodicity of the glued mean flux of a periodic field** (the lift must be periodic
in the slow variable; this is not supplied by `IsLiftSequence`, which gives periodicity in the fast
variable only). -/
def CovTruncGluedPeriodic (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) (t : ℝ)
    (v : CompIn G.comps) : Prop :=
  ∀ (rs ns : Finset ℕ) (a : ℝ → Vec 2 → ∀ w : CompIn G.comps, hr w.1.root),
    (∀ w, IsZ2Periodic (fun x => a t x w)) →
      IsZ2Periodic (fun x => menuGluedMeanFlux Mn G m rs ns CcT a t x v)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- **`menuGFlux` is periodic**, given the periodicity of the glued mean flux. -/
theorem covTruncReg_menuGFlux_periodic (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (m N p depth : ℕ) (hm : G.level = m) (hN : N = Mn.N) (hp : p = Mn.p)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (v : CompIn G.comps)
    (hglue : CovTruncGluedPeriodic Mn G m CcT t v) (K : ℕ) (hK : 2 * p + 3 ≤ K)
    (hg : ∀ w, ContDiff ℝ (K : ℕ∞) (fun x => aZ t x w))
    (hper : ∀ w, IsZ2Periodic (fun x => aZ t x w)) :
    IsZ2Periodic (fun y => menuGFlux Mn G m N p depth CcT aZ v t y) := by
  subst hm hN hp
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (G.level - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hpb : IsZ2Periodic (streamVel (D.Φ (G.level - 1)) t) :=
    fun k x => by simpa using (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (D.hΦ (G.level - 1))).periodic 0 k t x
  have hcomm := covTruncReg_comm_periodic _ hbv hpb (menuCovPrimitive D Mn G.level t) Mn.p K hK
    (hg v) (hper v)
  have hP : ∀ w, IsZ2Periodic (fun x => menuCovPRep Mn D G.level Mn.p aZ t x w) := fun w =>
    covTruncReg_covPolyP_periodic _ Mn.p K (hg w) (hper w) (by omega)
  have hga : ∀ l, IsZ2Periodic (fun x => gradE (fun y => menuCovPRep Mn D G.level Mn.p aZ t y v) x l) := by
    intro l
    refine covTruncReg_gradE_periodic ?_ (hP v) l
    exact (covPolyP_contDiff _ Mn.p 1 ((hg v).of_le (by exact_mod_cast
      (by omega : 1 + 2 * Mn.p ≤ K)))).differentiable one_ne_zero
  have g1 := hglue {0} (Finset.Icc 2 (Mn.N + 1))
    (fun s y w => covPolyP (menuCovPrimitive D Mn G.level s) Mn.p (fun y' => aZ s y' w) y) hP
  have g2 := hglue (Finset.Icc 1 depth) (Finset.Icc 2 (Mn.N + Dm)) (menuCovPRep Mn D G.level Mn.p aZ) hP
  intro n x
  have hc := hcomm n x
  simp only [Finset.sum_apply, Pi.smul_apply] at hc
  simp only [menuGFlux, menuTemporalFlux, menuDiagFluxPhys, menuMeanFluxE]
  have g1' := g1 n x
  have g2' := g2 n x
  beta_reduce at g1' g2'
  rw [hc, g1', g2']
  congr 3
  funext j
  refine Finset.sum_congr rfl fun l _ => ?_
  exact congrArg (fun z => _ • z) (hga l n x)

end AVRegularity.Construction.Residual.Presentation
end

section
open Homogenization AVRegularity.Sobolev AVenhance MeasureTheory
namespace AVRegularity.Construction.Preservation.FullLift

/-! # The cascade energy engine with the lifted-field hypothesis replaced by its clauses

Copies of `native_liftedFieldW_classical_reps`, `native_liftedField_value_eq_constructed` and
`native_liftedFieldW_strong_energy_le` where `hfield : IsLiftedFieldW ...` is replaced by the four
clauses the proofs use: the lift sequences `hseq`, the classical representative of `PZ` `hcl`, the
value clause `hval` and the compatibility `hcompat`. The cascade covariance primitive clause
(`IsCovImage`) is not used.

The original theorems follow by `hfield.1.1`, `hfield.1.2.1` with first projections. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D hr Dm bw j₀} {slot : OddSlot} {π : CompIn G.comps → ℝ} {H N K k L : ℕ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {S : ℝ}

/-- The lift-sequence clause of a lifted field. -/
def LiftSeqClause (G : GenStage D hr Dm bw j₀) (m N H sX sZ : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) : Prop :=
  ∀ (k : ℤ) (hk : Odd k),
    IsLiftSequence (familyLiftData D m k (nativeChain m k) (liftLength D m)
        (G.fam.fiber ⟨k, hk⟩ (G.actual ⟨k, hk⟩)))
      sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N H (CcT k)

/-- The value clause of a lifted field. -/
def LiftValueClause (G : GenStage D hr Dm bw j₀) (m N H : ℕ) (tp tf : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) {K : ℕ}
    (û : ∀ v : CompIn G.comps, ℝ → TorusHk K (hr v.1.root)) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc tp tf,
    (û v t).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => gluedLift (ocObsPulses D.α D.q D.Λ m t t) (fun k => ocCutoff D.α D.q D.Λ m k)
        (D.cellScaleSq m) (liftLength D m) (D.eps m)
        (ocDStar D.q D.Λ m (D.κ m) (D.κ (m - 1)) / liftLength D m) N H CcT
        (fun k s' y => D.flowOf (m - 1) s' y (D.slotAnchor m k))
        (fun k s' y => D.flowOf (m - 1) (D.slotAnchor m k) y s') aRep t x v

theorem value_eq_constructed
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (sX sZ : ℕ) (tp tf : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    {r : ℕ} (û : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (hseq : LiftSeqClause G G.level N H sX sZ CcT) (hval : LiftValueClause G G.level N H tp tf CcT aRep û) :
    ∀ v, ∀ t ∈ Set.Icc tp tf,
      (û v t).toFunction.jet (valueIndex2 r) =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => gluedLift (ocObsPulses D.α D.q D.Λ G.level t t)
          (fun j => ocCutoff D.α D.q D.Λ G.level j)
          (D.cellScaleSq G.level) (liftLength D G.level) (D.eps G.level)
          (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
          N H (nativeStageLiftFamily slotLifts)
          (fun j s' y => D.flowOf (G.level - 1) s' y (D.slotAnchor G.level j))
          (fun j s' y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s') aRep t x v := by
  classical
  intro v t ht
  have hc : 0 < D.cellScaleSq G.level :=
    EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  apply (hval v t ht).trans
  apply Filter.Eventually.of_forall
  intro x
  refine congrArg (fun f : ∀ w : CompIn G.comps, hr w.1.root => f v) ?_
  apply gluedLift_coeff_congr
  intro j hj hcut hh hhh n _hn m α X z v' u
  have hjodd : Odd j := (Finset.mem_filter.mp hj).2.1
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut
  have htcell : (D.cellScaleSq G.level)⁻¹ * t ∈
      Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
        ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le,
      div_le_div_of_nonneg_right htw.2 hc.le⟩
  exact nativeStageLiftFamily_coefficients_unique slotLifts sX sZ CcT hseq
    j hjodd hh hhh n m α _ htcell X z v' u

theorem classical_reps
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (P₀ : ℕ) (hreserve : ∀ slot : OddSlot, P₀ + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (r : ℕ) (hrP : r + 1 ≤ P₀) (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (tp tf : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hseq : LiftSeqClause G G.level N H sX sZ CcT)
    (hcl : ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (PZ v t) (fun x => a t x v) (Naux - 2 * p))
    (hval : LiftValueClause G G.level N H tp tf CcT a u)
    (hcompat : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf), truncateTorusHk (Nat.le_succ r) (w v t) = u v t)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((P₀ + N : ℕ) : ℕ∞) (a t)) :
    let F := fun t => gluedLift (ocObsPulses D.α D.q D.Λ G.level t t)
      (fun j => ocCutoff D.α D.q D.Λ G.level j) (D.cellScaleSq G.level) (liftLength D G.level)
      (D.eps G.level) (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
        liftLength D G.level) N H (nativeStageLiftFamily slotLifts)
      (fun j s y => D.flowOf (G.level - 1) s y (D.slotAnchor G.level j))
      (fun j s y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y s) a t
    (∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (u v t) (fun x => F t x v) r) ∧
    ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      IsClassicalRep (w v t) (fun x => F t x v) (r + 1) := by
  intro F
  classical
  have hc : 0 < D.cellScaleSq G.level := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband _
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have haper (t : ℝ) (ht : t ∈ Set.Icc tp tf) : IsZ2Periodic (a t) := by
    intro q x
    funext v
    exact (hcl v t ht).2.2.1 q x
  have hcell (t : ℝ) (j : ℤ) (hj : ocCutoff D.α D.q D.Λ G.level j t ≠ 0) :
      (D.cellScaleSq G.level)⁻¹ * t ∈
        Set.Icc (D.slotStart G.level j / D.cellScaleSq G.level)
          ((((j : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) := by
    have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hj
    rw [inv_mul_eq_div]
    exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩
  have hper (t : ℝ) (ht : t ∈ Set.Icc tp tf) : IsZ2Periodic (F t) :=
    nativeStageLiftFamily_glued_periodic slotLifts hi htorus _
      (fun j hj => (Finset.mem_filter.mp hj).2.1) _ _ _ _ hc.ne' a (haper t ht)
      (fun j _ hj => hcell t j hj)
  have hreg (t : ℝ) (ht : t ∈ Set.Icc tp tf) (v : CompIn G.comps) :
      ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (fun x => F t x v) := by
    apply nativeStageLiftFamily_glued_contDiff slotLifts P₀ hreserve (r + 1) hrP hrQ _
      (fun j hj => (Finset.mem_filter.mp hj).2.1) _ _ _ _ _ hc.ne' a (ha t ht) _ _ _ _
      (fun j _ hj => hcell t j hj) v
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
        (D.slotAnchor G.level j)).of_le (by simp)
    · intro j _ _
      exact (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
        (D.slotAnchor G.level j) t).of_le (by simp)
  have hval := value_eq_constructed slotLifts hΛ hζ hband sX sZ tp tf
    CcT a u hseq hval
  constructor
  · intro v t ht
    exact classicalRep_of_smooth_periodic_value_ae (u v t) (fun x => F t x v)
      ((hreg t ht v).of_le (by exact_mod_cast Nat.le_succ r))
      (fun q x => congrFun (hper t ht q x) v) (hval v t ht)
  · intro v
    filter_upwards [ae_restrict_mem measurableSet_Icc, hcompat v] with t ht hcompat
    exact classicalRep_of_compatible_smooth_value (u v t) (w v t) (fun x => F t x v)
      (hreg t ht v) (fun q x => congrFun (hper t ht q x) v) (hval v t ht) hcompat

theorem strong_energy_le
    (slotLifts : ∀ slot : OddSlot, NativeSlotLift G slot π H N K k L CG Cw Cj S)
    (hi : 1 ≤ G.level) (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (htorus : IsTorusCompatible G.fam G.actual (D.eps (G.level - 1)))
    (r : ℕ) (hreserve : ∀ slot : OddSlot, r + 1 + (N + (slotLifts slot).cap) ≤
      K + 4 * (H + 1) * (N + (slotLifts slot).cap) ^ 2)
    (hrQ : r + 1 ≤ max k (L + 2))
    (p Naux sX sZ : ℕ) (tp tf : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (PZ : ∀ v : CompIn G.comps, ℝ → TorusHk (Naux - 2 * p) (hr v.1.root))
    (a : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (u : ∀ v : CompIn G.comps, ℝ → TorusHk r (hr v.1.root))
    (w : ∀ v : CompIn G.comps, ℝ → TorusHk (r + 1) (hr v.1.root))
    (hseq : LiftSeqClause G G.level N H sX sZ CcT)
    (hcl : ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (PZ v t) (fun x => a t x v) (Naux - 2 * p))
    (hval : LiftValueClause G G.level N H tp tf CcT a u)
    (hcompat : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf), truncateTorusHk (Nat.le_succ r) (w v t) = u v t)
    (ha : ∀ t ∈ Set.Icc tp tf, ContDiff ℝ ((r + 1 + N : ℕ) : ℕ∞) (a t))
    (Sbar : ℝ) (hSbar : 0 ≤ Sbar) (hSSbar : S ≤ Sbar)
    {C rs : ℝ} (hC : 1 ≤ C) (hrs : 0 < rs) (hrse : rs ≤ D.eps G.level)
    (hρ : 0 < liftLength D G.level) (hν : 0 < D.κ G.level)
    (hB : 0 < D.κ (G.level - 1)) (hνB : D.κ G.level ≤ D.κ (G.level - 1))
    (hcell : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) /
      liftLength D G.level ≤ 1)
    (hflow : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t,
      ocCutoff D.α D.q D.Λ G.level j t ≠ 0 →
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
        (r + 1 + N) C (liftLength D G.level) ∧
      ChartTransport.JetBound (fun y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t)
        (r + 1 + N) C (liftLength D G.level))
    (Z : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N) (hr v.1.root))
    (Zw : ∀ v : CompIn G.comps, ℝ → TorusHk (r + N + 1) (hr v.1.root))
    (hZ : ∀ v, ∀ t ∈ Set.Icc tp tf, IsClassicalRep (Z v t) (fun x => a t x v) (r + N))
    (hZw : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc tp tf),
      IsClassicalRep (Zw v t) (fun x => a t x v) (r + N + 1))
    (hmeas : ∀ v, AEStronglyMeasurable (Zw v) (volume.restrict (Set.Icc tp tf))) :
    strongEnergy rs (D.κ G.level) π tp tf u w ≤
      (nativeLiftStrongEnergyPrice r (max k (L + 2)) Dm H N CG Cw Cj Sbar C) ^
        (1 / 2 : ℝ) * strongEnergy (liftLength D G.level) (D.κ (G.level - 1)) π tp tf Z Zw := by
  classical
  have hrep := classical_reps slotLifts hi hΛ hζ hband htorus
    (r + 1) hreserve r le_rfl hrQ p Naux sX sZ tp tf CcT PZ a u w hseq hcl hval hcompat ha
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hband G.level
  have hτ : 0 < ocTau D.α D.q D.Λ G.level := Construction.Stream.ocTau_pos hΛ
  have he : 0 < D.eps G.level := Construction.Stream.ocEpsilon_pos hΛ
  have hodd : ∀ t ∈ Set.Icc tp tf, ∀ j ∈ ocObsPulses D.α D.q D.Λ G.level t t, Odd j :=
    fun _ _ _ hj => (Finset.mem_filter.mp hj).2.1
  have hprice : ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) =
      D.eps G.level / Real.sqrt (D.κ G.level) * Real.sqrt (D.κ (G.level - 1)) := by
    rw [ocDStar, Real.sqrt_div hB.le]
    change D.eps G.level * (Real.sqrt (D.κ (G.level - 1)) / Real.sqrt (D.κ G.level)) = _
    ring
  have heρ : D.eps G.level ≤ liftLength D G.level := by
    apply cell_scale_le_lift_radius he.le hν hνB hρ
    exact hcell
  apply nativeStageLiftFamily_glued_sobolev_strong_energy_le slotLifts Sbar hSbar hSSbar r
    hreserve hrQ tp tf (fun t => ocObsPulses D.α D.q D.Λ G.level t t) hodd
    (fun j => ocCutoff D.α D.q D.Λ G.level j) (D.cellScaleSq G.level)
    (ocDStar D.q D.Λ G.level (D.κ G.level) (D.κ (G.level - 1)) / liftLength D G.level)
    hc.ne' (div_nonneg (by rw [hprice]; positivity) hρ.le) hcell a ha
    (fun j t y => D.flowOf (G.level - 1) t y (D.slotAnchor G.level j))
    (fun j t y => D.flowOf (G.level - 1) (D.slotAnchor G.level j) y t) hC
    (fun t _ j _ _ => (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1)) t
      (D.slotAnchor G.level j)).of_le (by simp))
    (fun t ht j hj hw => (hflow t ht j hj hw).1) hrs hrse heρ hν hB hνB
    (congrArg (fun x => x / liftLength D G.level) hprice)
    (fun t _ j _ _ => (CycleReference.streamFlow_spatial_smooth (D.hΦ (G.level - 1))
      (D.slotAnchor G.level j) t).of_le (by simp))
    (fun t ht j hj hw d hd hle => (hflow t ht j hj hw).2 d hd (hle.trans (by omega)))
    (fun _ _ _ _ => Real.smoothTransition.nonneg _)
    (fun t ht => Providers.CascadeInvariants.sum_ocCutoff_le_one hτ _ (hodd t ht) t)
    (fun t _ j _ _ y => (CycleReference.streamFlowHomeomorph (D.hΦ (G.level - 1)) t
      (D.slotAnchor G.level j)).right_inv y) ?_ Z Zw hZ hZw hmeas u w hrep.1 hrep.2
  intro t _ j _ hj
  have htw := Providers.GenSem.mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hj
  rw [inv_mul_eq_div]
  exact ⟨div_le_div_of_nonneg_right htw.1 hc.le, div_le_div_of_nonneg_right htw.2 hc.le⟩

end AVRegularity.Construction.Preservation.FullLift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route
open AVRegularity.Construction.Preservation.Residual.CovarianceTransport
open AVRegularity.Construction.Preservation.Residual.FluxCancellation.CovFluxReg
namespace AVRegularity.Construction.Residual.Presentation

/-! **The regularity of `G` at the terminal context** (`CovTruncGRegStatement`).

* `covTruncReg_actualFluxJointSmooth`: `ActualFluxJointSmooth Gw` from the stage invariant of the
  weak stage (`c.weak`), the births `[]` of its components and `reserve : G0 ≤ Hprod + 1`;
* `covTruncReg_smooth`: the smoothness of `G` (order `k_c + 4p_T`) and its periodicity modulo the
  glued mean flux, with the floors `s_X, s_Z ≥ k_c + 4p_T + D_t`, `K_out ≥ k_c + 6p_T + N_T + D_t + 2`;
* `covTruncGReg_of_bounded_gluedPeriodic`: `CovTruncGRegStatement` from the periodicity of the
  glued mean flux of a periodic field (`CovTruncGluedPeriodicBoundedStatement`). -/

section
section Terminal

variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}
  (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
    cker j₀ M)

/-- **`ActualFluxJointSmooth Gw`** from the weak stage invariant. -/
theorem covTruncReg_actualFluxJointSmooth (_x : TermResAux c) (hΛ : 1 ≤ A.Λ) (hV : A.Valid)
    (h1 : 1 ≤ M) (hj : j₀ ≤ M) : ActualFluxJointSmooth c.Gw := by
  obtain ⟨-, -, hlev, -, hbirths, -, -, -, -, hinv⟩ := c.weak
  obtain ⟨hnat, -, -, -, hslot, hcert, -⟩ := hinv
  obtain ⟨hDα, hDq, hDΛ, -, -, -, -⟩ := c.data
  have hε : 0 < c.D.eps (M - 1) := by
    unfold OCData.eps
    exact Construction.Stream.ocEpsilon_pos (hDΛ ▸ hΛ)
  have hb : 0 < A.bw := hV.2.2.1.1
  intro p v u γ d I t ht n
  refine AVRegularity.Construction.Preservation.FullLift.native_actual_flux_joint_contDiff hcert
    hslot hnat (by omega) (by omega) hb (by rw [hlev]; exact hε) p v u γ d I ?_ ?_ n t ht
  · have hbv : compGrade v.1 = 0 := by simp [compGrade, hbirths v]
    have := _x.reserve
    unfold compReserve
    rw [hbv]
    have h2 : (0 : ℝ) < (kW.Hprod : ℝ) + 1 := by positivity
    have h3 : ((kW.G0 + 0 : ℕ) : ℝ) ≤ (kW.Hprod : ℝ) + 1 := by exact_mod_cast this
    rw [sub_nonneg, div_le_one h2]
    exact h3
  · unfold compReserve
    have : (0 : ℝ) ≤ ((kW.G0 + compGrade v.1 : ℕ) : ℝ) / ((kW.Hprod : ℝ) + 1) := by positivity
    linarith

/-- The smoothness of `G` at the order `k_c + 4p_T`, and its periodicity once the glued mean flux
of periodic fields is periodic. -/
def CovTruncRegSmoothAt (x : TermResAux c) (kc : ℕ) (_C : ℝ) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    ContDiff ℝ ((kc + 4 * A.pT : ℕ) : ℕ∞)
        (fun y => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y) ∧
      (CovTruncGluedPeriodic (A.Mt M sXT sZT c.tp cr) c.Gw M c.CcT t v →
        IsZ2Periodic
          (fun y => menuGFlux (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW c.CcT x.aZ v t y))

/-- **The smoothness of `G` at a terminal context** (floors as in the module docstring). -/
theorem covTruncReg_smooth_of_floors (x : TermResAux c) (kc : ℕ) (C : ℝ) (hΛ : 128 ≤ A.Λ)
    (hV : A.Valid) (h1 : 1 ≤ M) (hj : j₀ ≤ M) (hX : kc + 4 * A.pT + A.Dt ≤ sXT)
    (hZ : kc + 4 * A.pT + A.Dt ≤ sZT) (hK : kc + 6 * A.pT + A.NT + A.Dt + 5 ≤ Kout) :
    CovTruncRegSmoothAt c x kc C := by
  have hΛ1 : 1 ≤ A.Λ := le_trans (by norm_num) hΛ
  have hE := covTruncReg_actualFluxJointSmooth c x hΛ1 hV h1 hj
  have hlev : c.Gw.level = M := c.weak.2.2.1
  obtain ⟨hDα, hDq, hDΛ, hDζ, -, hband, hterm⟩ := c.data
  have hbase : 1 ≤ c.D.Λ := hDΛ ▸ hΛ1
  have hprof : IsFastProfile c.D.ζ := hDζ ▸ X.hζ
  have hband' : IsOCBandChain c.D.α c.D.q c.D.Λ c.D.ζ c.D.term c.D.κ := by
    rw [hDα, hDq, hDΛ, hDζ, hterm]; exact hband
  have hord : 1 ≤ A.Dt := by
    have : 2 ≤ A.Dt := le_max_left _ _
    omega
  intro v t ht
  obtain ⟨hKc, hdiff, hper, -⟩ := x.repZ v t ht
  have hKK : kc + 6 * A.pT + A.NT + A.Dt + 3 ≤ A.Khat Kout - 2 := by
    have : Kout ≤ A.Khat Kout := le_max_left _ _
    omega
  have hg : ∀ w, ContDiff ℝ ((A.Khat Kout - 2 : ℕ) : ℕ∞) (fun y => x.aZ t y w) := fun w => by
    obtain ⟨-, hdw, -, -⟩ := x.repZ w t ht
    exact_mod_cast hdw
  have hpw : ∀ w, IsZ2Periodic (fun y => x.aZ t y w) := fun w => (x.repZ w t ht).2.2.1
  refine ⟨?_, fun hglue => ?_⟩
  · exact covTruncReg_menuGFlux_contDiff (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW hlev
      rfl rfl c.CcT hbase hprof hband' hord c.lift.1 (fun _ => hE) (kc + 4 * A.pT)
      (by exact (by omega : kc + 4 * A.pT + A.Dt ≤ sXT))
      (by exact (by omega : kc + 4 * A.pT + A.Dt ≤ sZT)) (A.Khat Kout - 2)
      (by show kc + 4 * A.pT + A.Dt + A.NT + 2 * A.pT ≤ _; omega) x.aZ t hg v
  · exact covTruncReg_menuGFlux_periodic (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW hlev
      rfl rfl c.CcT x.aZ t v hglue (A.Khat Kout - 2) (by show 2 * A.pT + 3 ≤ _; omega) hg hpw

end Terminal

/-- The smoothness statement, with the floors. -/
def CovTruncRegSmoothStatement : Prop :=
  TermResPrefix fun c x kc _ C _ _ => CovTruncRegSmoothAt c x kc C

/-- **The smoothness of `G`** (the floors are chosen here). -/
theorem covTruncReg_smooth : CovTruncRegSmoothStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ?_⟩⟩
  refine ⟨kc + 4 * A.pT + A.Dt, kc + 4 * A.pT + A.Dt, kc + 6 * A.pT + A.NT + A.Dt + 5,
    fun sXT sZT hsX hsZ Kout hK => ⟨0, ?_⟩⟩
  intro Kw Lt nW hk₀w hLw cr kS hKn hL0 hLp hLt hKO hcr0 hcr1 hcr hkS hc0 hKs hKan hLan hJm
    cK CK CL Cχ Cread Cid kW hcK hkW hAl cP CP cHP Cw Ce cker hcP Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, ?_⟩
  intro C hC j₀ hj₀
  refine ⟨max j₀ 1, fun M hM c x => ?_⟩
  exact covTruncReg_smooth_of_floors c x kc C hΛ hV (le_trans (le_max_right _ _) hM)
    (le_trans (le_max_left _ _) hM) hsX hsZ hK
end

/-! Regularity of the pre-truncation flux from glued periodicity on the grades actually consumed by menuGFlux.
The unrestricted helper asks about grades not constrained by IsLiftSequence; the present
helper bounds only the grade range. No regularity of the periodic input is needed in that
helper, since total spatial derivatives commute with translations. -/

section
section Generic

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- Periodicity of the glued mean flux at the bounded grades of a lift sequence. Degrees
remain unrestricted; IsLiftSequence makes coefficients above its degree cap vanish. -/
def CovTruncGluedPeriodicBounded (Mn : SuccMenu) (G : GenStage D hr Dm b j₀) (m depth : ℕ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root)) (t : ℝ)
    (v : CompIn G.comps) : Prop :=
  ∀ (rs ns : Finset ℕ) (a : ℝ → Vec 2 → ∀ w : CompIn G.comps, hr w.1.root),
    (∀ r ∈ rs, r ≤ depth) → (∀ w, IsZ2Periodic (fun x => a t x w)) →
      IsZ2Periodic (fun x => menuGluedMeanFlux Mn G m rs ns CcT a t x v)

omit [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)]
  [∀ r, CompleteSpace (hr r)] in
/-- The exact G flux consumes only bounded grades of the glued mean flux. -/
theorem covTruncGlued_menuGFlux_periodic (Mn : SuccMenu) (G : GenStage D hr Dm b j₀)
    (m N p depth : ℕ) (hm : G.level = m) (hN : N = Mn.N) (hp : p = Mn.p)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn G.comps) (fun v => hr v.1.root))
    (aZ : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root) (t : ℝ) (v : CompIn G.comps)
    (hglue : CovTruncGluedPeriodicBounded Mn G m depth CcT t v) (K : ℕ) (hK : 2 * p + 3 ≤ K)
    (hg : ∀ w, ContDiff ℝ (K : ℕ∞) (fun x => aZ t x w))
    (hper : ∀ w, IsZ2Periodic (fun x => aZ t x w)) :
    IsZ2Periodic (fun y => menuGFlux Mn G m N p depth CcT aZ v t y) := by
  subst hm hN hp
  have hbv : ContDiff ℝ (⊤ : ℕ∞) (streamVel (D.Φ (G.level - 1)) t) :=
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel (D.hΦ (G.level - 1))).smooth).comp
      (contDiff_const.prodMk contDiff_id)
  have hpb : IsZ2Periodic (streamVel (D.Φ (G.level - 1)) t) :=
    fun k x => by simpa using (AVenhance.Infra.Construction.smoothPeriodic_streamVel
      (D.hΦ (G.level - 1))).periodic 0 k t x
  have hcomm := covTruncReg_comm_periodic _ hbv hpb (menuCovPrimitive D Mn G.level t) Mn.p K hK
    (hg v) (hper v)
  have hP : ∀ w, IsZ2Periodic (fun x => menuCovPRep Mn D G.level Mn.p aZ t x w) := fun w =>
    covTruncReg_covPolyP_periodic _ Mn.p K (hg w) (hper w) (by omega)
  have hga : ∀ l, IsZ2Periodic (fun x => gradE (fun y => menuCovPRep Mn D G.level Mn.p aZ t y v) x l) := by
    intro l
    refine covTruncReg_gradE_periodic ?_ (hP v) l
    exact (covPolyP_contDiff _ Mn.p 1 ((hg v).of_le (by exact_mod_cast
      (by omega : 1 + 2 * Mn.p ≤ K)))).differentiable one_ne_zero
  have g1 := hglue {0} (Finset.Icc 2 (Mn.N + 1))
    (fun s y w => covPolyP (menuCovPrimitive D Mn G.level s) Mn.p (fun y' => aZ s y' w) y)
    (fun r hr => by simpa only [Finset.mem_singleton.mp hr] using Nat.zero_le depth) hP
  have g2 := hglue (Finset.Icc 1 depth) (Finset.Icc 2 (Mn.N + Dm))
    (menuCovPRep Mn D G.level Mn.p aZ) (fun r hr => (Finset.mem_Icc.mp hr).2) hP
  intro n x
  have hc := hcomm n x
  simp only [Finset.sum_apply, Pi.smul_apply] at hc
  simp only [menuGFlux, menuTemporalFlux, menuDiagFluxPhys, menuMeanFluxE]
  have g1' := g1 n x
  have g2' := g2 n x
  beta_reduce at g1' g2'
  rw [hc, g1', g2']
  congr 3
  funext j
  exact Finset.sum_congr rfl fun l _ => congrArg (fun z => _ • z) (hga l n x)

end Generic

section Terminal
variable {X : TermConstruction} {A : TermArgs X} {Kout sXT sZT Kw Lt : ℕ} {nW : ℕ+}
  {hk₀w : A.k₀ ≤ Kw} {cr : ℝ} {kS : InvConsts} {cK CK CL Cχ Cread Cid : ℝ} {kW : InvConsts}
  {cP CP cHP Cw Ce : ℝ} {cker : ℕ → ℝ} {j₀ M : ℕ}

/-- Periodicity on the grades read by G, at a terminal context. -/
def CovTruncGluedBoundedAt
    (c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) : Prop :=
  ∀ v, ∀ t ∈ Set.Icc c.tp (c.a + A.T₀),
    CovTruncGluedPeriodicBounded (A.Mt M sXT sZT c.tp cr) c.Gw M A.dW c.CcT t v

private def CovTruncGluedFieldOrderAt
    (_c : TermResCtx A Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce
      cker j₀ M) : Prop := 2 * A.pT + 3 ≤ A.Khat Kout - 2
end Terminal

/-- Bounded glued periodicity with the exact residual prefix. -/
def CovTruncGluedPeriodicBoundedStatement : Prop :=
  TermResPrefix fun c _ _ _ _ _ _ => CovTruncGluedBoundedAt c

private theorem covTruncGlued_field_orders :
    TermResPrefix fun c _ _ _ _ _ _ => CovTruncGluedFieldOrderAt c := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV => ⟨0, fun kc _ => ⟨0, 0, 2 * A.pT + 5,
    fun sXT sZT _ _ Kout hK => ⟨0, ?_⟩⟩⟩⟩
  intro Kw Lt nW hk₀w _ cr kS _ _ _ _ _ _ _ _ _ _ _ _ _ _ cK CK CL Cχ Cread Cid kW _ _ _
    cP CP cHP Cw Ce cker _ Cfl
  refine ⟨0, 1, 1, one_pos, 1, 1, le_rfl, one_pos, fun C _ j₀ _ => ⟨0, fun M _ c x => ?_⟩⟩
  have h : Kout ≤ A.Khat Kout := le_max_left _ _
  change 2 * A.pT + 3 ≤ A.Khat Kout - 2
  omega

/-- Exact regularity from bounded glued periodicity; the smoothness is discharged. -/
theorem covTruncGReg_of_bounded_gluedPeriodic (hper : CovTruncGluedPeriodicBoundedStatement) :
    CovTruncGRegStatement := by
  have hjoin := termFluxPrefix_and
    (P₁ := fun c x kc C => CovTruncRegSmoothAt c x kc C)
    (P₂ := fun c _ _ _ => CovTruncGluedBoundedAt c ∧ CovTruncGluedFieldOrderAt c) covTruncReg_smooth
    (termFluxPrefix_and (P₁ := fun c _ _ _ => CovTruncGluedBoundedAt c)
      (P₂ := fun c _ _ _ => CovTruncGluedFieldOrderAt c) hper covTruncGlued_field_orders)
  refine termFluxPrefix_map
    (P := fun c x kc C => CovTruncRegSmoothAt c x kc C ∧
      (CovTruncGluedBoundedAt c ∧ CovTruncGluedFieldOrderAt c))
    (R := fun c x kc C => CovTruncGRegAt c x kc C) ?_ hjoin
  intro X A kc C₁ hΛ128 hC₁
  refine ⟨0, ?_⟩
  intro Kout sXT sZT Kw Lt nW hk₀w cr kS cK CK CL Cχ Cread Cid kW cP CP cHP Cw Ce cker j₀ M c x hP C' _ v t ht
  have hg : ∀ w, ContDiff ℝ ((A.Khat Kout - 2 : ℕ) : ℕ∞) (fun y => x.aZ t y w) := fun w => by
    exact_mod_cast (x.repZ w t ht).2.1
  refine ⟨(hP.1 v t ht).1, ?_⟩
  exact covTruncGlued_menuGFlux_periodic (A.Mt M sXT sZT c.tp cr) c.Gw M A.NT A.pT A.dW
    c.weak.2.2.1 rfl rfl c.CcT x.aZ t v (hP.2.1 v t ht) (A.Khat Kout - 2) hP.2.2
    hg (fun w => (x.repZ w t ht).2.2.1)
end

end AVRegularity.Construction.Residual.Presentation
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.Construction.Preservation.Residual.FluxCancellation
open AVRegularity.CycleComparison.LiftMeanEntrywise
namespace AVRegularity.Construction.Residual.Presentation

/-! Periodicity of the cell-averaged Eulerian mean flux from slow-periodic coefficients.
The cell average has no physical fast argument, so this transfer needs no arithmetic condition
on the fast length. Total spatial derivatives commute with translations, without smoothness
assumptions on the input field. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ}

/-- The slow flux commutes with a slow translation when both its data and its bounded-grade
coefficient arrays, and the input field at the time in question, are invariant. -/
theorem covTruncPulse_liftFluxX_shift (Q : LiftOperatorData ι h Dm)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (H r n : ℕ) (hr : r ≤ H)
    (T : Vec 2) (τ : ℝ)
    (hG : ∀ X i j, Q.G τ (X + T) i j = Q.G τ X i j)
    (hc : ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z, γ.coeff α τ (X + T) z = γ.coeff α τ X z)
    (hCc : ∀ hh ≤ H, ∀ n m (α : DerivativeWord2 m) X z v u,
      Cc hh n m α τ (X + T) z v u = Cc hh n m α τ X z v u)
    (ha : ∀ X, a τ (X + T) = a τ X) (X z : Vec 2) (k : Fin 2) :
    liftFluxX Q Cc a r n τ (X + T) z k = liftFluxX Q Cc a r n τ X z k := by
  have he : EdgesShiftAt T τ Q.edge Q.edge := by
    intro v u d
    exact List.forall₂_same.mpr fun γ hγ => ⟨rfl, fun α X z => (hc v u d γ hγ α X z).symm⟩
  have hEq : liftFluxX Q (slowShiftSequence T Cc) a r n τ = liftFluxX Q Cc a r n τ := by
    apply Uniqueness.liftFluxX_congr
    intro hh hhR n m α
    funext X z v u
    exact hCc hh (hhR.trans hr) n m α X z v u
  have hs := liftFluxX_shiftRel Q Q Cc a a T τ rfl rfl
    (fun X i j => (hG X i j).symm) he (fun X => (ha X).symm) r n X z k
  rw [hEq] at hs
  exact hs.symm

/-- Periodicity of an Eulerian pulse mean flux, at any degree and a bounded grade. -/
theorem covTruncPulse_meanFluxEuler_periodic (c ρ εc : ℝ) (hρ : ρ ≠ 0) (hc : c ≠ 0)
    (Q : LiftOperatorData ι h Dm) (Cc : ℕ → ℕ → LiftCoeff ι h) (H r n : ℕ) (hr : r ≤ H)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (hchart : ∀ (p : Fin 2 → ℤ) Y, chart t (Y + latticeShift p) = chart t Y + latticeShift p)
    (hlabel : ∀ (p : Fin 2 → ℤ) Y, label t (Y + latticeShift p) = label t Y + latticeShift p)
    (hG : ∀ (p : Fin 2 → ℤ) X i j,
      Q.G (c⁻¹ * t) (X + ρ⁻¹ • latticeShift p) i j = Q.G (c⁻¹ * t) X i j)
    (hcoeff : ∀ (p : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α X z,
      γ.coeff α (c⁻¹ * t) (X + ρ⁻¹ • latticeShift p) z = γ.coeff α (c⁻¹ * t) X z)
    (hCc : ∀ (p : Fin 2 → ℤ) hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) X z v u,
      Cc hh n m α (c⁻¹ * t) (X + ρ⁻¹ • latticeShift p) z v u =
        Cc hh n m α (c⁻¹ * t) X z v u)
    (ha : ∀ v, IsZ2Periodic (fun x => a t x v)) (v : ι) :
    IsZ2Periodic (fun x => pulseMeanFluxEuler c ρ εc n r Q Cc chart label a t x v) := by
  intro p x
  funext j
  have hclock : c * (c⁻¹ * t) = t := by rw [← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  have hfield : ∀ Y, (fun s X => a (c * s) (chart (c * s) (ρ • X))) (c⁻¹ * t)
      (Y + ρ⁻¹ • latticeShift p) =
      (fun s X => a (c * s) (chart (c * s) (ρ • X))) (c⁻¹ * t) Y := by
    intro Y
    simp only [hclock, smul_add, smul_smul, mul_inv_cancel₀ hρ, one_smul, hchart]
    funext v
    exact ha v p _
  have hflux : ∀ Y z k,
      liftFluxX Q Cc (fun s X => a (c * s) (chart (c * s) (ρ • X))) r n (c⁻¹ * t)
        (Y + ρ⁻¹ • latticeShift p) z k =
      liftFluxX Q Cc (fun s X => a (c * s) (chart (c * s) (ρ • X))) r n (c⁻¹ * t) Y z k :=
    fun Y z k => covTruncPulse_liftFluxX_shift Q Cc _ H r n hr _ _ (hG p) (hcoeff p) (hCc p) hfield Y z k
  have hJ := CycleComparison.ActualMeans.jacMatrix_shift (latticeShift p) (hchart p) (label t x)
  simp only [pulseMeanFluxEuler, hlabel, hJ, smul_add]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (fun z => liftFluxX Q Cc (fun s X => a (c * s) (chart (c * s) (ρ • X))) r n
      (c⁻¹ * t) (ρ⁻¹ • label t x + ρ⁻¹ • latticeShift p) z k) =
      (fun z => liftFluxX Q Cc (fun s X => a (c * s) (chart (c * s) (ρ • X))) r n
      (c⁻¹ * t) (ρ⁻¹ • label t x) z k) from funext fun z => hflux _ z k]

end AVRegularity.Construction.Residual.Presentation
end
end
end
