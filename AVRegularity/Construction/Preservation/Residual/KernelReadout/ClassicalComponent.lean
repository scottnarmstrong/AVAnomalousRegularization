-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.Results.Iteration.PassageKernelSup
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
import AVRegularity.Analysis.Convolution.Kernel.PulseAxes
import AVRegularity.CycleComparison.QuietDecay.Engine.DiffConv
import AVRegularity.EntryTerminal.Ingredients.PrepCore.JetFacts
public import AVRegularity.Construction.Preservation.Residual.Assembly.RetainedReadoutOfIngredients
import AVRegularity.Construction.Preservation.Assembly.FullLiftFromInputs
import AVRegularity.Construction.Preservation.FullLift.NativePhysicalAllOrderSeminorm
import AVRegularity.Construction.Preservation.RetainedEnergy.UniformInputs
import AVRegularity.Construction.Preservation.Buffer.SmoothScalarCellStrongTime
public import AVRegularity.Proofs.Results.Iteration.PassageKernelSup.Periodic
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.CategoryTheory.Countable

section
section
/-! A classical periodic test has exactly the native value and gradient representatives needed
by the kernel solution's stored weak equation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Smooth periodic tests lie in the native first-order weak graph. -/
theorem kernel_readout_smooth_test (φ : Vec 2 → E) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hp : IsZ2Periodic φ) : ∃ ψ : TorusHk 1 E,
    ψ.toFunction.jet (valueIndex2 1) =ᵐ[volume.restrict unitCube] φ ∧
    ∀ j : Fin 2, ψ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => j⟩
      =ᵐ[volume.restrict unitCube] fun x => gradE φ x j := by
  let ψ := CycleWords.finiteSmoothPeriodicHk 1 φ (hφ.of_le (by exact_mod_cast le_top)) hp
  have he (a : JetIndex2 1) : ψ.toFunction.jet a =ᵐ[volume.restrict unitCube]
      orderedDerivative a.2 φ :=
    (KernelEnergy.torusHk_toFunction_jet_ae ψ a).trans
      (CycleWords.finiteSmoothPeriodicHk_jet_ae 1 φ _ hp a)
  refine ⟨ψ, ?_, ?_⟩
  · exact (he (valueIndex2 1)).trans (Filter.Eventually.of_forall fun x =>
      congrFun (orderedDerivative_zero φ _) x)
  · intro j
    have hw : orderedDerivative (fun _ : Fin 1 => j) φ = fun x => gradE φ x j := by
      rw [orderedDerivative_succ, orderedDerivative_zero]
      rfl
    exact (he ⟨⟨1, Nat.one_lt_two⟩, fun _ => j⟩).trans
      (Filter.Eventually.of_forall (congrFun hw))

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! A compact kernel average preserves the available regularity of a periodic field and
commutes with its ordered derivatives. The regularity proof reuses the finite-parameter
integral theorem; the derivative step reuses the field-side convolution calculus. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance
open AVRegularity.Providers AVRegularity.Providers.KernelSup
namespace AVRegularity.Construction.Preservation.Residual

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [MeasurableSpace V] [BorelSpace V] [SecondCountableTopology V] [ProperSpace V]
  {μ : Measure V} [IsFiniteMeasureOnCompacts μ]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology V] [ProperSpace V] in
/-- Averaging a periodic `C^n` field requires no invertibility of the averaging map. -/
theorem kernel_readout_op_contDiff {K : V → ℝ} (hK : IsKer K) (M : V →L[ℝ] Vec 2)
    {n : ℕ} {f : Vec 2 → E} (hf : ContDiff ℝ (n : ℕ∞) f) (hp : IsZ2Periodic f) :
    ContDiff ℝ (n : ℕ∞) (Op μ K M f) := by
  classical
  obtain ⟨BK, hBK⟩ := hK.smooth.continuous.bounded_above_of_compact_support hK.cpt
  have hb : ∀ j : Fin (n + 1), ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B := by
    intro j
    apply bdd_of_periodic (hf.continuous_iteratedFDeriv (by exact_mod_cast Nat.lt_succ_iff.mp j.2))
    intro z x
    have he : (fun y => f (y + latticeShift z)) = f := funext (hp z)
    exact (iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f) j (latticeShift z) x).symm.trans
      (congrArg (fun g => iteratedFDeriv ℝ j g x) he)
  choose B hB using hb
  have : IsFiniteMeasure (μ.restrict (tsupport K)) :=
    ⟨by simpa only [Measure.restrict_apply_univ] using hK.cpt.isCompact.measure_lt_top (μ := μ)⟩
  have heq : Op μ K M f = fun x => ∫ z in tsupport K, K z • f (x - M z) ∂μ := by
    funext x
    exact (setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => by
      rw [image_eq_zero_of_notMem_tsupport hz, zero_smul])).symm
  rw [heq]
  refine FullLift.finite_parameter_integral_contDiff (μ.restrict (tsupport K)) n E
    (fun z x => K z • f (x - M z)) ?_ ?_
    (fun j => BK * B ⟨min j n, Nat.lt_succ_of_le (min_le_right j n)⟩) ?_
  · intro x
    exact (hK.smooth.continuous.smul (hf.continuous.comp
      (continuous_const.sub M.continuous))).measurable
  · intro z
    exact (hf.comp (contDiff_id.sub contDiff_const)).const_smul (K z)
  · intro j hj z x
    have hshift : ContDiff ℝ (j : ℕ∞) (fun y => f (y - M z)) :=
      (hf.of_le (by exact_mod_cast hj)).comp (contDiff_id.sub contDiff_const)
    rw [iteratedFDeriv_const_smul_apply' hshift.contDiffAt,
      iteratedFDeriv_comp_sub, norm_smul]
    exact mul_le_mul (hBK z) (by simpa only [min_eq_left hj] using hB ⟨j, by omega⟩ (x - M z))
      (norm_nonneg _) ((norm_nonneg (K 0)).trans (hBK 0))

omit [BorelSpace V] [SecondCountableTopology V] [ProperSpace V]
  [IsFiniteMeasureOnCompacts μ] [CompleteSpace E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E] in
/-- Translation averages preserve spatial periodicity literally. -/
theorem kernel_readout_op_periodic (K : V → ℝ) (M : V →L[ℝ] Vec 2)
    {f : Vec 2 → E} (hp : IsZ2Periodic f) : IsZ2Periodic (Op μ K M f) := by
  intro z x
  unfold Op
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun y => by
    change K y • f (x + latticeShift z - M y) = K y • f (x - M y)
    rw [show x + latticeShift z - M y = (x - M y) + latticeShift z by abel, hp z]

omit [ProperSpace V] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
/-- Ordered spatial derivatives fall on the periodic input, through its available order. -/
theorem kernel_readout_op_word {K : V → ℝ} (hK : IsKer K) (M : V →L[ℝ] Vec 2)
    {n : ℕ} (w : Sobolev.DerivativeWord2 n) {f : Vec 2 → E}
    (hf : ContDiff ℝ (n : ℕ∞) f) (hp : IsZ2Periodic f) :
    orderedDerivative w (Op μ K M f) = Op μ K M (orderedDerivative w f) := by
  induction n with
  | zero => rw [orderedDerivative_zero, orderedDerivative_zero]
  | succ n ih =>
    let w0 : Sobolev.DerivativeWord2 n := fun i => w i.castSucc
    have hf0 : ContDiff ℝ (n : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ n)
    have hd : ContDiff ℝ (1 : ℕ∞) (orderedDerivative w0 f) :=
      ChartTransport.contDiff_orderedDerivative w0 (by simpa only [Nat.add_comm] using hf)
    have hp0 := ChartTransport.isZ2Periodic_orderedDerivative w0 hp
    obtain ⟨B, hB⟩ := bdd_of_periodic hd.continuous hp0
    obtain ⟨Bd, hBd⟩ := bdd_of_periodic (hd.continuous_fderiv (by norm_num))
      (periodic_fderiv hp0)
    rw [orderedDerivative_succ, ih w0 hf0, orderedDerivative_succ]
    funext x
    exact fderiv_op_field hK M hd hBd hB x (basisVec (w (Fin.last n)))

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! The torus carrier average and the literal average of a classical periodic representative
agree almost everywhere. This uses spatial translation and Fubini, not invertibility of the
kernel map. Every available ordered jet is then identified by the existing weak-graph average. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVenhance.Infra.Torus
open AVRegularity.Providers.KernelSup
namespace AVRegularity.Construction.Preservation.Residual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [BorelSpace E] in
/-- Carrier and literal averages agree even for a singular averaging map. -/
theorem kernel_readout_periodic_average_ae (M : Vec 2 →L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (F : Lp E 2 (volume.restrict unitCube))
    {f : Vec 2 → E} (hF : F =ᵐ[volume.restrict unitCube] f) (hp : IsZ2Periodic f) :
    periodicComponentAverage M.toLinearMap.toAddMonoidHom M.continuous κ hκ F
      =ᵐ[volume.restrict unitCube] Op volume κ M f := by
  let ρ := torusQuotient.comp M.toLinearMap.toAddMonoidHom
  have hρ : Continuous ρ := continuous_torusQuotient.comp M.continuous
  let fT : UnitAddTorus (Fin 2) → E := fun z => f (unitTorusRepresentative 2 z)
  have hFT : cellToTorus F =ᵐ[torusMeasure] fT := by
    filter_upwards [cellToTorus_ae F,
      measurePreserving_unitTorusRepresentative_cell.quasiMeasurePreserving.ae hF] with z hz hfz
    exact hz.trans hfz
  have hmap : Measure.QuasiMeasurePreserving
      (fun p : UnitAddTorus (Fin 2) × Vec 2 => p.1 - ρ p.2)
      (torusMeasure.prod volume) torusMeasure := by
    have hm : Measure.QuasiMeasurePreserving
        (fun p : Vec 2 × UnitAddTorus (Fin 2) => p.2 - ρ p.1)
        (volume.prod torusMeasure) torusMeasure := by
      apply QuasiMeasurePreserving.prod_of_right
      · exact (continuous_snd.sub (hρ.comp continuous_fst)).measurable
      · exact Filter.Eventually.of_forall fun z => by
          convert (measurePreserving_add_left torusMeasure (-ρ z)).quasiMeasurePreserving using 1
          funext y
          simp only [sub_eq_add_neg, add_comm]
    exact hm.comp Measure.measurePreserving_swap.quasiMeasurePreserving
  have hs := Measure.ae_ae_of_ae_prod (hmap.ae hFT)
  have ha := averagingOperator_ae ρ hρ hκ (cellToTorus F)
  have hc := measurePreserving_torusQuotient_cell.quasiMeasurePreserving
  filter_upwards [torusToCell_ae (averagingOperator ρ hρ κ hκ (cellToTorus F)), hc.ae ha,
    hc.ae hs] with x hx hax hsx
  change torusToCell (averagingOperator ρ hρ κ hκ (cellToTorus F)) x = _
  rw [hx, hax]
  change (∫ z, κ z • cellToTorus F (torusQuotient x - ρ z)) = ∫ z, κ z • f (x - M z)
  apply integral_congr_ae
  filter_upwards [hsx] with z hz
  rw [hz]
  change κ z • f (unitTorusRepresentative 2 (torusQuotient x - torusQuotient (M z))) = _
  rw [← map_sub, QuietDecay.periodic_eq_rep hp]

variable [FiniteDimensional ℝ E]

/-- The stored weak average carries the literal classical average through all input orders. -/
theorem kernel_readout_periodic_average_rep (M : Vec 2 →L[ℝ] Vec 2)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) (hK : IsKer κ) {k : ℕ} (U : TorusHk k E)
    (f : Vec 2 → E) (hf : IsClassicalRep U f k) :
    IsClassicalRep (periodicWeakAverage M.toLinearMap.toAddMonoidHom M.continuous κ hκ U)
      (Op volume κ M f) k := by
  refine ⟨le_rfl, kernel_readout_op_contDiff hK M hf.2.1 hf.2.2.1,
    kernel_readout_op_periodic κ M hf.2.2.1, ?_⟩
  intro n hn w
  let a : JetIndex2 k := ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩
  have hu : U.val a =ᵐ[volume.restrict unitCube] orderedDerivative w f := by
    have hj := KernelEnergy.torusHk_toFunction_jet_ae U a
    have hr := hf.2.2.2 n hn w
    change torusJetOrder U n w =ᵐ[volume.restrict unitCube] orderedDerivative w f at hr
    unfold torusJetOrder at hr
    simp only [hn, ↓reduceDIte] at hr
    exact hj.symm.trans hr
  have hjet := kernel_readout_periodic_average_ae M hκ (U.val a) hu
    (ChartTransport.isZ2Periodic_orderedDerivative w hf.2.2.1)
  have hW := KernelEnergy.torusHk_toFunction_jet_ae
    (periodicWeakAverage M.toLinearMap.toAddMonoidHom M.continuous κ hκ U) a
  unfold torusJetOrder
  simp only [hn, ↓reduceDIte]
  rw [kernel_readout_op_word hK M w (hf.2.1.of_le (by exact_mod_cast hn)) hf.2.2.1]
  exact hW.trans hjet

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! The actual paired kernel and its literal classical field have the same available jets.
The higher stored kernel lift is identified at each common order from its value alone. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
open AVRegularity.Analysis.Convolution AVRegularity.Providers.KernelSup
namespace AVRegularity.Construction.Preservation.Residual
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- The paired moment weak graph realizes the literal paired classical convolution. -/
theorem kernel_readout_kernel_classical_rep {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφc : HasCompactSupport φ₀)
    (S : KernelSpec) (t : ℝ) {k : ℕ} (U : TorusHk k E) (f : Vec 2 → E)
    (hf : IsClassicalRep U f k) :
    IsClassicalRep (pairedTorusMomentSmoothing S.width (S.H₁ t) (S.H₂ t) hφ₀ S.order U)
      (S.applyClassical φ₀ t f) k := by
  have hK : IsKer (momentKernel φ₀ S.order) :=
    ⟨contDiff_momentKernel hφc hφs S.order, hasCompactSupport_momentKernel hφc S.order⟩
  have hi := kernel_readout_periodic_average_rep (S.width • S.H₂ t)
    (integrable_momentKernel hφ₀ S.order) hK U f hf
  have ho := kernel_readout_periodic_average_rep (S.width • S.H₁ t)
    (integrable_momentKernel hφ₀ S.order) hK _ _ hi
  exact ho

/-- A stored kernel lift agrees with the literal classical convolution at each available order.
Its equality of values can be an almost-everywhere-in-time hypothesis of the solution class. -/
theorem kernel_readout_kernel_lift_jet {φ₀ : Vec 2 → ℝ} (hφ₀ : Integrable φ₀)
    (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφc : HasCompactSupport φ₀)
    (S : KernelSpec) (t : ℝ) {k L n : ℕ} (U : TorusHk k E) (V : TorusHk L E)
    (f : Vec 2 → E) (hf : IsClassicalRep U f k)
    (hv : V.val (valueIndex2 L) = S.op φ₀ hφ₀ t (U.val (valueIndex2 k)))
    (hnk : n ≤ k) (hnL : n ≤ L) (w : DerivativeWord2 n) :
    V.toFunction.jet ⟨⟨n, Nat.lt_succ_of_le hnL⟩, w⟩ =ᵐ[volume.restrict unitCube]
      fun x => orderedDerivative w (S.applyClassical φ₀ t f) x := by
  let W := pairedTorusMomentSmoothing S.width (S.H₁ t) (S.H₂ t) hφ₀ S.order U
  have hW := kernel_readout_kernel_classical_rep hφ₀ hφs hφc S t U f hf
  have he := EntryTerminal.Ingredients.torusHk_jet_eq_of_value (Y := V) (Z := W)
    hv hnL hnk (Nat.lt_succ_of_le hnL) (Nat.lt_succ_of_le hnk) w
  rw [he]
  have hj := hW.2.2.2 n hnk w
  unfold torusJetOrder at hj
  simpa only [hnk, ↓reduceDIte] using hj

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! Stored kernel jets and literal convolution jets agree on the time set supplied by the
kernel weak solution. Their finite coefficient sums therefore agree almost everywhere in space.
These statements do not assert stored-jet agreement at every time. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ k : ℕ}

/-- The literal finite kernel-jet flux appearing in the stored solution class. -/
def kernelReadoutStoredFlux (G : GenStage D hr Dm bw j₀)
    (Yk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (v : CompIn G.comps) (t : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
  ∑ u : CompIn G.comps, ∑ γ : G.fam.Γ v u, ∑ d : Finset.Icc 2 Dm,
    G.physCoeff v u γ d.1 t x (WithLp.toLp 2 fun w : DerivativeWord2 (d.1 - 1) =>
      (Yk v u γ t).toFunction.jet ⟨⟨d.1 - 1, by
        have hd := Finset.mem_Icc.mp d.2
        omega⟩, w⟩ x)

/-- Value matching in the solution class may use the continuous trajectory instead of its
almost-everywhere higher lift. -/
theorem kernel_readout_regularized_value_ae (G : GenStage D hr Dm bw j₀)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀)
    (ν a b : ℝ) (drift : ℝ → Vec 2 → Vec 2)
    (Y0 : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
    (Y : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (Yw : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
    (Yk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hsol : G.IsRegSolution P seedK freshK φ₀ hφ₀ ν drift k a b Y0
      (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      (Yk v u γ t).val (valueIndex2 (k + Dm - 1)) =
      (G.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t ((Y u t).val (valueIndex2 k)) := by
  filter_upwards [hsol.2.2.1 u, hsol.2.2.2.2.2.1 v u γ] with t ht hk
  have hv : (Yw u t).val (valueIndex2 (k + 1)) = (Y u t).val (valueIndex2 k) :=
    congrArg (fun Z => Z.val (valueIndex2 k)) ht
  have hi : (ContinuousLinearMap.id ℝ (hr u.1.root)).compLp
      ((Yw u t).val (valueIndex2 (k + 1))) = (Yw u t).val (valueIndex2 (k + 1)) := by
    apply Lp.ext
    exact (ContinuousLinearMap.id ℝ (hr u.1.root)).coeFn_compLp _
  change (Yk v u γ t).val (valueIndex2 (k + Dm - 1)) =
    (G.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t
      ((ContinuousLinearMap.id ℝ (hr u.1.root)).compLp ((Yw u t).val (valueIndex2 (k + 1)))) at hk
  exact hk.trans (congrArg ((G.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t) (hi.trans hv))

/-- At a time where kernel values match, every coefficient flux has the classical realization. -/
theorem kernel_readout_stored_flux_ae (G : GenStage D hr Dm bw j₀)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφc : HasCompactSupport φ₀)
    (aY : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Y : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
    (Yk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root))
    (hDm : Dm ≤ k) (t : ℝ) (hY : ∀ u, IsClassicalRep (Y u t) (fun x => aY t x u) k)
    (hv : ∀ v u (γ : G.fam.Γ v u), (Yk v u γ t).val (valueIndex2 (k + Dm - 1)) =
      (G.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ t ((Y u t).val (valueIndex2 k)))
    (v : CompIn G.comps) :
    kernelReadoutStoredFlux G Yk v t =ᵐ[volume.restrict unitCube]
      coeffFluxOn P seedK freshK φ₀ G .kernel aY v t := by
  have hj (u : CompIn G.comps) (γ : G.fam.Γ v u) (d : Finset.Icc 2 Dm)
      (w : DerivativeWord2 (d.1 - 1)) :
      (Yk v u γ t).toFunction.jet ⟨⟨d.1 - 1, by have := Finset.mem_Icc.mp d.2; omega⟩, w⟩
      =ᵐ[volume.restrict unitCube] fun x => orderedDerivative w
        ((G.kernelOf P seedK freshK v u γ).applyClassical φ₀ t (fun y => aY t y u)) x := by
    have hd := Finset.mem_Icc.mp d.2
    exact kernel_readout_kernel_lift_jet hφ₀ hφs hφc _ t (Y u t) (Yk v u γ t)
      (fun y => aY t y u) (hY u) (hv v u γ) (by omega) (by omega) w
  filter_upwards [ae_all_iff.mpr (fun u => ae_all_iff.mpr (fun γ =>
    ae_all_iff.mpr (fun d => ae_all_iff.mpr (hj u γ d))))] with x hx
  unfold kernelReadoutStoredFlux coeffFluxOn
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro γ _
  apply Finset.sum_congr rfl
  intro d _
  congr 1
  exact congrArg (WithLp.toLp 2) (funext (hx u γ d))

end AVRegularity.Construction.Preservation.Residual
end
end
end

section
section
/-! The replacement classical right-hand side is spatially integrable at every time.
This proof uses continuity on the compact closed cell, independently of the null set of times
on which the stored kernel lift is identified with its classical representative. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)] [∀ r, MeasurableSpace (hr r)]
  [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ k : ℕ}

/-- The finite classical kernel flux is continuous whenever the coefficient fields are. -/
theorem kernel_readout_flux_continuous (G : GenStage D hr Dm bw j₀)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφc : HasCompactSupport φ₀)
    (aY : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Y : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)) (hDm : Dm ≤ k)
    (t : ℝ) (hY : ∀ v, IsClassicalRep (Y v t) (fun x => aY t x v) k)
    (hA : ∀ v u (γ : G.fam.Γ v u) d, Continuous (G.physCoeff v u γ d t))
    (v : CompIn G.comps) : Continuous (coeffFluxOn P seedK freshK φ₀ G .kernel aY v t) := by
  unfold coeffFluxOn
  apply continuous_finsetSum
  intro u _
  apply continuous_finsetSum
  intro γ _
  apply continuous_finsetSum
  intro d _
  have hd : d.1 - 1 ≤ k := (Nat.sub_le _ _).trans ((Finset.mem_Icc.mp d.2).2.trans hDm)
  have hrep := kernel_readout_kernel_classical_rep hφ₀ hφs hφc
    (G.kernelOf P seedK freshK v u γ) t (Y u t) (fun x => aY t x u) (hY u)
  apply (hA v u γ d.1).clm_apply
  exact (PiLp.continuous_toLp 2 _).comp (continuous_pi fun word =>
    ChartTransport.continuous_orderedDerivative word (hrep.2.1.of_le (by exact_mod_cast hd)))

/-- A spatially continuous classical weak right-hand side is cell-integrable at each time. -/
theorem kernel_readout_rhs_integrable (G : GenStage D hr Dm bw j₀)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) {φ₀ : Vec 2 → ℝ}
    (hφ₀ : Integrable φ₀) (hφs : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hφc : HasCompactSupport φ₀)
    (aY : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root)
    (Y : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root)) (hDm : Dm ≤ k) (hk : 1 ≤ k)
    (ν : ℝ) (drift : ℝ → Vec 2 → Vec 2) (t : ℝ) (hV : Continuous (drift t))
    (hY : ∀ v, IsClassicalRep (Y v t) (fun x => aY t x v) k)
    (hA : ∀ v u (γ : G.fam.Γ v u) d, Continuous (G.physCoeff v u γ d t))
    (v : CompIn G.comps) (φ : Vec 2 → hr v.1.root) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) :
    Integrable (Weighted.weakIdentityRhs ν drift φ (fun j x => gradE φ x j)
      (fun s j x => gradE (fun y => aY s y v) x j) (fun _ _ => 0)
      (fun s x => coeffFluxOn P seedK freshK φ₀ G .kernel aY v s x) (fun _ _ => 0) t)
      (volume.restrict unitCube) := by
  have hy1 : ContDiff ℝ (1 : ℕ∞) (fun x => aY t x v) :=
    (hY v).2.1.of_le (by exact_mod_cast hk)
  have hgrad (j : Fin 2) : Continuous (fun x => gradE (fun y => aY t y v) x j) :=
    (hy1.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have htest (j : Fin 2) : Continuous (fun x => gradE φ x j) :=
    (hφ.continuous_fderiv (by simp)).clm_apply continuous_const
  have hflux := kernel_readout_flux_continuous G P seedK freshK hφ₀ hφs hφc aY Y hDm t hY hA v
  have hR : Continuous (Weighted.weakIdentityRhs ν drift φ (fun j x => gradE φ x j)
      (fun s j x => gradE (fun y => aY s y v) x j) (fun _ _ => 0)
      (fun s x => coeffFluxOn P seedK freshK φ₀ G .kernel aY v s x) (fun _ _ => 0) t) := by
    change Continuous (fun x => -(∑ j : Fin 2, drift t x j *
      inner ℝ (gradE (fun y => aY t y v) x j) (φ x)) -
      ν * ∑ j : Fin 2, inner ℝ (gradE (fun y => aY t y v) x j) (gradE φ x j) -
      ∑ j : Fin 2, inner ℝ ((0 : hr v.1.root) +
        coeffFluxOn P seedK freshK φ₀ G .kernel aY v t x j) (gradE φ x j) +
      inner ℝ (0 : hr v.1.root) (φ x))
    exact (((continuous_finsetSum _ fun j _ =>
      ((continuous_apply j).comp hV).mul ((hgrad j).inner hφ.continuous)).neg.sub
      (continuous_const.mul (continuous_finsetSum _ fun j _ => (hgrad j).inner (htest j)))).sub
      (continuous_finsetSum _ fun j _ =>
        (continuous_const.add ((PiLp.continuous_apply 2 _ j).comp hflux)).inner (htest j))).add
      (continuous_const.inner hφ.continuous)
  have : IsFiniteMeasure (volume.restrict unitCube) :=
    ⟨by rw [Measure.restrict_apply_univ]
        exact (measure_mono AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weakUnitCube_subset_closedCell).trans_lt
          AVenhance.Infra.Parabolic.WeakUniqueness.WeakAlgebra.weakSpatialClosedCell_compact.measure_lt_top⟩
  exact (CycleComparison.Lift.continuous_cell_memLp _ hR).integrable (by norm_num)

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! Subassembly of the raw retained kernel readout equation. The two analytic operations are
conversion of a stored kernel weak solution to its classical convolution flux and the finite
parent-word sum of classical weak equations. All stage certificates are discharged by their
producer; neither flux cancellation nor quiet transition enters this assembly. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Construction.Preservation.Residual
open AVRegularity.Construction.Preservation.Assembly FullLift

/-- Replace stored weak jets by the classical kernel
convolution, retaining spatial integrability at every time. The coefficient need only be
spatially continuous; the solution supplies time integrability of the stored equation.
At the initial endpoint the time interval is empty. No kernel invertibility or
positive width is needed: averaging a C^k periodic input preserves its available derivatives. -/
def ClassicalKernelComponentStatement : Prop :=
  ∀ {D : OCData} {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)]
    [∀ r, InnerProductSpace ℝ (hr r)] [∀ r, FiniteDimensional ℝ (hr r)]
    [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
    {Dm : ℕ} {bw : ℝ} {j₀ : ℕ} (G : GenStage D hr Dm bw j₀)
    (P : ProvParams) (seedK freshK : ℕ → KernelSpec) (φ₀ : Vec 2 → ℝ) (hφ₀ : Integrable φ₀),
    ContDiff ℝ (⊤ : ℕ∞) φ₀ → HasCompactSupport φ₀ →
    ∀ (k : ℕ) (ν a b : ℝ) (drift : ℝ → Vec 2 → Vec 2),
    Dm ≤ k → 1 ≤ k → a ≤ b → (∀ t ∈ Set.Icc a b, Continuous (drift t)) →
    (∀ v u (γ : G.fam.Γ v u) d, ∀ t ∈ Set.Icc a b, Continuous (G.physCoeff v u γ d t)) →
    ∀ (Y0 : ∀ v : CompIn G.comps, TorusHk k (hr v.1.root))
      (Y : ∀ v : CompIn G.comps, ℝ → TorusHk k (hr v.1.root))
      (Yw : ∀ v : CompIn G.comps, ℝ → TorusHk (k + 1) (hr v.1.root))
      (Yk : ∀ v u (_ : G.fam.Γ v u), ℝ → TorusHk (k + Dm - 1) (hr u.1.root)),
      G.IsRegSolution P seedK freshK φ₀ hφ₀ ν drift k a b Y0
        (fun _ _ => 0) (fun _ _ => 0) Y Yw Yk →
    ∀ aY : ℝ → Vec 2 → ∀ v : CompIn G.comps, hr v.1.root,
      (∀ v, ∀ t ∈ Set.Icc a b, IsClassicalRep (Y v t) (fun x => aY t x v) k) →
    ∀ v : CompIn G.comps, ∀ t ∈ Set.Icc a b, ∀ φ : Vec 2 → hr v.1.root,
      ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      CoupledWeakIdentity (volume.restrict unitCube) ν a t drift
        (fun x => aY t x v) (fun x => aY a x v) φ (fun j x => gradE φ x j)
        (fun s j x => gradE (fun y => aY s y v) x j) (fun _ _ => 0)
        (fun s x => coeffFluxOn P seedK freshK φ₀ G .kernel aY v s x) (fun _ _ => 0)

/-- Constant finite parent-word sums preserve the complete
weak identity, including the inner and outer integrability assertions.
Empty sums give zero, and one component gives scalar linearity; `E = 0`, `eta = 0` and
empty words use Lean's literal rpow conventions. The derivatives are of C^1 fields; the window may have length zero. -/
def FiniteParentReadoutWeakStatement : Prop :=
  ∀ {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {S S' : Finset Comp} (m : ℕ) (E η ν a b : ℝ) (drift : ℝ → Vec 2 → Vec 2), a ≤ b →
    ∀ (aY : ℝ → Vec 2 → ∀ c : CompIn S', hr c.1.root)
      (aZ : ℝ → Vec 2 → ∀ v : CompIn S, hr v.1.root)
      (Q : ∀ c : CompIn S', ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr c.1.root)),
      (∀ c, ∀ t ∈ Set.Icc a b, ContDiff ℝ (1 : ℕ∞) (fun x => aY t x c)) →
      (∀ v, ∀ t ∈ Set.Icc a b, (fun x => aZ t x v) = fun x =>
        ∑ c : CompIn S', if h : compParent m c.1 = v.1 then
          E ^ (η * (compWord m c.1).length) •
            cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h)))
              (aY t x c) else 0) →
      (∀ c : CompIn S', ∀ t ∈ Set.Icc a b, ∀ φ : Vec 2 → hr c.1.root,
        ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
        CoupledWeakIdentity (volume.restrict unitCube) ν a t drift
          (fun x => aY t x c) (fun x => aY a x c) φ (fun j x => gradE φ x j)
          (fun s j x => gradE (fun y => aY s y c) x j) (fun _ _ => 0) (Q c) (fun _ _ => 0)) →
      ∀ v : CompIn S, ∀ t ∈ Set.Icc a b, ∀ φ : Vec 2 → hr v.1.root,
        ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
        CoupledWeakIdentity (volume.restrict unitCube) ν a t drift
          (fun x => aZ t x v) (fun x => aZ a x v) φ (fun j x => gradE φ x j)
          (fun s j x => gradE (fun y => aZ s y v) x j) (fun _ _ => 0)
          (readoutFlux m E η (fun _ => True) Q v) (fun _ _ => 0)

/-- Exact uniform retained readout kernel equation from the two stage-generic operations.
All uniform choices precede data; at the smallest
scheduled orders the available auxiliary regularity exceeds the coefficient order. -/
theorem retained_readout_kernel_equation_of_ingredients {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    (hclass : ClassicalKernelComponentStatement) (hsum : FiniteParentReadoutWeakStatement) :
    RetainedReadoutKernelEquationStatement α s q ζ := by
  classical
  obtain ⟨Λ₀, hΛ₀, hc⟩ := retained_stage_certificates α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  refine ⟨Λ₀, hΛ₀, ?_⟩
  intro Λ hΛ
  obtain ⟨cmax, hcmax, hc⟩ := hc Λ hΛ
  refine ⟨cmax, hcmax, ?_⟩
  intro φ₀ hφ₀ hφsmooth hφpos hφint hφsupport bw hbw hbwupper Q T₀ hQ hT₀
    Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched
    hNaux hNout halloc hsX hsZ
  obtain ⟨thr, CH, Υ, hCH, hΥ, hc⟩ := hc φ₀ hφ₀ hφsmooth hφpos hφint hφsupport
    bw hbw hbwupper Q T₀ hQ hT₀ Ce τe kS r₀ D₀ hCe hτe hc₀ hc₀upper hcr hcrupper hσf hlamC
    H J N p nk Lc Lf Lpr Acl Naux Nout Kres npad sX sZ σ₀ a σ hsched hNaux hNout halloc hsX hsZ
  refine ⟨thr, CH, Υ, hCH, hΥ, ?_⟩
  intro kI hkI
  obtain ⟨CIthr, Cwthr, hc⟩ := hc kI hkI
  refine ⟨CIthr, Cwthr, ?_⟩
  intro CI Cw j₀ hledger hstart CQ Cpr
  obtain ⟨mc, hc⟩ := hc CI Cw j₀ hledger hstart
  change RetainedEnergy.RetainedCertificatesAt α s q ζ Λ φ₀ hφ₀ bw Ce τe kS r₀ D₀ H J N p nk
    npad sX sZ σ₀ kI CI Cw j₀ mc at hc
  refine ⟨max mc (j₀ + 2), ?_⟩
  intro D hDα hDq hDΛ hDζ hseq M hband hterm Mnat hMnat law hlaw
    hr _ _ _ _ _ _ _ seedK freshK hfresh seed n tS tf hseed m hm hn hnM
    tA s₀ htA hdelay hwindow _hT G G' hcascade hlevel hG hactual
    tp Preg hprep _f _Ain _hf Y0 Y Yw Yk _htrace hsol _CcT _PZ _aRep _û _hlift aZ aY hZ hY
  let P := succProvParams D Cw kI.cr σ₀ (succEta0 α q s) N p
  let Mn := succMenu Mnat r₀ D₀ H J N p npad sX sZ (succEta0 α q s)
  let Gr := G'.retained m H J
  have hlev : Gr.level = m - 1 := by
    change G'.level = m - 1
    rw [hactual.2.1, hlevel]
  have hcGr : IsCascadeStage D P Mn seed Gr := by
    simpa only [P, Mn, Gr, hlevel, succMenu] using IsCascadeStage.step hcascade hactual
  obtain ⟨hnat, _hshift, hslot, hctx, _hmarked, _hker⟩ := hc D hDα hDq hDΛ hDζ hseq M hband
    hterm Mnat hMnat law hlaw seedK freshK hfresh seed n tS tf hseed m (by omega) hn hnM
    tA htA G G' hcascade hlevel hG hactual
  obtain ⟨_hc0I, _hcrI, hprod⟩ := Buffer.invariantAdmissible_molecular_parameters hkI
  have hmGr v : 0 ≤ compReserve kI (v : CompIn Gr.comps).1 :=
    (Buffer.cascade_component_reserve_pos hseed.2.1 hcGr kI hprod v).le
  have hm2Gr v : compReserve kI (v : CompIn Gr.comps).1 ≤ 2 :=
    (Buffer.compReserve_le_one kI v.1).trans (by norm_num)
  have hi : 1 ≤ Gr.level := by rw [hlev]; omega
  have hj : j₀ ≤ Gr.level := by rw [hlev]; omega
  have hε : 0 < D.eps (Gr.level - 1) :=
    Construction.Stream.ocEpsilon_pos (by rw [hDΛ]; omega)
  have haux := hsched.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hDm : succSchedD D₀ N p (H + 1) ≤ Naux := by omega
  have hDm2 := Buffer.preparation_schedule_order_ge_two D₀ N p H
  have hk1 : 1 ≤ Naux := by omega
  have htptf : tp ≤ tf := by
    have hh := hprep.2.2.1
    rw [hlevel, hDα, hDq, hDΛ] at hh
    exact hh.trans hwindow
  have hcoeff : ∀ v u (γ : Gr.fam.Γ v u) d, ∀ t ∈ Set.Icc tp tf,
      Continuous (Gr.physCoeff v u γ d t) := by
    intro v u γ d t ht
    exact (native_physCoeff_all_order_smooth hctx hslot hnat hi hj hbw hε tp tf
      v u γ (hmGr v) (hm2Gr v) 0 d t ht).continuous
  have hstream : IsAdmissibleStream (D.Φ (m - 1)) :=
    Velocity.streamSeq_admissible hζ (by omega) hseq (m - 1)
  have hcomp := hclass Gr P seedK freshK φ₀ hφ₀ hφsmooth
    (Providers.hasCompactSupport_of_unitBall hφsupport) Naux (D.κ (m - 1)) tp tf
    (streamVel (D.Φ (m - 1))) hDm hk1 htptf
    (fun t _ => hstream.vel_continuous.comp (continuous_const.prodMk continuous_id)) hcoeff Y0 Y Yw Yk hsol aY hY
  apply hsum m (D.eps (m - 1)) (succEta0 α q s) (D.κ (m - 1)) tp tf
    (streamVel (D.Φ (m - 1))) htptf aY aZ
    (fun v s x => coeffFluxOn P seedK freshK φ₀ Gr .kernel aY v s x)
  · intro v t ht
    exact (hY v t ht).2.1.of_le (by exact_mod_cast hk1)
  · intro v t ht
    exact readout_representative_eq m (D.eps (m - 1)) (succEta0 α q s)
      (fun v => Y v t) (fun v x => aY t x v) (fun v x => aZ t x v)
      (fun v => hY v t ht) (fun v => hZ v t ht) v
  · exact hcomp

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! Root casts, spatial differentiation and restriction to the common time window for the
finite parent readout. These operations preserve the full integrated weak equation. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Weighted AVenhance
namespace AVRegularity.Construction.Preservation.Residual

/-- Equality of root indices preserves spatial smoothness. -/
theorem kernel_readout_contDiff_root_cast {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {i j : ℕ} (hij : i = j) {n : ℕ∞} (f : Vec 2 → hr i) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => cast (congrArg hr hij) (f x)) := by
  subst j
  exact hf

/-- Root casts preserve the classical-gradient form of the equation. -/
theorem kernel_readout_classical_weak_root_cast {hr : ℕ → Type}
    [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
    {i j : ℕ} (hij : i = j) (μ : Measure (Vec 2)) (ν a t : ℝ)
    (drift : ℝ → Vec 2 → Vec 2) (U : ℝ → Vec 2 → hr i)
    (Q : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr i))
    (h : ∀ φ : Vec 2 → hr i, ContDiff ℝ (⊤ : ℕ∞) φ → IsZ2Periodic φ →
      CoupledWeakIdentity μ ν a t drift (U t) (U a) φ (fun l x => gradE φ x l)
        (fun s l x => gradE (U s) x l) 0 Q 0)
    (φ : Vec 2 → hr j) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ) (hper : IsZ2Periodic φ) :
    CoupledWeakIdentity μ ν a t drift
      (fun x => cast (congrArg hr hij) (U t x)) (fun x => cast (congrArg hr hij) (U a x))
      φ (fun l x => gradE φ x l)
      (fun s l x => gradE (fun y => cast (congrArg hr hij) (U s y)) x l) 0
      (fun s x => cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) hij) (Q s x)) 0 := by
  subst j
  exact h φ hφ hper

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The constant word weight commutes with the spatial gradient. -/
theorem kernel_readout_grad_smul (c : ℝ) (f : Vec 2 → E) (x : Vec 2)
    (j : Fin 2) :
    gradE (fun y => c • f y) x j = c • gradE f x j := by
  change (fderiv ℝ (c • f) x) (basisVec j) = _
  rw [fderiv_const_smul_field]
  rfl

/-- Constant scaling commutes with the classical gradient in the full weak identity. -/
theorem kernel_readout_classical_weak_smul (μ : Measure (Vec 2)) (c ν a t : ℝ)
    (drift : ℝ → Vec 2 → Vec 2) (U : ℝ → Vec 2 → E)
    (Q : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (h : CoupledWeakIdentity μ ν a t drift (U t) (U a) φ dφ
      (fun s j x => gradE (U s) x j) 0 Q 0) :
    CoupledWeakIdentity μ ν a t drift (fun x => c • U t x) (fun x => c • U a x) φ dφ
      (fun s j x => gradE (fun y => c • U s y) x j) 0 (fun s x => c • Q s x) 0 := by
  have hh := CycleJointProofs.coupledWeakIdentity_smul μ c ν a t drift (U t) (U a) φ dφ
    (fun s j x => gradE (U s) x j) 0 Q 0 h
  simp only [smul_zero] at hh
  have hd : c • (fun s j x => gradE (U s) x j) =
      (fun s j x => gradE (fun y => c • U s y) x j) := by
    funext s j x
    exact (kernel_readout_grad_smul c (U s) x j).symm
  rw [hd] at hh
  exact hh

/-- The gradient of a finite sum is the literal finite sum of the gradients. -/
theorem kernel_readout_grad_sum {I : Type*} [Fintype I] (f : I → Vec 2 → E)
    (x : Vec 2) (hf : ∀ i, DifferentiableAt ℝ (f i) x) (j : Fin 2) :
    gradE (fun y => ∑ i, f i y) x j = ∑ i, gradE (f i) x j := by
  unfold gradE
  rw [fderiv_fun_sum (fun i _ => hf i)]
  simp only [sum_apply]

/-- Pointwise agreement of gradients on the integration window preserves every clause. -/
theorem kernel_readout_weak_gradient_congr (μ : Measure (Vec 2)) (ν a t : ℝ)
    (drift : ℝ → Vec 2 → Vec 2) (u f φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (du dz : ℝ → Fin 2 → Vec 2 → E)
    (Q : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (he : ∀ s ∈ Set.Ioc a t, dz s = du s)
    (h : CoupledWeakIdentity μ ν a t drift u f φ dφ du (fun _ _ => 0) Q (fun _ _ => 0)) :
    CoupledWeakIdentity μ ν a t drift u f φ dφ dz (fun _ _ => 0) Q (fun _ _ => 0) := by
  have hR (s : ℝ) (hs : s ∈ Set.Ioc a t) :
      weakIdentityRhs ν drift φ dφ dz (fun _ _ => 0) Q (fun _ _ => 0) s =
      weakIdentityRhs ν drift φ dφ du (fun _ _ => 0) Q (fun _ _ => 0) s := by
    change (fun x => -(∑ j, drift s x j * inner ℝ (dz s j x) (φ x)) -
      ν * ∑ j, inner ℝ (dz s j x) (dφ j x) -
      ∑ j, inner ℝ ((0 : E) + (Q s x) j) (dφ j x) + inner ℝ (0 : E) (φ x)) = _
    rw [he s hs]
    rfl
  apply coupledWeakIdentity_rhs_transfer μ ν a t drift _ _ φ dφ _ _ _ _ _ _ _ _ h
  · intro s hs
    rw [hR s hs]
    exact h.2.2.1 s hs
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Filter.Eventually.of_forall (congrFun (hR s hs))

/-- A finite sum of classical component equations has the classical gradient of the sum. -/
theorem kernel_readout_classical_weak_sum {I : Type*} [Fintype I]
    (μ : Measure (Vec 2)) (ν a b t : ℝ) (drift : ℝ → Vec 2 → Vec 2)
    (U : I → ℝ → Vec 2 → E) (Q : I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (ht : t ∈ Set.Icc a b) (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (hd : ∀ i, ∀ s ∈ Set.Icc a b, Differentiable ℝ (U i s))
    (h : ∀ i, CoupledWeakIdentity μ ν a t drift (U i t) (U i a) φ dφ
      (fun s j x => gradE (U i s) x j) 0 (Q i) 0) :
    CoupledWeakIdentity μ ν a t drift (fun x => ∑ i, U i t x) (fun x => ∑ i, U i a x)
      φ dφ (fun s j x => gradE (fun y => ∑ i, U i s y) x j) 0
      (fun s x => ∑ i, Q i s x) 0 := by
  classical
  have hh := CycleWords.coupledWeakIdentity_finset_sum Finset.univ μ ν a t drift
    (fun i => U i t) (fun i => U i a) φ dφ (fun i s j x => gradE (U i s) x j)
    (fun _ => (0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))) Q
    (fun _ => (0 : ℝ → Vec 2 → E)) (fun i _ => h i)
  simp only [Finset.sum_const_zero] at hh
  have hg (s : ℝ) (hs : s ∈ Set.Ioc a t) :
      (fun j x => gradE (fun y => ∑ i, U i s y) x j) =
      (∑ i, fun j x => gradE (U i s) x j) := by
    funext j x
    exact (kernel_readout_grad_sum _ x (fun i => hd i s ⟨hs.1.le, hs.2.trans ht.2⟩ x) j).trans
      (by simp only [Finset.sum_apply])
  have hu : (fun x => ∑ i, U i t x) = ∑ i, U i t := by
    funext x
    simp only [Finset.sum_apply]
  have hf : (fun x => ∑ i, U i a x) = ∑ i, U i a := by
    funext x
    simp only [Finset.sum_apply]
  have hQ : (fun s x => ∑ i, Q i s x) = ∑ i, Q i := by
    funext s x
    simp only [Finset.sum_apply]
  rw [hu, hf, hQ]
  exact kernel_readout_weak_gradient_congr μ ν a t drift
    (∑ i, U i t) (∑ i, U i a) φ dφ
    (∑ i, fun s j x => gradE (U i s) x j)
    (fun s j x => gradE (fun y => ∑ i, U i s y) x j)
    (∑ i, Q i)
    (fun s hs => (hg s hs).trans (by simp only [Finset.sum_apply])) hh

/-- A field equality throughout the closed window suffices for its endpoint values and all
spatial gradients in the weak equation. No equality is required outside that window. -/
theorem kernel_readout_weak_window_congr (μ : Measure (Vec 2)) (ν a b t : ℝ)
    (drift : ℝ → Vec 2 → Vec 2) (U Z : ℝ → Vec 2 → E)
    (Q : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => E))
    (hab : a ≤ b) (ht : t ∈ Set.Icc a b)
    (he : ∀ s ∈ Set.Icc a b, Z s = U s)
    (φ : Vec 2 → E) (dφ : Fin 2 → Vec 2 → E)
    (h : CoupledWeakIdentity μ ν a t drift (U t) (U a) φ dφ
      (fun s j x => gradE (U s) x j) (fun _ _ => 0) Q (fun _ _ => 0)) :
    CoupledWeakIdentity μ ν a t drift (Z t) (Z a) φ dφ
      (fun s j x => gradE (Z s) x j) (fun _ _ => 0) Q (fun _ _ => 0) := by
  rw [he t ht, he a ⟨le_rfl, hab⟩]
  have hR (s : ℝ) (hs : s ∈ Set.Ioc a t) :
      weakIdentityRhs ν drift φ dφ (fun s j x => gradE (Z s) x j)
        (fun _ _ => 0) Q (fun _ _ => 0) s =
      weakIdentityRhs ν drift φ dφ (fun s j x => gradE (U s) x j)
        (fun _ _ => 0) Q (fun _ _ => 0) s := by
    have hz := he s ⟨hs.1.le, hs.2.trans ht.2⟩
    change (fun x => -(∑ j, drift s x j * inner ℝ (gradE (Z s) x j) (φ x)) -
      ν * ∑ j, inner ℝ (gradE (Z s) x j) (dφ j x) -
      ∑ j, inner ℝ ((0 : E) + (Q s x) j) (dφ j x) + inner ℝ (0 : E) (φ x)) = _
    rw [hz]
    rfl
  apply coupledWeakIdentity_rhs_transfer μ ν a t drift _ _ φ dφ _ _ _ _ _ _ _ _ h
  · intro s hs
    rw [hR s hs]
    exact h.2.2.1 s hs
  · filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
    exact Filter.Eventually.of_forall (congrFun (hR s hs))

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! The literal constant parent-word readout of a finite system of classical weak equations.
No estimate, quiet-set hypothesis, or flux cancellation is used. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance
namespace AVRegularity.Construction.Preservation.Residual

/-- Finite parent readout preserves all spatial and time integrability clauses.
Special cases: the empty component type is the empty sum; zero word weights contribute zero;
a singleton is scalar linearity; zero-length windows and identity metrics need no exception. -/
theorem finite_parent_readout_weak : FiniteParentReadoutWeakStatement := by
  classical
  intro hr _ _ S S' m E η ν a b drift hab aY aZ Q hY hZ hcomp v t ht φ hφ hper
  let U (c : CompIn S') (s : ℝ) (x : Vec 2) : hr v.1.root :=
    if h : compParent m c.1 = v.1 then E ^ (η * (compWord m c.1).length) •
      cast (congrArg hr ((compParent_root m c.1).symm.trans (congrArg Comp.root h)))
        (aY s x c) else 0
  let F (c : CompIn S') (s : ℝ) (x : Vec 2) : PiLp 2 (fun _ : Fin 2 => hr v.1.root) :=
    if h : compParent m c.1 = v.1 then E ^ (η * (compWord m c.1).length) •
      cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r))
        ((compParent_root m c.1).symm.trans (congrArg Comp.root h))) (Q c s x) else 0
  have hd (c : CompIn S') (s : ℝ) (hs : s ∈ Set.Icc a b) :
      Differentiable ℝ (U c s) := by
    dsimp only [U]
    split_ifs with hp
    · have he := (compParent_root m c.1).symm.trans (congrArg Comp.root hp)
      have hc := kernel_readout_contDiff_root_cast he (fun x => aY s x c) (hY c s hs)
      exact (hc.const_smul _).differentiable (by norm_num)
    · exact differentiable_const _
  have hrow (c : CompIn S') : CoupledWeakIdentity (volume.restrict unitCube) ν a t drift
      (U c t) (U c a) φ (fun j x => gradE φ x j)
      (fun s j x => gradE (U c s) x j) (fun _ _ => 0) (F c) (fun _ _ => 0) := by
    by_cases hp : compParent m c.1 = v.1
    · let e := (compParent_root m c.1).symm.trans (congrArg Comp.root hp)
      have hc := kernel_readout_classical_weak_root_cast e (volume.restrict unitCube) ν a t drift
        (fun s x => aY s x c) (Q c) (hcomp c t ht) φ hφ hper
      have hh := kernel_readout_classical_weak_smul (volume.restrict unitCube)
        (E ^ (η * (compWord m c.1).length)) ν a t drift
        (fun s x => cast (congrArg hr e) (aY s x c))
        (fun s x => cast (congrArg (fun r => PiLp 2 (fun _ : Fin 2 => hr r)) e) (Q c s x))
        φ (fun j x => gradE φ x j) hc
      simp only [U, F, hp, ↓reduceDIte]
      exact hh
    · simp only [U, F, hp, ↓reduceDIte]
      have hg : (fun (_ : ℝ) (j : Fin 2) (x : Vec 2) => gradE (fun _ => (0 : hr v.1.root)) x j) = 0 := by
        funext s j x
        simp [gradE]
      rw [hg]
      exact CycleWords.coupledWeakIdentity_zero (volume.restrict unitCube) ν a t drift
        φ (fun j x => gradE φ x j)
  have hh := kernel_readout_classical_weak_sum (volume.restrict unitCube) ν a b t drift
    U F ht φ (fun j x => gradE φ x j) hd hrow
  have hF : (fun s x => ∑ c, F c s x) = readoutFlux m E η (fun _ => True) Q v := by
    funext s x
    simp only [F, readoutFlux, and_true]
  rw [hF] at hh
  apply kernel_readout_weak_window_congr (volume.restrict unitCube) ν a b t drift
    (fun s x => ∑ c, U c s x) (fun s x => aZ s x v)
    (readoutFlux m E η (fun _ => True) Q v) hab ht
  · intro s hs
    exact hZ v s hs
  · exact hh

end AVRegularity.Construction.Preservation.Residual
end
end

section
/-! Conversion of the stored kernel weak system to classical representatives. Spatial
integrability of the replacement is proved at every time; only the stored-to-classical jet
identification is restricted to almost every time, exactly as in the solution class. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.Construction.Preservation.Residual

/-- The classical kernel component equation follows from its actual stored weak solution.
Special cases: empty and singleton systems, zero-width or singular kernel maps, an edgeless
seed and zero-length time windows all use the same proof. The smallest order is max 1 Dm. -/
theorem classical_kernel_component : ClassicalKernelComponentStatement := by
  classical
  intro D hr _ _ _ _ _ _ Dm bw j₀ G P seedK freshK φ₀ hφ₀ hφs hφc k ν a b drift
    hDm hk hab hV hA Y0 Y Yw Yk hsol aY hY v t ht φ hφ hp
  let du : ℝ → Fin 2 → Vec 2 → hr v.1.root := fun s j =>
    (Yw v s).toFunction.jet ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos k)⟩, fun _ => j⟩
  let F0 : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root) := fun _ =>
    (0 : TorusHk k (PiLp 2 (fun _ : Fin 2 => hr v.1.root))).toFunction.jet (valueIndex2 k)
  let g0 : ℝ → Vec 2 → hr v.1.root := fun _ =>
    (0 : TorusHk k (hr v.1.root)).toFunction.jet (valueIndex2 k)
  let Q : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => hr v.1.root) := kernelReadoutStoredFlux G Yk v
  obtain ⟨ψ, hψ, hdψ⟩ := kernel_readout_smooth_test φ hφ hp
  have hw : CoupledWeakIdentity (volume.restrict unitCube) ν a t drift
      ((Y v t).toFunction.jet (valueIndex2 k)) ((Y0 v).toFunction.jet (valueIndex2 k))
      φ (fun j x => gradE φ x j) du Q F0 g0 := by
    exact CycleJointProofs.coupledWeakIdentity_test_congr (volume.restrict unitCube) ν a t drift
      _ _ _ φ _ (fun j x => gradE φ x j) du Q F0 g0 hψ hdψ
      (hsol.2.2.2.2.2.2 v t ht ψ)
  have hu := FullLift.classicalRep_value_ae (Y v t) (fun x => aY t x v) (hY v t ht)
  have hf : (Y0 v).toFunction.jet (valueIndex2 k) =ᵐ[volume.restrict unitCube]
      fun x => aY a x v := by
    rw [← hsol.2.2.2.1 v]
    exact FullLift.classicalRep_value_ae (Y v a) (fun x => aY a x v) (hY v a ⟨le_rfl, hab⟩)
  have hF0 (s : ℝ) : F0 s =ᵐ[volume.restrict unitCube] 0 :=
    EntryTerminal.Ingredients.torusHk_zero_jet_ae (valueIndex2 k)
  have hg0 (s : ℝ) : g0 s =ᵐ[volume.restrict unitCube] 0 :=
    EntryTerminal.Ingredients.torusHk_zero_jet_ae (valueIndex2 k)
  have hw0 : CoupledWeakIdentity (volume.restrict unitCube) ν a t drift
      (fun x => aY t x v) (fun x => aY a x v) φ (fun j x => gradE φ x j) du Q 0 0 := by
    apply CycleJointProofs.coupledWeakIdentity_integrands_congr (volume.restrict unitCube) ν a t
      drift drift _ (fun x => aY t x v) _ (fun x => aY a x v) φ φ
      (fun j x => gradE φ x j) (fun j x => gradE φ x j) du du Q Q F0 0 g0 0 _ _ _ hw
    · filter_upwards [hu] with x hx
      rw [hx]
    · filter_upwards [hf] with x hx
      rw [hx]
    · intro s _
      exact CycleJointProofs.weakIdentityRhs_congr_ae (volume.restrict unitCube) ν s
        drift drift φ φ _ _ du du Q Q F0 0 g0 0 Filter.EventuallyEq.rfl
        Filter.EventuallyEq.rfl (fun _ => Filter.EventuallyEq.rfl)
        (fun _ => Filter.EventuallyEq.rfl) Filter.EventuallyEq.rfl (hF0 s) (hg0 s)
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun s hs => ⟨hs.1.le, hs.2.trans ht.2⟩
  have hgrad : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), ∀ j : Fin 2,
      du s j =ᵐ[volume.restrict unitCube] fun x => gradE (fun y => aY s y v) x j := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 v),
      ae_restrict_mem measurableSet_Ioc] with s hs hsI
    intro j
    have he : du s j = (Y v s).toFunction.jet ⟨⟨1, by omega⟩, fun _ => j⟩ :=
      congrArg (fun Z : TorusHk k (hr v.1.root) =>
        Z.toFunction.jet ⟨⟨1, by omega⟩, fun _ => j⟩) hs
    rw [he]
    have hj := (hY v s (hsub hsI)).2.2.2 1 hk (fun _ => j)
    unfold torusJetOrder at hj
    simp only [hk, ↓reduceDIte] at hj
    have hwj : orderedDerivative (fun _ : Fin 1 => j) (fun y => aY s y v) =
        fun x => gradE (fun y => aY s y v) x j := by
      rw [orderedDerivative_succ, orderedDerivative_zero]
      rfl
    exact hj.trans (Filter.Eventually.of_forall (congrFun hwj))
  have hvalues : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ v u (γ : G.fam.Γ v u),
      (Yk v u γ s).val (valueIndex2 (k + Dm - 1)) =
      (G.kernelOf P seedK freshK v u γ).op φ₀ hφ₀ s ((Y u s).val (valueIndex2 k)) :=
    ae_all_iff.mpr fun v => ae_all_iff.mpr fun u => ae_all_iff.mpr fun γ =>
      kernel_readout_regularized_value_ae G P seedK freshK φ₀ hφ₀ ν a b drift Y0 Y Yw Yk hsol v u γ
  have hflux : ∀ᵐ s ∂volume.restrict (Set.Ioc a t), Q s =ᵐ[volume.restrict unitCube]
      coeffFluxOn P seedK freshK φ₀ G .kernel aY v s := by
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub hvalues,
      ae_restrict_mem measurableSet_Ioc] with s hs hsI
    exact kernel_readout_stored_flux_ae G P seedK freshK hφ₀ hφs hφc aY Y Yk hDm s
      (fun u => hY u s (hsub hsI)) hs v
  apply CycleWords.coupledWeakIdentity_gradient_flux_ae_time_congr (volume.restrict unitCube)
    ν a t drift (fun x => aY t x v) (fun x => aY a x v) φ (fun j x => gradE φ x j)
    du (fun s j x => gradE (fun y => aY s y v) x j)
    Q 0 0 (fun s x => coeffFluxOn P seedK freshK φ₀ G .kernel aY v s x) 0 hw0 hgrad
  · filter_upwards [hflux] with s hs
    filter_upwards [hs] with x hx
    change Q s x + 0 = 0 + coeffFluxOn P seedK freshK φ₀ G .kernel aY v s x
    rw [add_zero, zero_add]
    exact hx
  · intro s hs
    exact kernel_readout_rhs_integrable G P seedK freshK hφ₀ hφs hφc aY Y hDm hk ν drift s
      (hV s (hsub hs)) (fun u => hY u s (hsub hs))
      (fun v u γ d => hA v u γ d s (hsub hs)) v φ hφ

/-- The retained kernel system gives the raw parent-word readout weak equation, with all
uniform constants chosen before the stage data. Special cases: empty and singleton families,
the smallest scheduled orders, identity metric and an edgeless seed are included. No source
cancellation or quiet-transition assertion is used. -/
theorem retained_readout_kernel_equation {α s q : ℝ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) :
    RetainedReadoutKernelEquationStatement α s q ζ :=
  retained_readout_kernel_equation_of_ingredients hα₀ hα₁ hs₀ hs₁ hq hζ
    classical_kernel_component finite_parent_readout_weak

end AVRegularity.Construction.Preservation.Residual
end
end
end
