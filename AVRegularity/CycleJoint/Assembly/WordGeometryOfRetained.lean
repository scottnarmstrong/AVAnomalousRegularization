-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.BlockTransitionJets
import AVRegularity.CycleComparison.Charts.ChartDeviation
public import AVRegularity.Weighted.WordNativeSolutionPack

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleComparison.Charts
namespace AVRegularity.CycleJointProofs.Assembly

/-! The committed native transition operator reads values through the exact reference point map. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
  (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
  (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
  (J : ℕ) (hJ : J ≤ Jchart + 1)

/-- The reference return first undoes the physical chart and then the centred cell dilation. -/
theorem blockTransition_return_value (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ J E) :
    planeValue (preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht U) =ᵐ[volume]
      fun x => planeValue U (e⁻¹ • (streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) x t - yc)) := by
  let UA := planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) U
  have hUA := planeCarrierAffine_value_ae e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) U
  have hret :
      planeValue (preparationReferenceHkInverse hc hcover hTau ha J hJ t ht UA) =ᵐ[volume]
        planeValue UA ∘ streamFlowHomeomorph hφ ((l₀ : ℝ) * ocTauPP α q Λ m) t :=
    planeHkSmoothPullback_value_ae (streamFlowHomeomorph hφ ((l₀ : ℝ) * ocTauPP α q Λ m) t)
      (streamFlow_spatial_smooth hφ _ t) (streamFlow_measurePreserving hφ _ t)
      (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
      (fun _ _ _ => abs_nonneg _)
      (fun j hj hjJ x => preparation_reference_inverse_flow_jets hc hcover hTau ha t ht
        j hj (hjJ.trans hJ) x) UA
  apply hret.trans
  have heq := (streamFlow_measurePreserving hφ ((l₀ : ℝ) * ocTauPP α q Λ m) t).quasiMeasurePreserving.ae_eq_comp hUA
  apply heq.trans
  filter_upwards with x
  change planeValue U (-(e⁻¹ • yc) + e⁻¹ •
      streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) x t) =
    planeValue U (e⁻¹ • (streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) x t - yc))
  congr 1
  rw [smul_sub, sub_eq_add_neg, add_comm]

/-- Time cancels out of the transition: it is the flow between the two reference times. -/
theorem blockTransition_operator_value (σ : ℝ) (hσ : σ ∈ Icc a b)
    (e : ℝ) (he : e ≠ 0) (yc yc' : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    planeValue (preparationReferenceCellTransitionOperator hc hcover hTau ha J hJ
      σ hσ e he yc yc' t ht U) =ᵐ[volume]
      fun z => planeValue U (blockTransitionAffine
        (fun x => streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) x σ) e yc yc' z) := by
  let V := preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht U
  let Z := preparationWindowReferenceHkWindowPullOperator hc hcover σ hσ ha J hJ t ht V
  have hZ : planeValue Z =ᵐ[volume] planeValue V ∘ streamFlowHomeomorph hφ t σ :=
    planeHkSmoothPullback_value_ae (streamFlowHomeomorph hφ t σ)
      (streamFlow_spatial_smooth hφ t _) (streamFlow_measurePreserving hφ t _)
      (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
      (fun _ _ _ => abs_nonneg _)
      (fun j hj hjJ x => preparation_window_reference_time_flow_jets hc hcover σ hσ ha t ht
        j hj (hjJ.trans hJ) x) V
  have hV := blockTransition_return_value hc hcover hTau ha J hJ e he yc t ht U
  have hZA := hZ.trans ((streamFlow_measurePreserving hφ t σ).quasiMeasurePreserving.ae_eq_comp hV)
  have hA := planeCarrierAffine_value_ae e he yc' Z
  apply hA.trans
  have hcomp := (plane_affine_quasiMeasurePreserving e he yc').ae_eq_comp hZA
  apply hcomp.trans
  filter_upwards with z
  dsimp only [blockTransitionAffine, Function.comp_apply]
  congr 1
  congr 1
  rw [streamFlow_group_law hφ]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! The native renewal transition is centred, volume preserving, and has every certified inverse jet. -/

@[expose] public noncomputable section

open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleComparison.Charts

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The two recorded centres are the same physical particle in the successive reference charts. -/
theorem blockTransition_centres (α q : ℝ) (Λ m : ℕ) {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (l₀ : ℤ) (P : ℕ) (hP : 1 ≤ P) (y₀ : Vec 2) :
    windowCoverChartCentre α q Λ m φ hφ l₀ P y₀ (windowCoverFollowingChartIndex P hP) =
      ocTransition α q Λ m φ hφ (l₀ + 1) l₀
        (windowCoverChartCentre α q Λ m φ hφ l₀ P y₀ (windowCoverReferenceChartIndex P)) := by
  unfold windowCoverChartCentre windowCoverFollowingChartIndex windowCoverReferenceChartIndex
  change ocCellCentre α q Λ m φ hφ (l₀ - 1)
      (ocTransition α q Λ m φ hφ (l₀ - 1) l₀ y₀) (1 + 1) = _
  rw [ocCellCentre]
  rw [show l₀ - 1 + (1 : ℕ) + 1 = l₀ + 1 by omega,
    show l₀ - 1 + (1 : ℕ) = l₀ by omega]

/-- The exact affine chart change preserves volume. -/
theorem blockTransition_flow_volume {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (r σ e : ℝ) (he : e ≠ 0) (yc yc' z : Vec 2) :
    (fderiv ℝ (blockTransitionAffine (fun x => streamFlow φ hφ r x σ) e yc yc') z).det = 1 := by
  rw [blockTransitionAffine_fderiv _ (streamFlow_spatial_smooth hφ r σ) e he,
    AVRegularity.Velocity.Port.Section2FlowIdentities.continuousLinearMap_det_two]
  simpa only [Matrix.det_fin_two, jacMatrix, Matrix.of_apply] using
    streamFlow_jacMatrix_det_one hφ r σ (yc' + e • z)

/-- The actual native transition has the exact centred point map consumed by the seam. -/
theorem blockTransition : BlockTransitionStatement.{u, v, w, x} := by
  intro Kmax Jchart Cchart CG Cpad Cage
  let CU := blockTransitionConstant Jchart Cchart
  have hCU := blockTransitionConstant_bounds Jchart Cchart
  refine ⟨CU, lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) hCU.1, ?_⟩
  intro α q Λ m ζfast Φ hφ tS tZ Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb qJ y₀ cov
    hΛ ha hg0 ι h _ _ D P' Ctx F hprep hcover hnext t ht htblock
  dsimp only
  let T := ocTauPP α q Λ m
  let r := (l₀ : ℝ) * T
  let σ := ((l₀ + 1 : ℤ) : ℝ) * T
  let e := ocEpsilon q Λ m
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
    (windowCoverReferenceChartIndex P)
  let yc' := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
    (windowCoverFollowingChartIndex P cov.P_pos)
  let f := fun x => streamFlow (Φ (m - 1)) hφ r x σ
  let finv := fun x => streamFlow (Φ (m - 1)) hφ σ x r
  have hT : 0 < T := Construction.Stream.ocTauPP_pos hΛ
  have he : 0 < e := Construction.Stream.ocEpsilon_pos hΛ
  have hE : 0 < ocEpsilon q Λ (m - 1) := Construction.Stream.ocEpsilon_pos hΛ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := streamFlow_spatial_smooth hφ r σ
  have hi : ContDiff ℝ (⊤ : ℕ∞) finv := streamFlow_spatial_smooth hφ σ r
  have hleft : Function.LeftInverse finv f :=
    fun z => (streamFlowHomeomorph hφ r σ).symm_apply_apply z
  have hright : Function.LeftInverse f finv :=
    fun z => (streamFlowHomeomorph hφ r σ).apply_symm_apply z
  have hr : r ∈ preparationPaddedWindow tS tZ Cpad T := hprep.schedule.reference_mem
  have hσ : σ ∈ preparationPaddedWindow tS tZ Cpad T :=
    preparation_reference_time_padded hprep hcover σ hnext
  have hage : |σ - r| ≤ 2 * Cage * T := preparation_reference_time_age hprep hcover hT.le σ hnext
  have hage' : |r - σ| ≤ 2 * Cage * T := by simpa only [abs_sub_comm] using hage
  have hspan : |σ - r| = T := by
    have heq : σ - r = T := by dsimp only [σ, r]; push_cast; ring
    rw [heq, abs_of_pos hT]
  have hspan' : |r - σ| ≤ T := by rw [abs_sub_comm, hspan]
  refine ⟨blockTransitionAffine f e yc yc', blockTransitionAffine finv e yc' yc, ?_, ?_,
    blockTransitionAffine_smooth finv hi e yc' yc⟩
  · intro E _ _ _ _ _ _ J hJ U
    exact blockTransition_operator_value hprep hcover hT.le ha J hJ σ hnext e he.ne' yc yc' t ht U
  · refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · have hc : yc' = finv yc := blockTransition_centres α q Λ m hφ l₀ P cov.P_pos y₀
      change e⁻¹ • (f (yc' + e • (0 : Vec 2)) - yc) = 0
      rw [smul_zero, add_zero, hc, hright, sub_self, smul_zero]
    · exact fun z => blockTransitionAffine_inverse f finv hleft e he.ne' yc yc' z
    · exact fun z => blockTransitionAffine_inverse finv f hright e he.ne' yc' yc z
    · exact ⟨(blockTransitionAffine_smooth f hf e yc yc').of_le (by simp),
        (blockTransitionAffine_smooth finv hi e yc' yc).of_le (by simp)⟩
    · exact fun z => blockTransition_flow_volume hφ r σ e he.ne' yc yc' z
    · exact ⟨fun z => blockTransition_flow_deviation hprep.flow ha r σ hr hσ hage' T hspan'
        g cov.g_range.1 e he.ne' yc yc' z,
        fun z => blockTransition_flow_deviation hprep.flow ha σ r hσ hr hage T hspan.le
          g cov.g_range.1 e he.ne' yc' yc z⟩
    · intro j hj hjJ z
      exact ⟨blockTransition_flow_higher_jets hprep.flow ha r σ hr hσ hage' T hspan'
        g cov.g_range.1 e he hE yc yc' j hj hjJ z,
        blockTransition_flow_higher_jets hprep.flow ha σ r hσ hr hage T hspan.le
          g cov.g_range.1 e he hE yc' yc j hj hjJ z⟩

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! The analytic envelope of the centered diagonal metric letter. -/

variable {ι : Type*} [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

/-- The single-order metric budget has no dependent list index left. -/
theorem block_metric_list_analyticBudget_eq
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ : ℝ)
    (dom : Set (ℝ × Vec 2)) (Ks J : ℕ) (v u : ι) (o : Finset.Icc 2 D) :
    blockListAnalyticBudget (metricEdges (D := D) (h := h) G X₀ δ v u o) dom Ks J =
    if v = u ∧ o.val = 2 then
      ENNReal.ofReal ‖(ContinuousLinearMap.id ℝ (h v))‖ *
        ∑ I : DerivativeWord2 1, ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1),
          jetSupOn dom r q ((metricConstituent (h v) G X₀ δ).coeff I)
    else 0 := by
  rcases o with ⟨d, hdD⟩
  by_cases hvu : v = u
  · subst u
    by_cases hd : d = 2
    · subst d
      have he : metricEdges (D := D) (h := h) G X₀ δ v v ⟨2, hdD⟩ =
          [metricConstituent (h v) G X₀ δ] := by
        unfold metricEdges
        rw [dite_eq_left (show v = v ∧ 2 = 2 from ⟨rfl, rfl⟩)]
        rfl
      rw [he, ite_eq_left (show v = v ∧ (⟨2, hdD⟩ : Finset.Icc 2 D).val = 2 from ⟨rfl, rfl⟩)]
      change (∑ k : Fin 1, _) = _
      rw [Fin.sum_univ_one]
      rfl
    · have he : metricEdges (D := D) (h := h) G X₀ δ v v ⟨d, hdD⟩ = [] := by
        unfold metricEdges
        rw [dite_eq_right (show ¬ (v = v ∧ d = 2) from fun hh => hd hh.2)]
      rw [he, ite_eq_right (show ¬ (v = v ∧ (⟨d, hdD⟩ : Finset.Icc 2 D).val = 2) from fun hh => hd hh.2)]
      simp only [blockListAnalyticBudget, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]
  · have he : metricEdges (D := D) (h := h) G X₀ δ v u ⟨d, hdD⟩ = [] := by
      unfold metricEdges
      rw [dite_eq_right (show ¬ (v = u ∧ d = 2) from fun hh => hvu hh.1)]
    rw [he, ite_eq_right (show ¬ (v = u ∧ (⟨d, hdD⟩ : Finset.Icc 2 D).val = 2) from fun hh => hvu hh.1)]
    simp only [blockListAnalyticBudget, List.length_nil, Finset.univ_eq_empty, Finset.sum_empty]

/-- Only the order-two diagonal constituent contributes to the metric analytic budget. -/
theorem block_metric_analyticBudget_eq
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ : ℝ)
    (dom : Set (ℝ × Vec 2)) (Ks J : ℕ) (hD : 2 ≤ D) (v u : ι) :
    blockFiberAnalyticBudget (metricEdges (D := D) (h := h) G X₀ δ) dom Ks J v u =
    if v = u then
      ENNReal.ofReal ‖(ContinuousLinearMap.id ℝ (h v))‖ *
        ∑ I : DerivativeWord2 1, ∑ r ∈ Finset.range (Ks + 1), ∑ q ∈ Finset.range (J + 1),
          jetSupOn dom r q ((metricConstituent (h v) G X₀ δ).coeff I)
    else 0 := by
  classical
  unfold blockFiberAnalyticBudget
  simp_rw [block_metric_list_analyticBudget_eq]
  by_cases hvu : v = u
  · rw [ite_eq_left hvu]
    let o₂ : Finset.Icc 2 D := ⟨2, Finset.mem_Icc.mpr ⟨le_rfl, hD⟩⟩
    rw [Finset.sum_eq_single o₂]
    · rw [ite_eq_left ⟨hvu, rfl⟩]
    · intro o ho hne
      exact ite_eq_right (fun hh => hne (Subtype.ext hh.2))
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ _))
  · rw [ite_eq_right hvu]
    apply Finset.sum_eq_zero
    intro o ho
    exact ite_eq_right (fun hh => hvu hh.1)

/-- The metric price is uniform over components and all physical scales. -/
def blockMetricLetterPrice (Ks J : ℕ) (CG : ℕ → ℝ) : ℝ :=
  ((Fintype.card (DerivativeWord2 1) * (Ks + 1) * (J + 1) : ℕ) : ℝ) * blockMetricJetPrice Ks CG

theorem blockMetricLetterPrice_nonneg (Ks J : ℕ) (CG : ℕ → ℝ) :
    0 ≤ blockMetricLetterPrice Ks J CG :=
  mul_nonneg (Nat.cast_nonneg _) (blockMetricJetPrice_nonneg Ks CG)

/-- Local window bounds on the metric suffice for the full metric-letter analytic envelope. -/
theorem blockMetricLetter_analytic (π : ι → ℝ) (hπ : ∀ v, 0 < π v)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ g : ℝ)
    (a b : ℝ) (Ks J : ℕ) (CG : ℕ → ℝ) (hD : 2 ≤ D) (hδ : 0 < δ) (hg : 0 ≤ g)
    (hs : ∀ t ∈ Set.Icc a b, ∀ i j, ContDiff ℝ (Ks + J : ℕ) (fun x => G t x i j))
    (hnear : ∀ t ∈ Set.Icc a b, ∀ x, (G t x).IsSymm ∧ ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (G t x - 1) i j * ξ j| ≤ g * ∑ i, ξ i ^ 2)
    (hj : ∀ t ∈ Set.Icc a b, ∀ x j, 1 ≤ j → j ≤ Ks → ∀ i k,
      ‖iteratedFDeriv ℝ j (fun y => G t y i k) x‖ ≤ CG j * g * δ ^ j)
    (C : ℝ) (hC : blockMetricLetterPrice Ks J CG ≤ C) :
    IsAnalyticEnvelope (ChartedFamily.ofFiber (metricEdges (D := D) (h := h) G X₀ δ)) π
      (fun _ _ => Set.Icc a b ×ˢ Set.univ) 1 1 Ks J (fun v u => if v = u then C * g else 0) := by
  classical
  have hcoeff (v : ι) (I : DerivativeWord2 1) (r q : ℕ) (hr : r ≤ Ks) (hq : q ≤ J) :
      jetSupOn (Set.Icc a b ×ˢ Set.univ) r q ((metricConstituent (h v) G X₀ δ).coeff I) ≤
        ENNReal.ofReal (blockMetricJetPrice Ks CG * g) := by
    apply block_jetSupOn_le_of_ae_norm
    exact Filter.Eventually.of_forall (fun t X hX z => by
      change ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q (fun _ : Vec 2 =>
        fun k => G t (δ⁻¹ • (Y - X₀)) k (I ⟨0, Nat.one_pos⟩) - G t 0 k (I ⟨0, Nat.one_pos⟩)) z) X‖ ≤ _
      rw [block_fastConstant_mixed_norm]
      split_ifs
      · have hf : ContDiff ℝ (r : ℕ) (fun Y : Vec 2 =>
            fun k => G t (δ⁻¹ • (Y - X₀)) k (I ⟨0, Nat.one_pos⟩) - G t 0 k (I ⟨0, Nat.one_pos⟩)) := by
          apply contDiff_pi.mpr
          intro k
          exact (((hs t hX.1 k _).of_le (by exact_mod_cast (by omega : r ≤ Ks + J))).comp
            ((contDiff_id.sub contDiff_const).const_smul δ⁻¹)).sub contDiff_const
        apply block_vector_jet_norm_le _ r hf _ (mul_nonneg (blockMetricJetPrice_nonneg _ _) hg)
        intro k Y
        exact block_metric_normalized_entry_jet Ks CG (G t) X₀ δ g hδ hg
          (fun i j => (hs t hX.1 i j).of_le (by exact_mod_cast (Nat.le_add_right Ks J)))
          (hnear t hX.1) (hj t hX.1) r hr k _ Y
      · exact mul_nonneg (blockMetricJetPrice_nonneg _ _) hg)
  apply block_ofFiber_analyticEnvelope
  · intro v u d c hc I tX htX z
    rcases d with ⟨d, hdD⟩
    by_cases hvu : v = u
    · subst u
      by_cases hd : d = 2
      · subst d
        simp only [metricEdges, and_self, dite_true] at hc
        change c ∈ [metricConstituent (h v) G X₀ δ] at hc
        have he := List.mem_singleton.mp hc
        subst c
        apply ContDiff.contDiffAt
        apply contDiff_pi.mpr
        intro k
        exact ((hs tX.1 htX.1 k (I ⟨0, Nat.one_pos⟩)).comp
          (((contDiff_fst.sub contDiff_const).const_smul δ⁻¹))).sub contDiff_const
      · simp only [metricEdges, hd, and_false, dite_false, List.not_mem_nil] at hc
    · simp only [metricEdges, hvu, false_and, dite_false, List.not_mem_nil] at hc
  · intro v u
    rw [block_metric_analyticBudget_eq G X₀ δ _ Ks J hD v u]
    by_cases hvu : v = u
    · subst u
      simp only [ite_true, div_self (hπ v).ne', Real.sqrt_one, ENNReal.ofReal_one, one_mul]
      have hid : ‖(ContinuousLinearMap.id ℝ (h v))‖ ≤ 1 := by
        apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
        intro x
        simp only [ContinuousLinearMap.id_apply, one_mul, le_refl]
      have hp := block_constituent_analyticBudget_le (metricConstituent (h v) G X₀ δ)
        (Set.Icc a b ×ˢ Set.univ) Ks J (blockMetricJetPrice Ks CG * g) (by
          intro I r q hr hq
          exact (mul_le_mul' (ENNReal.ofReal_le_ofReal hid) (hcoeff v I r q hr hq)).trans_eq (by simp))
      apply hp.trans
      rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      apply ENNReal.ofReal_le_ofReal
      calc
        _ = blockMetricLetterPrice Ks J CG * g := by unfold blockMetricLetterPrice; ring
        _ ≤ _ := mul_le_mul_of_nonneg_right hC hg
    · simp only [hvu, ite_false, ENNReal.ofReal_zero, mul_zero, le_refl]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Word chains from the response operators**.

For a word `wd` (a list of insertions, last insertion first, `true` for a source insertion) the
chronological level carriers `wordLevelCarrier` start from the gradient carrier `Z` of the scalar
chain and apply the response `R` to the metric insertion `Dop` or the source insertion `Sop`; the
last level is `responseWordOperator 1 (R ∘ Dop) (R ∘ Sop) wd Z`.

`exists_wordChain_of_responses`: if the insertions read, at every time of the window, as the
letter fluxes of two letters `ML` (metric, `positive`) and `SL` (source), then the levels form a
word chain `IsPlaneChain (wordChainData M (blockWordLetters ML SL wd) X₀ δ)` from the datum of the
scalar chain, and the `H^{K+1}` field of every level is represented by its level carrier. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleJointProofs

namespace AVRegularity.CycleJointProofs.Assembly

section Levels

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

/-- The chronological level carriers of a word: level `0` is `Z`, level `n + 1` applies the source
operator if the `n`-th insertion (in chronological order) is a source insertion, the metric
operator otherwise. -/
def wordLevelCarrier (Dop Sop : Module.End ℝ V) (wd : List Bool) (Z : V) : ℕ → V
  | 0 => Z
  | n + 1 => (if wd.reverse.getD n false then Sop else Dop) (wordLevelCarrier Dop Sop wd Z n)

theorem wordLevelCarrier_cons_of_le (Dop Sop : Module.End ℝ V) (c : Bool) (wd : List Bool)
    (Z : V) : ∀ n, n ≤ wd.length →
    wordLevelCarrier Dop Sop (c :: wd) Z n = wordLevelCarrier Dop Sop wd Z n
  | 0, _ => rfl
  | n + 1, hn => by
    have ih := wordLevelCarrier_cons_of_le Dop Sop c wd Z n (by omega)
    simp only [wordLevelCarrier, ih]
    congr 2
    rw [List.reverse_cons, List.getD_append _ _ _ _ (by rw [List.length_reverse]; omega)]

/-- The last level carrier is the word operator. -/
theorem wordLevelCarrier_length (Dop Sop : Module.End ℝ V) (wd : List Bool) (Z : V) :
    wordLevelCarrier Dop Sop wd Z wd.length = responseWordOperator 1 Dop Sop wd Z := by
  induction wd with
  | nil => rfl
  | cons c wd ih =>
    rw [List.length_cons, wordLevelCarrier, wordLevelCarrier_cons_of_le Dop Sop c wd Z _ le_rfl,
      ih]
    have hc : (c :: wd).reverse.getD wd.length false = c := by
      rw [List.reverse_cons, List.getD_append_right _ _ _ _ (by rw [List.length_reverse])]
      simp
    rw [hc]
    cases c <;> simp [responseWordOperator, Module.End.mul_apply]

/-- The level carriers are linear in the initial carrier. -/
theorem wordLevelCarrier_add_smul (Dop Sop : Module.End ℝ V) (wd : List Bool) (c : ℝ)
    (Z Z' : V) : ∀ n, wordLevelCarrier Dop Sop wd (c • Z + Z') n =
      c • wordLevelCarrier Dop Sop wd Z n + wordLevelCarrier Dop Sop wd Z' n
  | 0 => rfl
  | n + 1 => by
    simp only [wordLevelCarrier, wordLevelCarrier_add_smul Dop Sop wd c Z Z' n, map_add,
      map_smul]

end Levels

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Word chains from the response operators: the construction**.

`exists_wordChain_of_responses`: the levels of a word, built from the frozen-metric response `R`
applied to the metric insertion `Dop` or the source insertion `Sop` of the previous level, form a
word chain `IsPlaneChain (wordChainData M (blockWordLetters ML SL wd) X₀ δ)`, provided the
insertions read as the letter fluxes of `ML` and `SL` at every time of the window. The `H^{K+1}`
field `wl` of every level is represented by its level carrier and truncates to the level value. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleJointProofs

namespace AVRegularity.CycleJointProofs.Assembly

section Bridge

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
/-- The value readout of a plane field is its value representative. -/
theorem planeJetReadout_value_ae (K : ℕ) (U : PlaneHk Set.univ K E) :
    (Weighted.planeJetReadoutOperator K (valueIndex2 K) U : Vec 2 → E) =ᵐ[volume]
      planeValue U := by
  rw [Weighted.planeJetReadoutOperator_apply]
  refine (Analysis.Convolution.univToPlane_ae (U.val (valueIndex2 K))).trans
    (Filter.Eventually.of_forall fun x => ?_)
  simp only [planeValue, planeJetOrder, dite_eq_left (Nat.zero_le K)]
  rfl

end Bridge

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The forcing of a level, represented by the insertion carrier `g` of the previous level, reads
as the letter flux of the previous level's field, when the insertion's raw readout is the letter
flux. -/
theorem level_readout_letterFlux {D : ℕ} (K : ι → ℕ) {a b : ℝ} (ϖ ρ : ℝ) (x : ι) (N : ℕ)
    (j : Fin N) (L : CycleLetter ι h D) (lo : ℕ) (X₀ : Vec 2) (δ : ℝ)
    (Hx : ℝ → (∀ u, PlaneHk Set.univ (K u + 1) (h u)) → Vec 2 → PiLp 2 (fun _ : Fin 2 => h x))
    (hL : ∀ (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ), t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux L (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x lo X₀ δ W t z) = Hx t W)
    (g : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h x)) (K x) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (F : ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
    (hF : PlaneTimeAllMomentRepresents (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b)) g F)
    (Yc : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (sw : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (hrep : ∀ u, PlaneTimeAllMomentRepresents (K u + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Yc u) (sw u))
    (hraw : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      planeValue (planeTimeAllMomentCarrierToLp (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b)) g t)
        =ᵐ[volume] Hx t (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (Yc u) t)) :
    ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
      Weighted.planeJetReadoutOperator (K x) (valueIndex2 (K x)) (F t) =ᵐ[volume]
        Weighted.letterAdmissibleFlux L (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
          (fun u => (j.castSucc, u)) x lo X₀ δ (fun u => sw u t) t := by
  have hrep' : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), ∀ u,
      planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (Yc u) t = sw u t :=
    ae_all_iff.2 fun u => hrep u
  have hmem : ∀ᵐ t ∂(volume.restrict (Set.Icc a b)), t ∈ Set.Icc a b :=
    ae_restrict_mem measurableSet_Icc
  filter_upwards [hraw, hF, hrep', hmem] with t hrt hFt hwt ht
  refine (planeJetReadout_value_ae (K x) (F t)).trans ?_
  rw [← hFt]
  refine hrt.trans (Filter.Eventually.of_forall fun z => ?_)
  have hW : (fun u => planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (Yc u) t) = fun u => sw u t := funext hwt
  rw [hW, ← hL (fun u => sw u t) t ht]

/-- The level predicate of a word: the level is the scalar chain from its datum (the datum of
the word at level `0`, zero above), its `H^{K+1}` field is represented by the level carrier `Y j`,
its forcing vanishes at level `0` and is represented by a carrier. -/
def WordLevelPred (K : ι → ℕ) (a b ϖ ρ : ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (N : ℕ) (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (Y : ℕ → ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (j : Fin (N + 1)) (s : Weighted.ScalarLevelState (fun x => K x) h) : Prop :=
  IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => Weighted.wordLevelDatum (fun (_ : Fin (N + 1)) (x : ι) => K x) f j i)
      (fun _ i => s.F i) (fun _ i => s.u i) (fun _ i => s.w i) ∧
    (∀ x, PlaneTimeAllMomentRepresents (K x + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Y j.val x) (s.w x)) ∧
    (j = 0 → s.F = 0) ∧
    (∀ x, ∃ g : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h x)) (K x) ϖ ρ 0
      (volume.restrict (Set.Icc a b)),
      PlaneTimeAllMomentRepresents (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b)) g (s.F x))

/-- The step relation of a word: the forcing of level `j + 1` reads as the flux of the `j`-th
letter of level `j`'s field. -/
def WordLevelRel {D N : ℕ} (K : ι → ℕ) (a b : ℝ) (letters : Fin N → CycleLetter ι h D)
    (X₀ : Vec 2) (δ : ℝ) (j : Fin N) (s s' : Weighted.ScalarLevelState (fun x => K x) h) :
    Prop :=
  ∀ x, ∀ᵐ t ∂(volume.restrict (Set.Icc a b)),
    Weighted.planeJetReadoutOperator (K x) (valueIndex2 (K x)) (s'.F x t) =ᵐ[volume]
      Weighted.letterAdmissibleFlux (letters j) (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x (if (letters j).positive then 1 else 0) X₀ δ
        (fun u => s.w u t) t

theorem wordLevel_zero (K : ι → ℕ) {a b : ℝ} (ϖ ρ : ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (N : ℕ) (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (Y : ℕ → ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (u0 : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (w0 : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (h0 : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u0 i) (fun _ i => w0 i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Y 0 i) (w0 i)) :
    ∃ s, WordLevelPred K a b ϖ ρ M v N f Y 0 s := by
  refine ⟨⟨u0, w0, 0⟩, ?_, fun x => hZ x, fun _ => rfl, fun x => ⟨0, ?_⟩⟩
  · have hd : (fun (_ : Fin 1) (i : ι) =>
        Weighted.wordLevelDatum (fun (_ : Fin (N + 1)) (x : ι) => K x) f 0 i) =
        fun _ i => f i :=
      funext fun _ => funext (Weighted.wordLevelDatum_zero (fun (_ : Fin (N + 1)) (x : ι) => K x) f)
    rw [hd]
    exact h0
  · change (fun t => planeTimeAllMomentCarrierToLp (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      0 t) =ᵐ[volume.restrict (Set.Icc a b)] fun _ => 0
    rw [map_zero]
    exact Lp.coeFn_zero _ _ _

/-- The next level of a word, from the response to the insertion carrier `g` of the previous
level: its scalar chain, its representation and the carrier of its forcing. -/
theorem wordLevel_next (K : ι → ℕ) {a b : ℝ} (ϖ ρ : ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (N : ℕ) (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (Y : ℕ → ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (j : Fin N) (g : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (hY : ∀ x, Y (j.val + 1) x = R x (g x)) :
    ∃ s' : Weighted.ScalarLevelState (fun x => K x) h,
      WordLevelPred K a b ϖ ρ M v N f Y j.succ s' ∧
      ∀ x, PlaneTimeAllMomentRepresents (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (g x)
        (s'.F x) := by
  choose F u w hchain hF hw using fun x => hR x (g x)
  refine ⟨⟨fun x => u x (), fun x => w x (), fun x => F x⟩,
    ⟨?_, fun x => ?_, fun hj => absurd hj (Fin.succ_ne_zero j), fun x => ⟨g x, hF x⟩⟩, hF⟩
  · have hd : (fun (_ : Fin 1) (i : ι) =>
        Weighted.wordLevelDatum (fun (_ : Fin (N + 1)) (x : ι) => K x) f j.succ i) =
        fun _ _ => 0 :=
      funext fun _ => funext (Weighted.wordLevelDatum_succ (fun (_ : Fin (N + 1)) (x : ι) => K x) f j)
    rw [hd]
    exact scalarPlaneChain_of_components K a b v (fun t _ => M t) (fun _ => 0)
      (fun x => F x) (fun x => u x ()) (fun x => w x ()) fun x => hchain x
  · change PlaneTimeAllMomentRepresents (K x + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Y (j.val + 1) x) (w x ())
    rw [hY x]
    exact hw x

/-- The step relation for a source insertion. -/
theorem wordLevel_rel_source {D : ℕ} (K : ι → ℕ) {a b : ℝ} (ϖ ρ : ℝ)
    (HS : ∀ i, ℝ → (∀ j, PlaneHk Set.univ (K j + 1) (h j)) → Vec 2 →
      PiLp 2 (fun _ : Fin 2 => h i))
    {Sop : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
          (volume.restrict (Set.Icc a b))}
    (hSraw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => HS i t (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) (X j) t)) (Sop i))
    (ML SL : CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ) (hSL : SL.positive = false)
    (hfluxS : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ),
      t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux SL (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 0 X₀ δ W t z) = HS x t W)
    (wd : List Bool) (j : Fin wd.length) (hc : wd.reverse.getD j.val false = true)
    {Yc : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))}
    (s s' : Weighted.ScalarLevelState (fun x => K x) h)
    (hrep : ∀ x, PlaneTimeAllMomentRepresents (K x + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Yc x) (s.w x))
    (hF : ∀ x, PlaneTimeAllMomentRepresents (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Sop x Yc) (s'.F x)) :
    WordLevelRel K a b (blockWordLetters ML SL wd) X₀ δ j s s' := by
  intro x
  have hjlt : j.val < wd.reverse.length := by rw [List.length_reverse]; exact j.2
  have hlj : blockWordLetters ML SL wd j = SL := by
    simp only [blockWordLetters]
    rw [← List.getD_eq_getElem _ false hjlt, hc, ite_eq_left rfl]
  have hL : ∀ (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ), t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux (blockWordLetters ML SL wd j)
        (fun p : Fin (wd.length + 1) × ι => K p.2) (j.succ, x) (fun u => (j.castSucc, u)) x
        (if (blockWordLetters ML SL wd j).positive then 1 else 0) X₀ δ W t z) = HS x t W := by
    intro W t ht
    rw [hlj, hSL]
    exact hfluxS wd.length j x W t ht
  exact level_readout_letterFlux K ϖ ρ x wd.length j _ _ X₀ δ (fun t W => HS x t W) hL
    (Sop x Yc) (s'.F x) (hF x) Yc s.w hrep (hSraw x Yc)

/-- The step relation for a metric insertion. -/
theorem wordLevel_rel_metric {D : ℕ} (K : ι → ℕ) {a b : ℝ} (ϖ ρ : ℝ)
    (HD : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) → Vec 2 → PiLp 2 (fun _ : Fin 2 => h i))
    {Dop : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
          (volume.restrict (Set.Icc a b))}
    (hDraw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => HD i t (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) X t)) (Dop i))
    (ML SL : CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ) (hML : ML.positive = true)
    (hfluxM : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ),
      t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux ML (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 1 X₀ δ W t z) = HD x t (W x))
    (wd : List Bool) (j : Fin wd.length) (hc : ¬ wd.reverse.getD j.val false = true)
    {Yc : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))}
    (s s' : Weighted.ScalarLevelState (fun x => K x) h)
    (hrep : ∀ x, PlaneTimeAllMomentRepresents (K x + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Yc x) (s.w x))
    (hF : ∀ x, PlaneTimeAllMomentRepresents (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Dop x (Yc x)) (s'.F x)) :
    WordLevelRel K a b (blockWordLetters ML SL wd) X₀ δ j s s' := by
  intro x
  have hjlt : j.val < wd.reverse.length := by rw [List.length_reverse]; exact j.2
  have hlj : blockWordLetters ML SL wd j = ML := by
    simp only [blockWordLetters]
    rw [← List.getD_eq_getElem _ false hjlt, ite_eq_right hc]
  have hL : ∀ (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ), t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux (blockWordLetters ML SL wd j)
        (fun p : Fin (wd.length + 1) × ι => K p.2) (j.succ, x) (fun u => (j.castSucc, u)) x
        (if (blockWordLetters ML SL wd j).positive then 1 else 0) X₀ δ W t z) =
        HD x t (W x) := by
    intro W t ht
    rw [hlj, hML]
    exact hfluxM wd.length j x W t ht
  exact level_readout_letterFlux K ϖ ρ x wd.length j _ _ X₀ δ (fun t W => HD x t (W x)) hL
    (Dop x (Yc x)) (s'.F x) (hF x) Yc s.w hrep (hDraw x (Yc x))

/-- **Word chains from responses.** -/
theorem exists_wordChain_of_responses {D : ℕ} (hD : 2 ≤ D) (K : ι → ℕ) {a b : ℝ} (ϖ ρ : ℝ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (Dop : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
          (volume.restrict (Set.Icc a b)))
    (Sop : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
          (volume.restrict (Set.Icc a b)))
    (HD : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) → Vec 2 → PiLp 2 (fun _ : Fin 2 => h i))
    (HS : ∀ i, ℝ → (∀ j, PlaneHk Set.univ (K j + 1) (h j)) → Vec 2 →
      PiLp 2 (fun _ : Fin 2 => h i))
    (hDraw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => HD i t (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) X t)) (Dop i))
    (hSraw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => HS i t (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) (X j) t)) (Sop i))
    (ML SL : CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ) (hML : ML.positive = true)
    (hSL : SL.positive = false)
    (hfluxM : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ),
      t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux ML (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 1 X₀ δ W t z) = HD x t (W x))
    (hfluxS : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ),
      t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux SL (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 0 X₀ δ W t z) = HS x t W)
    (wd : List Bool) (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (u0 : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i)) (w0 : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (h0 : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u0 i) (fun _ i => w0 i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z i) (w0 i)) :
    ∃ (u : ∀ (_ : Fin (wd.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (K x) (h x))
      (w wl : ∀ (_ : Fin (wd.length + 1)) (x : ι), ℝ → PlaneHk Set.univ (K x + 1) (h x))
      (Fl : ∀ (_ : Fin (wd.length + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x))),
      IsPlaneChain (wordChainData M (blockWordLetters ML SL wd) X₀ δ) (fun _ x => K x) a b v f
        (fun _ _ _ => 0) u w ∧
      (∀ (j : Fin (wd.length + 1)) x,
        PlaneTimeAllMomentRepresents (K x + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
          (wordLevelCarrier (nativeDiagonalResponseOperator R Dop)
            (nativeComponentResponseOperator R Sop) wd Z j.val x) (wl j x) ∧
        ∀ᵐ t ∂volume.restrict (Set.Icc a b),
          truncatePlaneHk (Nat.le_succ (K x)) (wl j x t) = u j x t) ∧
      ∀ j : Fin (wd.length + 1),
        IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
          (fun _ i => Weighted.wordLevelDatum (fun (_ : Fin (wd.length + 1)) (x : ι) => K x) f j i)
          (fun _ i => Fl j i) (fun _ i => u j i) (fun _ i => wl j i) ∧
        ∀ x, ∃ g : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h x)) (K x) ϖ ρ 0
          (volume.restrict (Set.Icc a b)),
          PlaneTimeAllMomentRepresents (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b)) g (Fl j x) := by
  classical
  let Y := wordLevelCarrier (nativeDiagonalResponseOperator R Dop)
    (nativeComponentResponseOperator R Sop) wd Z
  have hstep : ∀ (j : Fin wd.length) (s : Weighted.ScalarLevelState (fun x => K x) h),
      WordLevelPred K a b ϖ ρ M v wd.length f Y j.castSucc s →
      ∃ s', WordLevelPred K a b ϖ ρ M v wd.length f Y j.succ s' ∧
        WordLevelRel K a b (blockWordLetters ML SL wd) X₀ δ j s s' := by
    intro j s hs
    by_cases hc : wd.reverse.getD j.val false = true
    · obtain ⟨s', hs', hF⟩ := wordLevel_next K ϖ ρ M v wd.length f Y R hR j
        (fun x => Sop x (Y j.val)) (fun x => by
          change (if wd.reverse.getD j.val false then nativeComponentResponseOperator R Sop
            else nativeDiagonalResponseOperator R Dop) (Y j.val) x = _
          rw [ite_eq_left hc]
          rfl)
      exact ⟨s', hs', wordLevel_rel_source K ϖ ρ HS hSraw ML SL X₀ δ hSL hfluxS wd j hc s s'
        hs.2.1 hF⟩
    · obtain ⟨s', hs', hF⟩ := wordLevel_next K ϖ ρ M v wd.length f Y R hR j
        (fun x => Dop x (Y j.val x)) (fun x => by
          change (if wd.reverse.getD j.val false then nativeComponentResponseOperator R Sop
            else nativeDiagonalResponseOperator R Dop) (Y j.val) x = _
          rw [ite_eq_right hc]
          rfl)
      exact ⟨s', hs', wordLevel_rel_metric K ϖ ρ HD hDraw ML SL X₀ δ hML hfluxM wd j hc s s'
        hs.2.1 hF⟩
  obtain ⟨s, hs, hr⟩ := Weighted.exists_finite_chronological_family
    (fun _ => Weighted.ScalarLevelState (fun x => K x) h)
    (fun j s => WordLevelPred K a b ϖ ρ M v wd.length f Y j s)
    (fun j s s' => WordLevelRel K a b (blockWordLetters ML SL wd) X₀ δ j s s')
    (wordLevel_zero K ϖ ρ M v wd.length f Y u0 w0 h0 hZ) hstep
  have hz := (hs 0).2.2.1 rfl
  have hflux := Weighted.wordScalarFlux_agreement hD M (blockWordLetters ML SL wd)
    (fun (_ : Fin (wd.length + 1)) (x : ι) => K x) X₀ δ a b s hz hr
  obtain ⟨w, hw⟩ := Weighted.word_native_solution_pack M (blockWordLetters ML SL wd)
    (fun (_ : Fin (wd.length + 1)) (x : ι) => K x) X₀ δ a b v f s (fun j => (hs j).1) hflux
  refine ⟨fun j => (s j).u, w, fun j => (s j).w, fun j => (s j).F, hw,
    fun j x => ⟨(hs j).2.1 x, ?_⟩, fun j => ⟨(hs j).1, (hs j).2.2.2⟩⟩
  have hc := (hs j).1
  unfold IsPlaneChainFrom IsCoupledWeakSolutionPlane at hc
  exact hc.2.2.1 (0, x)

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleJointProofs
namespace AVRegularity.CycleJointProofs.Assembly

/-! **Word sums and continuous traces**.

* `finiteResponse_sum_eq_blockWords`: the retained sum `Σ_{j ≤ J} Σ_{k ≤ H} finiteResponse 1 D S Z j k`
  is the sum over `blockWords J H` of the last level carriers of the words (words with different
  numbers of metric and source insertions are different).
* `planeTimeAllMomentRepresents_sum`: representation of finite sums.
* `eqOn_of_same_carrier_sum`, `eqOn_of_same_carrier_linear`: a continuous curve whose `H^{K+1}`
  lift is represented by a carrier `W` is, on the window, the sum (or the linear combination) of
  continuous curves whose lifts are represented by carriers summing (combining) to `W`. -/

section WordSum

variable {V : Type*} [AddCommGroup V] [Module ℝ V]

theorem blockWords_pairwiseDisjoint_inner (j H : ℕ) :
    (↑(Finset.range (H + 1)) : Set ℕ).PairwiseDisjoint fun k => responseWordSet j k := by
  intro k _ k' _ hkk'
  refine Finset.disjoint_left.2 fun w hw hw' => hkk' ?_
  rw [mem_responseWordSet_iff] at hw hw'
  exact hw.2.symm.trans hw'.2

theorem blockWords_pairwiseDisjoint_outer (J H : ℕ) :
    (↑(Finset.range (J + 1)) : Set ℕ).PairwiseDisjoint fun j =>
      (Finset.range (H + 1)).biUnion fun k => responseWordSet j k := by
  intro j _ j' _ hjj'
  refine Finset.disjoint_left.2 fun w hw hw' => hjj' ?_
  obtain ⟨k, -, hk⟩ := Finset.mem_biUnion.1 hw
  obtain ⟨k', -, hk'⟩ := Finset.mem_biUnion.1 hw'
  rw [mem_responseWordSet_iff] at hk hk'
  omega

/-- The retained sum is the sum over the words of their last level carriers. -/
theorem finiteResponse_sum_eq_blockWords (Dop Sop : Module.End ℝ V) (Z : V) (J H : ℕ) :
    ∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1), finiteResponse 1 Dop Sop Z j k =
      ∑ wd ∈ blockWords J H, wordLevelCarrier Dop Sop wd Z wd.length := by
  unfold blockWords
  rw [Finset.sum_biUnion (blockWords_pairwiseDisjoint_outer J H)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_biUnion (blockWords_pairwiseDisjoint_inner j H)]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← finiteResponseOperator_apply, finiteResponseOperator_eq_responseWordSet_sum,
    LinearMap.sum_apply]
  exact Finset.sum_congr rfl fun wd _ => (wordLevelCarrier_length Dop Sop wd Z).symm

end WordSum

section Trace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- Representation of finite sums. -/
theorem planeTimeAllMomentRepresents_sum {α : Type*} (s : Finset α) (K : ℕ) (ϖ ρ : ℝ)
    (zc : Vec 2) (μ : Measure ℝ) (W : α → PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ)
    (w : α → ℝ → PlaneHk Set.univ K E)
    (hw : ∀ a ∈ s, PlaneTimeAllMomentRepresents K ϖ ρ zc μ (W a) (w a)) :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ (∑ a ∈ s, W a) (fun t => ∑ a ∈ s, w a t) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    change (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (∑ a ∈ (∅ : Finset α), W a) t)
      =ᵐ[μ] fun t => ∑ a ∈ (∅ : Finset α), w a t
    simp only [Finset.sum_empty, map_zero]
    exact Lp.coeFn_zero _ _ _
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    have hs := ih fun b hb => hw b (Finset.mem_insert_of_mem hb)
    have h1 := planeTimeAllMomentRepresents_add K ϖ ρ zc μ (W a) (∑ b ∈ s, W b) (w a)
      (fun t => ∑ b ∈ s, w b t) (hw a (Finset.mem_insert_self a s)) hs
    refine h1.trans (Filter.Eventually.of_forall fun t => ?_)
    simp only [Finset.sum_insert ha]

/-- A continuous curve whose lift is represented by `W` is the sum of continuous curves whose
lifts are represented by carriers summing to `W`. -/
theorem eqOn_of_same_carrier_sum {α : Type*} (s : Finset α) (K : ℕ) (ϖ ρ a b : ℝ)
    (hab : a < b)
    (W : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (Ws : α → PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (hW : W = ∑ c ∈ s, Ws c)
    (u : ℝ → PlaneHk Set.univ K E) (w : ℝ → PlaneHk Set.univ (K + 1) E)
    (hu : ContinuousOn u (Set.Icc a b))
    (htr : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncatePlaneHk (Nat.le_succ K) (w t) = u t)
    (hw : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) W w)
    (us : α → ℝ → PlaneHk Set.univ K E) (ws : α → ℝ → PlaneHk Set.univ (K + 1) E)
    (hus : ∀ c ∈ s, ContinuousOn (us c) (Set.Icc a b))
    (htrs : ∀ c ∈ s, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ K) (ws c t) = us c t)
    (hws : ∀ c ∈ s, PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Ws c) (ws c)) :
    Set.EqOn u (fun t => ∑ c ∈ s, us c t) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun t => ∑ c ∈ s, us c t) (Set.Icc a b) :=
    continuousOn_finsetSum s hus
  have htr' : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ K) (∑ c ∈ s, ws c t) = ∑ c ∈ s, us c t := by
    have hall : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ c ∈ s,
        truncatePlaneHk (Nat.le_succ K) (ws c t) = us c t :=
      (Filter.eventually_all_finset s).2 htrs
    filter_upwards [hall] with t ht
    rw [map_sum]
    exact Finset.sum_congr rfl ht
  have hrep : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) W
      (fun t => ∑ c ∈ s, ws c t) := by
    rw [hW]
    exact planeTimeAllMomentRepresents_sum s (K + 1) ϖ ρ 0 _ Ws ws hws
  exact planeAllMoment_same_carrier_continuous_traces K ϖ ρ a b hab 0 W u
    (fun t => ∑ c ∈ s, us c t) w (fun t => ∑ c ∈ s, ws c t) hu hcont htr htr' hw hrep

end Trace

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **The retained endpoint as a sum of word chains**.

`wordGeometry_of_retained`: from the retained structure on one block (the frozen-metric response
`R`, the insertions `Dop`, `Sop` with raw readouts equal to the letter fluxes, the scalar chain `Z`
of a linear datum `V₀`, and an endpoint `T ξ` that is the continuous trace at `τ` of the retained
sum `Wret ξ = Σ_{j ≤ J} Σ_{k ≤ H} finiteResponse 1 (R ∘ Dop) (R ∘ Sop) (Z ξ) j k`), the word chains of
the words with at most `J` metric and `H` source insertions exist, are linear in the datum, have
finite moments at every time of the window (from a finiteness principle for scalar chains), and
their last values at `τ` sum to `T ξ`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
  AVRegularity.CycleJointProofs

namespace AVRegularity.CycleJointProofs.Assembly

section Smul

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance wordGeometryNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  inferInstance
local instance wordGeometryModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) := inferInstance
local instance wordGeometryLpAdd (k : ℕ) (μ : Measure ℝ) :
    AddCommGroup (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance
local instance wordGeometryLpModule (k : ℕ) (μ : Measure ℝ) :
    Module ℝ (Lp (PlaneHk Set.univ k E) 2 μ) := inferInstance

/-- Representation of scalar multiples. -/
theorem planeTimeAllMomentRepresents_smul (K : ℕ) (ϖ ρ : ℝ) (zc : Vec 2) (μ : Measure ℝ)
    (c : ℝ) (f : PlaneTimeAllMomentCarrier (E := E) K ϖ ρ zc μ) (w : ℝ → PlaneHk Set.univ K E)
    (hf : PlaneTimeAllMomentRepresents K ϖ ρ zc μ f w) :
    PlaneTimeAllMomentRepresents K ϖ ρ zc μ (c • f) (fun t => c • w t) := by
  change (fun t => planeTimeAllMomentCarrierToLp K ϖ ρ zc μ (c • f) t) =ᵐ[μ] _
  rw [map_smul]
  filter_upwards [Lp.coeFn_smul c (planeTimeAllMomentCarrierToLp K ϖ ρ zc μ f), hf] with t ht hft
  rw [ht, Pi.smul_apply]
  exact congrArg (c • ·) hft

/-- A continuous curve whose lift is represented by `c • W + W'` is `c • u + u'`. -/
theorem eqOn_of_same_carrier_linear (K : ℕ) (ϖ ρ a b : ℝ) (hab : a < b) (c : ℝ)
    (W W' : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (u u' u'' : ℝ → PlaneHk Set.univ K E) (w w' w'' : ℝ → PlaneHk Set.univ (K + 1) E)
    (hu : ContinuousOn u (Set.Icc a b)) (hu' : ContinuousOn u' (Set.Icc a b))
    (hu'' : ContinuousOn u'' (Set.Icc a b))
    (htr : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncatePlaneHk (Nat.le_succ K) (w t) = u t)
    (htr' : ∀ᵐ t ∂volume.restrict (Set.Icc a b), truncatePlaneHk (Nat.le_succ K) (w' t) = u' t)
    (htr'' : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ K) (w'' t) = u'' t)
    (hw : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) W w)
    (hw' : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) W' w')
    (hw'' : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (c • W + W') w'') :
    Set.EqOn u'' (fun t => c • u t + u' t) (Set.Icc a b) := by
  have hcont : ContinuousOn (fun t => c • u t + u' t) (Set.Icc a b) :=
    (hu.const_smul c).add hu'
  have htrc : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      truncatePlaneHk (Nat.le_succ K) (c • w t + w' t) = c • u t + u' t := by
    filter_upwards [htr, htr'] with t ht ht'
    rw [map_add, map_smul, ht, ht']
  have hrep : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (c • W + W') (fun t => c • w t + w' t) :=
    planeTimeAllMomentRepresents_add (K + 1) ϖ ρ 0 _ (c • W) W' (fun t => c • w t) w'
      (planeTimeAllMomentRepresents_smul (K + 1) ϖ ρ 0 _ c W w hw) hw'
  exact planeAllMoment_same_carrier_continuous_traces K ϖ ρ a b hab 0 (c • W + W') u''
    (fun t => c • u t + u' t) w'' (fun t => c • w t + w' t) hu'' hcont htr'' htrc hw'' hrep

/-- A field that truncates to the same curve as a represented lift has the lift's finite
time-integrated moments. -/
theorem field_moment_ne_top_of_carrier (K : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (W : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 μ) (u : ℝ → PlaneHk Set.univ K E)
    (w wl : ℝ → PlaneHk Set.univ (K + 1) E)
    (hW : PlaneTimeAllMomentRepresents (K + 1) ϖ ρ 0 μ W wl)
    (hl : ∀ᵐ t ∂μ, truncatePlaneHk (Nat.le_succ K) (wl t) = u t)
    (hw : ∀ᵐ t ∂μ, truncatePlaneHk (Nat.le_succ K) (w t) = u t) (n : ℕ) :
    (∫⁻ t, weightedFactorialNormSq n ϖ 0 ρ (K + 1) (w t) ∂μ) ≠ ⊤ := by
  have heq : (fun t => weightedFactorialNormSq n ϖ 0 ρ (K + 1) (w t)) =ᵐ[μ]
      fun t => weightedFactorialNormSq n ϖ 0 ρ (K + 1)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 μ W t) := by
    filter_upwards [hW, hl, hw] with t hWt hlt hwt
    have hwl : w t = wl t := truncatePlaneHk_injective (Nat.le_succ K) (hwt.trans hlt.symm)
    rw [hwl, hWt]
  rw [lintegral_congr_ae heq]
  exact planeTimeAllMomentCarrier_moment (K + 1) ϖ ρ 0 μ W n

end Smul

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [Fintype ι] [∀ i, FiniteDimensional ℝ (h i)] in
/-- The datum of every level of a word has finite moments when the word's datum has. -/
theorem wordLevelDatum_weighted_ne_top {N : ℕ} (K : ι → ℕ) (ϖ ρ : ℝ)
    (f : ∀ x, PlaneHk Set.univ (K x) (h x))
    (hf : ∀ n x, weightedFactorialNormSq n ϖ 0 ρ (K x) (f x) ≠ ⊤) (j : Fin (N + 1)) (n : ℕ)
    (x : ι) :
    weightedFactorialNormSq n ϖ 0 ρ (K x)
      (Weighted.wordLevelDatum (fun (_ : Fin (N + 1)) (y : ι) => K y) f j x) ≠ ⊤ := by
  unfold Weighted.wordLevelDatum
  split_ifs with hj
  · subst hj
    exact hf n x
  · rw [Weighted.weightedFactorialNormSq_zero_carrier]
    exact ENNReal.zero_ne_top

/-- **The retained endpoint as a sum of word chains.** -/
theorem wordGeometry_of_retained {X : Type*} [AddCommGroup X] [Module ℝ X] {D : ℕ} (hD : 2 ≤ D)
    (K : ι → ℕ) {a b : ℝ} (hab : a < b) (ϖ ρ : ℝ) (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2)
    (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (Dop : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
          (volume.restrict (Set.Icc a b)))
    (Sop : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
          (volume.restrict (Set.Icc a b)))
    (HD : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i) → Vec 2 → PiLp 2 (fun _ : Fin 2 => h i))
    (HS : ∀ i, ℝ → (∀ j, PlaneHk Set.univ (K j + 1) (h j)) → Vec 2 →
      PiLp 2 (fun _ : Fin 2 => h i))
    (hDraw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => HD i t (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) X t)) (Dop i))
    (hSraw : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (fun X t => HS i t (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) (X j) t)) (Sop i))
    (ML SL : CycleLetter ι h D) (X₀ : Vec 2) (δ : ℝ) (hML : ML.positive = true)
    (hSL : SL.positive = false)
    (hfluxM : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ),
      t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux ML (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 1 X₀ δ W t z) = HD x t (W x))
    (hfluxS : ∀ (N : ℕ) (j : Fin N) (x : ι) (W : ∀ u, PlaneHk Set.univ (K u + 1) (h u)) (t : ℝ),
      t ∈ Set.Icc a b →
      (fun z => Weighted.letterAdmissibleFlux SL (fun p : Fin (N + 1) × ι => K p.2) (j.succ, x)
        (fun u => (j.castSucc, u)) x 0 X₀ δ W t z) = HS x t W)
    (J H : ℕ) (V₀ : X →ₗ[ℝ] (∀ i, PlaneHk Set.univ (K i) (h i)))
    (hf : ∀ ξ n i, weightedFactorialNormSq n ϖ 0 ρ (K i) (V₀ ξ i) ≠ ⊤)
    (u0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w0 : X → ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (Z : X →ₗ[ℝ] (∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))))
    (h0 : ∀ ξ, IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => V₀ ξ i) (fun _ _ _ => 0) (fun _ i => u0 ξ i) (fun _ i => w0 ξ i))
    (hZ : ∀ ξ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z ξ i) (w0 ξ i))
    (hfin : ∀ (F : ∀ x, ℝ → PlaneHk Set.univ (K x) (PiLp 2 (fun _ : Fin 2 => h x)))
      (f : ∀ x, PlaneHk Set.univ (K x) (h x)) (u : ∀ x, ℝ → PlaneHk Set.univ (K x) (h x))
      (w : ∀ x, ℝ → PlaneHk Set.univ (K x + 1) (h x)),
      (∀ n x, weightedFactorialNormSq n ϖ 0 ρ (K x) (f x) ≠ ⊤) →
      (∀ x, ∃ g : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h x)) (K x) ϖ ρ 0
        (volume.restrict (Set.Icc a b)),
        PlaneTimeAllMomentRepresents (K x) ϖ ρ 0 (volume.restrict (Set.Icc a b)) g (F x)) →
      IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ x => K x) a b v
        (fun _ x => f x) (fun _ x => F x) (fun _ x => u x) (fun _ x => w x) →
      ∀ n x t, t ∈ Set.Icc a b → weightedFactorialNormSq n ϖ 0 ρ (K x) (u x t) ≠ ⊤)
    (T : X → ∀ i, PlaneHk Set.univ (K i) (h i)) (τ : ℝ) (hτ : τ ∈ Set.Icc a b)
    (hT : ∀ ξ, ∃ (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      (∀ i, ContinuousOn (u i) (Set.Icc a b)) ∧
      (∀ i, ∀ᵐ t ∂volume.restrict (Set.Icc a b),
        truncatePlaneHk (Nat.le_succ (K i)) (w i t) = u i t) ∧
      (∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        ((∑ j ∈ Finset.range (J + 1), ∑ k ∈ Finset.range (H + 1),
          finiteResponse 1 (nativeDiagonalResponseOperator R Dop)
            (nativeComponentResponseOperator R Sop) (Z ξ) j k) i) (w i)) ∧
      ∀ i, T ξ i = u i τ) :
    ∃ (uW : ∀ wd : List Bool, X → ∀ (_ : Fin (wd.length + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (K x) (h x))
      (wW : ∀ wd : List Bool, X → ∀ (_ : Fin (wd.length + 1)) (x : ι), ℝ →
        PlaneHk Set.univ (K x + 1) (h x)),
      (∀ wd ξ, IsPlaneChain (wordChainData M (blockWordLetters ML SL wd) X₀ δ) (fun _ x => K x)
        a b v (V₀ ξ) (fun _ _ _ => 0) (uW wd ξ) (wW wd ξ)) ∧
      (∀ wd (c : ℝ) (ξ ξ' : X) j x, ∀ t ∈ Set.Icc a b,
        uW wd (c • ξ + ξ') j x t = c • uW wd ξ j x t + uW wd ξ' j x t) ∧
      (∀ wd ξ r x, ∀ t ∈ Set.Icc a b,
        weightedFactorialNormSq r ϖ 0 ρ (K x) (uW wd ξ (Fin.last _) x t) ≠ ⊤) ∧
      (∀ wd ξ j x r,
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq r ϖ 0 ρ (K x + 1) (wW wd ξ j x t)) ≠ ⊤) ∧
      ∀ ξ i, T ξ i = ∑ wd ∈ blockWords J H, uW wd ξ (Fin.last _) i τ := by
  classical
  have hex := fun (wd : List Bool) (ξ : X) => exists_wordChain_of_responses hD K ϖ ρ M v R hR
    Dop Sop HD HS hDraw hSraw ML SL X₀ δ hML hSL hfluxM hfluxS wd (V₀ ξ) (u0 ξ) (w0 ξ) (Z ξ)
    (h0 ξ) (hZ ξ)
  choose uW wW wlW FlW hchain hrep hlev using hex
  refine ⟨uW, wW, hchain, ?_, ?_, ?_, ?_⟩
  · intro wd c ξ ξ' j x t ht
    have hcont (η : X) : ContinuousOn (uW wd η j x) (Set.Icc a b) := by
      have hc := hchain wd η
      unfold IsPlaneChain IsCoupledWeakSolutionPlane at hc
      exact hc.1 (j, x)
    have hY : wordLevelCarrier (nativeDiagonalResponseOperator R Dop)
        (nativeComponentResponseOperator R Sop) wd (Z (c • ξ + ξ')) j.val x =
        c • wordLevelCarrier (nativeDiagonalResponseOperator R Dop)
          (nativeComponentResponseOperator R Sop) wd (Z ξ) j.val x +
        wordLevelCarrier (nativeDiagonalResponseOperator R Dop)
          (nativeComponentResponseOperator R Sop) wd (Z ξ') j.val x := by
      rw [map_add, map_smul, wordLevelCarrier_add_smul]
      rfl
    have heq := eqOn_of_same_carrier_linear (K x) ϖ ρ a b hab c _ _
      (uW wd ξ j x) (uW wd ξ' j x) (uW wd (c • ξ + ξ') j x)
      (wlW wd ξ j x) (wlW wd ξ' j x) (wlW wd (c • ξ + ξ') j x)
      (hcont ξ) (hcont ξ') (hcont (c • ξ + ξ'))
      (hrep wd ξ j x).2 (hrep wd ξ' j x).2 (hrep wd (c • ξ + ξ') j x).2
      (hrep wd ξ j x).1 (hrep wd ξ' j x).1 (by rw [← hY]; exact (hrep wd (c • ξ + ξ') j x).1)
    exact heq ht
  · intro wd ξ r x t ht
    obtain ⟨hlc, hg⟩ := hlev wd ξ (Fin.last _)
    refine hfin (fun y => FlW wd ξ (Fin.last _) y)
      (fun y => Weighted.wordLevelDatum (fun (_ : Fin (wd.length + 1)) (y : ι) => K y) (V₀ ξ)
        (Fin.last _) y) (fun y => uW wd ξ (Fin.last _) y) (fun y => wlW wd ξ (Fin.last _) y)
      ?_ hg hlc r x t ht
    exact wordLevelDatum_weighted_ne_top K ϖ ρ (V₀ ξ) (hf ξ) (Fin.last _)
  · intro wd ξ j x r
    have hc := hchain wd ξ
    unfold IsPlaneChain IsCoupledWeakSolutionPlane at hc
    exact field_moment_ne_top_of_carrier (K x) ϖ ρ _ _ (uW wd ξ j x) (wW wd ξ j x)
      (wlW wd ξ j x) (hrep wd ξ j x).1 (hrep wd ξ j x).2 (hc.2.2.1 (j, x)) r
  · intro ξ i
    obtain ⟨u, w, hu, htr, hw, hTu⟩ := hT ξ
    rw [hTu i]
    have hsum := finiteResponse_sum_eq_blockWords (nativeDiagonalResponseOperator R Dop)
      (nativeComponentResponseOperator R Sop) (Z ξ) J H
    have hcont : ∀ wd ∈ blockWords J H,
        ContinuousOn (uW wd ξ (Fin.last _) i) (Set.Icc a b) := by
      intro wd _
      have hc := hchain wd ξ
      unfold IsPlaneChain IsCoupledWeakSolutionPlane at hc
      exact hc.1 (Fin.last _, i)
    have heq := eqOn_of_same_carrier_sum (blockWords J H) (K i) ϖ ρ a b hab _
      (fun wd => wordLevelCarrier (nativeDiagonalResponseOperator R Dop)
        (nativeComponentResponseOperator R Sop) wd (Z ξ) wd.length i)
      (by rw [hsum, Finset.sum_apply]) (u i) (w i) (hu i) (htr i) (hw i)
      (fun wd => uW wd ξ (Fin.last _) i) (fun wd => wlW wd ξ (Fin.last _) i) hcont
      (fun wd _ => (hrep wd ξ (Fin.last _) i).2) (fun wd _ => (hrep wd ξ (Fin.last _) i).1)
    exact heq hτ

end AVRegularity.CycleJointProofs.Assembly
end
end
