-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneHkWindowChartH1
import AVRegularity.CycleWords.PlaneBlochEnergyOperator
public import AVRegularity.CycleJoint.PlaneCouplingSourceRowGradientTimeSchur
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The full physical coupling row is represented by every certified native map of its literal raw flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance fullRowRepresentationNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance fullRowRepresentationModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

theorem planeRaw_allMoment_couplingRow_represents
    {a b : ℝ} (hab : a ≤ b) (ϖ ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (T : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hT : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun W t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (W j) t) i) (T i))
    (W : ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hw : ∀ j, PlaneTimeAllMomentRepresents (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W j) (w j)) :
    ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (T i W) (planeCouplingFluxRow hab ρ hρ K D A hA hC w i) := by
  intro i
  apply planeRaw_allMoment_map_represents (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) _ (T i) (hT i) W
  filter_upwards [ae_all_iff.mpr hw, ae_restrict_mem measurableSet_Icc] with t ht hmem
  have he : (fun j => planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W j) t) = fun j => w j t := funext ht
  rw [he, planeValue_eq_rawValue]
  exact (univToPlane_ae ((planeCouplingFluxRow hab ρ hρ K D A hA hC w i t).val
    (valueIndex2 (K i)))).symm.trans
      (planeCouplingFluxRow_raw_value_ae hab ρ hρ K D A hA hC w i t hmem)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual full bounded physical array constructs native all-moment coupling maps before the datum. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance couplingRowAllMomentNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance couplingRowAllMomentModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

theorem exists_planeCouplingRow_allMoment_map
    {a b : ℝ} (hab : a ≤ b) (ϖ ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2)) :
    ∃ T : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)),
      ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun W t => planeRawCouplingFlux K D t A
          (fun j => planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) (W j) t) i) (T i) := by
  let μ := volume.restrict (Set.Icc a b)
  let X := ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ
  let U : X → ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j) := fun W j =>
    planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0 μ (W j)
  have hadd (W V : X) (j : ι) : U (W + V) j =ᵐ[μ] fun t => U W j t + U V j t :=
    planeTimeAllMomentCarrier_add (E := h j) (K j + 1) ϖ ρ 0 μ (W j) (V j)
  have hsmul (c : ℝ) (W : X) (j : ι) : U (c • W) j =ᵐ[μ] fun t => c • U W j t :=
    planeTimeAllMomentCarrier_smul (E := h j) (K j + 1) ϖ ρ 0 μ c (W j)
  obtain ⟨ha, hs⟩ := planeRawCouplingFlux_curve_superposition μ K D A U hadd hsmul
  have hex (i : ι) : ∃ T : X →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ,
      IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
        (fun W t => planeRawCouplingFlux K D t A (fun j => U W j t) i) T := by
    apply exists_planeRaw_allMoment_linearMap (K i) ϖ ρ 0 μ
      (fun W t => planeRawCouplingFlux K D t A (fun j => U W j t) i)
      (fun W V => ha W V i) (fun c W => hs c W i)
    intro W n
    obtain ⟨F, hF, he, hr⟩ := exists_planeCouplingFluxRow_polynomial_reserve hab ρ hρ K D
      A hA hC (U W) hAm
      (fun j => planeTimeAllMomentCarrier_memLp (E := h j) (K j + 1) ϖ ρ 0 μ (W j))
      n ϖ 0 (fun k _ j => planeTimeAllMomentCarrier_moment (E := h j)
        (K j + 1) ϖ ρ 0 μ (W j) k)
    exact ⟨F i, hF i, he n le_rfl i, hr i⟩
  choose T hT using hex
  exact ⟨T, hT⟩

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleReference AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! A time-dependent material chart acts continuously on compact smooth native Sobolev inputs. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkWindowChartPull_compact_continuousOn {K : ℕ} (a b : ℝ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j)
    (U : PlaneHk univ K E) (f : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hs : HasCompactSupport f) (hU : planeValue U =ᵐ[volume] f) :
    ContinuousOn (fun t => planeHkWindowChartPull a b hφ s B hB hb t U) (Icc a b) := by
  obtain ⟨η, hη, hsη, hfixed⟩ := exists_compact_spacetime_fixed_hilbert_field a b f hf hs
  let F := fun p : ℝ × Vec 2 => η (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)
  have hF : ContDiff ℝ (⊤ : ℕ∞) F :=
    hη.comp (contDiff_fst.prodMk ((streamFlow_joint_smooth hφ).comp
      (contDiff_fst.prodMk (contDiff_snd.prodMk contDiff_const))))
  have hsF : HasCompactSupport F := hsη.comp_homeomorph (streamFlowTimeHomeomorph hφ s)
  have he : ∀ t ∈ Icc a b, compactSpacetimeHilbertHk K F hF hsF t =
      planeHkWindowChartPull a b hφ s B hB hb t U := by
    intro t ht
    apply planeHk_eq_of_planeValue_ae
    unfold planeHkWindowChartPull
    rw [dite_eq_left ht]
    apply (compactSpacetimeHilbertHk_value_ae K F hF hsF t).trans
    apply Filter.EventuallyEq.trans _ (planeHkSmoothPullback_value_ae _ _ _ _ _ _ U).symm
    have hp := (streamFlow_measurePreserving hφ t s).quasiMeasurePreserving.ae_eq_comp hU
    filter_upwards [hp] with x hx
    change η (t, AVRegularity.streamFlow φ hφ t x s) =
      planeValue U (AVRegularity.streamFlow φ hφ t x s)
    exact (hfixed t ht _).trans hx.symm
  exact (compactSpacetimeHilbertHk_continuous K F hF hsF).continuousOn.congr
    (fun t ht => (he t ht).symm)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Every active certified family chart acts on its actual native Sobolev carriers with the reserved preparation flow budget. -/

def preparationPieceFlowJetBudget (Cchart : ℕ → ℝ) (e : ℝ) (j : ℕ) : ℝ :=
  |preparationFlowJetConstant Cchart j * e⁻¹ ^ (j - 1)|

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Every polynomial moment of compactly supported native data survives a smooth
volume-preserving pullback. No polynomial growth of the inverse chart is needed. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem planeHkSmoothPullback_polynomial_energy_ne_top_of_compact_support
    (X : Vec 2 ≃ₜ Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    (U : PlaneHk univ K E) (S : Set (Vec 2)) (hS : IsCompact S)
    (hs : ∀ a : JetIndex2 K, ∀ᵐ x ∂volume, x ∉ S → U.toFunction.jet a x = 0)
    (n : ℕ) (ϖ : ℝ) (zc : Vec 2) (ρ : ℝ) :
    weightedFactorialNormSq n ϖ zc ρ K (planeHkSmoothPullback X hX hμ B hB hb U) ≠ ⊤ := by
  let qout := planeMomentSquareRoot n ϖ zc
  let qin : Vec 2 → ℝ := fun x => qout (X.symm x)
  have hqout : Continuous qout := planeMomentSquareRoot_continuous n ϖ zc
  have hqin : Continuous qin := hqout.comp X.symm.continuous
  have hwin := planeHk_weighted_jets_memLp_of_compact_support U S hS hs qin hqin
  have hw := weighted_plane_pullback_memLp U (planeHkSmoothPullback X hX hμ B hB hb U)
    X hX hμ (planeHkSmoothPullback_value_ae X hX hμ B hB hb U)
    qout qin (fun _ => 1) hqout hqin
    (planeMomentSquareRoot_one_le n ϖ zc)
    (fun x => planeMomentSquareRoot_one_le n ϖ zc (X.symm x))
    B 1 zero_le_one (fun _ => le_refl _) hB
    (fun j hj hjK x => by simpa only [mul_one] using hb j hj hjK x)
    (fun x => by simp only [qin, X.symm_apply_apply, one_pow, mul_one, one_mul, le_refl])
    (by simpa only [JetMemL2On, Measure.restrict_univ] using hwin)
  exact weightedFactorialNormSq_ne_top_of_weighted_jets n ϖ zc ρ _ hw

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The preparation flow certificate gives actual bounded native pullbacks in both directions, and these maps are inverse on rough Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

variable (hc : IsPreparationFlowJets α q Λ m φ hφ a b Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow a b Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow a b Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (K : ℕ) (hK : K ≤ Jchart + 1)

def preparationFlowHkPullback : PlaneHk univ K E →L[ℝ] PlaneHk univ K E :=
  planeHkSmoothPullbackOperator (streamFlowHomeomorph hφ r σ)
    (streamFlow_spatial_smooth hφ r σ) (streamFlow_measurePreserving hφ r σ)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjK x =>
      (preparation_flow_positive_jets hc ha r σ hr hσ hage j hj (hjK.trans hK) x).trans
        (le_abs_self _))

theorem preparationFlowHkPullback_value_ae (U : PlaneHk univ K E) :
    planeValue (preparationFlowHkPullback hc ha r σ hr hσ hage K hK U) =ᵐ[volume]
      fun x => planeValue U (streamFlow φ hφ r x σ) := by
  exact planeHkSmoothPullback_value_ae (streamFlowHomeomorph hφ r σ)
    (streamFlow_spatial_smooth hφ r σ) (streamFlow_measurePreserving hφ r σ)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjK x =>
      (preparation_flow_positive_jets hc ha r σ hr hσ hage j hj (hjK.trans hK) x).trans
        (le_abs_self _)) U

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! The reserved material chart action is strongly continuous on every actual rough native Sobolev input. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkWindowChartPull_continuousOn {K : ℕ} (a b : ℝ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j)
    (U : PlaneHk univ K E) :
    ContinuousOn (fun t => planeHkWindowChartPull a b hφ s B hB hb t U) (Icc a b) := by
  obtain ⟨UN, fN, hUN, hsN, hvN⟩ := planeHk_exists_compact_smooth_approximation U
  let C := max (smoothPullbackNormBound B K) 1
  have hlim : Tendsto (fun N => C * dist U (UN N)) atTop (𝓝 0) := by
    have hc : Tendsto (fun _ : ℕ => U) atTop (𝓝 U) := tendsto_const_nhds
    simpa only [dist_self, mul_zero] using (hc.dist hUN).const_mul C
  have htu : TendstoUniformlyOn
      (fun N t => planeHkWindowChartPull a b hφ s B hB hb t (UN N))
      (fun t => planeHkWindowChartPull a b hφ s B hB hb t U) atTop (Icc a b) := by
    apply Metric.tendstoUniformlyOn_iff.mpr
    intro ε hε
    filter_upwards [hlim.eventually (gt_mem_nhds hε)] with N hN
    intro t ht
    rw [dist_eq_norm]
    apply (planeHkWindowChartPull_sub_norm_le a b hφ s B hB hb t ht U (UN N)).trans_lt
    have hh := mul_le_mul_of_nonneg_right (le_max_left (smoothPullbackNormBound B K) 1)
      (norm_nonneg (U - UN N))
    exact hh.trans_lt (by simpa only [dist_eq_norm] using hN)
  apply htu.continuousOn
  exact (Eventually.of_forall (fun N => planeHkWindowChartPull_compact_continuousOn a b hφ s B hB hb
    (UN N) (fN N) (hsN N).1 (hsN N).2 (hvN N))).frequently

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Output coverage and the schedule put every preparation time in the certified reference-flow range, without using a global construction-cover metric bound. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
include hc hcover

theorem preparation_reference_time_padded (t : ℝ) (ht : t ∈ Set.Icc a b) :
    t ∈ preparationPaddedWindow a b Cpad (ocTauPP α q Λ m) := by
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover ht)
  exact hc.schedule.geometry_padded p ⟨t, hp, ht⟩ ((F.piece p).output_subset hp)

theorem preparation_reference_time_age (hTau : 0 ≤ ocTauPP α q Λ m)
    (t : ℝ) (ht : t ∈ Set.Icc a b) :
    |t - (l₀ : ℝ) * ocTauPP α q Λ m| ≤ 2 * Cage * ocTauPP α q Λ m := by
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover ht)
  have hage := hc.schedule.reference_age p ⟨t, hp, ht⟩ t ((F.piece p).output_subset hp)
  have hn := mul_nonneg hc.schedule.age_pos.le hTau
  linarith

theorem preparation_reference_flow_jets
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ Jchart + 1)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => streamFlow φ hφ t y ((l₀ : ℝ) * ocTauPP α q Λ m)) x‖ ≤
      preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) j :=
  (preparation_flow_positive_jets hc.flow ha t _
    (preparation_reference_time_padded hc hcover t ht) hc.schedule.reference_mem
    (preparation_reference_time_age hc hcover hTau t ht) j hj hjJ x).trans (le_abs_self _)

theorem preparation_reference_inverse_flow_jets
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ Jchart + 1)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => streamFlow φ hφ ((l₀ : ℝ) * ocTauPP α q Λ m) y t) x‖ ≤
      preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) j :=
  (preparation_flow_positive_jets hc.flow ha _ t hc.schedule.reference_mem
    (preparation_reference_time_padded hc hcover t ht)
    (by simpa only [abs_sub_comm] using preparation_reference_time_age hc hcover hTau t ht)
    j hj hjJ x).trans (le_abs_self _)
end

/-! The schedule controls transitions to every reference time inside the covered preparation window. -/

section
variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
include hc hcover

theorem preparation_reference_time_age_sharp (t : ℝ) (ht : t ∈ Set.Icc a b) :
    |t - (l₀ : ℝ) * ocTauPP α q Λ m| ≤ Cage * ocTauPP α q Λ m := by
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover ht)
  exact hc.schedule.reference_age p ⟨t, hp, ht⟩ t ((F.piece p).output_subset hp)

theorem preparation_piece_to_window_reference_age (p : P')
    (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty)
    (r : ℝ) (hr : r ∈ (F.piece p).geometry) (σ : ℝ) (hσ : σ ∈ Set.Icc a b) :
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m := by
  calc
    |r - σ| ≤ |r - (l₀ : ℝ) * ocTauPP α q Λ m| +
        |(l₀ : ℝ) * ocTauPP α q Λ m - σ| := abs_sub_le _ _ _
    _ ≤ Cage * ocTauPP α q Λ m + Cage * ocTauPP α q Λ m :=
      add_le_add (hc.schedule.reference_age p hp r hr)
        (by simpa only [abs_sub_comm] using preparation_reference_time_age_sharp hc hcover σ hσ)
    _ = 2 * Cage * ocTauPP α q Λ m := by ring

theorem preparation_piece_window_reference_flow_jets
    (ha : 0 ≤ ocA α q Λ (m - 1)) (p : P')
    (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty)
    (r : ℝ) (hr : r ∈ (F.piece p).geometry) (σ : ℝ) (hσ : σ ∈ Set.Icc a b)
    (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ Jchart + 1) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => streamFlow φ hφ r y σ) x‖ ≤
      preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) j :=
  (preparation_flow_positive_jets hc.flow ha r σ
    (hc.schedule.geometry_padded p hp hr) (preparation_reference_time_padded hc hcover σ hσ)
    (preparation_piece_to_window_reference_age hc hcover p hp r hr σ hσ) j hj hjJ x).trans
      (le_abs_self _)

theorem preparation_piece_window_reference_inverse_flow_jets
    (ha : 0 ≤ ocA α q Λ (m - 1)) (p : P')
    (hp : ((F.piece p).output ∩ Set.Icc a b).Nonempty)
    (r : ℝ) (hr : r ∈ (F.piece p).geometry) (σ : ℝ) (hσ : σ ∈ Set.Icc a b)
    (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ Jchart + 1) (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => streamFlow φ hφ σ y r) x‖ ≤
      preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) j :=
  (preparation_flow_positive_jets hc.flow ha σ r
    (preparation_reference_time_padded hc hcover σ hσ) (hc.schedule.geometry_padded p hp hr)
    (by simpa only [abs_sub_comm] using
      preparation_piece_to_window_reference_age hc hcover p hp r hr σ hσ) j hj hjJ x).trans
      (le_abs_self _)
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual native edge maps obey the mass Schur energy estimate without a vertex count. -/

variable {ι : Type*} [Fintype ι] {E : ι → Type*}
  [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
  [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
  [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]

theorem planeAllMoment_edgeMap_mass_moment_budget
    (K : ι → ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (L : ∀ v u, PlaneTimeAllMomentCarrier (E := E u) (K u + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E v)) (K v) ϖ ρ 0 μ)
    (W : ∀ u, PlaneTimeAllMomentCarrier (E := E u) (K u + 1) ϖ ρ 0 μ)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (price : ι → ι → ℝ)
    (hp : ∀ v u, 0 ≤ price v u) (θ : ℝ) (hθ : 0 ≤ θ)
    (hrow : ∀ v, ∑ u, Real.sqrt (π u / π v) * price v u ≤ θ)
    (hcol : ∀ u, ∑ v, Real.sqrt (π u / π v) * price v u ≤ θ)
    (p n : ℕ)
    (hb : ∀ v u, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp (K v) ϖ ρ 0 μ (L v u (W u)) t) z ≤
        price v u ^ 2 * ((polynomialMomentRoot ϖ z ^ p) ^ 2 *
          planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ (W u) t) z)) :
    (∫⁻ t, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 ρ (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ ρ 0 μ (nativeFamilyEdgeForcingMap L v W) t) ∂μ) ≤
      ENNReal.ofReal (θ ^ 2) * ∫⁻ t, ∑ u, ENNReal.ofReal ((π u)⁻¹) *
        weightedGradFactorialNormSq (n + p) ϖ 0 ρ (K u)
          (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ (W u) t) ∂μ := by
  classical
  apply nativeFlux_time_moment_shift_mass_budget π (fun v => (hπ v).le) K n p ϖ ρ θ μ
  have hs : ∀ v, (fun t => planeTimeAllMomentCarrierToLp (K v) ϖ ρ 0 μ
      (nativeFamilyEdgeForcingMap L v W) t) =ᵐ[μ]
      fun t => ∑ u, planeTimeAllMomentCarrierToLp (K v) ϖ ρ 0 μ (L v u (W u)) t := by
    intro v
    rw [nativeFamilyEdgeForcingMap_apply]
    exact planeTimeAllMomentCarrier_sum_ae (K v) ϖ ρ 0 μ (fun u => L v u (W u))
  filter_upwards [ae_all_iff.mpr hs,
    ae_all_iff.mpr (fun v => ae_all_iff.mpr (hb v))] with t ht hbt
  simp only [ht]
  have hh := nativeFluxGraph_density_budget K ρ
    (fun v u => planeTimeAllMomentCarrierToLp (K v) ϖ ρ 0 μ (L v u (W u)) t)
    π hπ price hp θ hθ hrow hcol
    (fun u z => (polynomialMomentRoot ϖ z ^ p) ^ 2 *
      planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ (W u) t) z)
    (fun u z => mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg ρ _ z)) hbt
  filter_upwards [hh] with z hz
  have he : (∑ u, (π u)⁻¹ * ((polynomialMomentRoot ϖ z ^ p) ^ 2 *
      planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ (W u) t) z)) =
      (polynomialMomentRoot ϖ z ^ p) ^ 2 * ∑ u, (π u)⁻¹ *
        planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ (W u) t) z := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro u _
    ring
  rw [he] at hz
  simpa only [mul_assoc] using hz

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.CycleWords
open scoped Topology
namespace AVRegularity.CycleJointProofs

/-! Continuous native Sobolev solution traces remain continuous in the time-dependent material chart. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeHkWindowChartPull_trace_continuousOn {K : ℕ} (a b : ℝ)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j)
    (u : ℝ → PlaneHk univ K E) (hu : ContinuousOn u (Icc a b)) :
    ContinuousOn (fun t => planeHkWindowChartPull a b hφ s B hB hb t (u t)) (Icc a b) := by
  exact strongAction_trace_continuousOn (Icc a b)
    (planeHkWindowChartPull a b hφ s B hB hb) (smoothPullbackNormBound B K)
    (planeHkWindowChartPull_continuousOn a b hφ s B hB hb)
    (planeHkWindowChartPull_sub_norm_le a b hφ s B hB hb) u hu

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Certified preparation charts transfer pointwise native prices to the actual constituent seminorms. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}

theorem preparation_reference_constituent_lowering_budget (F : ChartedFamily ι h D P' Ctx)
    (hc : IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (hchart : Kmax + D + 2 ≤ Jchart)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hρ : 0 < ρ)
    (hE : 0 < ocEpsilon q Λ (m - 1)) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K
      (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
      ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (actual : ∀ p, Ctx p) (v u : ι) (γ : F.Γ v u)
    (dout : ℕ) (hdout : dout ∈ Finset.Icc 2 D) :
    coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e (ocEpsilon q Λ (m - 1)) actual v u γ dout) ≤
    ENNReal.ofReal (‖(F.identity v u γ).map‖ *
      preparationSamplingSeminormConstant D Kmax Jchart Cchart *
      (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (ocEpsilon q Λ (m - 1))⁻¹ ^ (din - dout) *
          (pointwiseMolecularJet ρ e (K v) 0
            (fun z : F.Index => ChartedFamily.Domain.onWindow F (Set.Icc tS tZ) z.1 z.2)
            (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ din I)).toReal)) := by
  classical
  let E := ocEpsilon q Λ (m - 1)
  let dom := ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)
  let M := fun din (I : DerivativeWord2 (din - 1)) =>
    pointwiseMolecularJet ρ e (K v) 0 (fun z : F.Index => dom z.1 z.2)
      (fun z => F.dimFlux ν e E z.1 z.2 v u γ din I)
  let S := ∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (din - 1), E⁻¹ ^ (din - dout) * (M din I).toReal
  by_cases hγ : (F.identity v u γ).map = 0
  · have hz : constituentPhysical (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e E actual v u γ dout = fun _ _ => 0 := by
      funext t x
      exact constituentPhysical_zero_map (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e E actual v u γ hγ dout t x
    change coefficientSeminorm ρ (K v) tS tZ
      (constituentPhysical (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e E actual v u γ dout) ≤ _
    rw [hz, coefficientSeminorm_zero_function]
    exact zero_le
  have hS : 0 ≤ S := by
    apply Finset.sum_nonneg
    intro din _
    apply Finset.sum_nonneg
    intro I _
    exact mul_nonneg (pow_nonneg (inv_nonneg.mpr hE.le) _) ENNReal.toReal_nonneg
  let B := ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart * S
  have hB : 0 ≤ B := mul_nonneg
    (mul_nonneg (norm_nonneg _) (preparationSamplingJetConstant_nonnegative _ _ _ _)) hS
  have hs : ∀ t ∈ Set.Icc tS tZ,
      ContDiff ℝ (K v : ℕ) (constituentPhysical (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e E actual v u γ dout t) := by
    intro t ht
    exact (reference_constituentPhysical_spatial_smooth F hc ν e E hE.ne' (fun v => K v + Jm)
      henv.1 actual v u γ dout ((l₀ : ℝ) * ocTauPP α q Λ m) t ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hjets : ∀ t ∈ Set.Icc tS tZ, ∀ j, j ≤ K v → ∀ x,
      ρ ^ j * ‖iteratedFDeriv ℝ j (constituentPhysical (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e E actual v u γ dout t) x‖ ≤ B := by
    intro t ht j hj x
    let ts : Set.Icc tS tZ := ⟨t, ht⟩
    let g := fun p y => nativeArrayAssembly (dout - 1) (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ (F.piece p).anchor ((l₀ : ℝ) * ocTauPP α q Λ m))
        (F.identity v u γ).maxOrder
        (fun din I => F.dimFlux ν e E p (actual p) v u γ din I t
          (streamFlow φ hφ (F.piece p).anchor y ((l₀ : ℝ) * ocTauPP α q Λ m))
          (e⁻¹ • streamFlow φ hφ (F.piece p).anchor y ((l₀ : ℝ) * ocTauPP α q Λ m))) (dout - 1) A y a)
    have hg p (hout : t ∈ (F.piece p).output) : ContDiff ℝ (K v : ℕ) (g p) := by
      exact (natural_flow_constituent_operator_smooth F ν e E hE.ne' (fun v => K v + Jm)
        dom henv.1 p (actual p) v u γ (dout - 1) φ hφ (F.piece p).anchor ((l₀ : ℝ) * ocTauPP α q Λ m) t
        (fun Y => by
          change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
          exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩)).of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
    apply positive_reference_constituentPhysical_jet_assembly F hc ν e E actual v u γ dout j
      ((l₀ : ℝ) * ocTauPP α q Λ m) ρ B hρ.le hB ts g (fun _ _ => rfl)
      (fun p hout => (hg p hout).of_le (by exact_mod_cast hj)) _ x
    intro p hout y
    have hp : ((F.piece p).output ∩ Set.Icc tS tZ).Nonempty := ⟨t, hout, ht⟩
    obtain ⟨has, hat, hage⟩ := preparation_reference_anchor_endpoints hc p hp (preparation_renewal_nonnegative α q Λ m)
    have hnchart : K v ≤ Jchart + 1 := by have hk := hK v; omega
    have hnN : j + (F.identity v u γ).maxOrder ≤ Kmax + D + 2 := by
      have hk := hK v
      have hd := (F.identity v u γ).le_D
      omega
    have hh := pointwise_molecular_native_flow_transport_uniform_budget F π hπ K Kmax hK dom ν e ρ
      hν he hE hρE (preparation_amplitude_nonnegative α q Λ (m - 1) hE.le) hρ
      Cm Jm b henv v u γ hγ p (actual p) hc.flow hnchart (Kmax + D + 2) hchart
      (F.piece p).anchor ((l₀ : ℝ) * ocTauPP α q Λ m) t has hat hage
      (fun Y => by
        change (t, Y) ∈ ((F.piece p).output ∩ Set.Icc tS tZ) ×ˢ Set.univ
        exact ⟨⟨hout, ht⟩, Set.mem_univ Y⟩) j (dout - 1) hj (by have hh := (Finset.mem_Icc.mp hdout).1; omega)
      hnN (by have hh := Finset.mem_Icc.mp hdout; omega) y
    have hr : dout - 1 + 1 = dout := by have hh := (Finset.mem_Icc.mp hdout).1; omega
    have hediff din : din - 1 - (dout - 1) = din - dout := by
      have hh := (Finset.mem_Icc.mp hdout).1
      omega
    dsimp only at hh
    simp only [hr, hediff] at hh
    change ρ ^ j * ‖iteratedFDeriv ℝ j (g p) y‖ ≤
      ‖(F.identity v u γ).map‖ * preparationSamplingJetConstant D Kmax Jchart Cchart *
        (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) at hh
    have heq : (∑ din ∈ Finset.Icc dout (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (din - 1), (M din I).toReal * E⁻¹ ^ (din - dout)) = S := by
      dsimp only [S]
      apply Finset.sum_congr rfl
      intro din _
      apply Finset.sum_congr rfl
      intro I _
      exact mul_comm _ _
    rw [heq] at hh
    exact hh
  have hh := uniform_pointwise_coefficient_seminorm ρ hρ (K v) Kmax (hK v) tS tZ
    (constituentPhysical (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e E actual v u γ dout) hs B hB hjets
  apply hh.trans_eq
  congr 1
  dsimp only [preparationSamplingSeminormConstant, B]
  ring

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory
namespace AVRegularity.CycleJointProofs

/-! Positive flow jets between any two covered preparation times. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Set.Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Set.Icc a b)
    (ha : 0 ≤ ocA α q Λ (m - 1))
include hc hcover hσ ha

theorem preparation_window_reference_time_flow_jets
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ Jchart + 1)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => streamFlow φ hφ t y σ) x‖ ≤
      preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) j := by
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover ht)
  exact preparation_piece_window_reference_flow_jets hc hcover ha p ⟨t, hp, ht⟩ t
    ((F.piece p).output_subset hp) σ hσ j hj hjJ x

theorem preparation_window_reference_time_inverse_flow_jets
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : ℕ) (hj : 1 ≤ j) (hjJ : j ≤ Jchart + 1)
    (x : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => streamFlow φ hφ σ y t) x‖ ≤
      preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)) j := by
  obtain ⟨p, hp⟩ := Set.mem_iUnion.mp (hcover ht)
  exact preparation_piece_window_reference_inverse_flow_jets hc hcover ha p ⟨t, hp, ht⟩ t
    ((F.piece p).output_subset hp) σ hσ j hj hjJ x

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! A spacetime test with a fixed spatial slice equals the genuine compact spatial native H1 test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem compactSpacetimeVectorH1_eq_fixed_test
    (η : ℝ × Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hsη : HasCompactSupport η)
    (q : Vec 2 → ℝ) (hq : ContDiff ℝ (⊤ : ℕ∞) q) (hsq : HasCompactSupport q)
    (e : E) (t : ℝ) (ht : ∀ x, η (t, x) = q x) :
    compactSpacetimeVectorH1 η hη hsη e t =
      compactSmoothHilbertH1 (fun x => q x • e) (hq.smul contDiff_const) (hsq.smul_right) := by
  apply planeH1_eq_of_value
  apply Lp.ext
  filter_upwards [compactSpacetimeVectorH1_valueOperator_ae η hη hsη e t,
    compactSmoothHilbertH1_value_ae (fun x => q x • e) (hq.smul contDiff_const) (hsq.smul_right)]
    with x hηx hqx
  rw [hηx, hqx, ht x]

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The physical inverse-flow test pulls to the intended native material H1 test. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem materialChart_native_test_cancellation {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s t : ℝ) (η : ℝ × Vec 2 → ℝ)
    (hη : ContDiff ℝ (⊤ : ℕ∞) η) (hcη : HasCompactSupport η) (e : E) :
    planeH1ChartPull hφ t s
      (compactSpacetimeVectorH1 (materialChartTestField hφ s η)
        (materialChartTestField_smooth hφ s η hη)
        (materialChartTestField_compact hφ s η hcη) e t) =
      compactSpacetimeVectorH1 η hη hcη e t := by
  apply planeH1_eq_of_value
  apply Lp.ext
  have hp := planeH1ChartPull_value_ae hφ t s
    (compactSpacetimeVectorH1 (materialChartTestField hφ s η)
      (materialChartTestField_smooth hφ s η hη)
      (materialChartTestField_compact hφ s η hcη) e t)
  have hv := (streamFlow_measurePreserving hφ t s).quasiMeasurePreserving.ae
    (compactSpacetimeVectorH1_valueOperator_ae (materialChartTestField hφ s η)
      (materialChartTestField_smooth hφ s η hη)
      (materialChartTestField_compact hφ s η hcη) e t)
  filter_upwards [hp, hv, compactSpacetimeVectorH1_valueOperator_ae η hη hcη e t]
    with y hpy hvy hηy
  rw [hpy, hηy]
  apply hvy.trans
  unfold materialChartTestField
  change η (t, AVRegularity.streamFlow φ hφ s
    (AVRegularity.streamFlow φ hφ t y s) t) • e = η (t, y) • e
  exact congrArg (fun x => η (t, x) • e) ((streamFlowHomeomorph hφ t s).left_inv y)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The actual finite native preparation source is exactly the physical Hilbert coupling flux already present in the homogeneous equation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem preparationPhysicalNativeFlux_eq_couplingRow
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E a b : ℝ) (hab : a ≤ b) (ρ : ℝ) (hρ : 0 < ρ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (hA : ∀ v u d, coefficientSeminorm ρ (K v) a b
      (edgeCoefficient F ν e E actual K v u d) ≠ ⊤)
    (hc : ∀ v u d t, t ∈ Set.Icc a b →
      ContDiff ℝ (K v : ℕ) (edgeCoefficient F ν e E actual K v u d t))
    (w : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (v : ι) :
    preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t ht v (fun u => w u t) =
      planeFluxValueOperator (E := h v) (K v)
        (planeCouplingFluxRow hab ρ hρ K D (edgeCoefficient F ν e E actual K) hA hc w v t) := by
  apply PiLp.ext
  intro k
  apply Lp.ext
  exact (preparationPhysicalNativeFlux_ae F K ν e E a b n hs actual hT he t ht v
    (fun u => w u t) hdesc k).trans
      (planeCouplingFluxRow_component_ae hab ρ hρ K D (edgeCoefficient F ν e E actual K)
        hA hc w v t ht k).symm
end

/-! A source constructed on the full preparation window is the same Hilbert coupling flux on any contained physical subwindow. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem preparationPhysicalNativeFlux_eq_subwindow_couplingRow
    (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ) (hdesc : F.IsDescending K)
    (ν e E a b : ℝ) (ρ : ℝ) (hρ : 0 < ρ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (actual : ∀ p, Ctx p) (hT : IsTorusCompatible F actual E)
    {N : ℕ} (he : e⁻¹ = N)
    (c d : ℝ) (hcd : c ≤ d) (hsub : Set.Icc c d ⊆ Set.Icc a b)
    (hAsub : ∀ v u d', coefficientSeminorm ρ (K v) c d
      (edgeCoefficient F ν e E actual K v u d') ≠ ⊤)
    (hcsub : ∀ v u d' t, t ∈ Set.Icc c d →
      ContDiff ℝ (K v : ℕ) (edgeCoefficient F ν e E actual K v u d' t))
    (w : ∀ u, ℝ → PlaneHk Set.univ (K u + 1) (h u))
    (t : ℝ) (ht : t ∈ Set.Icc c d) (v : ι) :
    preparationPhysicalNativeFlux F K ν e E a b n hs actual hT he t (hsub ht) v (fun u => w u t) =
      planeFluxValueOperator (E := h v) (K v)
        (planeCouplingFluxRow hcd ρ hρ K D (edgeCoefficient F ν e E actual K) hAsub hcsub w v t) := by
  apply PiLp.ext
  intro k
  apply Lp.ext
  exact (preparationPhysicalNativeFlux_ae F K ν e E a b n hs actual hT he t (hsub ht) v
    (fun u => w u t) hdesc k).trans
      (planeCouplingFluxRow_component_ae hcd ρ hρ K D (edgeCoefficient F ν e E actual K)
        hAsub hcsub w v t ht k).symm
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The common preparation reference chart has actual native Sobolev pullback and inverse operators, with every reserved bound derived from coverage and the chart certificate. -/

section
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

def preparationReferenceHkWindowPull (t : ℝ) (U : PlaneHk univ J E) : PlaneHk univ J E :=
  planeHkWindowChartPull a b hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun r hr j hj hjJ x =>
      preparation_reference_flow_jets hc hcover hTau ha r hr j hj (hjJ.trans hJ) x) t U

def preparationReferenceHkInverse (t : ℝ) (ht : t ∈ Icc a b) :
    PlaneHk univ J E →L[ℝ] PlaneHk univ J E :=
  planeHkSmoothPullbackOperator (streamFlowHomeomorph hφ ((l₀ : ℝ) * ocTauPP α q Λ m) t)
    (streamFlow_spatial_smooth hφ _ t) (streamFlow_measurePreserving hφ _ t)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_reference_inverse_flow_jets hc hcover hTau ha t ht j hj (hjJ.trans hJ) x)

theorem preparationReferenceHkInverse_windowPull (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    preparationReferenceHkInverse hc hcover hTau ha J hJ t ht
      (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t U) = U := by
  unfold preparationReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact planeHkSmoothPullback_inverse (streamFlowHomeomorph hφ t _)
    (streamFlow_spatial_smooth hφ t _) (streamFlow_spatial_smooth hφ _ t)
    (streamFlow_measurePreserving hφ t _) (streamFlow_measurePreserving hφ _ t)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _) (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_reference_flow_jets hc hcover hTau ha t ht j hj (hjJ.trans hJ) x)
    (fun j hj hjJ x =>
      preparation_reference_inverse_flow_jets hc hcover hTau ha t ht j hj (hjJ.trans hJ) x) U
end

/-! The common preparation reference chart has actual native Sobolev pullback and inverse operators, with every reserved bound derived from coverage and the chart certificate. -/

section
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

theorem preparationReferenceHkWindowPull_inverse (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    preparationReferenceHkWindowPull hc hcover hTau ha J hJ t
      (preparationReferenceHkInverse hc hcover hTau ha J hJ t ht U) = U := by
  unfold preparationReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact planeHkSmoothPullback_inverse (streamFlowHomeomorph hφ _ t)
    (streamFlow_spatial_smooth hφ _ t) (streamFlow_spatial_smooth hφ t _)
    (streamFlow_measurePreserving hφ _ t) (streamFlow_measurePreserving hφ t _)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _) (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_reference_inverse_flow_jets hc hcover hTau ha t ht j hj (hjJ.trans hJ) x)
    (fun j hj hjJ x =>
      preparation_reference_flow_jets hc hcover hTau ha t ht j hj (hjJ.trans hJ) x) U
end

/-! The actual fixed-time input chart is a continuous linear map. -/

section
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

def preparationReferenceHkWindowPullOperator (t : ℝ) (ht : t ∈ Icc a b) :
    PlaneHk univ J E →L[ℝ] PlaneHk univ J E :=
  planeHkSmoothPullbackOperator (streamFlowHomeomorph hφ t ((l₀ : ℝ) * ocTauPP α q Λ m))
    (streamFlow_spatial_smooth hφ t _) (streamFlow_measurePreserving hφ t _)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_reference_flow_jets hc hcover hTau ha t ht j hj (hjJ.trans hJ) x)

theorem preparationReferenceHkWindowPullOperator_apply
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ J E) :
    preparationReferenceHkWindowPullOperator hc hcover hTau ha J hJ t ht U =
      preparationReferenceHkWindowPull hc hcover hTau ha J hJ t U := by
  unfold preparationReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  rfl
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The full preparation sampling bridge from its independent pointwise certificate. -/

/-- Independent-to-sampled envelope bridge on the entire preparation window. -/
theorem preparation_reference_sampled_envelope_of_pointwise_certificate (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (b : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ b v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b →
        IsSampledEnvelope (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) π K actual tS tZ ν e (ocEpsilon q Λ (m - 1)) ρ Cprep b := by
  let C := preparationSamplingSeminormConstant D Kmax Jchart Cchart
  let Cbase := C * D * |Cm 0|
  refine ⟨max 1 Cbase, le_max_left _ _, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι h _ _ P' Ctx F π hπ K hK actual b hb hc henv
  have he : 0 < e := hρ.trans_le hρe
  have hρE : ρ ≤ ocEpsilon q Λ (m - 1) := hρe.trans heE
  have hE : 0 < ocEpsilon q Λ (m - 1) := hρ.trans_le hρE
  have hC : 0 ≤ C := preparationSamplingSeminormConstant_nonnegative _ _ _ _
  have hs : ∀ v u (γ : F.Γ v u) d, ∀ t ∈ Set.Icc tS tZ,
      ContDiff ℝ (K v : ℕ)
        (constituentPhysical (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) ν e (ocEpsilon q Λ (m - 1)) actual v u γ d t) := by
    intro v u γ d t ht
    exact (reference_constituentPhysical_spatial_smooth F hc ν e (ocEpsilon q Λ (m - 1)) hE.ne'
      (fun v => K v + Jm) henv.1 actual v u γ d ((l₀ : ℝ) * ocTauPP α q Λ m) t ht).of_le
        (by exact_mod_cast Nat.le_add_right (K v) Jm)
  have hh := sampled_envelope_of_lowering_budget (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)) π K
    (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)) actual tS tZ ν e
    (ocEpsilon q Λ (m - 1)) ρ C hν hρ hE hρE hC Cm Jm b hb henv hs
    (fun v u γ dout hdout => preparation_reference_constituent_lowering_budget F hc π hπ K Kmax hK
      hchart ν e ρ hν he hρ hE hρE Cm Jm b henv actual v u γ dout hdout)
  refine ⟨hh.1, ?_⟩
  intro v u
  exact (hh.2 v u).trans (ENNReal.ofReal_le_ofReal
    (mul_le_mul_of_nonneg_right (le_max_right 1 Cbase) (hb v u)))

end AVRegularity.CycleJointProofs
end
