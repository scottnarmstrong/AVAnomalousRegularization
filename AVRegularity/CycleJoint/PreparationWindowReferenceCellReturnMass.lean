-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PreparationReferenceSampledEnvelope
import AVRegularity.CycleJoint.PlaneJetMultiplierSuperposition

section
@[expose] public noncomputable section
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
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

def preparationWindowReferenceHkWindowPull (t : ℝ) (U : PlaneHk univ J E) : PlaneHk univ J E :=
  planeHkWindowChartPull a b hφ σ
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun r hr j hj hjJ x =>
      preparation_window_reference_time_flow_jets hc hcover σ hσ ha r hr j hj (hjJ.trans hJ) x) t U

def preparationWindowReferenceHkInverse (t : ℝ) (ht : t ∈ Icc a b) :
    PlaneHk univ J E →L[ℝ] PlaneHk univ J E :=
  planeHkSmoothPullbackOperator (streamFlowHomeomorph hφ σ t)
    (streamFlow_spatial_smooth hφ _ t) (streamFlow_measurePreserving hφ _ t)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_window_reference_time_inverse_flow_jets hc hcover σ hσ ha t ht j hj (hjJ.trans hJ) x)

theorem preparationWindowReferenceHkInverse_windowPull (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    preparationWindowReferenceHkInverse hc hcover σ hσ ha J hJ t ht
      (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U) = U := by
  unfold preparationWindowReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact planeHkSmoothPullback_inverse (streamFlowHomeomorph hφ t _)
    (streamFlow_spatial_smooth hφ t _) (streamFlow_spatial_smooth hφ _ t)
    (streamFlow_measurePreserving hφ t _) (streamFlow_measurePreserving hφ _ t)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _) (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_window_reference_time_flow_jets hc hcover σ hσ ha t ht j hj (hjJ.trans hJ) x)
    (fun j hj hjJ x =>
      preparation_window_reference_time_inverse_flow_jets hc hcover σ hσ ha t ht j hj (hjJ.trans hJ) x) U
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
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

def preparationWindowReferenceHkWindowPullOperator (t : ℝ) (ht : t ∈ Icc a b) :
    PlaneHk univ J E →L[ℝ] PlaneHk univ J E :=
  planeHkSmoothPullbackOperator (streamFlowHomeomorph hφ t σ)
    (streamFlow_spatial_smooth hφ t _) (streamFlow_measurePreserving hφ t _)
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun j hj hjJ x =>
      preparation_window_reference_time_flow_jets hc hcover σ hσ ha t ht j hj (hjJ.trans hJ) x)

theorem preparationWindowReferenceHkWindowPullOperator_apply
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ J E) :
    preparationWindowReferenceHkWindowPullOperator hc hcover σ hσ ha J hJ t ht U =
      preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U := by
  unfold preparationWindowReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  rfl
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Every actual coupled energy lift has its native higher-order material energy state. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem coupledPlane_chart_energy_state {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {D : ℕ} {K : ι → ℕ}
    {A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {u : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ) (i : ι)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K i + 1 → 0 ≤ B j)
    (hb : ∀ t ∈ Icc a b, ∀ j, 1 ≤ j → j ≤ K i + 1 → ∀ x,
      ‖iteratedFDeriv ℝ j (fun y => AVRegularity.streamFlow φ hφ t y s) x‖ ≤ B j) :
    MemLp (fun t => planeHkWindowChartPull a b hφ s B hB hb t (w i t))
      2 (volume.restrict (Icc a b)) := by
  have hd := coupledWeakSolution_h1_trace_data hs i
  apply planeHkWindowChartPull_memLp a b hφ s B hB hb (coupledPlaneL2Trace u i) (w i)
    hd.1 (hs.2.1 i)
  filter_upwards [hd.2.2] with t ht
  change coupledPlaneL2Trace u i t = planeHkValueOperator 1
    (truncatePlaneHk (by omega) (w i t)) at ht
  rw [planeHkValueOperator_truncate] at ht
  exact ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Retained finite native responses transfer to the full coupled coefficient array with an actual residual. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance retainedCoupledScalarNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance retainedCoupledScalarNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance retainedCoupledScalarCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance retainedCoupledScalarCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Lmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (f : ∀ i, PlaneHk Set.univ (K i) (h i))
  (u₀ : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)))

variable {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeComponentAllMomentResponse_retained_coupled_residual_solution
    (hab : a ≤ b) (hρ : 0 < ρ) (hD : 2 ≤ D)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d) ≠ ⊤)
    (hA' : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d t))
    (hC' : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (family : ChartedFamily ι h D P Ctx)
    (H J : ℕ) (hdepth : family.HasDepthAtMost H)
    (hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u₀ i) (fun _ i => w₀ i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z i) (w₀ i)) :
    let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
      (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
    let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    let T := ∑ n ∈ Finset.range (H + 1), U J n
    let Q := fun i => Lmetric i (W i) + nativeFamilyEdgeForcingMap Ledge i W - Lmetric i (T i)
    ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane 1 a b v D K A f
        (fun i t => F i t - planeCouplingFluxRow hab ρ hρ K D A hA' hC' w i t +
          planeCouplingFluxRow hab ρ hρ K D
            (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1))
            hA hC w i t) (fun _ _ => 0) u w ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (Q i) (F i) ∧
        PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (W i) (w i) := by
  obtain ⟨F, u, w, hs, hr⟩ :=
    planeComponentAllMomentResponse_retained_edge_mixed_solution M v K a b ϖ ρ R
      Lmetric Ledge f u₀ w₀ Z family H J hdepth hS hR hbase hZ
  refine ⟨F, u, w, ?_, hr⟩
  exact scalarPlaneChain_native_residual_construction hab ρ hρ hD (fun t _ => M t)
    hA hA' hC hC' hs

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Uniform polynomial energy of localized torus data after a scaled smooth
chart pullback, centered at the inverse image of the patch center. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem spatialPatch_scaled_pullback_energy_le {K : ℕ}
    (X : Vec 2 ≃ₜ Vec 2)
    (hX : ContDiff ℝ (⊤ : ℕ∞) (X : Vec 2 → Vec 2))
    (hμ : MeasurePreserving (X : Vec 2 → Vec 2) volume volume)
    (B : ℕ → ℝ) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j (X : Vec 2 → Vec 2) x‖ ≤ B j)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (C : ℕ → ℝ)
    (hscale : ∀ j, 1 ≤ j → j ≤ K → ρ ^ (j - 1) * B j ≤ C j)
    {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ) (N : ℕ) (hN : 0 < N)
    (k : Fin 2 → ℤ) (f : TorusHk K E)
    (L : NNReal) (hL : LipschitzWith L X.symm)
    (n : ℕ) (ϖ R : ℝ) (hϖ : 0 ≤ ϖ) (hR : 0 ≤ R)
    (hmesh : ϖ / (N : ℝ) ≤ R) :
    weightedFactorialNormSq n ϖ (X.symm (spatialPatchCenter N k)) ρ K
      (planeHkSmoothPullback X hX hμ B hB hb (spatialPatchLocalization hζ N hN k K f)) ≤
      ENNReal.ofReal ((1 + 2 * ((L : ℝ) * R) ^ 2) ^ n) *
        ENNReal.ofReal ((compositionFactorialNormBound C K) ^ 2) *
          ENNReal.ofReal (factorialNormSq ρ (spatialPatchLocalization hζ N hN k K f).val) := by
  apply planeHkScaledPullback_polynomial_energy_le_of_support X hX hμ B hB hb hρ C hscale
    (spatialPatchLocalization hζ N hN k K f) (tsupport (spatialPatchCutoff ζ N k))
    (spatialPatchLocalization_jet_support_ae hζ N hN k K f) n ϖ
    (X.symm (spatialPatchCenter N k)) _ (by positivity)
  intro x hx
  exact spatialPatch_pullback_polynomial_moment_bound hζ N hN k X L hL x hx n ϖ R hϖ hR hmesh

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual original constituent Taylor readout is zero on zero native input. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

local instance naturalTaylorRawNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k

def naturalFamilyTaylorRawConstituent (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (anchor : P → ℝ) (σ e E : ℝ) (yc : Vec 2)
    (ϖ ρ : ℝ) (μ : Measure ℝ) (v u : ι) (γ : F.Γ v u)
    (X : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ)
    (τ : ℝ) (z : Vec 2) : PiLp 2 (fun _ : Fin 2 => h v) :=
  ∑ j : Fin D, ∑ p : S,
    naturalFamilyTaylorNativeArray Ks F p.val (actual p.val) v u γ timeScale hφ
      (anchor p.val) σ e E yc (j.val + 1) τ z
      (WithLp.toLp 2 (fun I => planeJetOrder
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ X τ) (j.val + 1) I z))

theorem naturalFamilyTaylorRawConstituent_zero (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (anchor : P → ℝ) (σ e E : ℝ) (yc : Vec 2)
    (ϖ ρ : ℝ) (μ : Measure ℝ) (v u : ι) (γ : F.Γ v u) :
    ∀ᵐ τ ∂μ, naturalFamilyTaylorRawConstituent Ks F S actual K timeScale hφ
      anchor σ e E yc ϖ ρ μ v u γ 0 τ =ᵐ[volume] (fun _ => 0) := by
  have ht : ∀ᵐ τ ∂μ, ∀ j : Fin D, ∀ᵐ z ∂volume,
      WithLp.toLp 2 (fun I : DerivativeWord2 (j.val + 1) => planeJetOrder
        (planeTimeAllMomentCarrierToLp (K u + 1) ϖ ρ 0 μ
          (0 : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ) τ)
        (j.val + 1) I z) = 0 :=
    ae_all_iff.mpr (fun j => planeAllMoment_zero_jet_array (K u + 1) ϖ ρ 0 μ (j.val + 1))
  filter_upwards [ht] with τ ht
  filter_upwards [ae_all_iff.mpr ht] with z hz
  unfold naturalFamilyTaylorRawConstituent
  apply Finset.sum_eq_zero
  intro j _
  apply Finset.sum_eq_zero
  intro p _
  rw [hz j, map_zero]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
open AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Returning the native preparation model through the original chart has a
fixed factorial norm price at every radius below the slow scale. -/

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
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

theorem preparationWindowReferenceHkInverse_factorial_norm_le
    (hE : 0 < ocEpsilon q Λ (m - 1)) (t : ℝ) (ht : t ∈ Icc a b)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (U : PlaneHk univ J E) :
    Real.sqrt (factorialNormSq ρ (preparationWindowReferenceHkInverse hc hcover σ hσ ha J hJ t ht U).val) ≤
      compositionFactorialNormBound (preparationFlowJetConstant Cchart) J *
        Real.sqrt (factorialNormSq ρ U.val) := by
  have hp := preparation_reference_time_padded hc hcover t ht
  have hpσ := preparation_reference_time_padded hc hcover σ hσ
  have hage : |σ - t| ≤ 2 * Cage * ocTauPP α q Λ m := by
    have hσa := preparation_reference_time_age_sharp hc hcover σ hσ
    have hta := preparation_reference_time_age_sharp hc hcover t ht
    have hh := abs_sub_le σ ((l₀ : ℝ) * ocTauPP α q Λ m) t
    rw [abs_sub_comm ((l₀ : ℝ) * ocTauPP α q Λ m) t] at hh
    linarith only [hσa, hta, hh]
  obtain ⟨V, hV, hb⟩ := preparation_planeHk_factorial_pullback hc.flow ha hE
    σ t hpσ hp hage hρ hρE hJ U
  have hr := preparationFlowHkPullback_value_ae hc.flow ha σ t hpσ hp hage J hJ U
  have heq : V = preparationWindowReferenceHkInverse hc hcover σ hσ ha J hJ t ht U := by
    apply planeHk_eq_of_planeValue_ae
    exact hV.trans hr.symm
  rw [heq] at hb
  exact hb

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! The retained finite response yields an actual zero-initial error against the homogeneous coupled solution, preserving its native readouts. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance retainedHomogeneousErrorScalarNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance retainedHomogeneousErrorScalarNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance retainedHomogeneousErrorScalarCarrierAdd (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    AddCommGroup (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance
local instance retainedHomogeneousErrorScalarCarrierModule (i : ι) (k : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ) :
    Module ℝ (PlaneTimeAllMomentCarrier (E := h i) k ϖ ρ 0 μ) := inferInstance

variable (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
  (K : ι → ℕ) (a b ϖ ρ : ℝ)
  (R : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
  (Lmetric : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (Ledge : ∀ i j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
    PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
  (f : ∀ i, PlaneHk Set.univ (K i) (h i))
  (u₀ : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
  (w₀ : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
  (Z : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)))

variable {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem planeComponentAllMomentResponse_retained_homogeneous_error_solution
    (hab : a ≤ b) (hρ : 0 < ρ) (hD : 2 ≤ D)
    (A : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ] PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d) ≠ ⊤)
    (hA' : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hC : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ)
      (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1) i j d t))
    (hC' : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (family : ChartedFamily ι h D P Ctx)
    (H J : ℕ) (hdepth : family.HasDepthAtMost H)
    (hS : HasSourceDegreeOn family 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)))
    (hR : ∀ i, IsPlaneComponentAllMomentResponse (E := h i) M v (K i) a b ϖ ρ (R i))
    (hbase : IsPlaneChainFrom (geometryScalarData 2 (fun t _ => M t)) (fun _ i => K i) a b v
      (fun _ i => f i) (fun _ _ _ => 0) (fun _ i => u₀ i) (fun _ i => w₀ i))
    (hZ : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      (Z i) (w₀ i))
    (uH : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hH : IsCoupledWeakSolutionPlane 1 a b v D K A f
      (fun _ _ => 0) (fun _ _ => 0) uH wH) :
    let U := finiteResponse 1 (nativeDiagonalResponseOperator R Lmetric)
      (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) Z
    let W := ∑ j ∈ Finset.range (J + 1), ∑ n ∈ Finset.range (H + 1), U j n
    let T := ∑ n ∈ Finset.range (H + 1), U J n
    let Q := fun i => Lmetric i (W i) + nativeFamilyEdgeForcingMap Ledge i W - Lmetric i (T i)
    ∃ (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
      (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
      (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i)),
      IsCoupledWeakSolutionPlane 1 a b v D K A (fun _ => 0)
        (fun i t => -(F i t - planeCouplingFluxRow hab ρ hρ K D A hA' hC' w i t +
          planeCouplingFluxRow hab ρ hρ K D
            (planeDiagonalGradientCoefficient (h := h) K D (fun _ t _ => M t - 1))
            hA hC w i t)) (fun _ _ => 0)
        (fun i t => uH i t - u i t) (fun i t => wH i t - w i t) ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (Q i) (F i) ∧
        PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) (W i) (w i) := by
  obtain ⟨F, u, w, hs, hr⟩ :=
    planeComponentAllMomentResponse_retained_coupled_residual_solution M v K a b ϖ ρ R
      Lmetric Ledge f u₀ w₀ Z hab hρ hD A hA hA' hC hC'
      family H J hdepth hS hR hbase hZ
  refine ⟨F, u, w, ?_, hr⟩
  exact planeHomogeneousSolution_residual_error_equation K D 1 a b v A f _
    uH u wH w hH hs

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The exact reference-chart native source identity holds as an equality of actual continuous operators on rough Sobolev carriers. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planePeriodicNativeRow_reference_transfer {K : ℕ}
    (P X : Vec 2 ≃ₜ Vec 2)
    (hP : ContDiff ℝ (⊤ : ℕ∞) ⇑P) (hYP : ContDiff ℝ (⊤ : ℕ∞) ⇑P.symm)
    (hX : ContDiff ℝ (⊤ : ℕ∞) ⇑X) (hYX : ContDiff ℝ (⊤ : ℕ∞) ⇑X.symm)
    (hμ : MeasurePreserving ⇑X volume volume) (hμY : MeasurePreserving ⇑X.symm volume volume)
    (D : ℕ) (hD : D ≤ K + 1)
    (B : ∀ r : ℕ, DerivativeWord2 r → Vec 2 → Vec 2) (k : Fin 2)
    (hcS : ∀ z : JetIndex2 K,
      Continuous (transportedNativeScalarJetCoefficient (P.trans X.symm) D B k z))
    (hpS : ∀ z : JetIndex2 K,
      IsZ2Periodic (transportedNativeScalarJetCoefficient (P.trans X.symm) D B k z))
    (hcP : ∀ i (z : JetIndex2 K), Continuous (transportedNativeScalarJetCoefficient P D B i z))
    (hpP : ∀ i (z : JetIndex2 K), IsZ2Periodic (transportedNativeScalarJetCoefficient P D B i z))
    (hcJ : ∀ i, Continuous (fun y => (chartJacobian ⇑X y)⁻¹ k i))
    (MJ : Fin 2 → ℝ) (hMJ : ∀ i, 0 ≤ MJ i)
    (hbJ : ∀ i y, |(chartJacobian ⇑X y)⁻¹ k i| ≤ MJ i)
    (BF : ℕ → ℝ) (hBF : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ BF j)
    (hbF : ∀ j, 1 ≤ j → j ≤ K → ∀ x, ‖iteratedFDeriv ℝ j ⇑X.symm x‖ ≤ BF j) :
    periodicScalarRowOperator (E := E)
      (transportedNativeScalarJetCoefficient (P.trans X.symm) D B k) hcS hpS =
      planeJetRowPiolaOperator ⇑X hμ (fun i y => (chartJacobian ⇑X y)⁻¹ k i)
        hcJ MJ hMJ hbJ (fun i =>
          (periodicScalarRowOperator (transportedNativeScalarJetCoefficient P D B i)
            (hcP i) (hpP i)).comp
              (planeHkSmoothPullbackOperator X.symm hYX hμY BF hBF hbF)) := by
  apply planeHkOperator_eq_of_compact_smooth
  intro U f hf _hs hu
  let V : PlaneHk univ K E := planeHkSmoothPullback X.symm hYX hμY BF hBF hbF U
  have hv : planeValue V =ᵐ[volume] f ∘ ⇑X.symm :=
    (planeHkSmoothPullback_value_ae X.symm hYX hμY BF hBF hbF U).trans
      (hμY.quasiMeasurePreserving.ae_eq_comp hu)
  let R (i : Fin 2) : PlaneHk univ K E →L[ℝ] Lp E 2 (volume : Measure (Vec 2)) :=
    (periodicScalarRowOperator (transportedNativeScalarJetCoefficient P D B i)
      (hcP i) (hpP i)).comp (planeHkSmoothPullbackOperator X.symm hYX hμY BF hBF hbF)
  let Q (i : Fin 2) (x : Vec 2) := ∑ z : JetIndex2 K,
    transportedNativeScalarJetCoefficient P D B i z x • orderedDerivative z.2 (f ∘ ⇑X.symm) x
  have hQ : ∀ i, (R i U : Vec 2 → E) =ᵐ[volume] Q i := by
    intro i
    exact periodicScalarRowOperator_smooth_ae _ (hcP i) (hpP i) V _ (hf.comp hYX) hv
  apply Lp.ext
  have hl := periodicScalarRowOperator_smooth_ae _ hcS hpS U f hf hu
  have hr := planeJetRowPiolaOperator_ae ⇑X hμ
    (fun i y => (chartJacobian ⇑X y)⁻¹ k i) hcJ MJ hMJ hbJ R U Q hQ
  filter_upwards [hl, hr] with y hly hry
  rw [hly, hry]
  exact transportedNativeScalarJetCoefficient_reference_flux P X hP hYP hX hYX D hD B f hf y k

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.CoupledEnergyPlane.Variational AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! The actual full source map obeys the original inverse-mass gradient Schur estimate. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance rawCouplingMassBudgetNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance rawCouplingMassBudgetModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k

theorem planeRaw_allMoment_coupling_mass_budget
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
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (θ : ℝ)
    (hrow : ∀ i, ∑ u, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (hcol : ∀ u, ∑ i, schurMatrix 1 ρ π K D a b A i u ≤ θ)
    (W : ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) (n : ℕ) :
    planeAllMomentFamilyEnergy K n ϖ ρ (volume.restrict (Set.Icc a b)) π
      (fun i => T i W) ≤
      ENNReal.ofReal ((Real.sqrt ((2 : ℝ) ^ D) * θ) ^ 2) *
        planeAllMomentFamilyGradientEnergy K n ϖ ρ
          (volume.restrict (Set.Icc a b)) π W := by
  let w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j) := fun j t =>
    planeTimeAllMomentCarrierToLp (E := h j) (K j + 1) ϖ ρ 0
    (volume.restrict (Set.Icc a b)) (W j) t
  have hw j : PlaneTimeAllMomentRepresents (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W j) (w j) :=
    Filter.Eventually.of_forall (fun _ => rfl)
  have hr := planeRaw_allMoment_couplingRow_represents hab ϖ ρ hρ K D A hA hC T hT W w hw
  rw [planeAllMomentFamilyEnergy_represented K n ϖ ρ _ π _ _ hr]
  exact planeCouplingFluxRow_weighted_gradient_time_schur_budget a b hab ρ hρ K D A hA hC
    π hπ θ hrow hcol n ϖ 0 w
    (fun j => planeTimeAllMomentCarrier_memLp (K j + 1) ϖ ρ 0 _ (W j))
    (fun j => integrated_weightedGradFactorialNormSq_ne_top_of_lift n ϖ 0 ρ hρ _ _
      (planeTimeAllMomentCarrier_moment (K j + 1) ϖ ρ 0 _ (W j) n))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! The actual physical return of the cell model is a continuous linear inverse
with a uniform factorial price, retaining the exact plane dilation factor. -/

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

def preparationReferenceCellReturnOperator (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (t : ℝ) (ht : t ∈ Icc a b) : PlaneHk univ J E →L[ℝ] PlaneHk univ J E :=
  (preparationReferenceHkInverse hc hcover hTau ha J hJ t ht).comp
    (planeCarrierAffineOperator J e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)))

theorem preparationReferenceCellReturnOperator_windowPull
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht
      (planeCarrierAffine e he yc (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t U)) = U := by
  change preparationReferenceHkInverse hc hcover hTau ha J hJ t ht
    (planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc))
      (planeCarrierAffine e he yc (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t U))) = U
  rw [planeCarrierAffine_inverse, preparationReferenceHkInverse_windowPull]
end

/-! Literal native-time pullback of a physical curve and its exact physical return. -/

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

/-- Pull a physical curve into the reference cell, including the exact time dilation. -/
def preparationReferenceCellNativeCurve (ν e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ℝ → PlaneHk univ J E) : ℝ → PlaneHk univ J E :=
  fun τ => planeCarrierAffine e he yc
    (preparationReferenceHkWindowPull hc hcover hTau ha J hJ (ν⁻¹ * (e ^ 2 * τ))
      (U (ν⁻¹ * (e ^ 2 * τ))))

theorem preparationReferenceCellNativeCurve_apply (ν e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ℝ → PlaneHk univ J E) (τ : ℝ) :
    preparationReferenceCellNativeCurve hc hcover hTau ha J hJ ν e he yc U τ =
      planeCarrierAffine e he yc
        (preparationReferenceHkWindowPull hc hcover hTau ha J hJ (ν⁻¹ * (e ^ 2 * τ))
          (U (ν⁻¹ * (e ^ 2 * τ)))) := rfl

theorem preparationReferenceCellNativeCurve_at_physical_time (ν : ℝ) (hν : ν ≠ 0)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (U : ℝ → PlaneHk univ J E) (t : ℝ) :
    preparationReferenceCellNativeCurve hc hcover hTau ha J hJ ν e he yc U
      ((e⁻¹) ^ 2 * (ν * t)) =
      planeCarrierAffine e he yc (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t (U t)) := by
  have ht : ν⁻¹ * (e ^ 2 * ((e⁻¹) ^ 2 * (ν * t))) = t := by
    field_simp
  rw [preparationReferenceCellNativeCurve_apply, ht]

theorem preparationReferenceCellNativeCurve_return (ν : ℝ) (hν : ν ≠ 0)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (U : ℝ → PlaneHk univ J E)
    (t : ℝ) (ht : t ∈ Icc a b) :
    preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht
      (preparationReferenceCellNativeCurve hc hcover hTau ha J hJ ν e he yc U
        ((e⁻¹) ^ 2 * (ν * t))) = U t := by
  rw [preparationReferenceCellNativeCurve_at_physical_time hc hcover hTau ha J hJ ν hν e he yc U t]
  exact preparationReferenceCellReturnOperator_windowPull hc hcover hTau ha J hJ e he yc t ht (U t)
end

/-! Literal spatial value readouts of the actual reference-cell native curves. -/

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

theorem preparationReferenceHkWindowPull_value_ae
    (t : ℝ) (ht : t ∈ Icc a b) (U : PlaneHk univ J E) :
    planeValue (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t U) =ᵐ[volume]
      fun z => planeValue U (streamFlow φ hφ t z ((l₀ : ℝ) * ocTauPP α q Λ m)) := by
  unfold preparationReferenceHkWindowPull planeHkWindowChartPull
  rw [dite_eq_left ht]
  exact planeHkSmoothPullback_value_ae _ _ _ _ _ _ U

theorem preparationReferenceCellNativeCurve_value_ae_at_physical_time
    (ν : ℝ) (hν : ν ≠ 0) (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ℝ → PlaneHk univ J E) (t : ℝ) (ht : t ∈ Icc a b) :
    planeValue (preparationReferenceCellNativeCurve hc hcover hTau ha J hJ
      ν e he yc U ((e⁻¹) ^ 2 * (ν * t))) =ᵐ[volume]
      fun z => planeValue (U t) (streamFlow φ hφ t (yc + e • z) ((l₀ : ℝ) * ocTauPP α q Λ m)) := by
  rw [preparationReferenceCellNativeCurve_at_physical_time hc hcover hTau ha J hJ
    ν hν e he yc U t]
  have hh := (plane_affine_quasiMeasurePreserving e he yc).ae_eq_comp
    (preparationReferenceHkWindowPull_value_ae hc hcover hTau ha J hJ t ht (U t))
  exact (planeCarrierAffine_value_ae e he yc _).trans hh
end

/-! The actual physical return of the cell model is a continuous linear inverse
with a uniform factorial price, retaining the exact plane dilation factor. -/

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

theorem preparationReferenceCellPull_return
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    planeCarrierAffine e he yc (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t
      (preparationReferenceCellReturnOperator hc hcover hTau ha J hJ e he yc t ht U)) = U := by
  change planeCarrierAffine e he yc (preparationReferenceHkWindowPull hc hcover hTau ha J hJ t
    (preparationReferenceHkInverse hc hcover hTau ha J hJ t ht
      (planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) U))) = U
  rw [preparationReferenceHkWindowPull_inverse, planeCarrierAffine_inverse_right]
end

/-! The exact native initial datum at the original reference seam is a linear map of the physical trace. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

variable {X : Type*} [AddCommGroup X] [Module ℝ X]

variable (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)

/-- Pull a physical trace into the original reference cell, whose anchor may precede the preparation window. -/
def preparationReferenceCellTraceLinearMap
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i))) :
    X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)) :=
  LinearMap.pi (fun i =>
    (planeCarrierAffineOperator (K i) e he yc).toLinearMap.comp
      ((preparationReferenceHkWindowPullOperator hc hcover hTau ha
        (K i) (hK i) t ht).toLinearMap.comp ((LinearMap.proj i).comp T)))

omit [Fintype ι] in
theorem preparationReferenceCellTraceLinearMap_apply
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i))) (ξ : X) (i : ι) :
    preparationReferenceCellTraceLinearMap hc hcover hTau ha K hK e he yc t ht T ξ i =
      planeCarrierAffine e he yc
        (preparationReferenceHkWindowPull hc hcover hTau ha (K i) (hK i) t (T ξ i)) := by
  change planeCarrierAffine e he yc
    (preparationReferenceHkWindowPullOperator hc hcover hTau ha (K i) (hK i) t ht
      (T ξ i)) = _
  rw [preparationReferenceHkWindowPullOperator_apply]

omit [Fintype ι] in
theorem preparationReferenceCellTraceLinearMap_native_curve
    (T : X →ₗ[ℝ] (∀ i, PlaneHk univ (K i) (h i)))
    (U : X → ∀ i, ℝ → PlaneHk univ (K i) (h i))
    (hT : ∀ ξ i, T ξ i = U ξ i t) (ν : ℝ) (hν : ν ≠ 0) (ξ : X) (i : ι) :
    preparationReferenceCellTraceLinearMap hc hcover hTau ha K hK e he yc t ht T ξ i =
      preparationReferenceCellNativeCurve hc hcover hTau ha (K i) (hK i)
        ν e he yc (U ξ i) ((e⁻¹) ^ 2 * (ν * t)) := by
  rw [preparationReferenceCellTraceLinearMap_apply,
    preparationReferenceCellNativeCurve_at_physical_time hc hcover hTau ha
      (K i) (hK i) ν hν e he yc (U ξ i) t, hT]
end

/-! The actual physical return of the cell model is a continuous linear inverse
with a uniform factorial price, retaining the exact plane dilation factor. -/

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
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

def preparationWindowReferenceCellReturnOperator (e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (t : ℝ) (ht : t ∈ Icc a b) : PlaneHk univ J E →L[ℝ] PlaneHk univ J E :=
  (preparationWindowReferenceHkInverse hc hcover σ hσ ha J hJ t ht).comp
    (planeCarrierAffineOperator J e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)))

theorem preparationWindowReferenceCellReturnOperator_windowPull
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    (U : PlaneHk univ J E) :
    preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J hJ e he yc t ht
      (planeCarrierAffine e he yc (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U)) = U := by
  change preparationWindowReferenceHkInverse hc hcover σ hσ ha J hJ t ht
    (planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc))
      (planeCarrierAffine e he yc (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U))) = U
  rw [planeCarrierAffine_inverse, preparationWindowReferenceHkInverse_windowPull]

theorem preparationWindowReferenceCellReturnOperator_factorial_norm_le
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (U : PlaneHk univ J E) :
    Real.sqrt (factorialNormSq ρ
      (preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J hJ e he yc t ht U).val) ≤
      (compositionFactorialNormBound (preparationFlowJetConstant Cchart) J * |e|) *
        Real.sqrt (factorialNormSq (ρ / e) U.val) := by
  have hh := preparationWindowReferenceHkInverse_factorial_norm_le hc hcover σ hσ ha J hJ hE t ht hρ hρE
    (planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) U)
  have heq : Real.sqrt (factorialNormSq ρ
      (planeCarrierAffine e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) U).val) =
      |e| * Real.sqrt (factorialNormSq (ρ / e) U.val) := by
    simpa only [div_inv_eq_mul, div_mul_cancel₀ _ he, inv_inv] using
      planeCarrierAffine_factorial_norm (ρ / e) e⁻¹ (inv_ne_zero he) (-(e⁻¹ • yc)) U
  rw [heq] at hh
  exact hh.trans_eq (mul_assoc _ _ _).symm


/-- The exact return map converts the native approximation error into the
physical factorial norm, retaining the plane dilation price. -/
theorem preparationWindowReferenceCellReturnOperator_error_norm_le
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (U V : PlaneHk univ J E) :
    Real.sqrt (factorialNormSq ρ
      (U - preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J hJ e he yc t ht V).val) ≤
      (compositionFactorialNormBound (preparationFlowJetConstant Cchart) J * |e|) *
        Real.sqrt (factorialNormSq (ρ / e)
          (planeCarrierAffine e he yc
            (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U) - V).val) := by
  have hh := preparationWindowReferenceCellReturnOperator_factorial_norm_le hc hcover σ hσ ha J hJ
    hE e he yc t ht hρ hρE
    (planeCarrierAffine e he yc (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U) - V)
  rw [map_sub, preparationWindowReferenceCellReturnOperator_windowPull] at hh
  exact hh


/-- Every physical slot uses the same fixed chart-reserve constant. -/
theorem preparationWindowReferenceCellReturnOperator_error_norm_le_reserve
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (U V : PlaneHk univ J E) :
    Real.sqrt (factorialNormSq ρ
      (U - preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J hJ e he yc t ht V).val) ≤
      (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) * |e|) *
        Real.sqrt (factorialNormSq (ρ / e)
          (planeCarrierAffine e he yc
            (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t U) - V).val) := by
  exact (preparationWindowReferenceCellReturnOperator_error_norm_le hc hcover σ hσ ha J hJ
    hE e he yc t ht hρ hρE U V).trans
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (compositionFactorialNormBound_mono (preparationFlowJetConstant Cchart) hJ)
        (abs_nonneg e)) (Real.sqrt_nonneg _))
end

/-! Literal native-time pullback at any covered reference time and its exact physical return. -/

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
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (J : ℕ) (hJ : J ≤ Jchart + 1)

/-- Pull a physical curve into the reference cell, including the exact time dilation. -/
def preparationWindowReferenceCellNativeCurve (ν e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ℝ → PlaneHk univ J E) : ℝ → PlaneHk univ J E :=
  fun τ => planeCarrierAffine e he yc
    (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ (ν⁻¹ * (e ^ 2 * τ))
      (U (ν⁻¹ * (e ^ 2 * τ))))

theorem preparationWindowReferenceCellNativeCurve_apply (ν e : ℝ) (he : e ≠ 0) (yc : Vec 2)
    (U : ℝ → PlaneHk univ J E) (τ : ℝ) :
    preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha J hJ ν e he yc U τ =
      planeCarrierAffine e he yc
        (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ (ν⁻¹ * (e ^ 2 * τ))
          (U (ν⁻¹ * (e ^ 2 * τ)))) := rfl

theorem preparationWindowReferenceCellNativeCurve_at_physical_time (ν : ℝ) (hν : ν ≠ 0)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (U : ℝ → PlaneHk univ J E) (t : ℝ) :
    preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha J hJ ν e he yc U
      ((e⁻¹) ^ 2 * (ν * t)) =
      planeCarrierAffine e he yc (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha J hJ t (U t)) := by
  have ht : ν⁻¹ * (e ^ 2 * ((e⁻¹) ^ 2 * (ν * t))) = t := by
    field_simp
  rw [preparationWindowReferenceCellNativeCurve_apply, ht]

theorem preparationWindowReferenceCellNativeCurve_return (ν : ℝ) (hν : ν ≠ 0)
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (U : ℝ → PlaneHk univ J E)
    (t : ℝ) (ht : t ∈ Icc a b) :
    preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha J hJ e he yc t ht
      (preparationWindowReferenceCellNativeCurve hc hcover σ hσ ha J hJ ν e he yc U
        ((e⁻¹) ^ 2 * (ν * t))) = U t := by
  rw [preparationWindowReferenceCellNativeCurve_at_physical_time hc hcover σ hσ ha J hJ ν hν e he yc U t]
  exact preparationWindowReferenceCellReturnOperator_windowPull hc hcover σ hσ ha J hJ e he yc t ht (U t)
end

/-! Physical return of native errors respects the original component masses,
with one chart-reserve constant independent of component count and dimension. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P' : Type*} {Ctx : P' → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {a b Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {P : ℕ}
  {F : ChartedFamily ι h D P' Ctx}

theorem preparationWindowReferenceCellReturn_mass_error_le
    (hc : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ P F)
    (hcover : Icc a b ⊆ ⋃ p, (F.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (K : ι → ℕ) (hK : ∀ i, K i ≤ Jchart + 1)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (hE : 0 < ocEpsilon q Λ (m - 1))
    (e : ℝ) (he : e ≠ 0) (yc : Vec 2) (t : ℝ) (ht : t ∈ Icc a b)
    {ρ : ℝ} (hρ : 0 ≤ ρ) (hρE : ρ ≤ ocEpsilon q Λ (m - 1))
    (U V : ∀ i, PlaneHk univ (K i) (h i)) :
    (∑ i, (π i)⁻¹ * factorialNormSq ρ
      (U i - preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha
        (K i) (hK i) e he yc t ht (V i)).val) ≤
      (compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) * |e|) ^ 2 *
      ∑ i, (π i)⁻¹ * factorialNormSq (ρ / e)
        (planeCarrierAffine e he yc
          (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha (K i) (hK i) t (U i)) - V i).val := by
  let C := compositionFactorialNormBound (preparationFlowJetConstant Cchart) (Jchart + 1) * |e|
  have hC : 0 ≤ C := mul_nonneg (compositionFactorialNormBound_nonneg _ _) (abs_nonneg e)
  have hb (i : ι) : factorialNormSq ρ
      (U i - preparationWindowReferenceCellReturnOperator hc hcover σ hσ ha
        (K i) (hK i) e he yc t ht (V i)).val ≤
      C ^ 2 * factorialNormSq (ρ / e)
        (planeCarrierAffine e he yc
          (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha (K i) (hK i) t (U i)) - V i).val := by
    have hh := preparationWindowReferenceCellReturnOperator_error_norm_le_reserve
      hc hcover σ hσ ha (K i) (hK i) hE e he yc t ht hρ hρE (U i) (V i)
    have hs := (sq_le_sq₀ (Real.sqrt_nonneg _) (mul_nonneg hC (Real.sqrt_nonneg _))).mpr hh
    rw [Real.sq_sqrt (factorialNormSq_nonneg _ _), mul_pow,
      Real.sq_sqrt (factorialNormSq_nonneg _ _)] at hs
    exact hs
  calc
    _ ≤ ∑ i, (π i)⁻¹ * (C ^ 2 * factorialNormSq (ρ / e)
        (planeCarrierAffine e he yc
          (preparationWindowReferenceHkWindowPull hc hcover σ hσ ha (K i) (hK i) t (U i)) - V i).val) :=
      Finset.sum_le_sum (fun i _ => mul_le_mul_of_nonneg_left (hb i) (inv_nonneg.mpr (hπ i).le))
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      change (π i)⁻¹ * (C ^ 2 * _) = C ^ 2 * ((π i)⁻¹ * _)
      ring
end

end AVRegularity.CycleJointProofs
end
end
