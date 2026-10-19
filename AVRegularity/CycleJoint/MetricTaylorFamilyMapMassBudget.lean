-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlanePolynomialJetMultiplierDensity
import AVRegularity.CycleJoint.FamilyNaturalTimeRemainderReservedJets
import AVRegularity.CycleWords.CellTransverseGalerkinCorrectionLocalGrowthEnergy
import AVenhance.Infra.Classical.Drift
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Transfer a coupled error equation and its literal native residual forcing
through equality of the full coefficient array on the solution window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance rawErrorWindowNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k
local instance rawErrorWindowNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (h i)) := allMomentTimeNativeModule k
local instance rawErrorWindowFluxNativeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeNormed k
local instance rawErrorWindowFluxNativeModule (i : ι) (k : ℕ) :
    Module ℝ (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) :=
  allMomentTimeNativeModule k

theorem planeRaw_coupled_error_window_transfer
    (K : ι → ℕ) (D : ℕ) (a b ϖ ρ : ℝ) (hab : a ≤ b) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (A A' B : ∀ i j, (d : admissibleOrders K D i j) → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j) →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i j d, coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hAc : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (A i j d t))
    (hB : ∀ i j d, coefficientSeminorm ρ (K i) a b (B i j d) ≠ ⊤)
    (hBc : ∀ i j d t, t ∈ Set.Icc a b → ContDiff ℝ (K i : ℕ) (B i j d t))
    (heq : ∀ i j d t, t ∈ Set.Icc a b → A' i j d t = A i j d t)
    (Lfull Ldiag : ∀ i, (∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b))) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
        (volume.restrict (Set.Icc a b)))
    (hfull : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t A
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (X j) t) i) (Lfull i))
    (hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b))
      (fun X t => planeRawCouplingFlux K D t B
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) (X j) t) i) (Ldiag i))
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (Q : ∀ i, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (wret : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hF : ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (Q i) (F i))
    (hW : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W i) (wret i))
    (uerr : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (werr : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hs : IsCoupledWeakSolutionPlane 1 a b v D K A (fun _ => 0)
      (fun i t => -(F i t - planeCouplingFluxRow hab ρ hρ K D A hA hAc wret i t +
        planeCouplingFluxRow hab ρ hρ K D B hB hBc wret i t))
      (fun _ _ => 0) uerr werr) :
    ∃ ferr : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)),
      IsCoupledWeakSolutionPlane 1 a b v D K A' (fun _ => 0) ferr (fun _ _ => 0) uerr werr ∧
      ∀ i, PlaneTimeAllMomentRepresents (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (-(Q i - Lfull i W + Ldiag i W)) (ferr i) := by
  let ferr := fun i t => -(F i t - planeCouplingFluxRow hab ρ hρ K D A hA hAc wret i t +
    planeCouplingFluxRow hab ρ hρ K D B hB hBc wret i t)
  have hf := planeRaw_allMoment_couplingRow_represents hab ϖ ρ hρ K D A hA hAc
    Lfull hfull W wret hW
  have hd := planeRaw_allMoment_couplingRow_represents hab ϖ ρ hρ K D B hB hBc
    Ldiag hdiag W wret hW
  refine ⟨ferr, CycleWords.isCoupledWeakSolutionPlane_congr_coeff heq hs, ?_⟩
  intro i
  apply planeTimeAllMomentRepresents_neg (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
  exact planeTimeAllMomentRepresents_add (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
    _ _ _ _ (planeTimeAllMomentRepresents_sub (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
      _ _ _ _ (hF i) (hf i)) (hd i)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The actual original constituent Taylor readout is zero on zero native input. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

local instance naturalTaylorDegreeNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k

theorem naturalFamilyTaylor_constructed_split_edges
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) (actual : ∀ p, Ctx p) (K : ι → ℕ)
    (timeScale : ℝ) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (anchor : P → ℝ) (σ e E : ℝ) (yc : Vec 2)
    (ϖ ρ : ℝ) (μ : Measure ℝ)
    (Tfull Rs : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ ρ 0 μ)
    (hTaylor : ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ
      (fun x t z => ∑ u, ∑ γ, naturalFamilyTaylorRawConstituent Ks F S actual K timeScale hφ
        anchor σ e E yc ϖ ρ μ v u γ (x u) t z) (Tfull v - Rs v))
    (Hfull : ∀ v, (∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ) → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v))
    (hfull : ∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ (Hfull v) (Tfull v)) :
    ∃ Ledge : ∀ v u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ ρ 0 μ →ₗ[ℝ] PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ ρ 0 μ,
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ
        (Hfull v) (nativeFamilyEdgeForcingMap Ledge v + Rs v)) ∧
      (∀ v, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ ρ 0 μ
        (fun x t z => ∑ u, ∑ γ, naturalFamilyTaylorRawConstituent Ks F S actual K timeScale hφ anchor σ e E yc ϖ ρ μ v u γ (x u) t z)
        (nativeFamilyEdgeForcingMap Ledge v)) ∧
      (∀ v u, ¬ Nonempty (F.Γ v u) → Ledge v u = 0) ∧
      ∀ R : ∀ v, PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ ρ 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := h v) (K v + 1) ϖ ρ 0 μ,
        HasSourceDegreeOn F 1 (nativeComponentResponseOperator R (nativeFamilyEdgeForcingMap Ledge)) := by
  exact nativeRawOriginalFamilyMap_taylor_split_edges F K ϖ ρ 0 μ
    (naturalFamilyTaylorRawConstituent Ks F S actual K timeScale hφ anchor σ e E yc ϖ ρ μ)
    (naturalFamilyTaylorRawConstituent_zero Ks F S actual K timeScale hφ anchor σ e E yc ϖ ρ μ)
    Tfull Rs hTaylor Hfull hfull

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleReference
namespace AVRegularity.CycleJointProofs

/-! Exact native trace increments against material tests fixed in time on the preparation window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_material_test_increment {a b : ℝ} (hab : a ≤ b)
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E}
    (h : PlaneWeakHilbertCurve a b u slice dual)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ)
    (η : ℝ × Vec 2 → ℝ) (hη : ContDiff ℝ (⊤ : ℕ∞) η)
    (hcη : HasCompactSupport η) (e : E)
    (hηt : ∀ t ∈ Icc a b, ∀ x, deriv (fun r => η (r, x)) t = 0) :
    let f := materialChartTestField hφ s η
    let hf := materialChartTestField_smooth hφ s η hη
    let hs := materialChartTestField_compact hφ s η hcη
    inner ℝ (planeL2FlowPull hφ b s (u b))
        (planeHkValueOperator 1 (compactSpacetimeVectorH1 η hη hcη e b)) -
      inner ℝ (planeL2FlowPull hφ a s (u a))
        (planeHkValueOperator 1 (compactSpacetimeVectorH1 η hη hcη e a)) =
      ∫ t in a..b, inner ℝ (dual t) (compactSpacetimeVectorH1 f hf hs e t) +
        ∫ x, f (t, x) * ∑ i : Fin 2, streamVel φ t x i *
          inner ℝ (planeH1GradientOperator (slice t) i x) e := by
  let f := materialChartTestField hφ s η
  let hf := materialChartTestField_smooth hφ s η hη
  let hs := materialChartTestField_compact hφ s η hcη
  have hv : ∀ t ∈ Icc a b, ContDiff ℝ (⊤ : ℕ∞) (streamVel φ t) := by
    intro t _
    exact (Infra.Construction.smoothPeriodic_streamVel hφ).smooth.comp
      (contDiff_const.prodMk contDiff_id)
  have hdiv : ∀ t ∈ Icc a b, ∀ x,
      ∑ i : Fin 2, fderiv ℝ (fun y => streamVel φ t y i) x (basisVec i) = 0 := by
    intro t _ x
    exact Infra.Classical.streamVel_vecDiv_eq_zero φ hφ t x
  have hd : ∀ t ∈ Icc a b, ∀ x, deriv (fun r => f (r, x)) t =
      -vecDot (spaceGrad (fun y => f (t, y)) x) (streamVel φ t x) := by
    intro t ht x
    have hp := inverseMaterialTest_time_derivative hφ s t x (fun r y => η (r, y)) hη
    have he : chartUnpull hφ s (fun r y => η (r, y)) t = (fun y => f (t, y)) := by
      funext y
      rfl
    rw [he, hηt t ht, zero_sub] at hp
    exact hp
  have hp := planeWeakCurve_transport_test_increment hab h (streamVel φ) hv hdiv f hf hs e hd
  have hend (t : ℝ) : inner ℝ (planeL2FlowPull hφ t s (u t))
      (planeHkValueOperator 1 (compactSpacetimeVectorH1 η hη hcη e t)) =
      ∫ x, f (t, x) * inner ℝ (u t x) e := by
    rw [← materialChart_native_test_cancellation hφ s t η hη hcη e,
      planeChart_value_pairing, compactSpacetimeVectorH1_L2_pair]
  dsimp only
  rw [hend b, hend a]
  exact hp

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The full preparation sampling bridge from its independent pointwise certificate. -/

/-- Independent-to-sampled envelope bridge on the entire preparation window. -/
theorem preparation_reference_cell_source_schur_budget (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (b : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ b v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b →
        ∀ yc : Vec 2, ∀ v u,
          schurMatrix 1 (ρ / e) π K D ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ))
            (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
              ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * b v u := by
  obtain ⟨Cprep, hC, hsamp⟩ := preparation_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hC, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ P' Ctx F π hπ K hK actual b hb hc henv yc v u
  have he : 0 < e := hρ.trans_le hρe
  have hs := hsamp α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ
    hν hρ hρe heE F π hπ K hK actual b hb hc henv
  rw [preparationReferenceCellSourceCoefficient_schurMatrix F hφ _ ν e _ tS tZ ρ hν he hρ]
  exact sampledEnvelope_schurMatrix_le (referenceChartedFamily F hφ ((l₀ : ℝ) * ocTauPP α q Λ m))
    π hπ K actual tS tZ ν e _ ρ Cprep hν hρ b hs v u
    (mul_nonneg (zero_le_one.trans hC) (hb v u))

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! The preparation certificate and output cover give continuous native reference traces, L2 higher states, and exact truncation agreement for every actual coupled solution. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_chart_trace_data {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
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
    {P' : Type*} {Ctx : P' → Type*} (family : ChartedFamily ι h D P' Ctx)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover family)
    (hcover : Icc a b ⊆ ⋃ p, (family.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart) (i : ι) :
    ContinuousOn (fun t => preparationReferenceHkWindowPull hprep hcover hTau ha (K i)
      (by have hh := hK i; omega) t (u i t)) (Icc a b) ∧
    MemLp (fun t => preparationReferenceHkWindowPull hprep hcover hTau ha (K i + 1)
      (Nat.add_le_add_right (hK i) 1) t (w i t)) 2 (volume.restrict (Icc a b)) ∧
    (∀ᵐ t ∂volume.restrict (Icc a b),
      truncatePlaneHk (show K i ≤ K i + 1 by omega)
        (preparationReferenceHkWindowPull hprep hcover hTau ha (K i + 1)
          (Nat.add_le_add_right (hK i) 1) t (w i t)) =
      preparationReferenceHkWindowPull hprep hcover hTau ha (K i)
        (by have hh := hK i; omega) t (u i t)) := by
  exact coupledPlane_chart_trace_data hs hφ ((l₀ : ℝ) * ocTauPP α q Λ m) i
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun t ht j hj hjK x => preparation_reference_flow_jets hprep hcover hTau ha t ht j hj
      (hjK.trans (Nat.add_le_add_right (hK i) 1)) x)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Polynomially growing native arrays construct actual all-moment source maps at their literal jet order. -/

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

theorem exists_planeNativeArrayPolynomial_allMoment_map
    {K L r : ℕ} (hKL : K + r ≤ L + 1) (hr : 1 ≤ r)
    (p : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (c : Fin 2 → DerivativeWord2 r → ℝ → Vec 2 → ℝ)
    (hm : ∀ a I z, Measurable (fun t => c a I t z))
    (hc : ∀ a I t, ContDiff ℝ (K : ℕ) (c a I t)) (C : U →L[ℝ] V)
    (B : Fin 2 → DerivativeWord2 r → ℝ) (hB : ∀ a I, 0 ≤ B a I)
    (hb : ∀ a I, ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c a I t) z‖ ≤ B a I * polynomialMomentRoot ϖ z ^ p) :
    ∃ T : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => V)) K ϖ ρ 0 μ,
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
        (fun x t z => nativeArrayAssembly r C (fun a I => c a I t z)
          (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z))) T := by
  classical
  let X := PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ
  let H := fun (β : Fin 2 × DerivativeWord2 r) (x : X) t z =>
    c β.1 β.2 t z • Weighted.fluxCoordinateInjection β.1 C
      (planeJetOrder (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r β.2 z)
  have hex (β : Fin 2 × DerivativeWord2 r) :=
    exists_planePolynomialJetMultiplier_allMoment_map hKL hr β.2 p ϖ ρ hϖ hρ μ
      (c β.1 β.2) (hm β.1 β.2) (hc β.1 β.2) (Weighted.fluxCoordinateInjection β.1 C)
      (B β.1 β.2) (hB β.1 β.2) (hb β.1 β.2)
  choose T hT using hex
  have hraw := planeRaw_allMoment_linearMap_sum (X := X)
    (E := PiLp 2 (fun _ : Fin 2 => V)) K ϖ ρ 0 μ H T hT
  refine ⟨∑ β, T β, ?_⟩
  have heq : (fun (x : X) t z => nativeArrayAssembly r C (fun a I => c a I t z)
      (WithLp.toLp 2 (fun I => planeJetOrder
        (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z))) =
      fun x t z => ∑ β, H β x t z := by
    funext x t z
    rw [nativeArrayAssembly_value_expansion, Fintype.sum_prod_type]
  rw [heq]
  exact hraw

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Reference trace data for a physical solution on a preparation subwindow. The chart anchor remains in the original certificate window. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_chart_trace_data_subwindow {ν a b c d : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {D : ℕ} {K : ι → ℕ}
    {A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {u : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν c d v D K A f F g u w)
    {P' : Type*} {Ctx : P' → Type*} (family : ChartedFamily ι h D P' Ctx)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover family)
    (hcover : Icc a b ⊆ ⋃ p, (family.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart) (hsub : Icc c d ⊆ Icc a b) (i : ι) :
    ContinuousOn (fun t => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K i)
      (by have hh := hK i; omega) t (u i t)) (Icc c d) ∧
    MemLp (fun t => preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K i + 1)
      (Nat.add_le_add_right (hK i) 1) t (w i t)) 2 (volume.restrict (Icc c d)) ∧
    (∀ᵐ t ∂volume.restrict (Icc c d),
      truncatePlaneHk (show K i ≤ K i + 1 by omega)
        (preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K i + 1)
          (Nat.add_le_add_right (hK i) 1) t (w i t)) =
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K i)
        (by have hh := hK i; omega) t (u i t)) := by
  have hh := coupledPlane_chart_trace_data hs hφ σ i
    (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
    (fun _ _ _ => abs_nonneg _)
    (fun t ht j hj hjK x => preparation_window_reference_time_flow_jets hprep hcover σ hσ ha t (hsub ht) j hj
      (hjK.trans (Nat.add_le_add_right (hK i) 1)) x)
  have heq (k : ℕ) (hk : k ≤ Jchart + 1) (t : ℝ) (ht : t ∈ Icc c d)
      (V : PlaneHk univ k (h i)) :
      planeHkWindowChartPull c d hφ σ
        (preparationPieceFlowJetBudget Cchart (ocEpsilon q Λ (m - 1)))
        (fun _ _ _ => abs_nonneg _)
        (fun r hr j hj hjk x => preparation_window_reference_time_flow_jets hprep hcover σ hσ ha
          r (hsub hr) j hj (hjk.trans hk) x) t V =
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha k hk t V := by
    unfold preparationWindowReferenceHkWindowPull planeHkWindowChartPull
    rw [dite_eq_left ht, dite_eq_left (hsub ht)]
  refine ⟨hh.1.congr (fun t ht => (heq _ _ t ht _).symm), ?_, ?_⟩
  · apply MemLp.ae_eq _ hh.2.1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact heq _ _ t ht _
  · filter_upwards [hh.2.2, ae_restrict_mem measurableSet_Icc] with t htrace ht
    rw [heq _ _ t ht _, heq _ _ t ht _] at htrace
    exact htrace

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleJointProofs

/-! The full preparation sampling bridge from its independent pointwise certificate. -/

/-- Independent-to-sampled envelope bridge on the entire preparation window. -/
theorem preparation_reference_cell_source_subwindow_schur_budget (D Kmax Jchart Jm : ℕ)
    (hchart : Kmax + D + 2 ≤ Jchart) (_hmol : Kmax + D + 2 ≤ Jm)
    (Cm Cchart : ℕ → ℝ) :
    ∃ Cprep : ℝ, 1 ≤ Cprep ∧
      ∀ (α q : ℝ) (Λ m : ℕ) (φ : ℝ → Vec 2 → ℝ) (hφ : IsAdmissibleStream φ)
        (tS tZ Cpad Cage : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
        (ν e ρ : ℝ), 0 < ν → 0 < ρ → ρ ≤ e → e ≤ ocEpsilon q Λ (m - 1) →
      ∀ {ι : Type*} [Fintype ι] {h : ι → Type*}
        [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
        {P' : Type*} {Ctx : P' → Type*} (F : ChartedFamily ι h D P' Ctx)
        (π : ι → ℝ) (_hπ : ∀ v, 0 < π v) (K : ι → ℕ) (_hK : ∀ v, K v ≤ Kmax)
        (actual : ∀ p, Ctx p) (B : ι → ι → ℝ) (_hb : ∀ v u, 0 ≤ B v u),
        IsPreparationChartCertificate α q Λ m φ hφ tS tZ Cpad Cage Npad Jchart Cchart l₀ P F →
        IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F (Set.Icc tS tZ))
          ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm B →
        ∀ (yc : Vec 2) (a b : ℝ),
          Set.Icc a b ⊆ Set.Icc ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) → ∀ v u,
          schurMatrix 1 (ρ / e) π K D a b
            (preparationReferenceCellSourceCoefficient F hφ ((l₀ : ℝ) * ocTauPP α q Λ m)
              ν e (ocEpsilon q Λ (m - 1)) actual K yc) v u ≤ Cprep * B v u := by
  obtain ⟨Cprep, hCprep, hglobal⟩ := preparation_reference_cell_source_schur_budget
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  obtain ⟨Csamp, _, hsamp⟩ := preparation_reference_sampled_envelope_of_pointwise_certificate
    D Kmax Jchart Jm hchart _hmol Cm Cchart
  refine ⟨Cprep, hCprep, ?_⟩
  intro α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    ι _ h _ _ P' Ctx F π hπ K hK actual B hB hc henv yc a b hsub v u
  have hs := hsamp α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
    F π hπ K hK actual B hB hc henv
  have he : 0 < e := hρ.trans_le hρe
  have hfinite v u d := preparationReferenceCellSourceCoefficient_seminorm_ne_top
    F hφ ((l₀ : ℝ) * ocTauPP α q Λ m) ν e (ocEpsilon q Λ (m - 1)) actual K yc
    π hπ tS tZ ρ (ρ / e) Csamp hν hρ he.ne' B hs v u d
  exact (schurMatrix_time_mono 1 (ρ / e) zero_lt_one (div_pos hρ he) π K D a b
    ((e⁻¹) ^ 2 * (ν * tS)) ((e⁻¹) ^ 2 * (ν * tZ)) hsub _ hfinite v u).trans
    (hglobal α q Λ m φ hφ tS tZ Cpad Cage Npad l₀ P ν e ρ hν hρ hρe heE
      F π hπ K hK actual B hB hc henv yc v u)

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Actual higher reference traces and energy states retain their exact initial data and truncation agreement in positive diffusion time. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_reference_normalized_trace_data {ν a b : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {D : ℕ} {K : ι → ℕ}
    {A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {u : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (hν : 0 < ν)
    {P' : Type*} {Ctx : P' → Type*} (family : ChartedFamily ι h D P' Ctx)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover family)
    (hcover : Icc a b ⊆ ⋃ p, (family.piece p).output)
    (hTau : 0 ≤ ocTauPP α q Λ m) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart) (i : ι) :
    let U : ℝ → PlaneHk univ (K i) (h i) := fun t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K i)
        (by have hh := hK i; omega) (ν⁻¹ * t) (u i (ν⁻¹ * t))
    let W : ℝ → PlaneHk univ (K i + 1) (h i) := fun t =>
      preparationReferenceHkWindowPull hprep hcover hTau ha (K i + 1)
        (Nat.add_le_add_right (hK i) 1) (ν⁻¹ * t) (w i (ν⁻¹ * t))
    ContinuousOn U (Icc (ν * a) (ν * b)) ∧
    MemLp W 2 (volume.restrict (Icc (ν * a) (ν * b))) ∧
    (∀ᵐ t ∂volume.restrict (Icc (ν * a) (ν * b)),
      truncatePlaneHk (Nat.le_succ (K i)) (W t) = U t) ∧
    U (ν * a) = preparationReferenceHkWindowPull hprep hcover hTau ha (K i)
      (by have hh := hK i; omega) a (f i) := by
  dsimp only
  have hdata := preparation_reference_chart_trace_data hs family hprep hcover hTau ha hK i
  refine ⟨hdata.1.comp (continuous_const.mul continuous_id).continuousOn
      (fun _ ht => positiveTimeNormalization_mem_Icc hν ht),
    memLp_comp_inv_mul_restrict_Icc hν hdata.2.1,
    ae_comp_inv_mul_restrict_Icc hν hdata.2.2, ?_⟩
  rw [show ν⁻¹ * (ν * a) = a by rw [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul],
    hs.2.2.2.1 i]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The literal positive metric Taylor insertion is an actual native linear map on all-moment curves. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance metricTaylorMomentNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance metricTaylorMomentModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k

variable (Ks Kmax : ℕ) (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r)
  (K : ℕ) (hK : K ≤ Kmax)
  (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ)
  (hm : ∀ X k l, Measurable (fun t => G t X k l))
  (hf : ∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l))
  (hϖ : 0 < ϖ) (hρ : 0 < ρ) (hscale : ρ * ϖ ≤ 1)
  (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (hg : 0 ≤ g) (hδ : δ = ζ * ϖ)
  (hjet : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
    ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r)

include hM hK hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet in
theorem exists_metricTaylor_allMoment_linearMap :
    ∃ T : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
        (volume.restrict (Set.Icc a b)),
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) T := by
  let μ := volume.restrict (Set.Icc a b)
  let U := fun x t => planeTimeAllMomentCarrierToLp (E := E) (K + 1) ϖ ρ 0 μ x t
  let C := fun t z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z
  obtain ⟨hadd, hsmul⟩ := planeMatrixGradientFlux_curve_superposition μ C U
    (planeTimeAllMomentCarrier_add (K + 1) ϖ ρ 0 μ)
    (planeTimeAllMomentCarrier_smul (K + 1) ϖ ρ 0 μ)
  apply exists_planeRaw_allMoment_linearMap K ϖ ρ 0 μ
    (fun x t => planeMatrixGradientFlux (C t) (U x t)) hadd hsmul
  intro x n
  obtain ⟨C0, _, hnative⟩ := metricTaylorMatrix_native_flux_exists (E := E) Ks Kmax M hM
  have he := integrated_weightedGradFactorialNormSq_ne_top_of_lift (n + Ks) ϖ 0 ρ hρ μ (U x)
    (planeTimeAllMomentCarrier_moment (K + 1) ϖ ρ 0 μ x (n + Ks))
  obtain ⟨V, hV, hVe, hv, _⟩ := hnative K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale
    hζ hζ1 hg hδ hjet n (U x) (planeTimeAllMomentCarrier_memLp (K + 1) ϖ ρ 0 μ x) he
  exact ⟨V, hV, hVe, hv⟩
end

/-! Bounded smooth matrix coefficients act on the actual native all-moment lift carrier. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance matrixGradientMomentNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance matrixGradientMomentModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k

theorem exists_planeMatrixGradient_allMoment_map
    (K : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (C : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hm : ∀ k l z, Measurable (fun t => C t z k l))
    (hc : ∀ k l t, ContDiff ℝ (K : ℕ) (fun z => C t z k l))
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ k l, ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => C t z k l) z‖ ≤ B) :
    ∃ T : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0 μ,
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
        (fun x t => planeMatrixGradientFlux (C t)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 μ x t)) T := by
  let U := fun x t => planeTimeAllMomentCarrierToLp (E := E) (K + 1) ϖ ρ 0 μ x t
  obtain ⟨hadd, hsmul⟩ := planeMatrixGradientFlux_curve_superposition μ C U
    (planeTimeAllMomentCarrier_add (K + 1) ϖ ρ 0 μ)
    (planeTimeAllMomentCarrier_smul (K + 1) ϖ ρ 0 μ)
  apply exists_planeRaw_allMoment_linearMap K ϖ ρ 0 μ
    (fun x t => planeMatrixGradientFlux (C t) (U x t)) hadd hsmul
  intro x n
  have he := integrated_weightedGradFactorialNormSq_ne_top_of_lift n ϖ 0 ρ hρ μ (U x)
    (planeTimeAllMomentCarrier_moment (K + 1) ϖ ρ 0 μ x n)
  have hcoeff : ∀ k l, ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (fun z => C t z k l) z‖ ≤
        B * polynomialMomentRoot ϖ z ^ 0 := by
    simpa only [pow_zero, mul_one] using hb
  obtain ⟨V, hV, hVe, hv, _⟩ := metricMatrix_native_flux_exists K n 0 ϖ ρ hϖ hρ μ
    (fun k l t z => C t z k l) hm hc B hB hcoeff (U x)
    (planeTimeAllMomentCarrier_memLp (K + 1) ϖ ρ 0 μ x) (by simpa only [Nat.add_zero] using he)
  exact ⟨V, hV, hVe, hv⟩
end

end AVRegularity.CycleJointProofs
end

section
open Homogenization AVenhance MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleJointProofs

/-! Actual higher reference traces and energy states retain their exact initial data and truncation agreement in positive diffusion time. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {Cpad Cage : ℝ} {Npad Jchart : ℕ} {Cchart : ℕ → ℝ} {l₀ : ℤ} {Pcover : ℕ}

theorem preparation_window_reference_normalized_trace_data_subwindow {ν a b c d : ℝ} {v : ℝ → Vec 2 → Vec 2}
    {D : ℕ} {K : ι → ℕ}
    {A : ∀ i i', (d : admissibleOrders K D i i') → ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i)}
    {f : ∀ i, PlaneHk univ (K i) (h i)}
    {F : ∀ i, ℝ → PlaneHk univ (K i) (PiLp 2 (fun _ : Fin 2 => h i))}
    {g : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {u : ∀ i, ℝ → PlaneHk univ (K i) (h i)}
    {w : ∀ i, ℝ → PlaneHk univ (K i + 1) (h i)}
    (hs : IsCoupledWeakSolutionPlane ν c d v D K A f F g u w) (hν : 0 < ν)
    {P' : Type*} {Ctx : P' → Type*} (family : ChartedFamily ι h D P' Ctx)
    (hprep : IsPreparationChartCertificate α q Λ m φ hφ a b Cpad Cage Npad Jchart Cchart l₀ Pcover family)
    (hcover : Icc a b ⊆ ⋃ p, (family.piece p).output)
    (σ : ℝ) (hσ : σ ∈ Icc a b) (ha : 0 ≤ ocA α q Λ (m - 1))
    (hK : ∀ j, K j ≤ Jchart) (hsub : Icc c d ⊆ Icc a b) (i : ι) :
    let U : ℝ → PlaneHk univ (K i) (h i) := fun t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K i)
        (by have hh := hK i; omega) (ν⁻¹ * t) (u i (ν⁻¹ * t))
    let W : ℝ → PlaneHk univ (K i + 1) (h i) := fun t =>
      preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K i + 1)
        (Nat.add_le_add_right (hK i) 1) (ν⁻¹ * t) (w i (ν⁻¹ * t))
    ContinuousOn U (Icc (ν * c) (ν * d)) ∧
    MemLp W 2 (volume.restrict (Icc (ν * c) (ν * d))) ∧
    (∀ᵐ t ∂volume.restrict (Icc (ν * c) (ν * d)),
      truncatePlaneHk (Nat.le_succ (K i)) (W t) = U t) ∧
    U (ν * c) = preparationWindowReferenceHkWindowPull hprep hcover σ hσ ha (K i)
      (by have hh := hK i; omega) c (f i) := by
  dsimp only
  have hdata := preparation_window_reference_chart_trace_data_subwindow hs family hprep hcover σ hσ ha hK hsub i
  refine ⟨hdata.1.comp (continuous_const.mul continuous_id).continuousOn
      (fun _ ht => positiveTimeNormalization_mem_Icc hν ht),
    memLp_comp_inv_mul_restrict_Icc hν hdata.2.1,
    ae_comp_inv_mul_restrict_Icc hν hdata.2.2, ?_⟩
  rw [show ν⁻¹ * (ν * c) = c by rw [← mul_assoc, inv_mul_cancel₀ hν.ne', one_mul],
    hs.2.2.2.1 i]

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The bounded spatially central metric constructs its literal native
all-moment forcing map, independently of the positive Taylor insertions. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem exists_planeCentralMetric_allMoment_map
    (K : ℕ) (a b ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hm : ∀ k l, Measurable (fun t => M t k l))
    (g : ℝ) (hg : 0 ≤ g) (hsym : ∀ t ∈ Set.Icc a b, (M t).IsSymm)
    (hnear : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      |∑ i, ∑ j, ξ i * (M t - (1 : Matrix (Fin 2) (Fin 2) ℝ)) i j * ξ j| ≤
        g * ∑ i, ξ i ^ 2) :
    ∃ T : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
        (volume.restrict (Set.Icc a b)),
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux (fun _ => M t - 1)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) T := by
  apply exists_planeMatrixGradient_allMoment_map K ϖ ρ hϖ hρ
    (volume.restrict (Set.Icc a b)) (fun t _ => M t - 1)
  · intro k l _
    exact (hm k l).sub measurable_const
  · intro _ _ _
    exact contDiff_const
  · exact hg
  · intro k l
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    intro j _ z
    cases j with
    | zero =>
      simpa [iteratedFDeriv_zero_eq_comp, Real.norm_eq_abs] using symmetricMetric_difference_entry_abs_le (M t) g (hsym t ht) (hnear t ht) k l
    | succ j =>
      rw [iteratedFDeriv_const_of_ne (by omega)]
      simpa using hg

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Actual native positive metric insertion maps retain the uniform small metric gain and the exact polynomial moment shift. -/

theorem metricTaylor_allMoment_linearMap_budget_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E], ∀ K ≤ Kmax,
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r) →
      ∀ T : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
          (volume.restrict (Set.Icc a b)),
      IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) T →
      ∀ x n,
        (∫⁻ t in Set.Icc a b, weightedFactorialNormSq n ϖ 0 ρ K
          (planeTimeAllMomentCarrierToLp K ϖ ρ 0 (volume.restrict (Set.Icc a b)) (T x) t)) ≤
        ENNReal.ofReal ((4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) ^ 2) *
          ∫⁻ t in Set.Icc a b, weightedGradFactorialNormSq (n + Ks) ϖ 0 ρ K
            (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)) x t) := by
  obtain ⟨C, hC, hnative⟩ := metricTaylorMatrix_native_flux_exists_uniform Ks Kmax M hM
  refine ⟨C, hC, ?_⟩
  intro E _ _ _ _ _ _ K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet T hT x n
  let μ := volume.restrict (Set.Icc a b)
  let U := fun t => planeTimeAllMomentCarrierToLp (E := E) (K + 1) ϖ ρ 0 μ x t
  have he := integrated_weightedGradFactorialNormSq_ne_top_of_lift Ks ϖ 0 ρ hρ μ U
    (planeTimeAllMomentCarrier_moment (K + 1) ϖ ρ 0 μ x Ks)
  obtain ⟨V, _, _, hv, hdens⟩ := hnative K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale
    hζ hζ1 hg hδ hjet 0 U (planeTimeAllMomentCarrier_memLp (K + 1) ϖ ρ 0 μ x) (by simpa using he)
  have hrep := planeRaw_allMoment_map_represents K ϖ ρ 0 μ _ T hT x V hv
  have hi := lintegral_congr_ae (hrep.fun_comp (fun Q => weightedFactorialNormSq n ϖ 0 ρ K Q))
  simp only [Function.comp_apply] at hi
  rw [hi]
  exact nativeFlux_time_moment_shift_budget n Ks ϖ ρ
    (4 * Real.sqrt (multiplicationDensityBudget K) * (C * g * ζ)) μ V U hdens

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Polynomially growing native arrays construct actual all-moment source maps at their literal jet order. -/

variable {U V : Type*} [NormedAddCommGroup U] [InnerProductSpace ℝ U]
  [FiniteDimensional ℝ U] [MeasurableSpace U] [BorelSpace U] [CompleteSpace U]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]

theorem planeNativeArrayPolynomial_allMoment_density
    {K L r : ℕ} (hKL : K + r ≤ L + 1) (hr : 1 ≤ r)
    (p : ℕ) (ϖ ρ : ℝ) (hϖ : 0 < ϖ) (hρ : 0 < ρ) (μ : Measure ℝ)
    (c : Fin 2 → DerivativeWord2 r → ℝ → Vec 2 → ℝ)
    (hm : ∀ a I z, Measurable (fun t => c a I t z))
    (hc : ∀ a I t, ContDiff ℝ (K : ℕ) (c a I t)) (C : U →L[ℝ] V)
    (B : Fin 2 → DerivativeWord2 r → ℝ) (hB : ∀ a I, 0 ≤ B a I)
    (hb : ∀ a I, ∀ᵐ t ∂μ, ∀ j ≤ K, ∀ z,
      ρ ^ j * ‖iteratedFDeriv ℝ j (c a I t) z‖ ≤ B a I * polynomialMomentRoot ϖ z ^ p)
    (T : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => V)) K ϖ ρ 0 μ)
    (hT : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun x t z => nativeArrayAssembly r C (fun a I => c a I t z)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z))) T)
    (x : PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ) :
    ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ 0 μ (T x) t) z ≤
        (∑ β : Fin 2 × DerivativeWord2 r,
          Real.sqrt (multiplicationDensityBudget K) *
            (B β.1 β.2 * derivativeReserveFactor ρ K (r - 1) * ‖C‖)) ^ 2 *
          ((polynomialMomentRoot ϖ z ^ p) ^ 2 *
            planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) z) := by
  classical
  let X := PlaneTimeAllMomentCarrier (E := U) (L + 1) ϖ ρ 0 μ
  let H := fun (β : Fin 2 × DerivativeWord2 r) (x : X) t z =>
    c β.1 β.2 t z • Weighted.fluxCoordinateInjection β.1 C
      (planeJetOrder (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r β.2 z)
  have hex (β : Fin 2 × DerivativeWord2 r) :=
    exists_planePolynomialJetMultiplier_allMoment_map hKL hr β.2 p ϖ ρ hϖ hρ μ
      (c β.1 β.2) (hm β.1 β.2) (hc β.1 β.2) (Weighted.fluxCoordinateInjection β.1 C)
      (B β.1 β.2) (hB β.1 β.2) (hb β.1 β.2)
  choose S hS using hex
  have hraw := planeRaw_allMoment_linearMap_sum (X := X)
    (E := PiLp 2 (fun _ : Fin 2 => V)) K ϖ ρ 0 μ H S hS
  have heq : (fun (x : X) t z => nativeArrayAssembly r C (fun a I => c a I t z)
      (WithLp.toLp 2 (fun I => planeJetOrder
        (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z))) =
      fun x t z => ∑ β, H β x t z := by
    funext x t z
    rw [nativeArrayAssembly_value_expansion, Fintype.sum_prod_type]
  have hfull : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun (x : X) t z => nativeArrayAssembly r C (fun a I => c a I t z)
        (WithLp.toLp 2 (fun I => planeJetOrder
          (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) r I z))) (∑ β, S β) := by
    rw [heq]
    exact hraw
  have huniq := planeRaw_allMoment_map_unique (X := X) (E := PiLp 2 (fun _ : Fin 2 => V))
    K ϖ ρ 0 μ _ _ T (∑ β, S β) hT hfull (fun _ => Filter.Eventually.of_forall
      (fun _ => Filter.Eventually.of_forall (fun _ => rfl)))
  let R := derivativeReserveFactor ρ K (r - 1)
  have hR : 0 ≤ R := by dsimp only [R]; unfold derivativeReserveFactor; positivity
  let price := fun β : Fin 2 × DerivativeWord2 r =>
    Real.sqrt (multiplicationDensityBudget K) * (B β.1 β.2 * R * ‖C‖)
  have hp (β : Fin 2 × DerivativeWord2 r) : 0 ≤ price β :=
    mul_nonneg (Real.sqrt_nonneg _) (mul_nonneg (mul_nonneg (hB β.1 β.2) hR) (norm_nonneg _))
  have hden (β : Fin 2 × DerivativeWord2 r) : ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (planeTimeAllMomentCarrierToLp K ϖ ρ 0 μ (S β x) t) z ≤
        price β ^ 2 * ((polynomialMomentRoot ϖ z ^ p) ^ 2 *
          planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) z) := by
    have hh := planePolynomialJetMultiplier_allMoment_density hKL hr β.2 p ϖ ρ hϖ hρ μ
      (c β.1 β.2) (hm β.1 β.2) (hc β.1 β.2) (Weighted.fluxCoordinateInjection β.1 C)
      (B β.1 β.2) (hB β.1 β.2) (hb β.1 β.2) (S β) (hS β) x
    have hcost := mul_le_mul_of_nonneg_left (fluxCoordinateInjection_norm_le β.1 C)
      (mul_nonneg (hB β.1 β.2) hR)
    have hprice : price β ^ 2 = multiplicationDensityBudget K * (B β.1 β.2 * R * ‖C‖) ^ 2 := by
      dsimp only [price]
      rw [mul_pow, Real.sq_sqrt (multiplicationDensityBudget_nonneg K)]
    filter_upwards [hh] with t ht
    filter_upwards [ht] with z hz
    rw [hprice]
    simp only [← mul_assoc]
    apply hz.trans
    apply mul_le_mul_of_nonneg_right _ (planeGradFactorialDensity_nonneg _ _ _)
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (mul_nonneg (mul_nonneg (hB β.1 β.2) hR) (norm_nonneg _)) hcost 2)
      (multiplicationDensityBudget_nonneg K)
  rw [huniq]
  simp only [LinearMap.sum_apply]
  have hsum := planeTimeAllMomentCarrier_sum_ae K ϖ ρ 0 μ (fun β => S β x)
  filter_upwards [ae_all_iff.mpr hden, hsum] with t ht hsumt
  rw [hsumt]
  exact nativeFactorialDensity_sum_price_le ρ
    (fun β => planeTimeAllMomentCarrierToLp K ϖ ρ 0 μ (S β x) t) price hp
    (fun z => (polynomialMomentRoot ϖ z ^ p) ^ 2 *
      planeGradFactorialDensity ρ (planeTimeAllMomentCarrierToLp (L + 1) ϖ ρ 0 μ x t) z)
    (fun z => mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _)) ht

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Certified full metric maps equal their actual central, positive Taylor and remainder maps. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance metricMapConstructionNormed (k : ℕ) : NormedAddCommGroup (PlaneHk Set.univ k E) :=
  allMomentTimeNativeNormed k
local instance metricMapConstructionModule (k : ℕ) : Module ℝ (PlaneHk Set.univ k E) :=
  allMomentTimeNativeModule k

theorem metric_allMoment_map_taylor_construction
    (K Ks : ℕ) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (diag positive remainder : PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0 μ)
    (hdiag : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun x t => planeMatrixGradientFlux (fun _ => G t 0 - 1)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 μ x t)) diag)
    (hpositive : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun x t => planeMatrixGradientFlux
        (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 μ x t)) positive)
    (hremainder : IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun x t => planeMatrixGradientFlux
        (fun z k l => G t z k l - taylorSlow 0 Ks (fun y => G t y k l) 0 z)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 μ x t)) remainder) :
    IsPlaneTimeAllMomentRawLinearMap K ϖ ρ 0 μ
      (fun x t => planeMatrixGradientFlux (fun z => G t z - 1)
        (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 μ x t)) (diag + positive + remainder) := by
  have hp := planeRaw_allMoment_linearMap_add K ϖ ρ 0 μ _ _ diag positive hdiag hpositive
  have hr := planeRaw_allMoment_linearMap_add K ϖ ρ 0 μ _ _ _ remainder hp hremainder
  intro x
  filter_upwards [hr x] with t ht
  apply ht.trans
  exact Filter.Eventually.of_forall (fun z =>
    (planeMatrixGradientFlux_taylor_split Ks (G t)
      (planeTimeAllMomentCarrierToLp (K + 1) ϖ ρ 0 μ x t) z).symm)

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Variational
namespace AVRegularity.CycleJointProofs

/-! Componentwise central metric maps assemble into the literal diagonal
family forcing map through the coordinate projections. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeDiagonal_allMoment_family_map
    (K : ι → ℕ) (D : ℕ) (hD : 2 ≤ D) (ϖ ρ : ℝ) (μ : Measure ℝ)
    (M : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (diag : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0 μ →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i) ϖ ρ 0 μ)
    (hdiag : ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun X t => planeMatrixGradientFlux (fun _ => M t - 1)
        (planeTimeAllMomentCarrierToLp (K i + 1) ϖ ρ 0 μ X t)) (diag i)) :
    ∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 μ
      (fun (X : ∀ j, PlaneTimeAllMomentCarrier (E := h j) (K j + 1) ϖ ρ 0 μ) t =>
        planeRawCouplingFlux K D t
        (planeDiagonalGradientCoefficient K D (fun _ t _ => M t - 1))
        (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i)
      ((diag i).comp (LinearMap.proj i)) := by
  intro i X
  filter_upwards [hdiag i (X i)] with t ht
  filter_upwards [ht] with z hz
  exact hz.trans (planeRawCouplingFlux_diagonal_matrix_flux K D hD
    (fun _ t _ => M t - 1)
    (fun j => planeTimeAllMomentCarrierToLp (K j + 1) ϖ ρ 0 μ (X j) t) i t z).symm

end AVRegularity.CycleJointProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual positive metric maps obey a uniform family mass bound with their small metric factor and exact moment shift. -/

theorem metricTaylor_family_map_mass_moment_budget_uniform (Ks Kmax : ℕ)
    (M : ℕ → ℝ) (hM : ∀ r, 0 ≤ M r) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {ι : Type*} [Fintype ι] {E : ι → Type*}
      [∀ i, NormedAddCommGroup (E i)] [∀ i, InnerProductSpace ℝ (E i)]
      [∀ i, FiniteDimensional ℝ (E i)] [∀ i, MeasurableSpace (E i)]
      [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)],
      ∀ (K : ι → ℕ), (∀ i, K i ≤ Kmax) →
      ∀ (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (a b ϖ ρ δ ζ g : ℝ),
      (∀ X k l, Measurable (fun t => G t X k l)) →
      (∀ t ∈ Set.Icc a b, ∀ k l, ContDiff ℝ (Ks : ℕ) (fun z => G t z k l)) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → ζ ≤ 1 → 0 ≤ g → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r, 1 ≤ r → r ≤ Ks → ∀ k l,
        ‖iteratedFDeriv ℝ r (fun z => G t z k l) 0‖ ≤ M r * g * δ ^ r) →
      ∀ (π : ι → ℝ)
        (T : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
          (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
          PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E i)) (K i) ϖ ρ 0
            (volume.restrict (Set.Icc a b))),
      (∀ i, IsPlaneTimeAllMomentRawLinearMap (K i) ϖ ρ 0 (volume.restrict (Set.Icc a b))
        (fun x t => planeMatrixGradientFlux
          (fun z k l => taylorSlow 1 Ks (fun y => G t y k l) 0 z)
          (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0
            (volume.restrict (Set.Icc a b)) x t)) (T i)) →
      ∀ (W : ∀ i, PlaneTimeAllMomentCarrier (E := E i) (K i + 1) ϖ ρ 0
        (volume.restrict (Set.Icc a b))) (n : ℕ),
      planeAllMomentFamilyEnergy (E := fun i => PiLp 2 (fun _ : Fin 2 => E i))
        K n ϖ ρ (volume.restrict (Set.Icc a b)) π (fun i => T i (W i)) ≤
        ENNReal.ofReal (metricTaylorUniformDensityPrice Kmax * (C * g * ζ) ^ 2) *
          planeAllMomentFamilyGradientEnergy (E := E) K (n + Ks) ϖ ρ
            (volume.restrict (Set.Icc a b)) π W := by
  obtain ⟨C, hC, hb⟩ := metricTaylor_allMoment_linearMap_budget_uniform Ks Kmax M hM
  refine ⟨C, hC, ?_⟩
  intro ι _ E _ _ _ _ _ _ K hK G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet π T hT W n
  let μ := volume.restrict (Set.Icc a b)
  let F := fun i t => weightedFactorialNormSq n ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := PiLp 2 (fun _ : Fin 2 => E i))
      (K i) ϖ ρ 0 μ (T i (W i)) t)
  let Q := fun i t => weightedGradFactorialNormSq (n + Ks) ϖ 0 ρ (K i)
    (planeTimeAllMomentCarrierToLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i) t)
  have hF (i : ι) : AEMeasurable (F i) μ :=
    AVRegularity.Weighted.weightedFactorialNormSq_time_aemeasurable
      (E := PiLp 2 (fun _ : Fin 2 => E i)) n ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := PiLp 2 (fun _ : Fin 2 => E i))
        (K i) ϖ ρ 0 μ (T i (W i)))
  have hQ (i : ι) : AEMeasurable (Q i) μ :=
    weightedGradFactorialNormSq_time_aemeasurable (E := E i) (n + Ks) ϖ 0 ρ μ _
      (planeTimeAllMomentCarrier_memLp (E := E i) (K i + 1) ϖ ρ 0 μ (W i))
  apply finite_mass_time_integral_budget μ (fun i => ENNReal.ofReal ((π i)⁻¹))
    F Q _ hF hQ
  intro i
  have hi := hb (K i) (hK i) G a b ϖ ρ δ ζ g hm hf hϖ hρ hscale hζ hζ1 hg hδ hjet
    (T i) (hT i) (W i) n
  exact hi.trans (mul_le_mul_of_nonneg_right
    (ENNReal.ofReal_le_ofReal (metricTaylor_density_price_le (K i) Kmax (hK i) (C * g * ζ))) zero_le)

end AVRegularity.CycleJointProofs
end
