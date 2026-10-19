-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.PlaneAllMomentNativeResidualBudget
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
import Mathlib.MeasureTheory.SpecificCodomains.WithLp

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Actual component response certificates depend only on the metric on their native time window. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

local instance responseWindowFluxNormed : NormedAddCommGroup (PiLp 2 (fun _ : Fin 2 => E)) :=
  componentCertificateFluxNormed
local instance responseWindowFluxInner : InnerProductSpace ℝ (PiLp 2 (fun _ : Fin 2 => E)) :=
  componentCertificateFluxInner

theorem planeComponentAllMomentResponse_metric_window_congr
    (M M' : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (K : ℕ) (a b ϖ ρ : ℝ)
    (R : PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => E)) K ϖ ρ 0
      (volume.restrict (Set.Icc a b)) →ₗ[ℝ]
      PlaneTimeAllMomentCarrier (E := E) (K + 1) ϖ ρ 0 (volume.restrict (Set.Icc a b)))
    (hR : IsPlaneComponentAllMomentResponse M v K a b ϖ ρ R)
    (heq : ∀ t ∈ Set.Icc a b, M' t = M t) :
    IsPlaneComponentAllMomentResponse M' v K a b ϖ ρ R := by
  intro x
  obtain ⟨F, u, w, hs, hi, ho⟩ := hR x
  refine ⟨F, u, w, ?_, hi, ho⟩
  apply isPlaneChainFrom_geometryScalarData_congr _ hs
  intro t ht
  funext z
  exact heq t ht

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.Weighted
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The actual retained error inherits finite gradient energy from the prepared solution and the native response. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance retainedErrorGradientNormed (i : ι) (k : ℕ) :
    NormedAddCommGroup (PlaneHk Set.univ k (h i)) := allMomentTimeNativeNormed k

theorem planeRetained_error_gradient_finite
    (K : ι → ℕ) (n : ℕ) (ϖ ρ a b : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (uH : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (wH w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hwH : ∀ i, MemLp (wH i) 2 (volume.restrict (Set.Icc a b)))
    (hprepared : geometryEnergyNorm π K n ϖ 0 ρ a b uH wH < ⊤)
    (W : ∀ i, PlaneTimeAllMomentCarrier (E := h i) (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)))
    (hW : ∀ i, PlaneTimeAllMomentRepresents (K i + 1) ϖ ρ 0
      (volume.restrict (Set.Icc a b)) (W i) (w i))
    (hresponse : planeAllMomentFamilyGradientEnergy K n ϖ ρ
      (volume.restrict (Set.Icc a b)) π W ≠ ⊤) :
    ∀ i, (∫⁻ t in Set.Icc a b,
      weightedGradFactorialNormSq n ϖ 0 ρ (K i) (wH i t - w i t)) ≠ ⊤ := by
  intro i
  obtain ⟨_, _, _, heH⟩ := finite_geometry_energy_component π hπ K n ϖ 0 ρ a b uH wH hprepared i
  have heW := planeAllMomentFamilyGradientEnergy_component_ne_top K n ϖ ρ
    (volume.restrict (Set.Icc a b)) π hπ W w hW hresponse i
  exact integrated_weightedGradFactorialNormSq_sub_ne_top n ϖ 0 ρ
    (volume.restrict (Set.Icc a b)) (wH i) (w i) (hwH i) heH heW

end AVRegularity.CycleJointProofs
end
end

section
public noncomputable section
open Homogenization AVenhance AVRegularity.CycleReference AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! The actual and frozen metrics have simultaneous uniform adjoint weights
 and an internally chosen finite reserve at every requested moment order. -/

theorem windowCover_uniform_subwindow_weights_with_gains {α s q : ℝ}
    (hα0 : 0 < α) (hα1 : α < 1 / 3) (hs0 : 0 < s) (hs1 : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) {ζ : ℝ → ℝ} (hζ : IsFastProfile ζ)
    {ι : Type*} [Fintype ι] (C : ι → ℝ) :
    ∃ Cw : ℕ → ℝ, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ N : ℕ, ∃ L : ℕ, 1 ≤ L ∧
      (∀ k ≤ N, Real.exp (18 * Cw k) / (L : ℝ) ^ 2 ≤ 1 / 16) ∧
    ∀ Λ : ℕ, Λ₀ ≤ Λ →
    ∀ (Φ : ℕ → ℝ → Vec 2 → ℝ) (M : ℕ) (κ : ℕ → ℝ),
      IsOCBandChain α q Λ ζ M κ →
    ∀ m : ℕ, 2 ≤ m → m ≤ M → ∀ (ν B : ℝ), κ m = ν → κ (m - 1) = B →
    ∀ (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tA tZ ρs g g0 a B₀ lam Cb : ℝ) (qJ Kmax : ℕ) (CG : ℕ → ℝ)
      (l₀ : ℤ) (P : ℕ) (y₀ : Vec 2),
      IsWindowCover α q Λ m ζ Φ hφ ν B tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀ →
      g ≤ 1 → g0 ≤ 1 / 4 →
    ∀ (i : Fin (P + 2)) (u0 u1 : ℝ), u0 < u1 →
      Set.Icc u0 u1 ⊆ windowCoverChartWindow α q Λ m ν tA tZ l₀ P i →
      u1 - u0 ≤ ocTauPP α q Λ m / ocEll q Λ m ν ^ 2 →
    let G := ocCellMetric α q Λ m (Φ (m - 1)) hφ (l₀ - 1 + i) ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i)
    let v := ocCellDrift α q Λ ζ m ν
      (windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ i)
    let ϖ := ocEpsilon q Λ m / Real.sqrt (B * ocTauPP α q Λ m)
    Nonempty (ChartWeights G v u0 (u1 - u0) ϖ 0 N Cw) ∧
      Nonempty (ChartWeights (fun t _ => G t 0) v u0 (u1 - u0) ϖ 0 N Cw) ∧
      ∀ j, ENNReal.ofReal (C j * g *
        (Real.sqrt (B * ocTauPP α q Λ m) / ocEpsilon q Λ (m - 1))) ≤ 1 := by
  obtain ⟨Cw, Lw, hLw, hw⟩ :=
    windowCover_uniform_subwindow_weights_with_fixed_reserve hα0 hα1 hs0 hs1 hq hζ
  obtain ⟨Lg, hLg, hg⟩ := exists_uniform_preparation_response_gains hα0 hα1 hs0 hs1 hq hζ C
  refine ⟨Cw, max Lw Lg, hLw.trans (le_max_left _ _), ?_⟩
  intro N
  obtain ⟨L, hL, hreserve, hweights⟩ := hw N
  refine ⟨L, hL, hreserve, ?_⟩
  intro Λ hΛ Φ M κ hκ m hm hmM ν B hν hB hφ tA tZ ρs g g0 a B₀ lam Cb
    qJ Kmax CG l₀ P y₀ cov hg1 hg0 i u0 u1 hu hwindow hlength G v ϖ
  have hΛw := (le_max_left _ _).trans hΛ
  have hΛg := (le_max_right _ _).trans hΛ
  have hp := hweights Λ hΛw Φ M κ hκ m hm hmM ν B hν hB hφ
    tA tZ ρs g g0 a B₀ lam Cb qJ Kmax CG l₀ P y₀ cov hg0 i u0 u1 hu hwindow hlength
  have hgain := (hg Λ hΛg M (by omega) κ hκ m hm hmM).2 g cov.g_range.1 hg1
  rw [hB] at hgain
  exact ⟨hp.1, hp.2, hgain⟩

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set Filter AVRegularity.Weighted AVRegularity.CycleReference
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! Native material flux pullbacks have exact joint readouts and the genuine Bochner time class. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]

theorem planeFluxChartPull_joint_readout {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (s : ℝ) (F : ℝ → PlaneFluxL2 E) (Q : Fin 2 → ℝ × Vec 2 → E)
    (he : ∀ t k, (F t k : Vec 2 → E) =ᵐ[volume] fun x => Q k (t, x)) (t : ℝ) (k : Fin 2) :
    (planeFluxChartPull hφ t s (F t) k : Vec 2 → E) =ᵐ[volume]
      fun y => hilbertChartFlux hφ s Q k (t, y) := by
  have hq := ae_all_iff.mpr (fun j =>
    (streamFlow_measurePreserving hφ t s).quasiMeasurePreserving.ae_eq_comp (he t j))
  apply (planeFluxChartPull_ae hφ t s (F t) k).trans
  filter_upwards [hq] with y hqy
  change (∑ j : Fin 2, (chartJac hφ s t y)⁻¹ k j • F t j (AVRegularity.streamFlow φ hφ t y s)) =
    ∑ j : Fin 2, (chartJac hφ s t y)⁻¹ k j • Q j (t, AVRegularity.streamFlow φ hφ t y s)
  apply Finset.sum_congr rfl
  intro j _
  exact congrArg (fun z : E => (chartJac hφ s t y)⁻¹ k j • z) (hqy j)

variable [FiniteDimensional ℝ E] [CompleteSpace E]

theorem planeFluxChartPull_time_memLp {a b : ℝ} {φ : ℝ → Vec 2 → ℝ}
    (hφ : IsAdmissibleStream φ) (s : ℝ) (F : ℝ → PlaneFluxL2 E)
    (hF : MemLp F 2 (volume.restrict (Icc a b))) :
    MemLp (fun t => planeFluxChartPull hφ t s (F t)) 2 (volume.restrict (Icc a b)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  obtain ⟨Q, hQ, heQ⟩ := planeFlux_exists_joint_fields F hF
  have hm : volume.restrict (Icc a b ×ˢ (univ : Set (Vec 2))) =
      (volume.restrict (Icc a b)).prod volume := by
    rw [Measure.volume_eq_prod ℝ (Vec 2), ← Measure.prod_restrict, Measure.restrict_univ]
  apply memLp_piLp_iff.mpr
  intro k
  have hq : MemLp (hilbertChartFlux hφ s Q k) 2 ((volume.restrict (Icc a b)).prod volume) := by
    rw [← hm]
    exact hilbertChartFlux_joint_memLp hφ s a b Q (fun j => by rw [hm]; exact hQ j) k
  exact bochner_memLp_of_joint_representation (volume.restrict (Icc a b)) volume
    (hilbertChartFlux hφ s Q k) hq (fun t => planeFluxChartPull hφ t s (F t) k)
    (Eventually.of_forall (fun t => planeFluxChartPull_joint_readout hφ s F Q heQ t k))

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Reference and cell transformations preserve the original strict source-depth rank. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

theorem preparationReferenceCellSourceCoefficient_zero_of_rank
    (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
    (H : ℕ) (hdepth : F.HasDepthAtMost H) (s ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (yc : Vec 2)
    (v u : ι) (d : admissibleOrders K D v u)
    (hr : ¬ sourceDepthRank F H u < sourceDepthRank F H v) :
    preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d = 0 := by
  have hz := physicalCoefficient_zero_of_no_edge (referenceChartedFamily F hφ s)
    ν e E actual v u d.1 (fun hed => hr (sourceDepthRank_edge_lt hdepth hed))
  funext t z
  unfold preparationReferenceCellSourceCoefficient edgeCoefficient
  rw [hz]
  simp only [Pi.zero_apply]
  change ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) •
    (0 : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h v)) = 0
  exact smul_zero (A := PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => h v)) ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! The original active constituents have genuine scalar native source rows in the common reference chart, with continuity and periodicity proved from the preparation inputs. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {φ : ℝ → Vec 2 → ℝ}

variable (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ) (s : ℝ)
    (ν e E : ℝ) (actual : ∀ p, Ctx p) (p : P) (v u : ι) (γ : F.Γ v u) (t : ℝ)

def pieceReferenceNativeScalarJetCoefficient (J : ℕ) (k : Fin 2) (z : JetIndex2 J) : Vec 2 → ℝ :=
  transportedNativeScalarJetCoefficient (pieceReferenceMaterial F hφ s p t)
    (F.identity v u γ).maxOrder
    (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t) k z

theorem pieceReferenceNativeScalarJetCoefficient_periodic
    (hT : IsTorusCompatible F actual E) {N : ℕ} (he : e⁻¹ = N)
    (J : ℕ) (k : Fin 2) (z : JetIndex2 J) :
    IsZ2Periodic (pieceReferenceNativeScalarJetCoefficient F hφ s ν e E actual p v u γ t J k z) :=
  transportedNativeScalarJetCoefficient_periodic (pieceReferenceMaterial F hφ s p t)
    (pieceReferenceMaterial_equivariant F hφ s p t E actual hT)
    (F.identity v u γ).maxOrder _
    (pieceDimensionalNativeJetArray_periodic F ν e E actual hT he p v u γ t) k z

theorem active_pieceReferenceNativeScalarJetCoefficient_continuous
    (a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (ht : t ∈ Set.Icc a b) (hp : p ∈ (F.locally_finite t t).toFinset)
    (J : ℕ) (k : Fin 2) (z : JetIndex2 J) :
    Continuous (pieceReferenceNativeScalarJetCoefficient F hφ s ν e E actual p v u γ t J k z) := by
  have hB (r : ℕ) (I : DerivativeWord2 r) : ContDiff ℝ (0 : ℕ)
      (pieceDimensionalNativeJetArray F ν e E p (actual p) v u γ t r I) :=
    (active_pieceDimensionalNativeJetArray_smooth F ν e E a b n hs t ht ⟨p, hp⟩
      (actual p) v u γ r I).of_le (by simp)
  exact (transportedNativeScalarJetCoefficient_smooth (pieceReferenceMaterial F hφ s p t)
    (pieceReferenceMaterial_smooth F hφ s p t) (pieceReferenceMaterial_symm_smooth F hφ s p t)
    (F.identity v u γ).maxOrder 0 _ hB k z).continuous

variable [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

def activePieceReferenceScalarRowOperator
    (a b : ℝ) (n : ι → ℕ)
    (hs : F.IsSmoothOn (ChartedFamily.Domain.onWindow F (Set.Icc a b)) E n)
    (hT : IsTorusCompatible F actual E) {N : ℕ} (he : e⁻¹ = N)
    (ht : t ∈ Set.Icc a b) (hp : p ∈ (F.locally_finite t t).toFinset)
    (J : ℕ) (k : Fin 2) : PlaneHk Set.univ J (h v) →L[ℝ] Lp (h v) 2 (volume : Measure (Vec 2)) :=
  periodicScalarRowOperator
    (pieceReferenceNativeScalarJetCoefficient F hφ s ν e E actual p v u γ t J k)
    (active_pieceReferenceNativeScalarJetCoefficient_continuous F hφ s ν e E actual p v u γ t
      a b n hs ht hp J k)
    (pieceReferenceNativeScalarJetCoefficient_periodic F hφ s ν e E actual p v u γ t hT he J k)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem inactiveTimeZeroFamily_natural_remainder_bounded_price_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p) :
    ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ρ / e ≤ ocEpsilon q Λ (m - 1) / e →
    ∀ (ϖ ζ : ℝ), 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
    K v ≤ Jchart + 1 → ∀ τ, τ ∈ W →
    ∀ (yc z : Vec 2) (k : Fin 2) (j : ℕ), j ≤ K v →
    let Y := fun x => streamFlow φ hφ r (yc + e • x) σ
    let Yc := streamFlow φ hφ r yc σ
    let Dchart := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
      molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
            derivativeReserveFactor (ρ / e) (K v) (d - 2)
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j (fun x =>
      (inactiveTimeZeroFamily F).flux p c v u γ d I τ (E⁻¹ • Y x) (e⁻¹ • Y x) k -
        taylorSlow 0 Ks (fun X => (inactiveTimeZeroFamily F).flux p c v u γ d I τ X (e⁻¹ • Y x) k)
          (E⁻¹ • Yc) (E⁻¹ • (Y x - Yc))) z‖ ≤
      (Kmax.factorial : ℝ) * Dchart ^ Kmax * ((Kmax + 1 : ℕ) * (centeredSlowRemainderBoundedJetPrice Ks Kmax * B * ζ ^ (Ks + 1))) *
        (3 + max (Cchart 0) 0) ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  have henv0 := inactiveTimeZeroFamily_pointwiseMolecularEnvelope F W π K ν e E ρ C J b₀ henv
  have hb := familyPointwiseMolecular_natural_remainder_bounded_price_jet_budget
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) Ks (inactiveTimeZeroFamily F)
    π hπ K Kmax hK (fun _ _ => W ×ˢ Set.univ) ν e E ρ hν he hE hρ
    C J b₀ henv0 v u γ hγ d hd I hKs p c
  intro hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn τ hτ yc z k j hj
  have hh := hb hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn τ
    (fun _ => ⟨hτ, Set.mem_univ _⟩) yc z k j hj
  apply hh.trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (zero_le_one.trans
    (polynomialMomentRoot_one_le ϖ z)) _)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg hζ _)
  apply mul_le_mul_of_nonneg_left _ (centeredSlowRemainderBoundedJetPrice_nonneg Ks Kmax)
  apply div_le_div_of_nonneg_right _ (by unfold derivativeReserveFactor; positivity)
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  unfold molecularRealPrice
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply mul_le_mul_of_nonneg_right _ (by positivity)
  apply ENNReal.toReal_mono
  · exact pointwiseMolecularEnvelope_constituent_jet_ne_top F π hπ K
      (ChartedFamily.Domain.onWindow F W) ν e E ρ hν he hρ C J b₀ henv
      v u γ hγ d hd I (Ks + 1) hKs
  · exact inactiveTimeZeroFamily_pointwiseMolecularJet_le F W ν e E ρ v u γ d I (K v) (Ks + 1)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Reference cell sources retain exact support on the original constituent graph. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

theorem preparationReferenceCellSourceCoefficient_zero_of_no_edge
    (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ) (s ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (yc : Vec 2)
    (v u : ι) (d : admissibleOrders K D v u) (hΓ : ¬ Nonempty (F.Γ v u)) :
    preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc v u d = 0 := by
  have hz := physicalCoefficient_zero_of_no_edge (referenceChartedFamily F hφ s)
    ν e E actual v u d.1 hΓ
  funext t z
  unfold preparationReferenceCellSourceCoefficient edgeCoefficient
  rw [hz]
  simp only [Pi.zero_apply]
  change ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹) •
    (0 : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h v)) = 0
  exact smul_zero (A := PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u) →L[ℝ]
    PiLp 2 (fun _ : Fin 2 => h v)) ((e * (e ^ (d.1 - 1))⁻¹) * ν⁻¹)
end

/-! Exact reference cell scaling preserves the original mass-weighted source Schur matrix. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {φ : ℝ → Vec 2 → ℝ}

theorem preparationReferenceCellSourceCoefficient_schurMatrix
    (F : ChartedFamily ι h D P Ctx) (hφ : IsAdmissibleStream φ)
    (s ν e E a b ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hρ : 0 < ρ)
    (actual : ∀ p, Ctx p) (π : ι → ℝ) (K : ι → ℕ) (yc : Vec 2) :
    schurMatrix 1 (ρ / e) π K D ((e⁻¹) ^ 2 * (ν * a)) ((e⁻¹) ^ 2 * (ν * b))
      (preparationReferenceCellSourceCoefficient F hφ s ν e E actual K yc) =
    schurMatrix ν ρ π K D a b (edgeCoefficient (referenceChartedFamily F hφ s) ν e E actual K) := by
  funext v u
  unfold schurMatrix
  congr 1
  apply Finset.sum_congr rfl
  intro d _
  rw [preparationReferenceCellSourceCoefficient_seminorm_price F hφ s ν e E a b ρ hν he hρ.le]
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity), one_mul]
  congr 1
  exact cell_source_schur_price ν e ρ _ hν.ne' he.ne' hρ.ne' d.1
    (Finset.mem_Icc.mp (Finset.mem_filter.mp d.property).1).1
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleJointProofs

/-! Finite public polynomial energy pays the endpoint image series and its actual torus readout. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem polynomial_planeImageJet_enorm_tsum_lt_top (U : Set (Vec 2))
    (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (f : PlaneHk Set.univ K E) (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2)
    (ρ : ℝ) (hρ : 0 < ρ) (he : weightedFactorialNormSq 4 ϖ z ρ K f ≠ ⊤)
    (α : JetIndex2 K) :
    (∑' n : Fin 2 → ℤ, ‖planeImageJetCLM U (AVenhance.latticeShift n) α f‖ₑ) < ⊤ := by
  have hm := hasRadialPlaneMoments_of_finite_polynomial f ϖ hϖ z ρ hρ he α
  apply planeImageJetCLM_radial_enorm_tsum_lt_top U R hR hU z α f
    (eLpNorm (fun y => (1 + ‖y - z‖) ^ 4 • f.toFunction.jet α y) 2 volume).toReal
    ENNReal.toReal_nonneg hm.aestronglyMeasurable
  rw [ENNReal.ofReal_toReal hm.eLpNorm_ne_top]

theorem polynomial_periodized_compact_pairing (U : Set (Vec 2))
    (R : ℝ) (hR : 0 < R) (hU : U ⊆ Metric.ball (0 : Vec 2) R)
    (f : PlaneHk Set.univ K E) (F : TorusHk K E)
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (he : weightedFactorialNormSq 4 ϖ z ρ K f ≠ ⊤) (α : JetIndex2 K)
    (hr : F.toFunction.jet α =ᵐ[volume] periodizeRawJet f.toFunction.jet α)
    (ψ : PlaneHk Set.univ L E) (β : JetIndex2 L)
    (hψ : ∀ᵐ x ∂volume, x ∉ U → ψ.toFunction.jet β x = 0) :
    Summable (fun n : Fin 2 → ℤ => ∫ x,
      inner ℝ ((planeCarrierTranslation K (AVenhance.latticeShift n) f).toFunction.jet α x)
        (ψ.toFunction.jet β x)) ∧
    (∑' n : Fin 2 → ℤ, ∫ x,
      inner ℝ ((planeCarrierTranslation K (AVenhance.latticeShift n) f).toFunction.jet α x)
        (ψ.toFunction.jet β x)) = ∫ x, inner ℝ (F.toFunction.jet α x) (ψ.toFunction.jet β x) := by
  have hs := polynomial_planeImageJet_enorm_tsum_lt_top U R hR hU f ϖ hϖ z ρ hρ he α
  refine ⟨translated_compact_jet_pairing_summable U f α ψ β hψ hs, ?_⟩
  refine (summed_compact_jet_pairing U f α ψ β hψ hs).trans (integral_congr_ae ?_)
  filter_upwards [hr] with x hx
  rw [hx]

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs

/-! Any finite selection of actual preparation pieces retains its common native density budget. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem familyWeighted_native_sum_density_le (F : ChartedFamily ι h D P Ctx)
    (S : Finset P) {K : ℕ} (s ρ : ℝ) (μ : Measure ℝ)
    (V : S → ℝ → PlaneHk Set.univ K E) (B : ℝ → Vec 2 → ℝ)
    (hB : ∀ᵐ t ∂μ, ∀ z, 0 ≤ B t z)
    (hb : ∀ p, ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (V p t) z ≤ (F.weight p.val (s * t)) ^ 2 * B t z) :
    ∀ᵐ t ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity ρ (∑ p, V p t) z ≤ B t z := by
  classical
  apply positiveSubpartition_native_density_sum_le ρ μ V
    (fun p t => F.weight p.val (s * t)) B _ hB hb
  exact Filter.Eventually.of_forall (fun t => ⟨fun p => F.weight_nonneg p.val (s * t), by
    rw [S.sum_coe_sort (fun p => F.weight p (s * t))]
    exact family_weight_finset_sum_le_one F S (s * t)⟩)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory Set Filter AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CycleReference
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! A genuine weak Hilbert curve has a native H1 Bochner state in every fixed-start material chart. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeWeakCurve_chart_state_memLp {a b : ℝ}
    {u : ℝ → Lp E 2 (volume : Measure (Vec 2))}
    {slice dual : ℝ → PlaneHk univ 1 E} (h : PlaneWeakHilbertCurve a b u slice dual)
    {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ) (s : ℝ) :
    MemLp (fun t => planeH1ChartPull hφ t s (slice t)) 2 (volume.restrict (Icc a b)) := by
  let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
  let : Fact ((1 : ENNReal) ≤ 2) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume : Measure (Vec 2))) := Lp.SecondCountableTopology
  obtain ⟨θ, G, hθ, hG, heθ, heG, _⟩ := planeWeakCurve_exists_joint_fields h
  have hm : volume.restrict (Icc a b ×ˢ (univ : Set (Vec 2))) =
      (volume.restrict (Icc a b)).prod volume := by
    rw [Measure.volume_eq_prod ℝ (Vec 2), ← Measure.prod_restrict, Measure.restrict_univ]
  let Θ := fun p : ℝ × Vec 2 => θ (p.1, AVRegularity.streamFlow φ hφ p.1 p.2 s)
  let DG := fun k (p : ℝ × Vec 2) =>
    hilbertChartGradient hφ p.1 s (fun i x => G i (p.1, x)) k p.2
  have hΘ : MemLp Θ 2 ((volume.restrict (Icc a b)).prod volume) := by
    rw [← hm] at hθ ⊢
    exact hθ.comp_measurePreserving (streamFlowTime_window_measurePreserving hφ s measurableSet_Icc)
  have hDG k : MemLp (DG k) 2 ((volume.restrict (Icc a b)).prod volume) := by
    rw [← hm]
    exact hilbertChartGradient_joint_memLp hφ s a b G (fun i => by rw [hm]; exact hG i) k
  apply planeH1_time_memLp_of_readouts
  · apply bochner_memLp_of_joint_representation (volume.restrict (Icc a b)) volume Θ hΘ
    filter_upwards [h.agrees] with t ht
    have he : (planeHkValueOperator 1 (slice t) : Vec 2 → E) =ᵐ[volume]
        fun x => θ (t, x) := by
      rw [← ht]
      exact heθ t
    exact (planeH1ChartPull_value_ae hφ t s (slice t)).trans
      ((streamFlow_measurePreserving hφ t s).quasiMeasurePreserving.ae_eq_comp he)
  · intro k
    apply bochner_memLp_of_joint_representation (volume.restrict (Icc a b)) volume (DG k) (hDG k)
    apply Eventually.of_forall
    intro t
    have he := ae_all_iff.mpr (fun i =>
      (streamFlow_measurePreserving hφ t s).quasiMeasurePreserving.ae_eq_comp (heG t i))
    apply (planeH1ChartPull_gradient_ae hφ t s (slice t) k).trans
    filter_upwards [he] with y hey
    change (∑ i : Fin 2,
      jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y i k •
        planeH1GradientOperator (slice t) i (AVRegularity.streamFlow φ hφ t y s)) =
      ∑ i : Fin 2, jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y i k •
        G i (t, AVRegularity.streamFlow φ hφ t y s)
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (fun z : E =>
      jacMatrix (fun x => AVRegularity.streamFlow φ hφ t x s) y i k • z) (hey i)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem inactiveTimeZeroFamily_natural_time_remainder_uniform_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ρ / e ≤ ocEpsilon q Λ (m - 1) / e →
    ∀ (ϖ ζ : ℝ), 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
    K v ≤ Jchart + 1 → ∀ (timeScale a b : ℝ),
    (∀ t ∈ Set.Icc a b, timeScale * t ∈ W) → ∀ τ,
    ∀ (yc z : Vec 2) (k : Fin 2) (j : ℕ), j ≤ K v →
    let Dchart := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
      molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
            derivativeReserveFactor (ρ / e) (K v) (d - 2)
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j
      (naturalSlowRemainderTimeCoefficient Ks
        (fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k)
        a b hφ r (fun _ => σ) e E yc τ) z‖ ≤
      ((K v).factorial : ℝ) * Dchart ^ K v * ((K v + 1 : ℕ) * (CR * B * ζ ^ (Ks + 1))) *
        (3 + max (Cchart 0) 0) ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  obtain ⟨CR, hCR, hb⟩ := inactiveTimeZeroFamily_natural_remainder_uniform_jet_budget
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) Ks F π hπ K Kmax hK W ν e E ρ hν he hE hρ
    C J b₀ henv v u γ hγ d hd I hKs p c
  refine ⟨CR, hCR, ?_⟩
  intro hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime τ yc z k j hj
  by_cases ht : τ ∈ Set.Icc a b
  · have heq : naturalSlowRemainderTimeCoefficient Ks
        (fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k)
        a b hφ r (fun _ => σ) e E yc τ = fun x =>
          let Y := streamFlow φ hφ r (yc + e • x) σ
          let Yc := streamFlow φ hφ r yc σ
          (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * τ) (E⁻¹ • Y) (e⁻¹ • Y) k -
            taylorSlow 0 Ks
              (fun X => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * τ) X (e⁻¹ • Y) k)
              (E⁻¹ • Yc) (E⁻¹ • (Y - Yc)) := by
        funext x
        simp only [naturalSlowRemainderTimeCoefficient, ite_eq_left ht]
    rw [heq]
    exact
      hb hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn (timeScale * τ)
        (htime τ ht) yc z k j hj
  · have heq : naturalSlowRemainderTimeCoefficient Ks
        (fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k)
        a b hφ r (fun _ => σ) e E yc τ = fun _ => 0 := by
      funext x
      simp only [naturalSlowRemainderTimeCoefficient, ite_eq_right ht]
    rw [heq]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    apply mul_nonneg
    · have hM := molecularRealPrice_nonneg ν ρ hν.le hρ.le (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1)
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
      unfold derivativeReserveFactor
      positivity
    · exact pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
namespace AVRegularity.CycleJointProofs

/-! Finite integrated public polynomial energy gives the actual periodized L2 time curve. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K : ℕ}

theorem exists_polynomialCarrier_periodization_time_memLp
    (ϖ : ℝ) (hϖ : 0 < ϖ) (z : Vec 2) (ρ : ℝ) (hρ : 0 < ρ)
    (μ : Measure ℝ) (f : ℝ → PlaneHk Set.univ K E) (hf : MemLp f 2 μ)
    (he : (∫⁻ t, weightedFactorialNormSq 4 ϖ z ρ K (f t) ∂μ) ≠ ⊤) :
    ∃ u : ℝ → TorusHk K E, MemLp u 2 μ ∧
      ∀ᵐ t ∂μ, ∀ a, (u t).val a =ᵐ[volume.restrict AVenhance.unitCube]
        periodizeRawJet (f t).toFunction.jet a := by
  classical
  let W := fun (a : JetIndex2 K) t => weightedPlaneLpReadout (planeMomentSquareRoot 4 ϖ z)
    (planeMomentSquareRoot_continuous 4 ϖ z) (planeJetReadoutOperator K a (f t))
  have hW (a : JetIndex2 K) : MemLp (W a) 2 μ :=
    polynomialMomentLpReadout_time_memLp ϖ z ρ hρ μ f hf he a
  let C := (Real.sqrt (2 + 4 / ϖ ^ 2)) ^ 4
  have hC : 0 ≤ C := by positivity
  let M : ℝ → ℝ := fun t => C * ∑ a : JetIndex2 K, ‖W a t‖
  have hsum : MemLp (fun t => ∑ a : JetIndex2 K, ‖W a t‖) 2 μ := by
    simpa only using
      memLp_finsetSum Finset.univ (fun a _ => (hW a).norm)
  have hM : MemLp M 2 μ := hsum.const_mul C
  have hfinite := polynomialMoment_energy_ae_finite ϖ z ρ μ f hf he
  have hm : ∀ᵐ t ∂μ, HasRadialPlaneMoments (f t) z := hfinite.mono (fun t ht =>
    hasRadialPlaneMoments_of_finite_polynomial (f t) ϖ hϖ z ρ hρ ht)
  apply exists_periodized_radial_carrier_time_memLp μ f hf z hm M hM
  filter_upwards [hfinite] with t ht
  intro a
  have hs : ‖W a t‖ ≤ ∑ b : JetIndex2 K, ‖W b t‖ :=
    Finset.single_le_sum (f := fun b => ‖W b t‖) (fun _ _ => norm_nonneg _)
      (Finset.mem_univ a)
  have hMn : 0 ≤ M t := mul_nonneg hC (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
  calc
    _ ≤ ENNReal.ofReal C *
        eLpNorm (fun y => planeMomentSquareRoot 4 ϖ z y • (f t).toFunction.jet a y) 2 volume :=
      radialMoment_eLpNorm_le_polynomial ϖ hϖ z _
        (by simpa only [Measure.restrict_univ] using ((f t).toFunction.memL2 a).aestronglyMeasurable)
    _ = ENNReal.ofReal (C * ‖W a t‖) := by
      rw [polynomialMoment_eLpNorm_eq_readout_norm (f t) ϖ z ρ hρ ht a,
        ← ENNReal.ofReal_mul hC]
    _ ≤ ENNReal.ofReal ‖M t‖ := by
      rw [Real.norm_eq_abs, abs_of_nonneg hMn]
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left hs hC)

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem inactiveTimeZeroFamily_natural_time_remainder_bounded_price_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p) :
    ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ρ / e ≤ ocEpsilon q Λ (m - 1) / e →
    ∀ (ϖ ζ : ℝ), 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
    K v ≤ Jchart + 1 → ∀ (timeScale a b : ℝ),
    (∀ t ∈ Set.Icc a b, timeScale * t ∈ W) → ∀ τ,
    ∀ (yc z : Vec 2) (k : Fin 2) (j : ℕ), j ≤ K v →
    let Dchart := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let B := (Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
      molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1) (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) /
            derivativeReserveFactor (ρ / e) (K v) (d - 2)
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j
      (naturalSlowRemainderTimeCoefficient Ks
        (fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k)
        a b hφ r (fun _ => σ) e E yc τ) z‖ ≤
      (Kmax.factorial : ℝ) * Dchart ^ Kmax * ((Kmax + 1 : ℕ) * (centeredSlowRemainderBoundedJetPrice Ks Kmax * B * ζ ^ (Ks + 1))) *
        (3 + max (Cchart 0) 0) ^ (Ks + 1) * polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  have hb := inactiveTimeZeroFamily_natural_remainder_bounded_price_jet_budget
    (α := α) (q := q) (Λ := Λ) (m := m) (φ := φ) (hφ := hφ)
    (tS := tS) (tZ := tZ) (Cpad := Cpad) (Cage := Cage)
    (Jchart := Jchart) (Cchart := Cchart) Ks F π hπ K Kmax hK W ν e E ρ hν he hE hρ
    C J b₀ henv v u γ hγ d hd I hKs p c
  intro hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime τ yc z k j hj
  by_cases ht : τ ∈ Set.Icc a b
  · have heq : naturalSlowRemainderTimeCoefficient Ks
        (fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k)
        a b hφ r (fun _ => σ) e E yc τ = fun x =>
          let Y := streamFlow φ hφ r (yc + e • x) σ
          let Yc := streamFlow φ hφ r yc σ
          (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * τ) (E⁻¹ • Y) (e⁻¹ • Y) k -
            taylorSlow 0 Ks
              (fun X => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * τ) X (e⁻¹ • Y) k)
              (E⁻¹ • Yc) (E⁻¹ • (Y - Yc)) := by
        funext x
        simp only [naturalSlowRemainderTimeCoefficient, ite_eq_left ht]
    rw [heq]
    exact
      hb hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn (timeScale * τ)
        (htime τ ht) yc z k j hj
  · have heq : naturalSlowRemainderTimeCoefficient Ks
        (fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k)
        a b hφ r (fun _ => σ) e E yc τ = fun _ => 0 := by
      funext x
      simp only [naturalSlowRemainderTimeCoefficient, ite_eq_right ht]
    rw [heq]
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, mul_zero]
    apply mul_nonneg
    · have hCR := centeredSlowRemainderBoundedJetPrice_nonneg Ks Kmax
      have hM := molecularRealPrice_nonneg ν ρ hν.le hρ.le (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) (Ks + 1)
          (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
      unfold derivativeReserveFactor
      positivity
    · exact pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open AVenhance Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport AVRegularity.CycleReference
open scoped ENNReal
namespace AVRegularity.CycleJointProofs

/-! The independent pointwise certificate bounds the actual native Piola operator before partition assembly. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_native_flow_transport_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hnchart : K v ≤ Jchart + 1) (N : ℕ) (hN : N ≤ Jchart)
    (s t τ : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (ht : t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |s - t| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hdom : ∀ Y : Vec 2, (τ, Y) ∈ dom p c)
    (n r : ℕ) (hn : n ≤ K v) (hr : 1 ≤ r)
    (hnN : n + (F.identity v u γ).maxOrder ≤ N) (x : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let CK := compConst Cflow N * Cflow
    let Bcost := (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
      ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2))
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ s t)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I τ
          (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)) r A y a)) x‖ ≤
      ∑ _a : Fin 2, ∑ _A : DerivativeWord2 r, ‖(F.identity v u γ).map‖ *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
            (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * CK *
              (3 * (N + 1 : ℕ) * 2 ^ N * CK) ^ D) *
            (Bcost * (pointwiseMolecularJet ρ e (K v) 0
              (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
              (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r))) := by
  dsimp only
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let B := fun d (I : DerivativeWord2 (d - 1)) y =>
    F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I τ
      (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)
  have hy : ContDiff ℝ (K v : ℕ) (fun y : Vec 2 => streamFlow φ hφ s y t) :=
    ((streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).of_le (by simp)
  have hBs d I : ContDiff ℝ (K v : ℕ) (B d I) := by
    have hh := molecular_joint_contDiff F dom (ocEpsilon q Λ (m - 1)) hE.ne'
      (fun v => K v + Jm) henv.1 p c τ hdom v u γ d I
    have hh' : ContDiff ℝ (K v : ℕ) (Function.uncurry (F.flux p c v u γ d I τ)) :=
      hh.of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
    exact ((hh'.comp ((hy.const_smul (ocEpsilon q Λ (m - 1))⁻¹).prodMk
      (hy.const_smul e⁻¹))).const_smul (ν * e ^ (d - 2)))
  apply uniform_native_vector_transport_assembly_jet_bound
    (naturalPreparationJacobian hφ s t)
    (fun i j => (naturalPreparationJacobian_entry_smooth hφ s i j).comp
      (contDiff_const.prodMk contDiff_id)) N (F.identity v u γ).maxOrder D Kmax n r
    (F.identity v u γ).le_D (hn.trans (hK v)) (compConst Cflow N * Cflow)
    (ocEpsilon q Λ (m - 1)) ρ (preparation_jacobian_constant_ge_one Jchart Cchart N)
    hE hρ.le hρE hnN
    (fun a b j hj y => naturalPreparationJacobian_scaled_jet_bound hc ha hE s t hs ht
      (by simpa only [abs_sub_comm] using hage) N hN a b y j hj)
    B (fun d I => (hBs d I).of_le (by exact_mod_cast hn)) _ (fun d I => by positivity)
  intro d hd I j hj y
  have hd' : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder :=
    Finset.mem_Icc.mpr ⟨by have hh := (Finset.mem_Icc.mp hd).1; omega,
      (Finset.mem_Icc.mp hd).2⟩
  have hh := pointwise_molecular_flow_sample_uniform_budget F π hπ K Kmax hK dom ν e ρ
    hν he hE hρE ha hρ Cm Jm b henv v u γ hγ d hd' I p c hc hnchart s τ hs
    t hdom ht hage j (hj.trans hn) y
  convert hh using 1; ring
end

/-! The independent pointwise certificate bounds the actual native Piola operator before partition assembly. -/

section
variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem pointwise_molecular_native_transport_budget (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain)
    (ν e ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1))
    (hρE : ρ ≤ ocEpsilon q Λ (m - 1)) (ha : 0 ≤ ocA α q Λ (m - 1)) (hρ : 0 < ρ)
    (Cm : ℕ → ℝ) (Jm : ℕ) (b : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e (ocEpsilon q Λ (m - 1)) ρ Cm Jm b)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0)
    (p : P) (c : Ctx p)
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (hnchart : K v ≤ Jchart + 1) (N : ℕ) (hN : N ≤ Jchart)
    (s t : ℝ)
    (hs : s ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (ht : t ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |s - t| ≤ 2 * Cage * ocTauPP α q Λ m)
    (hdom : ∀ Y : Vec 2, (t, Y) ∈ dom p c)
    (n r : ℕ) (hn : n ≤ K v) (hr : 1 ≤ r)
    (hnN : n + (F.identity v u γ).maxOrder ≤ N) (x : Vec 2) :
    let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
    let CK := compConst Cflow N * Cflow
    let Bcost := (Kmax.factorial : ℝ) * Cflow ^ Kmax * ((Kmax + 1 : ℕ) *
      ((4 : ℝ) ^ Kmax * (Kmax.factorial : ℝ) ^ 2))
    ρ ^ n * ‖iteratedFDeriv ℝ n (fun y => nativeArrayAssembly r (F.identity v u γ).map
      (fun a A => transportedCoeff (naturalPreparationJacobian hφ s t)
        (F.identity v u γ).maxOrder
        (fun d I => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I t
          (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)) r A y a)) x‖ ≤
      ∑ _a : Fin 2, ∑ _A : DerivativeWord2 r, ‖(F.identity v u γ).map‖ *
        (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
            (((Kmax + 1 : ℕ) * (2 : ℝ) ^ Kmax) ^ 2 * CK *
              (3 * (N + 1 : ℕ) * 2 ^ N * CK) ^ D) *
            (Bcost * (pointwiseMolecularJet ρ e (K v) 0
              (fun z : F.Index => dom z.1 z.2)
              (fun z => F.dimFlux ν e (ocEpsilon q Λ (m - 1)) z.1 z.2 v u γ d I)).toReal *
              (ocEpsilon q Λ (m - 1))⁻¹ ^ (d - 1 - r))) := by
  dsimp only
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  let B := fun d (I : DerivativeWord2 (d - 1)) y =>
    F.dimFlux ν e (ocEpsilon q Λ (m - 1)) p c v u γ d I t
      (streamFlow φ hφ s y t) (e⁻¹ • streamFlow φ hφ s y t)
  have hy : ContDiff ℝ (K v : ℕ) (fun y : Vec 2 => streamFlow φ hφ s y t) :=
    ((streamFlow_joint_smooth hφ).comp
      (contDiff_const.prodMk (contDiff_id.prodMk contDiff_const))).of_le (by simp)
  have hBs d I : ContDiff ℝ (K v : ℕ) (B d I) := by
    have hh := molecular_joint_contDiff F dom (ocEpsilon q Λ (m - 1)) hE.ne'
      (fun v => K v + Jm) henv.1 p c t hdom v u γ d I
    have hh' : ContDiff ℝ (K v : ℕ) (Function.uncurry (F.flux p c v u γ d I t)) :=
      hh.of_le (by exact_mod_cast Nat.le_add_right (K v) Jm)
    exact ((hh'.comp ((hy.const_smul (ocEpsilon q Λ (m - 1))⁻¹).prodMk
      (hy.const_smul e⁻¹))).const_smul (ν * e ^ (d - 2)))
  apply uniform_native_vector_transport_assembly_jet_bound
    (naturalPreparationJacobian hφ s t)
    (fun i j => (naturalPreparationJacobian_entry_smooth hφ s i j).comp
      (contDiff_const.prodMk contDiff_id)) N (F.identity v u γ).maxOrder D Kmax n r
    (F.identity v u γ).le_D (hn.trans (hK v)) (compConst Cflow N * Cflow)
    (ocEpsilon q Λ (m - 1)) ρ (preparation_jacobian_constant_ge_one Jchart Cchart N)
    hE hρ.le hρE hnN
    (fun a b j hj y => naturalPreparationJacobian_scaled_jet_bound hc ha hE s t hs ht
      (by simpa only [abs_sub_comm] using hage) N hN a b y j hj)
    B (fun d I => (hBs d I).of_le (by exact_mod_cast hn)) _ (fun d I => by positivity)
  intro d hd I j hj y
  have hd' : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder :=
    Finset.mem_Icc.mpr ⟨by have hh := (Finset.mem_Icc.mp hd).1; omega,
      (Finset.mem_Icc.mp hd).2⟩
  have hh := pointwise_molecular_material_sample_uniform_budget F π hπ K Kmax hK dom ν e ρ
    hν he hE hρE ha hρ Cm Jm b henv v u γ hγ d hd' I p c hc hnchart s hs
    t hdom ht hage j (hj.trans hn) y
  convert hh using 1; ring
end

end AVRegularity.CycleJointProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.CycleWords AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs

/-! Inactive-time natural remainders retain the original output-window constituent price. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

theorem inactiveTimeZeroFamily_natural_time_remainder_reserved_jet_budget
    (Ks : ℕ) (F : ChartedFamily ι h D P Ctx)
    (π : ι → ℝ) (hπ : ∀ v, 0 < π v) (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (W : Set ℝ)
    (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e) (hE : 0 < E) (hρ : 0 < ρ)
    (C : ℕ → ℝ) (J : ℕ) (b₀ : ι → ι → ℝ)
    (henv : IsPointwiseMolecularEnvelope F π K (ChartedFamily.Domain.onWindow F W) ν e E ρ C J b₀)
    (v u : ι) (γ : F.Γ v u) (hγ : (F.identity v u γ).map ≠ 0) (d : ℕ)
    (hd : d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder)
    (I : DerivativeWord2 (d - 1)) (hKs : Ks + 1 ≤ J) (p : P) (c : Ctx p) :
    ∀
    (_hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (_ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ),
    r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m) →
    |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m →
    ρ / e ≤ ocEpsilon q Λ (m - 1) / e →
    ∀ (ϖ ζ : ℝ), 0 < ϖ → (ρ / e) * ϖ ≤ 1 → 0 ≤ ζ → e / E = ζ * ϖ →
    K v ≤ Jchart + 1 → ∀ (timeScale a b : ℝ),
    (∀ t ∈ Set.Icc a b, timeScale * t ∈ W) → ∀ τ,
    ∀ (yc z : Vec 2) (k : Fin 2) (j : ℕ), j ≤ K v →
    (ρ / e) ^ j * ‖iteratedFDeriv ℝ j
      (naturalSlowRemainderTimeCoefficient Ks
        (fun t X z => (inactiveTimeZeroFamily F).flux p c v u γ d I (timeScale * t) X z k)
        a b hφ r (fun _ => σ) e E yc τ) z‖ ≤
      (naturalRemainderChartPrice Ks Kmax Jchart Cchart * ζ ^ (Ks + 1) *
        ((Kmax.factorial : ℝ) ^ 2 * E ^ (Ks + 1) *
          molecularRealPrice ν ρ (K v) (d - 2)
            (pointwiseMolecularJet ρ e (K v) (Ks + 1)
              (fun x : F.Index => ChartedFamily.Domain.onWindow F W x.1 x.2)
              (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))) /
        derivativeReserveFactor (ρ / e) (K v) (d - 2)) *
        polynomialMomentRoot ϖ z ^ (Ks + 1) := by
  intro hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime τ yc z k j hj
  have hb := inactiveTimeZeroFamily_natural_time_remainder_bounded_price_jet_budget
    Ks F π hπ K Kmax hK W ν e E ρ hν he hE hρ C J b₀ henv v u γ hγ d hd I hKs p c
    hc ha r σ hr hσ hage hsE ϖ ζ hϖ hscale hζ hδ hn timeScale a b htime τ yc z k j hj
  dsimp only at hb
  convert hb using 1
  unfold naturalRemainderChartPrice
  ring

end AVRegularity.CycleJointProofs
end
end
