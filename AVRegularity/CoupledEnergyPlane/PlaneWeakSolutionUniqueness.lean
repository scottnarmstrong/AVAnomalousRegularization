-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergyPlane.SourceRawSpatialTimeIdentity
public import AVRegularity.CoupledEnergyPlane.SourceFixedBandUniformBound
import AVRegularity.CoupledEnergyPlane.SourceCarrierResidualRhs
public import AVRegularity.Statements.Intermediate.CoupledEnergy.CoupledSolutionPlane
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
open scoped Topology
namespace AVRegularity.CoupledEnergyPlane

/-! The uniform Galerkin energy bound controls the genuine lower weak Sobolev carrier almost everywhere. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceContinuousRepAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceContinuousRepTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem exists_sourceContinuousSobolevRepresentative {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (u : ℕ → C(Set.Icc a b, ProjectedFamily h))
    (heq : ∀ N, ∀ t : Set.Icc a b, u N t = projectedInitial N f + ∫ s in a..t.1,
      projectedOperator
        ((sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf).reindex
          (clampPoint a b hab)) N ν s (extendCurve hab (u N) s) + projectedSource N F g s)
    (φ : ℕ → ℕ) (hφ : StrictMono φ) (W : PlaneHighTime (h := h) K a b) (R : ℝ)
    (hu : ∀ n, ‖higherBandBochner (φ n) K a b hab (u (φ n))‖ ≤ R)
    (hw : ∀ ell : PlaneHighTime (h := h) K a b →L[ℝ] ℝ,
      Tendsto (fun n => ell (higherBandBochner (φ n) K a b hab (u (φ n))))
        atTop (𝓝 (ell W)))
    (hrange : ∀ N t, familyProjection N (u N t) = u N t)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (C : ℝ)
    (hmass : ∀ N t, massNormSq ρ π
      (fun i => (hilbertBandHk N (K i) (u N t i)).val) ≤ C)
    (hW : ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ j,
      W s j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (i : ι) :
    ∃ U : C(Set.Icc a b, PlaneHk Set.univ (K i) (h i)),
      Tendsto (fun N => sourceFixedBandSobolevPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf
        hvm hAm ν f F hF g hg W i N) atTop (𝓝 U) ∧
      U ⟨a, le_rfl, hab⟩ = f i ∧
      extendCurve hab U =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (weakHighCarrier K a b W i t) := by
  let S := sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i (F i) (hF i)
  let H := timeValueSource (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets W) (g i)
  have hH : Integrable H (volume.restrict (Set.Icc a b)) :=
    timeValueSource_integrable _ _ (hg i)
  have hc := fun N => sourceFixedBandSobolevPrimitive_eq_sourcePrimitive hab ρ hρ v hv V hV hbv
    K D A hAc hAf hvm hAm ν f F hF g hg W Kmax hK strain B lam hstrain hB hlam hjets hW i N
  have hq : ∀ N, extendCurve hab
      (planeBandSobolevPrimitive hab N (K i) (f i) S (Lp.memLp _) H hH)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        planeHkCutoff (E := h i) N (K i)
          (truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (weakHighCarrier K a b W i t)) := by
    intro N
    have hp := sourceFixedBandSobolevPrimitive_ae_eq_cutoff hab ρ hρ v hv V hV hbv
      K D A hAc hAf hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass hW i N
    rw [hc N] at hp
    filter_upwards [hp, weakLowerCarrierTimeCLM_ae K a b i W] with t ht hl
    exact ht.trans (congrArg (planeHkCutoff (E := h i) N (K i)) hl)
  have hb := sourceWeakLowerCarrier_norm_le_ae hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass hW i
  have hb' : ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      ‖truncatePlaneHk (E := h i) (Nat.le_succ (K i)) (weakHighCarrier K a b W i t)‖ ≤
        Real.sqrt ((∑ j, π j / factorialWeightMin ρ (K j)) * C) := by
    filter_upwards [hb, weakLowerCarrierTimeCLM_ae K a b i W] with t ht hl
    rwa [hl] at ht
  obtain ⟨U, hU, hUa⟩ := exists_continuous_sobolevRepresentative_of_source_primitives hab
    (K i) (Real.sqrt ((∑ j, π j / factorialWeightMin ρ (K j)) * C)) (f i)
    S (Lp.memLp _) H hH (weakHighCarrier K a b W i) (weakHighCarrier_memLp K a b W i) hq hb'
  refine ⟨U, ?_, sourcePrimitive_limit_initial hab (K i) (f i) S (Lp.memLp _) H hH U hU, hUa⟩
  convert hU using 1
  funext N
  exact hc N

end AVRegularity.CoupledEnergyPlane
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceNativeResidualRowAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceNativeResidualRowTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceNativeRhs_carrierResidual_ae {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι)
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j)) (N : ℕ)
    (q : ℝ → ProjectedFamily h)
    (hq : ∀ j, (fun t => q t j) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      hilbertProjection (E := h j) N (planeHkValueOperator (E := h j) (K j + 1) (weakHighCarrier (h := h) K a b W j t))) :
    let Cc := sourceProjectedCoefficients (h := h) a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable (h := h) a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hAc hAf hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets (U j) (g j) N
    fixedBandRhs (E := h i) N ν
      ((planeHkValueOperator (E := h i) 1).compLpL 2 (volume.restrict (Set.Icc a b))
        (weakH1CarrierTimeCLM (h := h) K a b i W))
      (limitDriftField (h := h) hab Cc hc i W)
      (limitFluxField (h := h) hab Cc hc W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
      (fun s => planeHkValueOperator (E := h i) (K i) (g i s)) =ᵐ[volume.restrict (Set.Icc a b)] fun s =>
        projectedOperator (Cc.reindex (clampPoint a b hab)) N ν s (q s) i + projectedSource N RF Rg s i := by
  intro Cc hc U Φ RF Rg
  exact (sourceFixedBandRhs_carrier_ae (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW i ν (F i) (hF i) (g i) N).trans
      (sourceCarrierRhs_residual_ae (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
        Kmax hK strain B lam hstrain hB hlam hjets W i ν F hF g N q hq)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceFamilyResidualAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceFamilyResidualTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceNativeFamily_residualRhs_of_alignment {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j)) (N : ℕ)
    (q : ℝ → ProjectedFamily h)
    (hq : ∀ j, (fun t => q t j) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
      hilbertProjection (E := h j) N (planeHkValueOperator (E := h j) (K j + 1) (weakHighCarrier (h := h) K a b W j t))) :
    let Cc := sourceProjectedCoefficients (h := h) a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable (h := h) a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hAc hAf hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets (U j) (g j) N
    nativeFamilyRhs (h := h) N ν (fun i => weakH1CarrierTimeCLM (h := h) K a b i W)
      (fun i => limitDriftField (h := h) hab Cc hc i W)
      (fun i => limitFluxField (h := h) hab Cc hc W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
      (fun i s => planeHkValueOperator (E := h i) (K i) (g i s)) =ᵐ[volume.restrict (Set.Icc a b)] fun s =>
        projectedOperator (Cc.reindex (clampPoint a b hab)) N ν s (q s) + projectedSource N RF Rg s := by
  intro Cc hc U Φ RF Rg
  have he := ae_all_iff.mpr (fun i =>
    sourceNativeRhs_carrierResidual_ae (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      Kmax hK strain B lam hstrain hB hlam hjets W hW i ν F hF g N q hq)
  filter_upwards [he] with s hs
  apply PiLp.ext
  intro i
  exact hs i
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceFamilyRegularityAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceFamilyRegularityTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceNativeFamily_timeRegularity_of_alignment {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (ν : ℝ) (f : ∀ i, PlaneHk Set.univ (K i) (h i)) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b))) (N : ℕ)
    (hq : ∀ j, (fun t => extendCurve hab (sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg W N) t j)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t => hilbertProjection (E := h j) N
        (planeHkValueOperator (E := h j) (K j + 1) (weakHighCarrier (h := h) K a b W j t))) :
    let Cc := sourceProjectedCoefficients (h := h) a b ρ hρ v hv V hV hbv K D A hAc hAf
    let _hc := sourceProjectedCoefficients_isMeasurable (h := h) a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hAc hAf hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets (U j) (g j) N
    let qN := sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg W N
    AbsolutelyContinuousOnInterval (extendCurve hab qN) a b ∧
      (∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt (extendCurve hab qN)
        (projectedOperator (Cc.reindex (clampPoint a b hab)) N ν t (extendCurve hab qN t) +
          projectedSource N RF Rg t) t) := by
  intro Cc hc U Φ RF Rg qN
  have he := sourceNativeFamily_residualRhs_of_alignment (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW ν F hF g N (extendCurve hab qN) hq
  have hqeq := sourceNativeFamilyPrimitive_eq_nativeFamily (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    ν f F hF g hg W N
  dsimp only [qN] at he ⊢
  rw [hqeq] at he ⊢
  exact nativeFamilyPrimitive_timeRegularity_of_rhs_ae (h := h) hab N ν
    (fun i => planeHkValueOperator (E := h i) (K i) (f i))
    (fun i => weakH1CarrierTimeCLM (h := h) K a b i W)
    (fun i => limitDriftField (h := h) hab Cc hc i W)
    (fun i => limitFluxField (h := h) hab Cc hc W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
    (fun i s => planeHkValueOperator (E := h i) (K i) (g i s))
    (fun i => (planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i))
    (projectedOperator (Cc.reindex (clampPoint a b hab)) N ν) (projectedSource N RF Rg) he
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakFamilyRegularityAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakFamilyRegularityTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_nativeFamily_timeRegularity {a b : ℝ} (hab : a ≤ b)
    (ρ : ℝ) (hρ : 0 < ρ)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (K : ι → ℕ) (D : ℕ)
    (A : ∀ i j, ∀ d : AVRegularity.admissibleOrders K D i j, ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h j)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h i)))
    (hAc : ∀ i j d, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i j d t))
    (hAf : ∀ i j d, AVRegularity.coefficientSeminorm ρ (K i) a b (A i j d) ≠ ⊤)
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (ν : ℝ) (F : ∀ j, ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    (hF : ∀ j, MemLp (F j) 2 (volume.restrict (Set.Icc a b)))
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (hg : ∀ j, Integrable (g j) (volume.restrict (Set.Icc a b)))
    (f : ∀ j, PlaneHk Set.univ (K j) (h j))
    (u : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j))
    (w : ∀ j, ℝ → PlaneHk Set.univ (K j + 1) (h j))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (N : ℕ) :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let Cc := sourceProjectedCoefficients (h := h) a b ρ hρ v hv V hV hbv K D A hAc hAf
    let _hc := sourceProjectedCoefficients_isMeasurable (h := h) a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hAc hAf hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets (U j) (g j) N
    let qN := sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
      ν f F hF g hg W N
    AbsolutelyContinuousOnInterval (extendCurve hab qN) a b ∧
      (∀ᵐ t ∂volume, t ∈ Set.Icc a b → HasDerivAt (extendCurve hab qN)
        (projectedOperator (Cc.reindex (clampPoint a b hab)) N ν t (extendCurve hab qN t) +
          projectedSource N RF Rg t) t) := by
  intro W Cc hc U Φ RF Rg qN
  have hq := fun i => planeWeakSolution_nativeFamily_alignment_ae (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets ν F hF g hg f u w hsol N i
  exact sourceNativeFamily_timeRegularity_of_alignment (h := h) hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W
    (planeCarrierHighTime_graph_ae (h := h) K a b w hsol.2.1) ν f F hF g hg N hq
end

end AVRegularity.CoupledEnergyPlane
end
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakNativeEnergyAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakNativeEnergyTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_nativeCutoffEnergy (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hC hA hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain0 (le_trans zero_le_one hB) hlam hbv hjets (U j) (g j) N
    let qN := sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
      ν f F hF g hg W N
    ∃ S : ℝ, 0 ≤ S ∧
      (∀ t : Set.Icc a b, massNormSq ρ π
        (fun i => (hilbertBandHk N (K i) (qN t i)).val) ≤ S ^ 2) ∧
      S ^ 2 + (ν / 2) * (∫ s in a..b, massGradNormSq ρ π
        (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab qN s i)).val)) ≤
      2 * massNormSq ρ π (fun i => (hilbertBandHk N (K i) (qN ⟨a, le_rfl, hab⟩ i)).val) +
        (8 / ν) * (∫ s in a..b, massNormSq ρ π (fun i => (RF i s).val)) +
          10 * (∫ s in a..b, Real.sqrt (massNormSq ρ π (fun i => (Rg i s).val))) ^ 2 := by
  intro W U Φ RF Rg qN
  have ht := planeWeakSolution_nativeFamily_timeRegularity (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
    Kmax hK strain B lam hstrain0 (le_trans zero_le_one hB) hlam hjets ν F hF g hg f u w hsol N
  exact sourceProjectedEnergy_uniform_of_timeRegularity (h := h) K Kmax hK N
    ρ strain B lam ν hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b hab qN
    v hv V hV hbv hdiv hjets D A hA hC hschur RF Rg
    (fun i => Lp.memLp (planeResidualFluxTime (h := h) hab ρ hρ K D A hC hA hAm U Φ N i))
    (fun i => planeResidualValueSource_integrable hab (hK i) v hvm hv V strain B lam
      hV hstrain0 (le_trans zero_le_one hB) hlam hbv hjets (U i) (g i) N (hg i))
    ht.1 ht.2
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakNativePointEnergyAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakNativePointEnergyTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_nativePointEnergy (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (t : Set.Icc a b) :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hC hA hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain0 (le_trans zero_le_one hB) hlam hbv hjets (U j) (g j) N
    let qN := sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
      ν f F hF g hg W N
    massNormSq (E := h) (K := K) ρ π (fun i => (hilbertBandHk (E := h i) N (K i) (qN t i)).val) +
      (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq (E := h) (K := K) ρ π
        (fun i => (hilbertBandHk (E := h i) N (K i + 1) (extendCurve hab qN s i)).val)) ≤
      2 * massNormSq (E := h) (K := K) ρ π (fun i => (hilbertBandHk (E := h i) N (K i) (qN ⟨a, le_rfl, hab⟩ i)).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π (fun i => (RF i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun i => (Rg i s).val))) ^ 2 := by
  intro W U Φ RF Rg qN
  obtain ⟨S, _hS, hpoint, he⟩ := planeWeakSolution_nativeCutoffEnergy (h := h) K Kmax hK N
    ρ strain B lam ν hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b hab
    v hv hvm V hV hbv hdiv hjets D A hA hC hAm hschur F g hF hg f u w hsol
  simp only [intervalIntegral.integral_of_le hab, ← integral_Icc_eq_integral_Ioc] at he
  exact (add_le_add (hpoint t) (le_refl ((ν / 2) * (∫ s in Set.Icc a b,
    massGradNormSq (E := h) (K := K) ρ π
      (fun i => (hilbertBandHk (E := h i) N (K i + 1) (extendCurve hab qN s i)).val))))).trans he
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakProjectedEnergyAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakProjectedEnergyTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_projectedEnergy (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax) (N : ℕ)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) (t : Set.Icc a b) :
    let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
    let U := fun j => weakHighCarrierTimeCLM (h := h) K a b j W
    let Φ := fun j => (hF j).toLp (F j)
    let RF := fun j => (planeResidualFluxTime (h := h) hab ρ hρ K D A hC hA hAm U Φ N j :
      ℝ → PlaneHk Set.univ (K j) (PiLp 2 (fun _ : Fin 2 => h j)))
    let Rg := fun j => planeResidualValueSource hab (hK j) v hvm hv V strain B lam
      hV hstrain0 (le_trans zero_le_one hB) hlam hbv hjets (U j) (g j) N
    let qN := sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
      ν f F hF g hg W N
    massNormSq (E := h) (K := K) ρ π (fun i => (planeHkCutoff N (K i) (u i t)).val) +
      (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq (E := h) (K := K) ρ π
        (fun i => (hilbertBandHk N (K i + 1) (extendCurve hab qN s i)).val)) ≤
      2 * massNormSq (E := h) (K := K) ρ π (fun i => (planeHkCutoff N (K i) (f i)).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π (fun i => (RF i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun i => (Rg i s).val))) ^ 2 := by
  intro W U Φ RF Rg qN
  have he :
    massNormSq (E := h) (K := K) ρ π (fun i => (hilbertBandHk (E := h i) N (K i) (qN t i)).val) +
      (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq (E := h) (K := K) ρ π
        (fun i => (hilbertBandHk (E := h i) N (K i + 1) (extendCurve hab qN s i)).val)) ≤
      2 * massNormSq (E := h) (K := K) ρ π (fun i => (hilbertBandHk (E := h i) N (K i) (qN ⟨a, le_rfl, hab⟩ i)).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π (fun i => (RF i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq (E := h) (K := K) ρ π (fun i => (Rg i s).val))) ^ 2 := by
    exact planeWeakSolution_nativePointEnergy (h := h) K Kmax hK N
      ρ strain B lam ν hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b hab
      v hv hvm V hV hbv hdiv hjets D A hA hC hAm hschur F g hF hg f u w hsol t
  have hj := fun s => planeWeakSolution_nativeFamily_massJets (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
    Kmax hK strain B lam hstrain0 (le_trans zero_le_one hB) hlam hjets ν F hF g hg f u w hsol N s
  have hi := planeWeakSolution_nativeFamily_initialMassJets (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
    Kmax hK strain B lam hstrain0 (le_trans zero_le_one hB) hlam hjets ν F hF g hg f u w hsol N
  have hm : massNormSq (E := h) (K := K) ρ π
      (fun i => (hilbertBandHk (E := h i) N (K i) (qN t i)).val) =
      massNormSq (E := h) (K := K) ρ π (fun i => (planeHkCutoff (E := h i) N (K i) (u i t)).val) :=
    congrArg (massNormSq (E := h) (K := K) ρ π) (hj t)
  have hm0 : massNormSq (E := h) (K := K) ρ π
      (fun i => (hilbertBandHk (E := h i) N (K i) (qN ⟨a, le_rfl, hab⟩ i)).val) =
      massNormSq (E := h) (K := K) ρ π (fun i => (planeHkCutoff (E := h i) N (K i) (f i)).val) :=
    congrArg (massNormSq (E := h) (K := K) ρ π) hi
  let J := (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq (E := h) (K := K) ρ π
    (fun i => (hilbertBandHk (E := h i) N (K i + 1) (extendCurve hab qN s i)).val))
  let Z := (8 / ν) * (∫ s in Set.Icc a b,
    massNormSq (E := fun i => PiLp 2 (fun _ : Fin 2 => h i)) (K := K) ρ π (fun i => (RF i s).val))
  let T := 10 * (∫ s in Set.Icc a b, Real.sqrt
    (massNormSq (E := h) (K := K) ρ π (fun i => (Rg i s).val))) ^ 2
  have hl := congrArg (fun x : ℝ => x + J) hm.symm
  have hr := congrArg (fun x : ℝ => 2 * x + Z + T) hm0
  exact hl.le.trans (he.trans hr.le)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakFinalEnergyAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakFinalEnergyTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_energy (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w) :
    ∀ t ∈ Set.Icc a b,
      massNormSq ρ π (fun i => (u i t).val) +
        (ν / 2) * (∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (w i s).val)) ≤
      2 * massNormSq ρ π (fun i => (f i).val) +
        (8 / ν) * (∫ s in Set.Icc a b, massNormSq ρ π (fun i => (F i s).val)) +
          10 * (∫ s in Set.Icc a b, Real.sqrt (massNormSq ρ π (fun i => (g i s).val))) ^ 2 := by
  let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
  let U := fun i => weakHighCarrierTimeCLM (h := h) K a b i W
  let Φ := fun i => (hF i).toLp (F i)
  let q := fun N => sourceNativeFamilyPrimitive (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
    ν f F hF g hg W N
  have hflux := sourceResidualFlux_budget_tendsto (h := h) hab ρ hρ K D A hC hA hAm U F hF π
  have hvalue := sourceResidualValue_budget_tendsto (h := h) hab K Kmax hK v hvm hv V strain B lam
    hV hstrain0 (le_trans zero_le_one hB) hlam hbv hjets U g hg ρ π hπ
  have hq (N : ℕ) (i : ι) : (fun t => extendCurve hab (q N) t i)
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i + 1) (U i t)) := by
    have ha := planeWeakSolution_nativeFamily_alignment_ae (h := h) hab ρ hρ v hv V hV hbv K D A hC hA hvm hAm
      Kmax hK strain B lam hstrain0 (le_trans zero_le_one hB) hlam hjets ν F hF g hg f u w hsol N i
    have hc := weakHighCarrierTimeCLM_ae (h := h) K a b i W
    filter_upwards [ha, hc] with t ht hc
    exact ht.trans (congrArg (fun p : PlaneHk Set.univ (K i + 1) (h i) =>
      hilbertProjection (E := h i) N (planeHkValueOperator (E := h i) (K i + 1) p)) hc.symm)
  have hgrad := bandCurve_gradient_integral_tendsto_of_alignment (E := h)
    (volume.restrict (Set.Icc a b)) K ρ π U (fun N => extendCurve hab (q N)) hq
  have hw (i : ι) : (U i : ℝ → PlaneHk Set.univ (K i + 1) (h i)) =ᵐ[volume.restrict (Set.Icc a b)] w i :=
    (weakHighCarrierTimeCLM_ae (h := h) K a b i W).trans
      (planeCarrierHighTime_readout_ae (h := h) K a b w hsol.2.1 i)
  have hgi : (∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (U i s).val)) =
      ∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (w i s).val) := by
    apply integral_congr_ae
    filter_upwards [ae_all_iff.mpr hw] with s hs
    exact congrArg (massGradNormSq ρ π) (funext (fun i => congrArg Subtype.val (hs i)))
  rw [hgi] at hgrad
  have hinitial := planeMassNormSq_cutoff_tendsto K ρ π hπ f
  intro t ht
  have htime := planeMassNormSq_cutoff_tendsto K ρ π hπ (fun i => u i t)
  have hleft := htime.add (hgrad.const_mul (ν / 2))
  have hright := ((hinitial.const_mul 2).add (hflux.const_mul (8 / ν))).add ((hvalue.pow 2).const_mul 10)
  exact le_of_tendsto_of_tendsto' hleft hright (fun N =>
    planeWeakSolution_projectedEnergy (h := h) K Kmax hK N
      ρ strain B lam ν hρ hstrain0 hB hlam hν hsmall hstrain π hπ a b hab
      v hv hvm V hV hbv hdiv hjets D A hA hC hAm hschur F g hF hg f u w hsol ⟨t, ht⟩)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance weakUniqueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance weakUniqueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem planeWeakSolution_unique (K : ι → ℕ) (Kmax : ℕ)
    (hK : ∀ i, K i ≤ Kmax)
    (ρ strain B lam ν : ℝ) (hρ : 0 < ρ) (hstrain0 : 0 ≤ strain) (hB : 1 ≤ B)
    (hlam : 0 < lam) (hν : 0 < ν)
    (hsmall : B * ρ / lam ≤ 1 / 2) (hstrain : strain * B * ρ ^ 2 ≤ ν / 8)
    (π : ι → ℝ) (hπ : ∀ i, 0 < π i) (a b : ℝ) (hab : a ≤ b)
    (v : ℝ → Vec 2 → Vec 2)
    (hv : ∀ t ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (hvm : Measurable (fun p : Set.Icc a b × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : 0 ≤ V) (hbv : ∀ t ∈ Set.Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hdiv : ∀ t ∈ Set.Icc a b, ∀ x, ∑ k : Fin 2, fderiv ℝ (v t) x (basisVec k) k = 0)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (D : ℕ)
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (hC : ∀ i i' d, ∀ s ∈ Set.Icc a b, ContDiff ℝ (K i : ℕ) (A i i' d s))
    (hAm : ∀ i j d, Measurable (fun p : Set.Icc a b × Vec 2 => A i j d p.1 p.2))
    (hschur : SchurCondition (schurMatrix ν ρ π K D a b A))
    (F : ∀ i, ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Set.Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Set.Icc a b)))
    (f : ∀ i, PlaneHk Set.univ (K i) (h i))
    (u : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol : IsCoupledWeakSolutionPlane ν a b v D K A f F g u w)
    (u' : ∀ i, ℝ → PlaneHk Set.univ (K i) (h i))
    (w' : ∀ i, ℝ → PlaneHk Set.univ (K i + 1) (h i))
    (hsol' : IsCoupledWeakSolutionPlane ν a b v D K A f F g u' w') :
    ∀ i, ∀ t ∈ Set.Icc a b, u i t = u' i t := by
  let W := planeCarrierHighTime (h := h) K a b w hsol.2.1
  let W' := planeCarrierHighTime (h := h) K a b w' hsol'.2.1
  let U := planeWeakDifferenceCurve (h := h) K a b u u' hsol.1 hsol'.1
  let ud := fun i => extendCurve hab (U i)
  let wd := weakHighCarrier (h := h) K a b (W - W')
  have hsol0 := planeWeakSolution_difference_isWeakSolution (h := h) hab ρ hρ v hv V hV hbv
    K D A hC hA hvm hAm Kmax hK strain B lam hstrain0 (le_trans zero_le_one hB) hlam hjets
    ν F hF g hg f u w hsol u' w' hsol'
  have hF0 (i : ι) : MemLp (fun _ : ℝ => (0 : PlaneHk Set.univ (K i)
      (PiLp 2 (fun _ : Fin 2 => h i)))) 2 (volume.restrict (Set.Icc a b)) := timeMemLp_zero _ _
  have hg0 (i : ι) : Integrable (fun _ : ℝ => (0 : PlaneHk Set.univ (K i) (h i)))
      (volume.restrict (Set.Icc a b)) := timeIntegrable_zero _
  have he := planeWeakSolution_energy (h := h) K Kmax hK ρ strain B lam ν hρ hstrain0 hB hlam hν
    hsmall hstrain π hπ a b hab v hv hvm V hV hbv hdiv hjets D A hA hC hAm hschur
    (fun _ _ => 0) (fun _ _ => 0) hF0 hg0 (fun _ => 0) ud wd hsol0
  have hm0 := planeMassNormSq_zero (h := h) K ρ π hπ
  have hmf0 := planeMassNormSq_zero (h := fun i => PiLp 2 (fun _ : Fin 2 => h i)) K ρ π hπ
  have hgpos : 0 ≤ ν / 2 * (∫ s in Set.Icc a b, massGradNormSq ρ π (fun i => (wd i s).val)) :=
    mul_nonneg (div_nonneg hν.le (by norm_num))
      (integral_nonneg (fun s => massGradNormSq_nonneg ρ π hπ _))
  intro i t ht
  have het := he t ht
  simp only [hm0, hmf0, Real.sqrt_zero, integral_zero, mul_zero, zero_pow (by decide : 2 ≠ 0), add_zero] at het
  have hm : massNormSq ρ π (fun i => (ud i t).val) ≤ 0 :=
    (le_add_of_nonneg_right hgpos).trans het
  have hz := planeCarrier_eq_zero_of_mass_le_zero K ρ hρ π hπ (fun i => ud i t) hm i
  change extendCurve hab (U i) t = 0 at hz
  rw [extendCurve_eq_of_mem hab (U i) ht, planeWeakDifferenceCurve_apply] at hz
  exact sub_eq_zero.mp hz
end

end AVRegularity.CoupledEnergyPlane
end
end
end
