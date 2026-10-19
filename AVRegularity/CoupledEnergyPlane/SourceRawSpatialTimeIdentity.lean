-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CoupledEnergyPlane.SourceFixedBandUniformBound
import Mathlib.CategoryTheory.Countable

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier AVRegularity.CoupledEnergyPlane.Variational
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.CoupledEnergyPlane

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceTransportValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceTransportValueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceWeakTransport_value {a b : ℝ} (hab : a ≤ b)
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
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι) :
    limitDriftField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
      i W = (planeHkValueOperator (E := h i) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b))
        (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
          hV hstrain hB hlam hbv hjets W) := by
  have hp := limitDriftField_ae hab
    (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
    (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
    W i
  have hvv := weakTransportTime_value_ae hab K Kmax hK i v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets W hW
  exact Lp.ext (hp.trans hvv.symm)

end AVRegularity.CoupledEnergyPlane
end

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

local instance sourceWeakLowerBoundAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceWeakLowerBoundTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceWeakLowerCarrier_norm_le_ae {a b : ℝ} (hab : a ≤ b)
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
    (i : ι) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b), ‖weakLowerCarrierTimeCLM K a b i W t‖ ≤
      Real.sqrt ((∑ j, π j / factorialWeightMin ρ (K j)) * C) := by
  exact ae_norm_le_of_continuous_cutoff_bounds hab (weakLowerCarrierTimeCLM K a b i W)
    (fun N => planeHkCutoff (E := h i) N (K i)) (tendsto_planeHkCutoff (K i))
    (fun N => sourceFixedBandSobolevPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg W i N)
    (fun N => sourceFixedBandSobolevPrimitive_ae_eq_cutoff hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass hW i N)
    (Real.sqrt ((∑ j, π j / factorialWeightMin ρ (K j)) * C))
    (fun N t => sourceFixedBandSobolevPrimitive_norm_le hab ρ hρ v hv V hV hbv K D A hAc hAf
      hvm hAm ν f F hF g hg u heq φ hφ W R hu hw hrange π hπ C hmass hW i N t)

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

local instance sourceTransportRawValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceTransportRawValueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceLimitDriftField_raw_value_ae {a b : ℝ} (hab : a ≤ b)
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
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      limitDriftField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
        (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
        i W t =ᵐ[volume] fun x => ∑ k : Fin 2, v (clampPoint a b hab t) x k •
          (weakHighCarrier K a b W i t).toFunction.jet
            ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos (K i))⟩, fun _ => k⟩ x := by
  have he := sourceWeakTransport_value hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW i
  rw [he]
  exact weakTransportTime_raw_value_ae hab K Kmax hK i v hvm hv V strain B lam
    hV hstrain hB hlam hbv hjets W
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceCouplingValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceCouplingValueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceWeakCoupledFlux_value {a b : ℝ} (hab : a ≤ b)
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
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i j : ι) (d : admissibleOrders K D i j) :
    limitEdgeField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
      i j d W =
      (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
        (volume.restrict (Set.Icc a b))
        (weakCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
          (hAc i j d) (hAm i j d) W) := by
  have hp := limitEdgeField_ae hab
    (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
    (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
    W i j d
  have hvv := weakCoupledFluxTime_value_ae hab ρ hρ K D i j d (A i j d) (hAf i j d)
    (hAc i j d) (hAm i j d) W hW
  exact Lp.ext (hp.trans hvv.symm)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceRawCouplingValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceRawCouplingValueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceLimitEdgeField_raw_value_ae {a b : ℝ} (hab : a ≤ b)
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
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i j : ι) (d : admissibleOrders K D i j) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      limitEdgeField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
        (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
        i j d W t =ᵐ[volume] fun x =>
          A i j d (clampPoint a b hab t) x (WithLp.toLp 2
            (fun word : DerivativeWord2 (d.1 - 1) =>
              (weakHighCarrier K a b W j t).toFunction.jet ⟨⟨d.1 - 1, by
                have hh := AVRegularity.CoupledEnergyPlane.Variational.admissibleOrders_reserve K D i j d; omega⟩, word⟩ x)) := by
  have he := sourceWeakCoupledFlux_value hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm W hW i j d
  rw [he]
  exact weakCoupledFluxTime_raw_value_ae hab ρ hρ K D i j d (A i j d) (hAf i j d)
    (hAc i j d) (hAm i j d) W
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceFluxValueAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceFluxValueTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance sourceFluxValueTensorAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance sourceFluxValueTensorTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem sourceSobolevFlux_value {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (F : ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) :
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
      (volume.restrict (Set.Icc a b))
      (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i F hF) =
      ν • (highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W +
        limitFluxField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
          (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
          W i ((planeHkValueOperator (K i)).compLpL 2 (volume.restrict (Set.Icc a b))
            (hF.toLp F)) := by
  let L := (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
    (volume.restrict (Set.Icc a b))
  have hg : L (weakGradientTimeCLM K a b i W) =
      (highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W := by
    apply Lp.ext
    exact (weakGradientTime_value_ae K a b W hW i).trans
      (ContinuousLinearMap.coeFn_compLpL (highGradientReadout (h := h) K i) W).symm
  have he (j : ι) (d : admissibleOrders K D i j) :=
    sourceWeakCoupledFlux_value hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm W hW i j d
  exact assembleTimeFlux_apply_of_fields (volume.restrict (Set.Icc a b)) L ν
    (weakGradientTimeCLM K a b i W)
    (fun j d => weakCoupledFluxTimeCLM hab ρ hρ K D i j d (A i j d) (hAf i j d)
      (hAc i j d) (hAm i j d) W) (hF.toLp F)
    ((highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W)
    (fun j d => limitEdgeField hab
      (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
      i j d W) hg (fun j d => (he j d).symm)
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceFluxFieldsAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceFluxFieldsTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance
local instance sourceFluxFieldsTensorAdd (i : ι) (k : ℕ) :
    AddCommGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance
local instance sourceFluxFieldsTensorTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (PiLp 2 (fun _ : Fin 2 => h i))) := inferInstance

theorem sourceSobolevFlux_value_ae {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (F : ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) :
    (fun t => planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
      (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i F hF t))
      =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        ν • planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (planeGradientTensor (E := h i) (weakH1CarrierTimeCLM K a b i W t)) +
          limitFluxField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
            (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
            W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2 (volume.restrict (Set.Icc a b))
              (hF.toLp F)) t := by
  have hc := sourceSobolevFlux_value hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm ν W hW i F hF
  have hg := (ContinuousLinearMap.coeFn_compLpL (highGradientReadout (h := h) K i) W).trans
    (weakH1CarrierTimeCLM_gradient_ae K a b i W hW).symm
  exact timeFlux_value_ae (volume.restrict (Set.Icc a b))
    (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)) ν
    (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i F hF)
    ((highGradientReadout (h := h) K i).compLpL 2 (volume.restrict (Set.Icc a b)) W)
    (limitFluxField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
      W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2 (volume.restrict (Set.Icc a b)) (hF.toLp F)))
    _ hc hg
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceRawFullFluxAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceRawFullFluxTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceLimitFluxField_raw_value_ae {a b : ℝ} (hab : a ≤ b)
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
    (W : PlaneHighTime (h := h) K a b)
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1))
    (i : ι) (F : ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b))) :
    ∀ᵐ t ∂volume.restrict (Set.Icc a b),
      limitFluxField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
        (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
        W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
          (volume.restrict (Set.Icc a b)) (hF.toLp F)) t =ᵐ[volume] fun x =>
        planeRawCouplingFlux K D t A (fun j => weakHighCarrier K a b W j t) i x +
          (F t).toFunction.jet (valueIndex2 (K i)) x := by
  let μ := volume.restrict (Set.Icc a b)
  let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
  let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
  let P := planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)
  let Fc := P.compLpL 2 μ (hF.toLp F)
  have htime := doubleSum_add_coeFn_ae μ (fun j d => limitEdgeField hab Cc hc i j d W) Fc
  have hedge := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun d : admissibleOrders K D i j =>
    sourceLimitEdgeField_raw_value_ae hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm W hW i j d))
  filter_upwards [htime, hedge, ContinuousLinearMap.coeFn_compLpL P (hF.toLp F), hF.coeFn_toLp,
    ae_restrict_mem measurableSet_Icc] with t ht he hf hft hmem
  change limitFluxField hab Cc hc W i Fc t =ᵐ[volume] _
  change limitFluxField hab Cc hc W i Fc t = (∑ j, ∑ d, limitEdgeField hab Cc hc i j d W t) + Fc t at ht
  rw [ht]
  have hs := doubleSum_add_coeFn_ae (volume : Measure (Vec 2))
    (fun j d => limitEdgeField hab Cc hc i j d W t) (Fc t)
  refine hs.trans ?_
  rw [hf, hft]
  have hedges := ae_all_iff.mpr (fun j => ae_all_iff.mpr (fun d : admissibleOrders K D i j => he j d))
  filter_upwards [hedges, (planeRawValue_ae (F t)).symm] with x hx hfx
  change (∑ j, ∑ d, limitEdgeField hab Cc hc i j d W t x) + P (F t) x = _
  rw [hfx]
  congr 1
  unfold planeRawCouplingFlux
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro d _
  have hclamp : (clampPoint a b hab t).val = t := by
    simp only [clampPoint, min_eq_right hmem.2, max_eq_right hmem.1]
  simpa only [hclamp] using hx j d
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceSobolevRhsAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceSobolevRhsTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceFixedBandSobolevRhs_ae {a b : ℝ} (hab : a ≤ b)
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
    (ν : ℝ) (F : ℝ → PlaneHk Set.univ (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (hF : MemLp F 2 (volume.restrict (Set.Icc a b)))
    (g : ℝ → PlaneHk Set.univ (K i) (h i)) (N : ℕ) :
    (fun t => hilbertBandHkOperator (E := h i) N (K i) (fixedBandRhs (E := h i) N ν
      ((planeHkValueOperator (E := h i) 1).compLpL 2 (volume.restrict (Set.Icc a b))
        (weakH1CarrierTimeCLM K a b i W))
      (limitDriftField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
        (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm) i W)
      (limitFluxField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
        (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
        W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2 (volume.restrict (Set.Icc a b)) (hF.toLp F)))
      (fun s => planeHkValueOperator (E := h i) (K i) (g s)) t)) =ᵐ[volume.restrict (Set.Icc a b)]
      planeBandSobolevRhs (E := h i) N (K i)
        (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i F hF)
        (timeValueSource (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
          hV hstrain hB hlam hbv hjets W) g) := by
  have hf := sourceSobolevFlux_value_ae hab ρ hρ v hv V hV hbv K D A hAc hAf
    hvm hAm ν W hW i F hF
  have hd := sourceWeakTransport_value hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW i
  exact fixedBandSobolevRhs_ae_eq_sourceRhs_of_field_values (E := h i) N (K i) ν
    (weakH1CarrierTimeCLM K a b i W)
    (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam hV hstrain hB hlam hbv hjets W)
    (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i F hF)
    (limitFluxField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
      W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2 (volume.restrict (Set.Icc a b)) (hF.toLp F)))
    (limitDriftField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm) i W)
    hd g hf
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceFullPrimitiveCarrierAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceFullPrimitiveCarrierTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceFixedBandSobolevPrimitive_eq_sourcePrimitive {a b : ℝ} (hab : a ≤ b)
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
    (W : PlaneHighTime (h := h) K a b)
    (Kmax : ℕ) (hK : ∀ i, K i ≤ Kmax) (strain B lam : ℝ)
    (hstrain : 0 ≤ strain) (hB : 0 ≤ B) (hlam : 0 < lam)
    (hjets : ∀ t ∈ Set.Icc a b, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (AVRegularity.driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (hW : ∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j,
      W t j ∈ planeHkGraph (E := h j) Set.univ (K j + 1)) (i : ι) (N : ℕ) :
    sourceFixedBandSobolevPrimitive hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm ν
      f F hF g hg W i N =
      planeBandSobolevPrimitive (E := h i) hab N (K i) (f i)
        (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i (F i) (hF i))
        (Lp.memLp _)
        (timeValueSource (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
          hV hstrain hB hlam hbv hjets W) (g i))
        (timeValueSource_integrable _ _ (hg i)) := by
  have hrhs := sourceFixedBandSobolevRhs_ae hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW i ν (F i) (hF i) (g i) N
  apply ContinuousMap.ext
  intro t
  exact fixedBandSobolevPrimitive_eq_sourcePrimitive_of_rhs (E := h i) hab N (K i) ν (f i)
    ((planeHkValueOperator (E := h i) 1).compLpL 2 (volume.restrict (Set.Icc a b))
      (weakH1CarrierTimeCLM K a b i W))
    (limitDriftField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm) i W)
    (limitFluxField hab (sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf)
      (sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm)
      W i ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2 (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))))
    (fun s => planeHkValueOperator (E := h i) (K i) (g i s))
    ((planeHkValueOperator (E := h i) (K i)).integrable_comp (hg i))
    (sourceSobolevFlux hab ρ hρ K D A hAc hAf hAm ν W i (F i) (hF i)) (Lp.memLp _)
    (timeValueSource (weakTransportTimeCLM hab K Kmax hK i v hvm hv V strain B lam
      hV hstrain hB hlam hbv hjets W) (g i))
    (timeValueSource_integrable _ _ (hg i)) hrhs t
end

/-! The actual limiting carrier fields recover the precise native weak test formula. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

local instance sourceRawSpatialTimeAdd (i : ι) (k : ℕ) : AddCommGroup (PlaneHk Set.univ k (h i)) :=
  inferInstance
local instance sourceRawSpatialTimeTopAdd (i : ι) (k : ℕ) :
    IsTopologicalAddGroup (PlaneHk Set.univ k (h i)) := inferInstance

theorem sourceRawSpatialRhs_time_ae_native {a b : ℝ} (hab : a ≤ b)
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
    (g : ∀ j, ℝ → PlaneHk Set.univ (K j) (h j)) (ψ : PlaneHk Set.univ 1 (h i)) :
    let Cc := sourceProjectedCoefficients a b ρ hρ v hv V hV hbv K D A hAc hAf
    let hc := sourceProjectedCoefficients_isMeasurable a b ρ hρ v hv hvm V hV hbv K D A hAc hAf hAm
    (fun t => ∫ x, planeRawSpatialRhs K D ν t v A F g
      (fun j => weakHighCarrier K a b W j t) i ψ x) =ᵐ[volume.restrict (Set.Icc a b)] fun t =>
        -inner ℝ (limitDriftField hab Cc hc i W t) (planeHkValueOperator (E := h i) 1 ψ) -
          ν * inner ℝ (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0
            (planeGradientTensor (E := h i) (weakH1CarrierTimeCLM K a b i W t)))
            (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (planeGradientTensor (E := h i) ψ)) -
          inner ℝ (limitFluxField hab Cc hc W i
            ((planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) (K i)).compLpL 2
              (volume.restrict (Set.Icc a b)) ((hF i).toLp (F i))) t)
            (planeHkValueOperator (E := PiLp 2 (fun _ : Fin 2 => h i)) 0 (planeGradientTensor (E := h i) ψ)) +
          inner ℝ (planeHkValueOperator (E := h i) (K i) (g i t)) (planeHkValueOperator (E := h i) 1 ψ) := by
  have hd := sourceLimitDriftField_raw_value_ae hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    Kmax hK strain B lam hstrain hB hlam hjets W hW i
  have hf := sourceLimitFluxField_raw_value_ae hab ρ hρ v hv V hV hbv K D A hAc hAf hvm hAm
    W hW i (F i) (hF i)
  have hg := weakH1CarrierTime_raw_gradient_ae K a b i W
  dsimp only
  filter_upwards [hd, hf, hg, ae_restrict_mem measurableSet_Icc] with t ht hf hg hmem
  have hclamp : (clampPoint a b hab t).val = t := by
    simp only [clampPoint, min_eq_right hmem.2, max_eq_right hmem.1]
  have hd' := ht
  simp only [hclamp] at hd'
  have hp := planeRawSpatialRhs_ae_native_of_fields K D ν t v A F g
    (fun j => weakHighCarrier K a b W j t) i ψ _ _ _ hd' hg hf
  exact (integral_congr_ae hp).trans
    (nativeRawSpatialRhs_integrable_and_integral ν _ _ _ _ ψ).2
end

end AVRegularity.CoupledEnergyPlane
end
