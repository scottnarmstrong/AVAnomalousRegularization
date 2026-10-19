-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CoupledEnergy.Galerkin.TorusBandSourceIntegrand
public import AVRegularity.CoupledEnergy.Galerkin.PlainWeightedSynthesis
public import AVRegularity.CoupledEnergy.Galerkin.PlainSourcePairing

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter
open AVenhance.Infra.Parabolic.FourierGalerkin
open scoped ENNReal
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Strong measurability of bounded coefficient actions, recovered from finite
Fourier readouts. This is the finite-projection argument used in the reused
Galerkin limit construction; it requires no time continuity. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [CompleteSpace E] in
/-- Jointly measurable, spatially continuous bounded coefficients act strongly
measurably on every fixed spatial L² class. -/
theorem boundedCoefficientL2_stronglyMeasurable {T : Type*} [MeasurableSpace T]
    (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖C t x‖ ≤ M)
    (u : Lp E 2 (volume.restrict AVenhance.unitCube)) :
    StronglyMeasurable (fun t => boundedCoefficientL2 (C t) (hc t) M hM (hb t) u) := by
  let v := fun t => boundedCoefficientL2 (C t) (hc t) M hM (hb t) u
  have hpair (z : Lp F 2 (volume.restrict AVenhance.unitCube)) :
      StronglyMeasurable (fun t => inner ℝ z (v t)) := by
    have hm := coefficientPairing_stronglyMeasurable C hC u z
    have he : (fun t => inner ℝ z (v t)) =
        (fun t => ∫ x, inner ℝ (C t x (u x)) (z x) ∂volume.restrict AVenhance.unitCube) := by
      funext t
      rw [real_inner_comm]
      exact boundedCoefficientL2_inner_eq_integral (C t) (hc t) M hM (hb t) u z
    rw [he]
    exact hm
  have hp (N : ℕ) : StronglyMeasurable (fun t => cellVectorFourierProjection N (v t)) := by
    simp only [cellVectorFourierProjection_eq_plain_sum (h := fun _ : Unit => F) N ()]
    exact Finset.stronglyMeasurable_fun_sum Finset.univ (fun p _ =>
      (hpair _).smul stronglyMeasurable_const)
  apply stronglyMeasurable_of_tendsto atTop hp
  exact tendsto_pi_nhds.mpr (fun t => cellVectorFourierProjection_tendsto (v t))

omit [CompleteSpace E] in
/-- A bounded jointly measurable coefficient preserves Bochner L² in time. -/
theorem boundedCoefficientL2_time_memLp {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖C t x‖ ≤ M)
    (u : T → Lp E 2 (volume.restrict AVenhance.unitCube)) (hu : MemLp u 2 μ) :
    MemLp (fun t => boundedCoefficientL2 (C t) (hc t) M hM (hb t) (u t)) 2 μ := by
  let : TopologicalSpace.SeparableSpace E := inferInstance
  let : SFinite (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : MeasurableSpace.CountablyGenerated (Vec 2) := inferInstance
  let : IsSeparable (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := inferInstance
  let : Fact (1 ≤ (2 : ℝ≥0∞)) := ⟨by norm_num⟩
  let : Fact ((2 : ℝ≥0∞) ≠ ∞) := ⟨by norm_num⟩
  let : SecondCountableTopology (Lp E 2 (volume.restrict AVenhance.unitCube)) := Lp.SecondCountableTopology
  borelize ↥(Lp E 2 (volume.restrict AVenhance.unitCube))
  let L := fun t => boundedCoefficientL2CLM (U := AVenhance.unitCube) (C t) (hc t) M hM (hb t)
  have hm (x : Lp E 2 (volume.restrict AVenhance.unitCube)) :
      StronglyMeasurable (fun t => L t x) :=
    boundedCoefficientL2_stronglyMeasurable C hC hc M hM hb x
  have hn (t : T) : ‖L t‖ ≤ M := by
    exact boundedCoefficientL2CLM_norm_le (C t) (hc t) M hM (hb t)
  exact Variational.memLp_operator_action L hm hu hM hn

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Native bounded spatial coefficients as fixed temporal operators. These
operators retain the literal coefficient integrals when tested on subintervals. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

/-- The original coefficient field acts as one bounded operator on time L². -/
def coefficientTimeCLM {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖C t x‖ ≤ M) :
    Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2 μ →L[ℝ]
      Lp (Lp F 2 (volume.restrict AVenhance.unitCube)) 2 μ := by
  let : SecondCountableTopology (Lp E 2 (volume.restrict AVenhance.unitCube)) :=
    Variational.cellL2SecondCountableTopology
  borelize ↥(Lp E 2 (volume.restrict AVenhance.unitCube))
  let L := fun t => boundedCoefficientL2CLM (U := AVenhance.unitCube) (C t) (hc t) M hM (hb t)
  exact Variational.timeOperatorCLM μ L
    (fun x => boundedCoefficientL2_stronglyMeasurable C hC hc M hM hb x)
    M hM (fun t => boundedCoefficientL2CLM_norm_le (C t) (hc t) M hM (hb t))

omit [CompleteSpace E] in
/-- The temporal operator represents the actual spatial multiplication almost everywhere. -/
theorem coefficientTimeCLM_ae {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖C t x‖ ≤ M)
    (U : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2 μ) :
    coefficientTimeCLM μ C hC hc M hM hb U =ᵐ[μ]
      fun t => boundedCoefficientL2 (C t) (hc t) M hM (hb t) (U t) := by
  let : SecondCountableTopology (Lp E 2 (volume.restrict AVenhance.unitCube)) :=
    Variational.cellL2SecondCountableTopology
  borelize ↥(Lp E 2 (volume.restrict AVenhance.unitCube))
  exact Variational.timeOperatorValue_ae μ
    (fun t => boundedCoefficientL2CLM (U := AVenhance.unitCube) (C t) (hc t) M hM (hb t))
    (fun x => boundedCoefficientL2_stronglyMeasurable C hC hc M hM hb x) M hM
    (fun t => boundedCoefficientL2CLM_norm_le (C t) (hc t) M hM (hb t)) U

omit [CompleteSpace E] in
/-- Testing the native temporal coefficient action gives the literal double integral. -/
theorem coefficientTimeCLM_test_integral {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ r, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r x, ‖C r x‖ ≤ M)
    (U : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b)))
    (z : ℝ → Lp F 2 (volume.restrict AVenhance.unitCube))
    (hz : MemLp z 2 (volume.restrict (Set.Icc a b))) :
    Variational.timeTestIntegralCLM a b s t z hz
      (coefficientTimeCLM (volume.restrict (Set.Icc a b)) C hC hc M hM hb U) =
      ∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (U r x)) (z r x) := by
  rw [Variational.timeTestIntegralCLM_apply_class hs ht hst]
  apply intervalIntegral.integral_congr_ae_restrict
  have he := coefficientTimeCLM_ae (volume.restrict (Set.Icc a b)) C hC hc M hM hb U
  have hsub : Set.uIoc s t ⊆ Set.Icc a b := by
    rw [Set.uIoc_of_le hst]
    exact Set.Ioc_subset_Icc_self.trans (Set.Icc_subset_Icc hs.1 ht.2)
  filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub he] with r hr
  rw [hr]
  exact boundedCoefficientL2_inner_eq_integral (C r) (hc r) M hM (hb r) (U r) (z r)

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open scoped Topology
namespace AVRegularity.CoupledEnergy.Galerkin

/-! The coupled Fourier ODE with coefficient hypotheses discharged from the data of the coupled
energy statement. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Initial coefficients obtained by scalar Fourier value pairings. -/
def plainInitialCoefficients (N : ℕ) (K : ι → ℕ) (f : ∀ i, TorusHk (K i) (h i)) :
    CoupledPlainCoefficients (h := h) N :=
  fun r => ∑ i, plainValueForcingCLM N r i (K i) (f i)

/-- Existence and uniqueness for the actual finite matrix of Fourier coefficient integrals.
This solves only the finite ODE; the PDE and energy claims require the synthesis identities. -/
theorem plainCoupledFourierODE_existsUnique (N D : ℕ) (ν ρ : ℝ) (hρ : 0 < ρ) (K : ι → ℕ)
    (a b : ℝ) (hab : a ≤ b) (v : ℝ → Vec 2 → Vec 2)
    (hv_bdd : ∃ V : ℝ, ∀ t ∈ Icc a b, ∀ x, ‖v t x‖ ≤ V)
    (hv_meas : Measurable (fun p : Icc a b × Vec 2 => v p.1 p.2))
    (A : ∀ (i i' : ι) (d : admissibleOrders K D i i'), ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') →L[ℝ]
        PiLp 2 (fun _ : Fin 2 => h i))
    (hA_meas : ∀ i i' d, Measurable (fun p : Icc a b × Vec 2 => A i i' d p.1 p.2))
    (hA_fin : ∀ i i' d, coefficientSeminorm ρ (K i) a b (A i i' d) ≠ ⊤)
    (f : ∀ i, TorusHk (K i) (h i))
    (F : ∀ i, ℝ → TorusHk (K i) (PiLp 2 (fun _ : Fin 2 => h i)))
    (g : ∀ i, ℝ → TorusHk (K i) (h i))
    (hF : ∀ i, MemLp (F i) 2 (volume.restrict (Icc a b)))
    (hg : ∀ i, Integrable (g i) (volume.restrict (Icc a b))) :
    ∃! y : C(Icc a b, CoupledPlainCoefficients (h := h) N),
      AVenhance.Infra.ODE.IsLinearIntegralSolution
        (fun t => plainMatrixCLM (plainIntervalMatrix N D ν K a b hab v A t))
        (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t))
        (plainInitialCoefficients N K f) a b (AVenhance.Infra.ODE.extendCurve hab y) ∧
      AbsolutelyContinuousOnInterval (AVenhance.Infra.ODE.extendCurve hab y) a b := by
  obtain ⟨C₀, hC₀, hbound⟩ := plainIntervalMatrix_bounded N D ν ρ hρ K a b hab v hv_bdd A hA_fin
  have hm : ∀ r c, AEStronglyMeasurable
      (fun t => plainIntervalMatrix N D ν K a b hab v A t r c) volume :=
    fun r c => (plainIntervalMatrix_stronglyMeasurable N D ν K a b hab v hv_meas A hA_meas r c).aestronglyMeasurable
  have hf : IntervalIntegrable
      (fun t => plainSourceCoefficients N K (fun i => F i t) (fun i => g i t)) volume a b :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le hab).mpr
      (plainSourceCoefficients_integrable N K a b F g hF hg)
  exact plainMatrixODE_existsUnique hab _ _ _ C₀ hC₀ hm hbound hf

end AVRegularity.CoupledEnergy.Galerkin
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CoupledEnergy.Galerkin

/-! Time integrability of the literal scalar coefficient pairings. This
supplies integrability when assembling the individual weak-limit terms. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [CompleteSpace E] in
/-- Bounded native coefficients paired with a time L² test give an L¹ scalar time function. -/
theorem coefficientTime_pairing_integrable {T : Type*} [MeasurableSpace T]
    (μ : Measure T) (C : T → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (Function.uncurry C)) (hc : ∀ t, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t x, ‖C t x‖ ≤ M)
    (U : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2 μ)
    (z : T → Lp F 2 (volume.restrict AVenhance.unitCube)) (hz : MemLp z 2 μ) :
    Integrable (fun t => ∫ x in AVenhance.unitCube, inner ℝ (C t x (U t x)) (z t x)) μ := by
  have hi := L2.integrable_inner (𝕜 := ℝ)
    (coefficientTimeCLM μ C hC hc M hM hb U) (hz.toLp z)
  apply hi.congr
  filter_upwards [coefficientTimeCLM_ae μ C hC hc M hM hb U, hz.coeFn_toLp] with t ht hzt
  rw [ht, hzt]
  exact boundedCoefficientL2_inner_eq_integral (C t) (hc t) M hM (hb t) (U t) (z t)

omit [CompleteSpace E] in
/-- Interval-only measurability and bounds suffice for integrability of the native pairing. -/
theorem intervalCoefficientTime_pairing_integrable {a b : ℝ} (hab : a ≤ b)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ t ∈ Set.Icc a b, Continuous (C t))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ t ∈ Set.Icc a b, ∀ x, ‖C t x‖ ≤ M)
    (U : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2
      (volume.restrict (Set.Icc a b)))
    (z : ℝ → Lp F 2 (volume.restrict AVenhance.unitCube))
    (hz : MemLp z 2 (volume.restrict (Set.Icc a b))) :
    Integrable (fun t => ∫ x in AVenhance.unitCube, inner ℝ (C t x (U t x)) (z t x))
      (volume.restrict (Set.Icc a b)) := by
  let Cp := fun t x => C (Set.projIcc a b hab t) x
  have hCp : Measurable (Function.uncurry Cp) :=
    hC.comp (((continuous_projIcc (a := a) (b := b) (h := hab)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hi := coefficientTime_pairing_integrable (volume.restrict (Set.Icc a b)) Cp hCp
    (fun t => hc _ (Set.projIcc a b hab t).property) M hM
    (fun t => hb _ (Set.projIcc a b hab t).property) U z hz
  apply hi.congr
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  simp only [Cp, Set.projIcc_of_mem hab ht]
end

/-! Literal interval coefficient pairings commute with subtraction of
Bochner classes, by the temporal coefficient operator. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
  [MeasurableSpace F] [BorelSpace F] [CompleteSpace F]
  [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

omit [CompleteSpace E] in
theorem intervalCoefficient_integral_sub {a b s t : ℝ}
    (hs : s ∈ Set.Icc a b) (ht : t ∈ Set.Icc a b) (hst : s ≤ t)
    (C : ℝ → Vec 2 → E →L[ℝ] F)
    (hC : Measurable (fun p : Set.Icc a b × Vec 2 => C p.1 p.2))
    (hc : ∀ r ∈ Set.Icc a b, Continuous (C r))
    (M : ℝ) (hM : 0 ≤ M) (hb : ∀ r ∈ Set.Icc a b, ∀ x, ‖C r x‖ ≤ M)
    (U V : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2 (volume.restrict (Set.Icc a b)))
    (z : Lp F 2 (volume.restrict AVenhance.unitCube)) :
    (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x ((U - V) r x)) (z x)) =
      (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (U r x)) (z x)) -
        (∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (V r x)) (z x)) := by
  have hab : a ≤ b := hs.1.trans hs.2
  let Cp := fun r x => C (Set.projIcc a b hab r) x
  have hm : Measurable (Function.uncurry Cp) :=
    hC.comp (((continuous_projIcc (a := a) (b := b) (h := hab)).measurable.comp
      measurable_fst).prodMk measurable_snd)
  have hcont (r : ℝ) : Continuous (Cp r) := hc _ (Set.projIcc a b hab r).property
  have hbound (r : ℝ) (x : Vec 2) : ‖Cp r x‖ ≤ M := hb _ (Set.projIcc a b hab r).property x
  let L := coefficientTimeCLM (volume.restrict (Set.Icc a b)) Cp hm hcont M hM hbound
  let ell := Variational.timeTestIntegralCLM a b s t (fun _ => z) (memLp_const z)
  have he (W : Lp (Lp E 2 (volume.restrict AVenhance.unitCube)) 2 (volume.restrict (Set.Icc a b))) :
      ell (L W) = ∫ r in s..t, ∫ x in AVenhance.unitCube, inner ℝ (C r x (W r x)) (z x) := by
    rw [coefficientTimeCLM_test_integral hs ht hst Cp hm hcont M hM hbound]
    apply intervalIntegral.integral_congr
    intro r hr
    have hrI : r ∈ Set.Icc a b := by
      rw [Set.uIcc_of_le hst] at hr
      exact ⟨hs.1.trans hr.1, hr.2.trans ht.2⟩
    simp only [Cp, Set.projIcc_of_mem hab hrI]
  have hh : ell (L (U - V)) = ell (L U) - ell (L V) := by rw [map_sub, map_sub]
  simpa only [he] using hh
end

end AVRegularity.CoupledEnergy.Galerkin
end
