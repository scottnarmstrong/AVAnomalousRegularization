-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.CycleEvolution.CellEnergySpaceRawSmul
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Identification of the Galerkin moment primitives with the weak state. -/

variable {a b : ℝ} {hab : a ≤ b} {P : MolecularData}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The weak temporal state satisfies the actual integrated cell equation a.e. for each test. -/
theorem MolecularGalerkinLimitData.moment_ae
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (z : TorusHk 1 ℂ) : ∀ᵐ t ∂volume.restrict (Icc a b),
      inner ℝ (torusHkValueCLM (D.limit t)) (torusHkValueCLM z) =
        inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t,
          dataGeneratorForm P r (D.limit r) z +
            cellRawSourceFunctional 0 src F r z := by
  obtain ⟨E, hE, hbound⟩ := D.uniform_trace_bound hsrc hF
  let L := (innerSL ℝ (torusHkValueCLM z)).comp (torusHkValueCLM (E := ℂ) (K := 1))
  let p := fun t => inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t,
    dataGeneratorForm P r (D.limit r) z + cellRawSourceFunctional 0 src F r z
  have he (n : ℕ) (t : ℝ) : L (D.state (D.subsequence n) t) =
      inner ℝ (cellGalerkinValue (D.subsequence n)
        (extendCurve hab (D.curve (D.subsequence n)) t)) (torusHkValueCLM z) := by
    change inner ℝ (torusHkValueCLM z)
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t)) = _
    exact real_inner_comm _ _
  have hsq : ∀ n, ∀ᵐ t ∂volume.restrict (Icc a b),
      (L (D.state (D.subsequence n) t)) ^ 2 ≤ E * ‖torusHkValueCLM z‖ ^ 2 := by
    intro n
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    rw [he]
    have hi := abs_real_inner_le_norm
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)
    calc
      _ ≤ (‖cellGalerkinValue (D.subsequence n)
          (extendCurve hab (D.curve (D.subsequence n)) t)‖ * ‖torusHkValueCLM z‖) ^ 2 :=
        by
          have hh := (sq_le_sq₀ (abs_nonneg _)
            (mul_nonneg (norm_nonneg _) (norm_nonneg _))).mpr hi
          simpa only [sq_abs] using hh
      _ ≤ E * ‖torusHkValueCLM z‖ ^ 2 := by
        rw [mul_pow]
        exact mul_le_mul_of_nonneg_right (hbound _ t ht) (sq_nonneg _)
  have hl : ∀ᵐ t ∂volume.restrict (Icc a b),
      Tendsto (fun n => L (D.state (D.subsequence n) t)) atTop (𝓝 (p t)) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    simpa only [he, p] using D.moment_primitive_tendsto hsrc hF z t ht
  have hm := cellWeak_scalar_moment_identification
    (fun n => D.state (D.subsequence n)) (fun n => D.stateLp (D.subsequence n))
    D.limit D.weak L p (E * ‖torusHkValueCLM z‖ ^ 2)
    (mul_nonneg hE (sq_nonneg _)) hsq hl
  filter_upwards [hm] with t ht
  exact (real_inner_comm _ _).trans ht

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Actual weak time data and continuous Hilbert trace of the Galerkin limit. -/

variable {a b : ℝ} {hab : a ≤ b} {P : MolecularData}
  {src : ℝ → Vec 2 → ℂ} {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
  {initial : ComplexCellL2}

/-- The actual dual derivative of the weak Galerkin state. -/
def MolecularGalerkinLimitData.dualState
    (D : MolecularGalerkinLimitData a b hab P src F initial) (t : ℝ) : TorusHk 1 ℂ :=
  dataDualDerivative P t (D.limit t) (cellSourceSlice src t)
    (fun j => cellSourceSlice (fun r x => F r x j) t)

/-- All actual weak time premises follow from the Galerkin construction and L² data. -/
theorem MolecularGalerkinLimitData.weakTimeData
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    CellWeakTimeData a b D.limit D.dualState initial := by
  have hS := cellSourceSlice_memLp (Icc a b) src hsrc
  have hQ (j : Fin 2) := cellSourceSlice_memLp (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  refine ⟨Lp.memLp D.limit, ?_, ?_⟩
  · exact dataDualDerivative_memLp P D.limit (Lp.memLp D.limit)
      _ hS _ hQ
  · intro z
    filter_upwards [D.moment_ae hsrc hF z] with t ht
    convert ht using 1
    congr 1
    apply intervalIntegral.integral_congr
    intro r _
    exact dataDualDerivative_pairing P r (D.limit r) z _ _

/-- The actual Galerkin limit has a continuous L² trace, its prescribed initial value,
and the integrated weak equation on every closed subinterval. -/
theorem MolecularGalerkinLimitData.exists_continuous_trace
    (D : MolecularGalerkinLimitData a b hab P src F initial) (hab' : a < b)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube))) :
    ∃ U : C(Icc a b, ComplexCellL2),
      CellWeakHilbertCurve a b (extendCurve hab U) D.limit D.dualState ∧
        extendCurve hab U a = initial := by
  exact (D.weakTimeData hsrc hF).exists_hilbert_curve hab'

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Closed-time Galerkin moment limits identify the continuous molecular trace. -/

theorem MolecularGalerkinLimitData.trace_moment {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {initial : ComplexCellL2}
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (u : ℝ → ComplexCellL2) (hu : CellWeakHilbertCurve a b u D.limit D.dualState)
    (hi : u a = initial) (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    inner ℝ (u t) (torusHkValueCLM z) = inner ℝ initial (torusHkValueCLM z) +
      ∫ r in a..t, dataGeneratorForm P r (D.limit r) z + cellRawSourceFunctional 0 src F r z := by
  have hh := hu.increment a ⟨le_rfl, hab⟩ t ht ht.1 z
  rw [hi] at hh
  have he : (∫ r in a..t, inner ℝ (D.dualState r) z) =
      ∫ r in a..t, dataGeneratorForm P r (D.limit r) z + cellRawSourceFunctional 0 src F r z := by
    apply intervalIntegral.integral_congr
    intro r _
    exact dataDualDerivative_pairing P r (D.limit r) z _ _
  rw [he] at hh
  linarith

theorem MolecularGalerkinLimitData.trace_moments_tendsto {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)} {initial : ComplexCellL2}
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (u : ℝ → ComplexCellL2) (hu : CellWeakHilbertCurve a b u D.limit D.dualState)
    (hi : u a = initial) (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => inner ℝ (cellGalerkinValue (D.subsequence n)
      (AVenhance.Infra.ODE.extendCurve hab (D.curve (D.subsequence n)) t)) (torusHkValueCLM z))
      atTop (𝓝 (inner ℝ (u t) (torusHkValueCLM z))) := by
  rw [D.trace_moment u hu hi z t ht]
  exact D.moment_primitive_tendsto hsrc hF z t ht

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVenhance.Infra.ODE
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Actual Hilbert weak cell solutions for arbitrary L² data, including singleton intervals. -/

/-- Measurable coefficient and source premises construct an actual Hilbert weak solution. -/
theorem dataActual_exists_Hilbert {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrcm : Measurable (Function.uncurry src)) (hFm : Measurable (Function.uncurry F))
    (hsrc : ∫⁻ t in Icc a b, cellL2Norm (src t) ^ 2 < ⊤)
    (hF : ∫⁻ t in Icc a b, cellL2Norm (F t) ^ 2 < ⊤)
    (initial : ComplexCellL2) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      CellWeakHilbertCurve a b u slice (fun r => dataDualDerivative P r
        (slice r) (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)) ∧
      u a = initial := by
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨D⟩ := dataGalerkin_limit_data hab P
      src F hsrcm hFm hsrc hF initial
    obtain ⟨U, hU, hi⟩ := D.exists_continuous_trace hlt
      (cellSource_memLp_product (Icc a b) src hsrcm hsrc)
      (cellSource_memLp_product (Icc a b) F hFm hF)
    exact ⟨extendCurve hab U, D.limit, hU, hi⟩
  · subst b
    exact ⟨fun _ => initial, fun _ => 0, cellSingleton_weak_curve a initial _, rfl⟩

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! The actual spatially constant metric perturbation is a produced higher flux. -/

def HigherSourceCarrierData.withMetricFlux {I : Set ℝ} [IsFiniteMeasure (volume.restrict I)]
    {K : ℕ} {src : ℝ → Vec 2 → ℂ} {flux : ℝ → Vec 2 → ComplexCellVector}
    (Q : HigherSourceCarrierData I K src flux)
    (A : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (D : ℝ → RawJet2 1 ℂ)
    (w : ℝ → TorusHk (K + 1) ℂ)
    (B R : ℝ) (hB : 0 ≤ B) (hR : 0 ≤ R)
    (hAm : ∀ i j, Measurable (fun t => A t i j))
    (hAb : ∀ t i j, |A t i j| ≤ B)
    (hwm : StronglyMeasurable w) (hwb : ∀ t, ‖w t‖ ≤ R)
    (hD : ∀ᵐ t ∂volume.restrict I, HasPeriodicOrderedWeakJet (D t))
    (hwD : ∀ᵐ t ∂volume.restrict I, torusHkValueCLM (w t) =ᵐ[
      volume.restrict AVenhance.unitCube] D t (valueIndex2 1))
    (hJ : MemLp (Function.uncurry (cellMetricFlux (fun t _ => A t) D)) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    HigherSourceCarrierData I K src (flux + cellMetricFlux (fun t _ => A t) D) :=
  Q.withAdditionalFlux (cellMetricFlux (fun t _ => A t) D)
    (fun t => metricGradientCarrier K (A t) (w t))
    (B * metricGradientCarrierConstant K * R)
    (mul_nonneg (mul_nonneg hB (metricGradientCarrierConstant_nonneg K)) hR) hJ
    (metricGradientCarrier_memLp K A hAm w hwm B R hB hAb hwb)
    (by
      filter_upwards [hD, hwD] with t ht hwt
      exact metricGradientCarrier_raw_flux_ae K (A t) (w t) (D t) ht hwt)
    (fun t _ => (metricGradientCarrier_norm_le K (A t) B hB (hAb t) (w t)).trans
      (mul_le_mul_of_nonneg_left (hwb t)
        (mul_nonneg hB (metricGradientCarrierConstant_nonneg K))))

/-! Genuine lower inverse carriers produce a finite ordered sum of metric-gradient higher sources. -/

section
variable {J : Type*} {I : Set ℝ} [IsFiniteMeasure (volume.restrict I)]
variable {K : ℕ} {src : ℝ → Vec 2 → ℂ} {flux : ℝ → Vec 2 → ComplexCellVector}

theorem HigherSourceCarrierData.metricFluxList_exists
    (Q : HigherSourceCarrierData I K src flux) (l : List J)
    (A : J → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (D : J → ℝ → RawJet2 1 ℂ) (u : J → ℝ → TorusHk (K + 1) ℂ)
    (B R : J → ℝ)
    (hB : ∀ j ∈ l, 0 ≤ B j) (hR : ∀ j ∈ l, 0 ≤ R j)
    (hAm : ∀ j ∈ l, ∀ a b, Measurable (fun t => A j t a b))
    (hAb : ∀ j ∈ l, ∀ t a b, |A j t a b| ≤ B j)
    (hum : ∀ j ∈ l, StronglyMeasurable (u j))
    (hub : ∀ j ∈ l, ∀ t, ‖u j t‖ ≤ R j)
    (hD : ∀ j ∈ l, ∀ᵐ t ∂volume.restrict I, HasPeriodicOrderedWeakJet (D j t))
    (huD : ∀ j ∈ l, ∀ᵐ t ∂volume.restrict I,
      torusHkValueCLM (u j t) =ᵐ[volume.restrict AVenhance.unitCube] D j t (valueIndex2 1))
    (hM : ∀ j ∈ l, MemLp (Function.uncurry (cellMetricFlux (fun t _ => A j t) (D j))) 2
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube))) :
    ∃ Qnext : HigherSourceCarrierData I K src
        (flux + (l.map (fun j => cellMetricFlux (fun t _ => A j t) (D j))).sum),
      Qnext.Ns = Q.Ns ∧ Qnext.Nf = Q.Nf +
        (l.map (fun j => B j * metricGradientCarrierConstant K * R j)).sum := by
  induction l generalizing flux with
  | nil =>
    refine ⟨Q.congrSources rfl (by simp), ?_, ?_⟩ <;> simp [HigherSourceCarrierData.congrSources]
  | cons j l ih =>
    let Qhead := Q.withMetricFlux (A j) (D j) (u j) (B j) (R j)
      (hB j (by simp)) (hR j (by simp)) (hAm j (by simp)) (hAb j (by simp))
      (hum j (by simp)) (hub j (by simp)) (hD j (by simp)) (huD j (by simp)) (hM j (by simp))
    obtain ⟨Qt, hts, htf⟩ := ih Qhead
      (fun k hk => hB k (by simp [hk])) (fun k hk => hR k (by simp [hk]))
      (fun k hk => hAm k (by simp [hk])) (fun k hk => hAb k (by simp [hk]))
      (fun k hk => hum k (by simp [hk])) (fun k hk => hub k (by simp [hk]))
      (fun k hk => hD k (by simp [hk])) (fun k hk => huD k (by simp [hk]))
      (fun k hk => hM k (by simp [hk]))
    simp only [List.map_cons, List.sum_cons]
    refine ⟨Qt.congrSources rfl (add_assoc _ _ _), ?_, ?_⟩
    · exact hts
    · change Qt.Nf = _
      rw [htf]
      change (Q.Nf + B j * metricGradientCarrierConstant K * R j) + _ = _
      exact add_assoc _ _ _
end

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Uniqueness for the actual weak cell equation with common forcing. -/

/-- Common scalar and divergence forcing cancels in the difference dual equation. -/
theorem dataDualDerivative_difference_pairing
    (P : MolecularData)
    
    (t : ℝ) (u v z : TorusHk 1 ℂ) (S : ComplexCellL2) (F : Fin 2 → ComplexCellL2) :
    inner ℝ (dataDualDerivative P t u S F -
      dataDualDerivative P t v S F) z = dataGeneratorForm P t (u - v) z := by
  rw [inner_sub_left, dataDualDerivative_pairing, dataDualDerivative_pairing]
  have he := congrArg (fun L : TorusHk 1 ℂ →L[ℝ] ℝ => L z)
    ((dataGeneratorForm P t).map_sub u v)
  simp only [sub_apply] at he
  rw [he]
  ring

/-- The actual cell equation has a cutoff-independent one-sided growth bound. -/
theorem dataGenerator_garding (P : MolecularData)
    
    (t : ℝ) (z : TorusHk 1 ℂ) :
    2 * dataGeneratorForm P t z z ≤
      (1 + 8 * P.V ^ 2) * ‖torusHkValueCLM z‖ ^ 2 := by
  have hp := molecularGenerator_source_energy_bound P.G P.v P.V P.metric_coercive P.drift_measurable P.drift_bounded t z 0 (fun _ => 0)
  simp only [cellSourceFunctional, ContinuousLinearMap.comp_apply, sub_apply, sum_apply,
    innerSL_apply_apply, inner_zero_left, Finset.sum_const_zero, sub_self, add_zero,
    norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero] at hp
  have hd : 0 ≤ (1 / 2 : ℝ) * ∑ j : Fin 2, ‖cellDerivativeCLM j z‖ ^ 2 := by positivity
  change 2 * dataGeneratorForm P t z z +
    (1 / 2) * ∑ j : Fin 2, ‖cellDerivativeCLM j z‖ ^ 2 ≤
      (1 + 8 * P.V ^ 2) * ‖torusHkValueCLM z‖ ^ 2 at hp
  linarith

/-- All Hilbert traces of weak solutions of the actual cell equation agree for common initial data. -/
theorem dataActualWeak_unique {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData)
    
    (S : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u v : ℝ → ComplexCellL2) (slice other : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => dataDualDerivative P t (slice t) (S t) (F t)))
    (h' : CellWeakHilbertCurve a b v other
      (fun t => dataDualDerivative P t (other t) (S t) (F t)))
    (hi : u a = v a) : ∀ t ∈ Icc a b, u t = v t := by
  let R := (1 + 8 * P.V ^ 2)
  have hR : 0 ≤ R := by
    dsimp only [R]
    positivity
  apply cellWeakHilbert_unique_of_difference_growth hab h h' hi R hR
  filter_upwards [h.agrees, h'.agrees] with t ht ht'
  rw [dataDualDerivative_difference_pairing, ht, ht', ← map_sub]
  exact dataGenerator_garding P t (slice t - other t)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! One actual source witness carries its tags, lift histories, and dimensional transfer together. -/

section
variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, NormedSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}

open scoped Classical in
theorem weakPassage_production_data (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (G G' : GenStage D hr Dm bw j₀) (hp : IsWeakPassage D P Mn rW Din G G')
    (ht : G'.HasTags P) (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) :
    ∃ (s : WeakSource G)
      (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
      (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)),
      s.Valid Mn.N Mn.R Din ∧ s.srcComp G.level = u.1 ∧ s.tgtComp G.level = v.1 ∧
      (G'.fam.identity v u γ).maxOrder = s.degree ∧
      (G'.fam.identity v u γ).record.size = (s.weakTag P G.level rW Mn.η0).size ∧
      s.IsLiftFamily Mn.sX Mn.sZ Mn.N (D.eps (G.level - 1)) Cc ∧
      (∀ (slot : ℤ) (A : RealChain), Odd slot → IsAdmissibleChain D bw j₀ G.level slot A →
        IsLiftSequence (familyLiftData (Dm := Dm) D G.level slot A
          (D.eps (G.level - 1)) (fun _ _ _ => [])) Mn.sX Mn.sZ
          (D.slotStart G.level slot / D.cellScaleSq G.level)
          ((((slot : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)
          Mn.N 0 (Cc0 slot A)) ∧
      ∀ (p : OddSlot) (c : StageCtx D bw j₀ G'.level p) (d : ℕ)
        (word : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
        p c v u γ d word t Y z =
      if IsAdmissibleChain D bw j₀ G'.level p.1 (c.1.recenter D Y) then
        s.lam G.level Mn.η0 • ∑ᶠ (slot : ℤ) (_ : Odd slot ∧ IsScheduledIn D (G.level - 1) slot p.1),
          ocCutoff D.α D.q D.Λ G.level slot t • transportedCoeff
            (fun h => (childTransition D slot t ((c.1.recenter D Y).recenter D h)
              (z + (D.eps (G.level - 1))⁻¹ • h))⁻¹) s.degree
            (fun d I => fluxCoeff
              (s.fluxOp (D.eps (G.level - 1)) Cc Cc0 slot t
                ((c.1.recenter D Y).appendChild D slot t z)) d I 0) (d - 1) word 0
      else 0 := by
  classical
  obtain ⟨_, hlevel, _, _, _, e, idx, Cc, Cc0, hlift, hzero, _, he⟩ := hp
  let s := (e v u γ).1
  have hs := (e v u γ).2
  have htags := ht v u γ
  rw [(he v u γ).1] at htags
  refine ⟨s, Cc s, Cc0, hs.1, hs.2.1, hs.2.2,
    htags.2.trans (weakSource_tag_order s P G.level rW Mn.η0), htags.1.1,
    hlift s, hzero, ?_⟩
  intro p c d word t Y z hd
  have hε : D.eps (G'.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  unfold ChartedFamily.dimFlux ChartedFamily.slowFlux
  rw [(he v u γ).2.2 p c d word t _ z hd, smul_inv_smul₀ hε]
  split_ifs with hA
  · have hden : D.kap G'.level * D.eps G'.level ^ (d - 2) =
        D.kap (G.level - 1) * D.eps (G.level - 1) ^ (d - 2) := by rw [hlevel]
    rw [hden]
    exact weak_transferAt_dimensionalization D G.level p.1 _ _ _ t _ z d word
      (weakData_kap_pos D hΛ hζ hband _).ne' (Construction.Stream.ocEpsilon_pos hΛ).ne'
  · exact smul_zero _
end

/-! Actual incoming dimensional bounds normalize without increasing the stored witness. -/

theorem actual_weak_incoming_dimensional_le (D : OCData) (hq : 1 < D.q)
    (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (m birth : ℕ) (hm : D.term ≤ m) (hb : m ≤ birth)
    (n d : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) :
    D.κ D.term * D.eps birth ^ (n - 2) * D.eps m ^ ((d : ℝ) - (n : ℝ)) ≤
      D.kap m * D.eps m ^ (d - 2) := by
  rw [weakData_kap_terminal D m hm]
  have he : 0 < D.eps m := Construction.Stream.ocEpsilon_pos (by omega)
  have hbirth : 0 ≤ D.eps birth := (Construction.Stream.ocEpsilon_pos (by omega)).le
  have hbe : D.eps birth ≤ D.eps m := EntryScales.epsilon_antitone hq hΛ hb
  have hh := weak_birth_dimensional_le (D.eps birth) (D.eps m) hbirth he hbe n d hn hd
  have hκ : 0 ≤ D.κ D.term := by
    simpa only [weakData_kap_terminal D D.term le_rfl] using
      (weakData_kap_pos D (by omega) hζ hband D.term).le
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hh hκ

/-- The genuine incoming jet budget becomes a normalized edge budget with the same stored weight. -/
theorem actual_weak_incoming_normalized_jet_bound
    {X E : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (D : OCData) (hq : 1 < D.q) (hΛ : 128 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (m birth : ℕ) (hm : D.term ≤ m) (hb : m ≤ birth)
    (n d r : ℕ) (hn : 2 ≤ n) (hd : 2 ≤ d) (f : X → E)
    (hf : ContDiff ℝ (r : ℕ∞) f) (ρ θ C : ℝ) (hθ : 0 ≤ θ) (hC : 0 ≤ C)
    (hjet : ∀ x, ρ ^ r * ‖iteratedFDeriv ℝ r f x‖ ≤
      θ * (D.κ D.term * D.eps birth ^ (n - 2) * D.eps m ^ ((d : ℝ) - (n : ℝ))) * C)
    (x : X) :
    ρ ^ r * ‖iteratedFDeriv ℝ r
      (fun y => (D.kap m * D.eps m ^ (d - 2))⁻¹ • f y) x‖ ≤ θ * C := by
  let den := D.kap m * D.eps m ^ (d - 2)
  have hden : 0 < den := mul_pos (weakData_kap_pos D (by omega) hζ hband m)
    (pow_pos (Construction.Stream.ocEpsilon_pos (by omega)) _)
  have ha := actual_weak_incoming_dimensional_le D hq hΛ hζ hband m birth hm hb n d hn hd
  have hh : ρ ^ r * ‖iteratedFDeriv ℝ r f x‖ ≤ den * (θ * C) := by
    apply (hjet x).trans
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ha hθ) hC
    convert hh using 1
    dsimp only [den]
    ring
  change ρ ^ r * ‖iteratedFDeriv ℝ r (fun y => den⁻¹ • f y) x‖ ≤ θ * C
  rw [iteratedFDeriv_const_smul_apply' hf.contDiffAt, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr hden)]
  calc
    _ = den⁻¹ * (ρ ^ r * ‖iteratedFDeriv ℝ r f x‖) := by ring
    _ ≤ den⁻¹ * (den * (θ * C)) := mul_le_mul_of_nonneg_left hh (inv_pos.mpr hden).le
    _ = θ * C := by rw [← mul_assoc, inv_mul_cancel₀ hden.ne', one_mul]

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Homogeneous molecular energy decay for every centered Hilbert trace. -/

theorem dataGeneratorForm_eq_diffusion_sub_drift (P : MolecularData) (t : ℝ) :
    dataGeneratorForm P t = molecularDiffusionForm P.G t -
      cellDriftForm P.v P.V P.drift_measurable P.drift_bounded t := rfl

theorem dataGeneratorForm_centered_gap (P : MolecularData) (hv : IsCellDrift P.v)
    (t : ℝ) (u : TorusHk 1 ℂ) (hm : cellMean (torusHkValueCLM u) = 0) :
    dataGeneratorForm P t u u + 3 * Real.pi ^ 2 * ‖torusHkValueCLM u‖ ^ 2 ≤ 0 := by
  have hd := molecularDiffusionForm_meanZero_gap P.G P.metric_coercive t u hm
  have hz := cellDriftForm_energy_zero hv P.V P.drift_bounded t u
  rw [dataGeneratorForm_eq_diffusion_sub_drift, sub_apply, sub_apply]
  rw [show cellDriftForm P.v P.V P.drift_measurable P.drift_bounded t u u = 0 from hz]
  linarith

theorem dataWeak_homogeneous_decay {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (hv : IsCellDrift P.v)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice
      (fun t => dataDualDerivative P t (slice t) 0 (fun _ => 0)))
    (hm : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (torusHkValueCLM (slice t)) = 0) :
    ∀ t ∈ Icc a b,
      ‖u t‖ ^ 2 ≤ Real.exp (-(6 * Real.pi ^ 2) * (t - a)) * ‖u a‖ ^ 2 := by
  apply (h.energy_strongTime hab).scalar_decay hab (6 * Real.pi ^ 2)
  filter_upwards [h.agrees, hm] with t ht hmt
  have hg := dataGeneratorForm_centered_gap P hv t (slice t) hmt
  rw [ht, dataDualDerivative_pairing]
  simp only [cellSourceFunctional, sub_apply, sum_apply, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, inner_zero_left, Finset.sum_const_zero, sub_self, add_zero]
  linarith

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Literal ordered corrections are componentwise left application to the normalized slow mean. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

def normalizedLiftCompositionComponentReserve (H j : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (p q degree : ℕ) (A : Vec 2 →L[ℝ] ℝ) (v : ι)
    (Qc : ∀ m : Fin (j + 1), ∀ α : DerivativeWord2 m.val, ∀ u,
      JointSourceReserve H (fun t z Y => Cc p j m.val α t Y z v u 1))
    (QA : ∀ u, JointSourceReserve (H + j)
      (fun t z Y => normalizedLiftASource Q Cc f q degree A t z Y u)) :
    JointSourceReserve H (fun t z Y => (Real.exp (A Y))⁻¹ •
      liftApply j (Cc p j) (liftMean Q Cc f q degree) t Y z v) := by
  let F := fun t Y => (Real.exp (A Y))⁻¹ • liftMean Q Cc f q degree t Y
  let QM := fun u => normalizedLiftMeanComponentReserve (H + j) Q Cc f q degree A u QA
  have he : (fun t Y => Real.exp (A Y) • F t Y) = liftMean Q Cc f q degree := by
    funext t Y
    simp only [F, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  have hf : normalizedLiftApplySource j (Cc p j) A F v =
      fun t z Y => (Real.exp (A Y))⁻¹ •
        liftApply j (Cc p j) (liftMean Q Cc f q degree) t Y z v := by
    unfold normalizedLiftApplySource
    rw [he]
  exact (normalizedLiftApplyComponentReserve H j (Cc p j) A F v Qc QM).congrSource hf

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Arbitrary public cell solutions satisfy the actual Hilbert fixed-test time equation. -/

/-- The public complex bilinear identity yields every real Hilbert H¹ test increment. -/
theorem dataSolution_Hilbert_increment {a b : ℝ}
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) (dataCoefficients P) src F D)
    (s : ℝ) (hs : s ∈ Icc a b) (t : ℝ) (ht : t ∈ Icc a b) (hst : s ≤ t)
    (z : TorusHk 1 ℂ) :
    inner ℝ (cellRawTrace D t) (torusHkValueCLM z) -
      inner ℝ (cellRawTrace D s) (torusHkValueCLM z) =
        ∫ r in s..t, inner ℝ (dataRawSolutionDual P src F D r) z := by
  let ψ := cellHilbertTest z
  let R := fun r => cellLiteralRHS (dataCoefficients P) r (cellValue D r) (cellGradComp (D r))
    (ψ.jet (valueIndex2 1)) (fun j => ψ.jet ⟨⟨1, by decide⟩, fun _ => j⟩) (src r) (F r)
  have hid := h.2.2.2.2.2.2 s hs t ht hst ψ
  change Integrable (fun x => cellValue D t x * ψ.jet (valueIndex2 1) x) _ ∧
    Integrable (fun x => cellValue D s x * ψ.jet (valueIndex2 1) x) _ ∧
    (∀ᵐ r ∂volume.restrict (Ioc s t), Integrable (R r) _) ∧
    Integrable (fun r => ∫ x in AVenhance.unitCube, R r x) (volume.restrict (Ioc s t)) ∧
    (∫ x in AVenhance.unitCube, cellValue D t x * ψ.jet (valueIndex2 1) x) -
      (∫ x in AVenhance.unitCube, cellValue D s x * ψ.jet (valueIndex2 1) x) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x at hid
  have hsub : Ioc s t ⊆ Icc a b := Ioc_subset_Icc_self.trans (Icc_subset_Icc hs.1 ht.2)
  have hFlux (j : Fin 2) := cellSource_memLp_slices (Icc a b) (fun r x => F r x j)
    ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hF)
  have he : (fun r => ∫ x in AVenhance.unitCube, R r x) =ᵐ[volume.restrict (Ioc s t)]
      fun r => cellDualComplexPair (dataRawSolutionDual P src F D r) z := by
    have hj := (cellSolution_slice_ae h).filter_mono (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hS := (cellSource_memLp_slices (Icc a b) src hsrc).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    have hQ := (ae_all_iff.mpr hFlux).filter_mono
      (ae_mono (Measure.restrict_mono hsub le_rfl))
    filter_upwards [hj, hS, hQ] with r hr hsr hfr
    have heq := (dataRawSpatial_equation P r (cellH1Slice D r) (D r) hr ψ
      (cellSourceSlice src r) (fun j => cellSourceSlice (fun t x => F t x j) r)
      (src r) (F r) (cellSourceSlice_ae src r hsr)
      (fun j => cellSourceSlice_ae (fun t x => F t x j) r (hfr j))).2
    change (∫ x in AVenhance.unitCube, R r x) =
      cellDualComplexPair (dataRawSolutionDual P src F D r) (cellRawTest ψ) at heq
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at heq
    exact heq
  have hp (r : ℝ) (hr : r ∈ Icc a b) := cellRawTest_pairing_integral ψ (cellRawTrace D r)
    (cellValue D r) (cellRawTrace_ae D r (h.2.2.1 r hr).1)
  have hinc : cellComplexPair (cellRawTrace D t) (torusHkValueCLM z) -
      cellComplexPair (cellRawTrace D s) (torusHkValueCLM z) =
        ∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x := by
    have hpt := hp t ht
    have hps := hp s hs
    rw [show cellRawTest ψ = z from cellHilbertTest_inverse z] at hpt hps
    rw [hpt, hps]
    exact hid.2.2.2.2
  have hre := congrArg Complex.re hinc
  simp only [Complex.sub_re, cellComplexPair_re] at hre
  have hmap := Complex.reCLM.integral_comp_comm hid.2.2.2.1
  change (∫ r in Ioc s t, (∫ x in AVenhance.unitCube, R r x).re) =
    (∫ r in Ioc s t, ∫ x in AVenhance.unitCube, R r x).re at hmap
  rw [← hmap] at hre
  rw [intervalIntegral.integral_of_le hst]
  have hreal : (fun r => (∫ x in AVenhance.unitCube, R r x).re) =ᵐ[
      volume.restrict (Ioc s t)] fun r => inner ℝ (dataRawSolutionDual P src F D r) z :=
    he.mono (fun r hr => (congrArg Complex.re hr).trans (cellDualComplexPair_re _ _))
  exact hre.trans (integral_congr_ae hreal)

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Every public raw cell solution satisfies the actual Hilbert variational equation. -/

/-- The public raw solution predicate discharges every premise of the weak Hilbert energy calculus. -/
theorem dataSolution_to_Hilbert {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData)
    (src : ℝ → Vec 2 → ℂ) (F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (D : ℝ → RawJet2 1 ℂ) (h : IsCellSolution (Icc a b) (dataCoefficients P) src F D) :
    CellWeakHilbertCurve a b (cellRawTrace D) (cellH1Slice D)
      (dataRawSolutionDual P src F D) :=
  ⟨IsCellSolution.trace_continuous h, cellSolution_slice_memLp hab h,
    dataSolution_dual_memLp hab P src F hsrc hF D h,
    cellSolution_trace_agrees h,
    dataSolution_Hilbert_increment P src F hsrc hF D h⟩

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
open scoped Classical
namespace AVRegularity.EntryWeakProofs

/-! Finite exponential tests recover genuine reserves for the actual symmetric scalar coefficients. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem jointSourceReserve_scalar_coefficient_calibration
    (H n m : ℕ) (hm : m ≤ n) (c : LiftCoeff ι (fun _ => ℝ))
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0) (v u : ι)
    (Q : ∀ p : Fin (m + 1) × Fin (n + 1), JointSourceReserve H
      (fun t z Y => normalizedLiftTestField c n
        (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v 1 t Y z)) :
    ∃ R : JointSourceReserve H (fun t z Y => c m α t Y z v u 1),
      ∀ r, R.budget r = ∑ p : Fin (m + 1) × Fin (n + 1),
        ‖liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ‖ * (Q p).budget r := by
  let L := fun p : Fin (m + 1) × Fin (n + 1) =>
    liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ
  let F := fun p t z Y => L p (normalizedLiftTestField c n
    (lam • ((p.2 : ℝ) • coordinateSymbolDirection (p.1 : ℝ))) u v 1 t Y z)
  have he : (fun t z Y => ∑ p : Fin (m + 1) × Fin (n + 1), F p t z Y) =
      (fun t z Y => c m α t Y z v u 1) := by
    funext t z Y
    exact liftCalibration_synthesis n m hm c lam hlam hc α t Y z v u 1
  obtain ⟨R, hR⟩ := jointSourceReserve_sum_with_budget Finset.univ H F (fun p => (Q p).map (L p))
  refine ⟨R.congrSource he, ?_⟩
  intro r
  rw [JointSourceReserve.congrSource_budget]
  exact hR r

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! The literal passage readout commutes with slow recentering on its admissible carrier. -/

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G G' : GenStage D (fun _ => ℝ) Dm bw j₀}

theorem weakPassage_dimFlux_recenter
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (P : ProvParams) (Mn : WeakMenu) (rW : ℝ) (Din : ℕ)
    (hp : IsWeakPassage D P Mn rW Din G G') (ht : G'.HasTags P)
    (v u : CompIn G'.comps) (γ : G'.fam.Γ v u) (p : OddSlot)
    (c : StageCtx D bw j₀ G'.level p) (h : Vec 2)
    (hc : IsAdmissibleChain D bw j₀ G'.level p.1 (c.1.recenter D h))
    (d : ℕ) (hd : 2 ≤ d) (word : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2) :
    G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
      p c v u γ d word t (h + Y) z =
    G'.fam.dimFlux (D.kap G'.level) (D.eps G'.level) (D.eps (G'.level - 1))
      p ⟨c.1.recenter D h, hc⟩ v u γ d word t Y z := by
  obtain ⟨s, Cc, Cc0, _, _, _, _, _, _, _, hf⟩ :=
    weakPassage_production_data hΛ hζ hband P Mn rW Din G G' hp ht v u γ
  rw [hf p c d word t (h + Y) z hd, hf p ⟨c.1.recenter D h, hc⟩ d word t Y z hd]
  dsimp only
  simp only [Providers.GenSem.recenter_recenter D hζ, add_assoc]
  rw [Providers.GenSem.recenter_recenter D hζ c.1 h Y]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Energy continuity and uniform higher carriers produce joint parameter/cell continuity. -/

variable {P : Type*} [TopologicalSpace P]

theorem independent_classical_fast_jet_joint_continuous (K n : ℕ) (hn : n + 4 ≤ K)
    (c : P → ℝ → RawJet2 1 ℂ)
    (hc : ∀ Y, Tendsto (fun X => cellEnergyNorm Set.univ (c X - c Y)) (𝓝 Y) (𝓝 0))
    (u : P → TorusHk K ℂ) (t : ℝ)
    (he : ∀ Y, torusHkValueCLM (u Y) =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (c Y) t)
    (R : ℝ) (hb : ∀ Y, ‖u Y‖ ≤ R) :
    Continuous (fun X : P × Vec 2 => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (u X.1))) X.2) := by
  apply joint_continuous_of_uniform_slice_variation
    (fun Y z => iteratedFDeriv ℝ n
      (realClassicalLift K (mapTorusHk Complex.reCLM (u Y))) z)
    (fun z => independent_classical_fast_jet_continuous K n hn c hc u t he R hb z)
    (cellClassicalSobolevConstant K (n + 1) * R)
  intro Y z x
  have hs := realHigherCarrier_fast_jet_lipschitz K n (by omega) (u Y) z x
  exact hs.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left (hb Y) (cellClassicalSobolevConstant_nonneg K (n + 1)))
    (norm_nonneg _))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift Set
namespace AVRegularity.EntryWeakProofs

/-! Finite calibration of genuine local test extensions produces actual coefficient extensions. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def finiteScalarCalibrationBudget (n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ)
    (B : Fin (m + 1) × Fin (n + 1) → ℝ) : ℝ :=
  ∑ p, ‖liftCalibrationWeight n m α lam p • ContinuousLinearMap.id ℝ ℝ‖ * B p

theorem finiteScalarCalibrationBudget_nonneg (n m : ℕ) (α : DerivativeWord2 m) (lam : ℝ)
    (B : Fin (m + 1) × Fin (n + 1) → ℝ) (hB : ∀ p, 0 ≤ B p) :
    0 ≤ finiteScalarCalibrationBudget n m α lam B :=
  Finset.sum_nonneg fun p _ => mul_nonneg (norm_nonneg _) (hB p)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Produced inherited and Eddy means have exactly the original source readout and stored size. -/

variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {G : GenStage D (fun _ => ℝ) Dm bw j₀}

def weakSourceMeanWeight (P : ProvParams) (s : WeakSource G) : ℝ :=
  match s with
  | .inherited _ _ π _ => (π.provList.map (fun y => (y.2.2.tags P).witness)).prod
  | .eddy .. => D.weakPe G.level ^ 2

theorem weakSourceMeanWeight_nonneg (P : ProvParams) (ht : G.HasTags P) (s : WeakSource G) :
    0 ≤ weakSourceMeanWeight P s := by
  cases s with
  | inherited w h π n =>
    have he := stagePathStoredMatrix_endpoint G P ht π
    change finiteMatrixPower (weightedPathMatrix h (stagePathStoredWeight G π)) h (Fin.last h) 0 = _ at he
    change 0 ≤ (π.provList.map (fun y => (y.2.2.tags P).witness)).prod
    rw [← he]
    exact finiteMatrixPower_nonneg _ (stagePathStoredMatrix_nonneg G π) _ _ _
  | eddy v w n => exact sq_nonneg _

theorem weakSource_lam_nonneg (hΛ : 1 ≤ D.Λ) (η : ℝ) (s : WeakSource G) :
    0 ≤ s.lam G.level η := by
  cases s with
  | inherited => exact zero_le_one
  | eddy => exact (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ) _).le

theorem weakSource_tag_size_meanWeight (P : ProvParams) (rW η : ℝ) (s : WeakSource G) :
    (s.weakTag P G.level rW η).size = s.lam G.level η * weakSourceMeanWeight P s := by
  cases s with
  | inherited => exact (one_mul _).symm
  | eddy => rfl

theorem weakSource_inherited_native_readout
    (w : List WordLetter) (h : ℕ) (π : StagePath G h) (n : ℕ) (ρ : ℝ)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (p : OddSlot) (A : StageCtx D bw j₀ G.level p) (t : ℝ) :
    (WeakSource.inherited w h π n).fluxOp ρ Cc Cc0 p.1 t A.1 =
      pathMeanFlux D G.level ρ
        (familyLiftData D G.level p.1 A.1 ρ (pathEdges G π p A)) (Cc p.1 A.1) n t := by
  have hA : IsAdmissibleChain D bw j₀ G.level p.1 A.1 ∧ Odd p.1 := ⟨A.2, p.2⟩
  simp only [WeakSource.fluxOp, dite_eq_left hA]

theorem weakSource_eddy_native_readout
    (v : CompIn G.comps) (w : List WordLetter) (n : ℕ) (ρ : ℝ)
    (Cc Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (p : OddSlot) (A : StageCtx D bw j₀ G.level p) (t : ℝ) :
    (WeakSource.eddy v w n).fluxOp ρ Cc Cc0 p.1 t A.1 =
      weakEddyFlux D G.level ρ
        (familyLiftData (Dm := Dm) D G.level p.1 A.1 ρ (fun _ _ _ => [])) (Cc0 p.1 A.1) n t := by
  have hA : IsAdmissibleChain D bw j₀ G.level p.1 A.1 ∧ Odd p.1 := ⟨A.2, p.2⟩
  simp only [WeakSource.fluxOp, dite_eq_left hA]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs

/-! Produced higher word states uniformly bound every genuine metric perturbation source. -/

variable {I Y : Type*}

theorem uniform_word_perturbed_higher_source_exists (a b : ℝ) (N K : ℕ)
    (A : Y → List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (E : Y → List I → ℝ → RawJet2 1 ℂ)
    (C : Y → CellCoefficients)
    (f : Y → List I → ℝ → Vec 2 → ℂ)
    (F : Y → List I → ℝ → Vec 2 → ComplexCellVector)
    (hE : ∀ y w, w.length ≤ N → IsCellInverseValue (C y) (f y w) (F y w) (E y w))
    (B : List I → ℝ) (hB : ∀ w, w.length ≤ N → 0 ≤ B w)
    (hb : ∀ y w, w.length ≤ N → ∀ t i j, |A y w t i j| ≤ B w)
    (hm : ∀ y w, w.length ≤ N → ∀ i j, Measurable (fun t => A y w t i j))
    (w : List I) (hw : w.length ≤ N)
    (hcarrier : ∀ u : List I, u.length ≤ w.length →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ v : ℝ → TorusHk (K + 1) ℂ,
        StronglyMeasurable v ∧ (∀ t, ‖v t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (v t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (E y u) t)
    (src : Y → ℝ → Vec 2 → ℂ) (flux : Y → ℝ → Vec 2 → ComplexCellVector)
    (Q : ∀ y, HigherSourceCarrierData (Icc a b) K (src y) (flux y))
    (Ns Nf : ℝ) (hNs : 0 ≤ Ns) (hNf : 0 ≤ Nf)
    (hQs : ∀ y, (Q y).Ns ≤ Ns) (hQf : ∀ y, (Q y).Nf ≤ Nf) :
    ∃ Rs Rf : ℝ, 0 ≤ Rs ∧ 0 ≤ Rf ∧ ∀ y,
      ∃ Qnext : HigherSourceCarrierData (Icc a b) K (src y)
        ((flux y + independentWordMetricFlux (fun p t _ => A y p t) (E y) w) +
          cellMetricFlux (fun t _ => A y [] t) (E y w)), Qnext.Ns ≤ Rs ∧ Qnext.Nf ≤ Rf := by
  classical
  have hall (u : List I) : ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ v : ℝ → TorusHk (K + 1) ℂ,
      StronglyMeasurable v ∧ (∀ t, ‖v t‖ ≤ R) ∧
      (u.length ≤ w.length → ∀ t ∈ Icc a b,
        torusHkValueCLM (v t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (E y u) t) := by
    by_cases hu : u.length ≤ w.length
    · obtain ⟨R, hR, hh⟩ := hcarrier u hu
      refine ⟨R, hR, fun y => ?_⟩
      obtain ⟨v, hvm, hvb, hve⟩ := hh y
      exact ⟨v, hvm, hvb, fun _ => hve⟩
    · exact ⟨0, le_rfl, fun _ => ⟨0, stronglyMeasurable_const,
        (fun _ => by simp), fun h => (hu h).elim⟩⟩
  choose R hR v hvm hvb hve using hall
  let r := ((independentWordForcing w).map
    (fun p => B p.1 * metricGradientCarrierConstant K * R p.2)).sum
  have hr : 0 ≤ r := by
    apply List.sum_nonneg
    intro x hx
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
    have hl := independentWordForcing_lengths w p hp
    exact mul_nonneg (mul_nonneg (hB p.1 (by omega)) (metricGradientCarrierConstant_nonneg K)) (hR p.2)
  let Rf := (Nf + r) + B [] * metricGradientCarrierConstant K * R w
  have hRf : 0 ≤ Rf := add_nonneg (add_nonneg hNf hr)
    (mul_nonneg (mul_nonneg (hB [] (by simp)) (metricGradientCarrierConstant_nonneg K)) (hR w))
  refine ⟨Ns, Rf, hNs, hRf, fun y => ?_⟩
  have hAfin u hu := bounded_matrix_field_admissible (A y u) (B u) (hb y u hu) (hm y u hu)
  have hM u hu := inverse_metric_flux_memLp_window (fun t _ => A y u t)
    (hAfin u hu).1 (hAfin u hu).2 (hE y u hu) a b
  have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
  obtain ⟨Qt, hts, htf⟩ := (Q y).metricFluxList_exists (independentWordForcing w)
    (fun p => A y p.1) (fun p => E y p.2) (fun p => v p.2 y)
    (fun p => B p.1) (fun p => R p.2)
    (fun p hp => hB p.1 (by have hh := hl p hp; omega)) (fun p _ => hR p.2)
    (fun p hp => hm y p.1 (by have hh := hl p hp; omega))
    (fun p hp => hb y p.1 (by have hh := hl p hp; omega))
    (fun p _ => hvm p.2 y) (fun p _ => hvb p.2 y)
    (fun p hp => ae_mono (Measure.restrict_mono (subset_univ _) le_rfl)
      (hE y p.2 (by have hh := hl p hp; omega)).1.2.1)
    (fun p hp => ae_restrict_of_forall_mem measurableSet_Icc (hve p.2 y (by have hh := hl p hp; omega)))
    (fun p hp => inverse_metric_flux_memLp_window (fun t _ => A y p.1 t)
      (hAfin p.1 (by have hh := hl p hp; omega)).1
      (hAfin p.1 (by have hh := hl p hp; omega)).2
      (hE y p.2 (by have hh := hl p hp; omega)) a b)
  let Qnext := Qt.withMetricFlux (A y []) (E y w) (v w y) (B []) (R w)
    (hB [] (by simp)) (hR w) (hm y [] (by simp)) (hb y [] (by simp))
    (hvm w y) (hvb w y)
    (ae_mono (Measure.restrict_mono (subset_univ _) le_rfl) (hE y w hw).1.2.1)
    (ae_restrict_of_forall_mem measurableSet_Icc (hve w y le_rfl))
    (inverse_metric_flux_memLp_window (fun t _ => A y [] t) (hAfin [] (by simp)).1
      (hAfin [] (by simp)).2 (hE y w hw) a b)
  refine ⟨Qnext, ?_, ?_⟩
  · change Qt.Ns ≤ Ns
    rw [hts]
    exact hQs y
  · change Qt.Nf + B [] * metricGradientCarrierConstant K * R w ≤ Rf
    rw [htf]
    exact add_le_add (add_le_add (hQf y) (le_refl r)) (le_refl _)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! Exact exponential normalization of the literal slow flux, including its inherited Taylor sum. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

theorem normalizedLiftTestField_exp_cancel (c : LiftCoeff ι (fun _ => ℝ))
    (n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (u : ι) (t : ℝ) :
    (fun X z => Real.exp (A X) •
      (fun v => normalizedLiftTestField c n A u v 1 t X z)) =
    liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u (1 : ℝ)) t := by
  funext X z v
  change Real.exp (A X) • ((Real.exp (A X))⁻¹ • (_ : ℝ)) = _
  rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]

theorem normalizedLiftFluxX_decomposition (H : ℕ)
    (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (A : Vec 2 →L[ℝ] ℝ)
    (hh n : ℕ) (hn : 2 ≤ n) (hhpos : hh ≠ 0) (u v : ι) (k : Fin 2)
    (Q₁ : ∀ w, JointSourceReserve (H + 1)
      (fun t z Y => normalizedLiftTestField (Cc hh (n - 1)) (n - 1) A u w 1 t Y z))
    (Q₂ : ∀ w, JointSourceReserve (H + 1)
      (fun t z Y => normalizedLiftTestField (Cc hh (n - 2)) (n - 2) A u w 1 t Y z))
    (t : ℝ) (z Y : Vec 2) :
    (Real.exp (A Y))⁻¹ •
      (liftFluxX Q Cc (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) hh n t Y z k) v =
    normalizedLiftFluxCrossSource A Q.η Q.G Q.v
      (fun t z Y => normalizedLiftTestField (Cc hh (n - 1)) (n - 1) A u v 1 t Y z)
      (fun t z Y => normalizedLiftTestField (Cc hh (n - 2)) (n - 2) A u v 1 t Y z)
      k t z Y -
    Real.sqrt Q.η • ∑ j ∈ Finset.Icc 1 (min D n),
      (Real.exp (A Y))⁻¹ •
        ((((j - 1).factorial : ℝ)⁻¹) • iteratedDeriv (j - 1)
          (fun ε => sourceFlux Q.edge Q.η ε t
            (liftApply (n - j) (Cc (hh - 1) (n - j))
              (fun _ X => Real.exp (A X) • Pi.single u (1 : ℝ)) t) k Y z) 0) v := by
  have hc := normalizedLiftFluxCrossSource_component H A Q.η Q.G Q.v
    (fun t z Y w => normalizedLiftTestField (Cc hh (n - 1)) (n - 1) A u w 1 t Y z)
    (fun t z Y w => normalizedLiftTestField (Cc hh (n - 2)) (n - 2) A u w 1 t Y z)
    Q₁ Q₂ k t z Y v
  rw [normalizedLiftTestField_exp_cancel, normalizedLiftTestField_exp_cancel] at hc
  have hd := congrFun (congrFun (congrFun
    (normalizedLiftTestField_exp_cancel (Cc hh (n - 1)) (n - 1) A u t) Y) z) v
  simp only [Pi.sub_apply, Pi.smul_apply] at hc hd
  rw [hd] at hc
  rw [hc]
  simp only [liftFluxX, ite_eq_left hn, ite_eq_right hhpos, Pi.sub_apply, Pi.add_apply,
    Pi.neg_apply, Pi.smul_apply, Finset.sum_apply, smul_add, smul_neg,
    sub_eq_add_neg, Finset.smul_sum, smul_smul]
  simp only [smul_eq_mul, mul_comm, mul_left_comm, mul_assoc]

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Each scalar lift source uses its own lower-degree and inherited-source reserves. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {D : ℕ}

omit [DecidableEq ι] in
theorem normalized_lift_a_component_decomposition (H : ℕ) (Q : LiftOperatorData ι (fun _ => ℝ) D)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (f : ℝ → Vec 2 → ι → ℝ)
    (hh n : ℕ) (A : Vec 2 →L[ℝ] ℝ) (v : ι)
    (QG : ∀ i j, JointSourceReserve (H + 1) (fun t _ Y => Q.G t Y i j))
    (Q1 : ∀ u, JointSourceReserve (H + 2) (fun t z Y => (Real.exp (A Y))⁻¹ •
      liftApply (n - 1) (Cc hh (n - 1)) f t Y z u))
    (Q2 : 2 ≤ n → ∀ u, JointSourceReserve (H + 2) (fun t z Y => (Real.exp (A Y))⁻¹ •
      liftApply (n - 2) (Cc hh (n - 2)) f t Y z u))
    (t : ℝ) (z Y : Vec 2) :
    normalizedLiftASource Q Cc f hh n A t z Y v =
      normalizedCellB1Source A Q.η Q.G Q.v
        (fun t z Y => (Real.exp (A Y))⁻¹ • liftApply (n - 1) (Cc hh (n - 1)) f t Y z v) t z Y +
      (if 2 ≤ n then normalizedCellB2Source A Q.η Q.G
        (fun t z Y => (Real.exp (A Y))⁻¹ • liftApply (n - 2) (Cc hh (n - 2)) f t Y z v) t z Y else 0) -
      (if hh = 0 then 0 else ∑ j ∈ Finset.range (min D n + 1), (Real.exp (A Y))⁻¹ •
        sourceCoeff Q.edge Q.η j t (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) Y z v) := by
  let F := fun d t z Y => (Real.exp (A Y))⁻¹ • liftApply d (Cc hh d) f t Y z
  have he (d : ℕ) (t : ℝ) : liftApply d (Cc hh d) f t =
      fun X y => Real.exp (A X) • F d t y X := by
    funext X y
    simp only [F, smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]
  let B1 := normalizedCellB1Source A Q.η Q.G Q.v (fun t z Y => F (n - 1) t z Y v)
  let B2 := fun t z Y => if 2 ≤ n then
    normalizedCellB2Source A Q.η Q.G (fun t z Y => F (n - 2) t z Y v) t z Y else 0
  let S := fun t z Y => if hh = 0 then 0 else
    ∑ j ∈ Finset.range (min D n + 1), (Real.exp (A Y))⁻¹ •
      sourceCoeff Q.edge Q.η j t
        (liftApply (n - j) (Cc (hh - 1) (n - j)) f t) Y z v
  have hfield : (fun t z Y => normalizedLiftASource Q Cc f hh n A t z Y v) =
      fun t z Y => B1 t z Y + B2 t z Y - S t z Y := by
    funext t z Y
    unfold normalizedLiftASource liftA
    rw [he (n - 1) t, he (n - 2) t]
    simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply, smul_sub, smul_add, B1, B2, S]
    rw [normalizedCellB1Source_component H A Q.η Q.G Q.v (F (n - 1)) QG Q1 t z Y v]
    by_cases hn : 2 ≤ n
    · simp only [ite_eq_left hn]
      rw [normalizedCellB2Source_component H A Q.η Q.G (F (n - 2)) QG (Q2 hn) t z Y v]
      by_cases hhh : hh = 0
      · simp only [ite_eq_left hhh, Pi.zero_apply, smul_zero,
          normalizedCellB1Source, normalizedCellB2Source, Pi.smul_apply]
      · simp only [ite_eq_right hhh, Finset.sum_apply, Finset.smul_sum,
          normalizedCellB1Source, normalizedCellB2Source, Pi.smul_apply]
    · simp only [ite_eq_right hn]
      by_cases hhh : hh = 0
      · simp only [ite_eq_left hhh, Pi.zero_apply, smul_zero,
          normalizedCellB1Source, Pi.smul_apply]
      · simp only [ite_eq_right hhh, Finset.sum_apply, Finset.smul_sum,
          Pi.zero_apply, smul_zero, normalizedCellB1Source, Pi.smul_apply]
  exact congrFun (congrFun (congrFun hfield t) z) Y

end AVRegularity.EntryWeakProofs
end
