-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.MolecularUlFluxNormBound
public import AVRegularity.EntryWeak.NormalizedLiftAComponentDecomposition
import AVRegularity.CycleDamping.ReferenceSourceMode
public import AVRegularity.EntryWeak.FluxProductionArithmetic
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit

section
section
/-! Literal triangular difference equations for spatially constant weak cell metrics. -/
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs
variable {I : Type*}

theorem independent_word_difference_time_inverse_value
    (P : MolecularData) (G H : List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hP : dataCoefficients P = ⟨fun t _ => G [] t, P.v, 0, 0⟩)
    (f g : List I → ℝ → Vec 2 → ℂ)
    (F F' : List I → ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ))
    (D E : List I → ℝ → RawJet2 1 ℂ) (α : List I) (r : ℝ)
    (hGsym : ∀ t, (G [] t).IsSymm) (hHsym : ∀ t, (H [] t).IsSymm)
    (hD : IsCellInverseValue (dataCoefficients P) (f α)
      (F α + independentWordMetricFlux (fun β t _ => G β t) D α) (D α))
    (hE : IsCellInverseValue ⟨fun t _ => H [] t, P.v, 0, 0⟩ (g α)
      (F' α + independentWordMetricFlux (fun β t _ => H β t) E α) (E α)) :
    IsCellInverseValue (dataCoefficients P) (r • (g α - f α))
      (((r • (F' α - F α) +
        independentWordMetricFlux (fun β t _ => r • (H β t - G β t)) E α) +
        cellMetricFlux (fun t _ => r • (H [] t - G [] t)) (E α)) +
          independentWordMetricFlux (fun β t _ => G β t) (fun β => r • (E β - D β)) α)
      (r • (E α - D α)) := by
  have hd : IsCellInverseValue ⟨fun t _ => G [] t, P.v, 0, 0⟩ (f α)
      (F α + independentWordMetricFlux (fun β t _ => G β t) D α) (D α) := hP ▸ hD
  have hc := independent_word_difference_inverse_value (fun β t _ => G β t)
    (fun β t _ => H β t) P.v f g F F' D E α r
    (fun t _ => hGsym t) (fun t _ => hHsym t) hd hE
  rw [hP]
  exact hc

end AVRegularity.EntryWeakProofs
end
end

section
/-! A literal linear readout of an actual inverse agrees with the produced scalar inverse without a fast reserve premise. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.EntryWeakProofs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem dataActual_inverse_canonical_eq_functional {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (src : ℝ → Vec 2 → ℂ)
    (D : ℝ → RawJet2 1 ℂ) (hD : IsCellSolution univ (dataCoefficients P) src 0 D)
    (g c : ℝ → Vec 2 → E) (ℓ : E →L[ℝ] ℝ)
    (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      src t =ᵐ[volume.restrict AVenhance.unitCube] fun z => (ℓ (g t z) : ℂ))
    (hg : MemLp (Function.uncurry (fun t z => (ℓ (g t z) : ℂ))) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (r : ℕ) (hc : IsCellFieldInverse P.G P.v r a b 0 g c)
    (K : ℕ) (hK : 2 ≤ K) (w : ℝ → TorusHk K ℂ)
    (hw : ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue D t) :
    ∀ t ∈ Icc a b, realCellClassicalReadout (cellRawTrace D t) = fun z => ℓ (c t z) := by
  have hd := cellSolution_source_congr_sections (Icc a b) (dataCoefficients P) src
    (fun t z => (ℓ (g t z) : ℂ)) 0 0 D hs
    (Filter.Eventually.of_forall fun _ => Filter.EventuallyEq.rfl)
    (cellSolution_restrict (subset_univ _) ordConnected_Icc hD)
  have hh := hc.2 ℓ
  have ha : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] cellValue (cellJetOfField ℓ c) a :=
    hi.trans (by
      have hz : (fun x : Vec 2 => (ℓ ((0 : Vec 2 → E) x) : ℂ)) = 0 := by
        funext x
        simp
      rw [hz] at hh
      exact hh.2.2.1.symm)
  have he := dataActual_unique_raw hab P (fun t z => (ℓ (g t z) : ℂ)) 0 hg MemLp.zero
    D (cellJetOfField ℓ c) hd hh.1 ha
  intro t ht
  apply realCellRawReadout_eq_periodic_field K hK D t (w t)
    (hD.2.2.1 t (mem_univ _)).1 (hw t ht) (fun z => ℓ (c t z))
    (ℓ.continuous.comp (hc.1 t ht).continuous) _ (he t ht)
  intro n z
  exact Complex.ofReal_injective ((hh.1.2.2.1 t ht).2 n z)

end AVRegularity.EntryWeakProofs
end
end

section
/-! A zero forcing component has zero actual response even when the inverse has fast order zero. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem dataActual_inverse_zero_functional {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (g c : ℝ → Vec 2 → E) (ℓ : E →L[ℝ] ℝ) (r : ℕ)
    (hc : IsCellFieldInverse P.G P.v r a b 0 g c)
    (hg : ∀ t ∈ Icc a b, ∀ z, ℓ (g t z) = 0) :
    ∀ t ∈ Icc a b, ∀ z, ℓ (c t z) = 0 := by
  have hh := hc.2 ℓ
  have hs : IsCellSolution (Icc a b) (dataCoefficients P) (fun _ _ => 0) 0
      (cellJetOfField ℓ c) := by
    apply cellSolution_source_congr_sections (Icc a b) (dataCoefficients P)
      (fun t z => (ℓ (g t z) : ℂ)) (fun _ _ => 0) 0 0 (cellJetOfField ℓ c)
      ?_ (Filter.Eventually.of_forall fun _ => Filter.EventuallyEq.rfl) hh.1
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact Filter.Eventually.of_forall fun z => by
      change (ℓ (g t z) : ℂ) = 0
      rw [hg t ht z, Complex.ofReal_zero]
  have hz : IsCellSolution (Icc a b) (dataCoefficients P) (fun _ _ => 0) 0
      (0 : ℝ → RawJet2 1 ℂ) := by
    simpa only [zero_smul] using! cellSolution_complex_smul hs (0 : ℂ)
  have hi : cellValue (cellJetOfField ℓ c) a =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (0 : ℝ → RawJet2 1 ℂ) a := by
    simpa only [Pi.zero_apply, map_zero, Complex.ofReal_zero] using! hh.2.2.1
  have he := dataActual_unique_raw hab P (fun _ _ => 0) 0 MemLp.zero MemLp.zero
    (cellJetOfField ℓ c) 0 hs hz hi
  intro t ht z
  have hae : (fun z => (ℓ (c t z) : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube] 0 := he t ht
  have hpoint := periodicContinuous_zero_of_cell_ae _
    (Complex.ofRealCLM.continuous.comp (ℓ.continuous.comp (hc.1 t ht).continuous))
    ((hs.2.2.1 t ht).2) hae
  exact Complex.ofReal_injective (by simpa using! congrFun hpoint z)

end AVRegularity.EntryWeakProofs
end
end

section
/-! Regular scalar data retain high spatial regularity and reality at every closed time. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE

namespace AVRegularity.EntryWeakProofs

theorem dataRegular_exists_trace {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (g : ℝ → Vec 2 → ℝ) (hm : Measurable (Function.uncurry g))
    (hg : MemLp (fun p : ℝ × Vec 2 => (g p.1 p.2 : ℂ)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (S : ℝ → TorusHk K ℂ) (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hs : ∀ t, (S t).val (valueIndex2 K) = cellSourceSlice (fun s x => (g s x : ℂ)) t)
    (u₀ : TorusHk K ℂ) (c₀ : Vec 2 → ℝ)
    (h₀ : (torusHkValueCLM u₀ : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => (c₀ x : ℂ)) :
    ∃ (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ),
      Continuous u ∧
      CellWeakHilbertCurve a b u slice (fun r => dataDualDerivative P r
        (slice r) (cellSourceSlice (fun s x => (g s x : ℂ)) r)
        (fun j => cellSourceSlice (fun _ _ => (0 : PiLp 2 (fun _ : Fin 2 => ℂ)) j) r)) ∧
      u a = torusHkValueCLM u₀ ∧
      (∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t) ∧
      (∀ t ∈ Icc a b, (fun x => ((u t x).re : ℂ)) =ᵐ[
        volume.restrict AVenhance.unitCube] u t) := by
  have hsm : Measurable (Function.uncurry (fun t x => (g t x : ℂ))) :=
    Complex.ofRealCLM.continuous.measurable.comp hm
  have he := cellProduct_cellNormSq_finite (Icc a b) (fun t x => (g t x : ℂ)) hg
  rcases lt_or_eq_of_le hab with hlt | heq
  · obtain ⟨D⟩ := dataGalerkin_limit_data hab P _ (fun _ _ => 0)
      hsm measurable_const he (cellProduct_cellNormSq_finite (Icc a b) (fun _ _ => (0 : PiLp 2 (fun _ : Fin 2 => ℂ))) MemLp.zero)
      (torusHkValueCLM u₀)
    obtain ⟨U, hU, hi⟩ := D.exists_continuous_trace hlt hg MemLp.zero
    let u := extendCurve hab U
    obtain ⟨R, hR, htrace⟩ := dataWeakHilbert_exists_raw_solution P (fun t x => (g t x : ℂ)) (fun _ _ => 0)
      hg MemLp.zero u D.limit hU
    have hri : cellValue R a =ᵐ[volume.restrict AVenhance.unitCube]
        fun x => (c₀ x : ℂ) :=
      (htrace a).symm.trans ((Filter.EventuallyEq.of_eq
        (congrArg (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) hi)).trans h₀)
    have hr := dataRaw_real_trace hab P g c₀ hg R hR hri
    refine ⟨u, D.limit, continuous_extendCurve hab U, hU, hi,
      D.higher_trace hg K Cv hCv hv hp hb S hS hs u₀ rfl u hU hi, ?_⟩
    intro t ht
    filter_upwards [htrace t, hr t ht] with x hx hy
    exact (congrArg (fun z : ℂ => (z.re : ℂ)) hx).trans (hy.trans hx.symm)
  · subst b
    refine ⟨fun _ => torusHkValueCLM u₀, fun _ => 0, continuous_const,
      cellSingleton_weak_curve a _ _, rfl, ?_, ?_⟩
    · intro t _
      exact ⟨u₀, rfl⟩
    · intro t _
      filter_upwards [h₀] with x hx
      rw [hx]
      simp

end AVRegularity.EntryWeakProofs
end
end

section
/-! Uniform higher Sobolev bounds on every closed-time molecular trace. -/

@[expose] public noncomputable section

open MeasureTheory Set Homogenization AVRegularity.Sobolev Filter
open scoped Topology
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE

namespace AVRegularity.EntryWeakProofs

theorem MolecularGalerkinLimitData.higher_flux_trace_uniform_bound {a b : ℝ} {hab : a ≤ b}
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (D : MolecularGalerkinLimitData a b hab P src F initial)
    (hsrc : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hF : MemLp (Function.uncurry F) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (K : ℕ) (R : ℝ)
    (hR : ∀ N t, t ∈ Icc a b →
      ‖dataFourierHighCLM N K (cellGalerkinValue N (extendCurve hab (D.curve N) t))‖ ≤ R)
    (u : ℝ → ComplexCellL2) (hu : CellWeakHilbertCurve a b u D.limit D.dualState)
    (hi : u a = initial) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ, torusHkValueCLM w = u t ∧ ‖w‖ ≤ R := by
  intro t ht
  let v := fun n => dataFourierHighCLM (D.subsequence n) K
    (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
  refine higherTrace_exists_bounded K v (u t) R
    (fun n => hR (D.subsequence n) t ht) (fun z => ?_)
  have hh := D.trace_moments_tendsto hsrc hF u hu hi z t ht
  simpa only [v, dataFourierHigh_value] using hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! Genuine arbitrary-parameter inverse data restrict to affine planar slices without changing cell dimension. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open scoped ContDiff ENNReal
namespace AVRegularity.EntryWeakProofs

theorem finite_affine_derivative_norm_le
    {V P E : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : P → E) (n : ℕ) (hf : ContDiff ℝ (n : ℕ∞) f)
    (L : V →L[ℝ] P) (hL : ‖L‖ ≤ 1) (a : P) (Y : V) :
    ‖iteratedFDeriv ℝ n (fun X => f (L X + a)) Y‖ ≤
      ‖iteratedFDeriv ℝ n f (L Y + a)‖ := by
  have hh := finite_realWordJet_affine_derivative_bound f 0 n
    (by simpa only [Nat.zero_add] using hf) (fun i => Fin.elim0 i)
    (fun i => Fin.elim0 i) L hL a Y
  simp only [realWordJet, iteratedFDeriv_zero_apply] at hh
  rw [Nat.zero_add] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end
end

section
/-! A smooth clamp bounds geometric coordinates while preserving every complementary phase. -/
@[expose] public noncomputable section
open Filter Topology Set Metric
namespace AVRegularity.EntryWeakProofs
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [FiniteDimensional ℝ X]

def independentProjectionBump : ContDiffBump (0 : X) :=
  ⟨1 / 4, 1 / 2, by norm_num, by norm_num⟩

def independentProjectionClamp (Q : X →L[ℝ] X) (x : X) : X :=
  x - Q x + (independentProjectionBump (X := X) : X → ℝ) (Q x) • Q x

theorem independentProjectionClamp_contDiff (Q : X →L[ℝ] X) :
    ContDiff ℝ (⊤ : ℕ∞) (independentProjectionClamp Q) :=
  (contDiff_id.sub Q.contDiff).add
    (((independentProjectionBump (X := X)).contDiff.comp Q.contDiff).smul Q.contDiff)

theorem independentProjectionClamp_identity_germ (Q : X →L[ℝ] X) (x : X)
    (hx : ‖Q x‖ < 1 / 4) : independentProjectionClamp Q =ᶠ[𝓝 x] id := by
  have hx' : Q x ∈ ball (0 : X) (independentProjectionBump (X := X)).rIn := by
    simpa only [mem_ball_iff_norm, sub_zero, independentProjectionBump] using hx
  have hh := ((independentProjectionBump (X := X)).eventuallyEq_one_of_mem_ball hx').comp_tendsto
    Q.continuous.continuousAt
  filter_upwards [hh] with y hy
  change y - Q y + (independentProjectionBump (X := X) : X → ℝ) (Q y) • Q y = y
  change (independentProjectionBump (X := X) : X → ℝ) (Q y) = 1 at hy
  rw [hy, one_smul, sub_add_cancel]

theorem independentProjectionClamp_kernel_translation (Q : X →L[ℝ] X) (δ x : X)
    (hδ : Q δ = 0) : independentProjectionClamp Q (x + δ) = independentProjectionClamp Q x + δ := by
  simp only [independentProjectionClamp, map_add, hδ, add_zero]
  abel

theorem independentProjectionClamp_project (Q : X →L[ℝ] X)
    (hQ : ∀ x, Q (Q x) = Q x) (x : X) :
    Q (independentProjectionClamp Q x) = (independentProjectionBump (X := X) : X → ℝ) (Q x) • Q x := by
  simp only [independentProjectionClamp, map_add, map_sub, map_smul, hQ, sub_self, zero_add]

theorem independentProjectionClamp_project_norm (Q : X →L[ℝ] X)
    (hQ : ∀ x, Q (Q x) = Q x) (x : X) :
    ‖Q (independentProjectionClamp Q x)‖ ≤ 1 / 2 := by
  rw [independentProjectionClamp_project Q hQ]
  by_cases hx : Q x ∈ tsupport (independentProjectionBump (X := X) : X → ℝ)
  · have hb : ‖Q x‖ ≤ 1 / 2 := by
      rw [(independentProjectionBump (X := X)).tsupport_eq] at hx
      simpa only [mem_closedBall_iff_norm, sub_zero, independentProjectionBump] using hx
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (independentProjectionBump (X := X)).nonneg]
    exact (mul_le_of_le_one_left (norm_nonneg _) (independentProjectionBump (X := X)).le_one).trans hb
  · rw [image_eq_zero_of_notMem_tsupport hx, zero_smul, norm_zero]
    norm_num

theorem independentProjectionBump_mul_jet_budget :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ (n : ℕ) (x : X),
      ‖iteratedFDeriv ℝ n (fun y : X => (independentProjectionBump (X := X) : X → ℝ) y • y) x‖ ≤ B n := by
  let f := fun y : X => (independentProjectionBump (X := X) : X → ℝ) y • y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := (independentProjectionBump (X := X)).contDiff.smul contDiff_id
  have hc : HasCompactSupport f := (independentProjectionBump (X := X)).hasCompactSupport.smul_right
  have hb (n : ℕ) : ∃ B : ℝ, ∀ x, ‖iteratedFDeriv ℝ n f x‖ ≤ B :=
    (hc.iteratedFDeriv n).exists_bound_of_continuous
      (ContDiff.continuous_iteratedFDeriv (by simp) hf)
  choose B hB using hb
  exact ⟨B, (fun n => (norm_nonneg _).trans (hB n 0)), hB⟩

end AVRegularity.EntryWeakProofs
end
end

section
/-! Independent family-parameter metric reserves restrict to the existing planar inverse API. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

structure IndependentParameterMetricReserve (H : ℕ)
    (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ) where
  regular : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j)
  measurable : ∀ Y i j, Measurable (fun t => G t Y i j)
  metric : ∀ Y, IsCellMetric (fun t _ => G t Y)
  budget : ℕ → ℝ
  budget_nonneg : ∀ n, 0 ≤ budget n
  derivative_bound : ∀ n, n ≤ H → ∀ t Y i j,
    ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ budget n

def IndependentParameterMetricReserve.affineSlice {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G)
    (L : Vec 2 →L[ℝ] P) (hL : ‖L‖ ≤ 1) (a : P) :
    ParameterMetricReserve H (fun t Y => G t (L Y + a)) where
  regular := fun t i j => (Q.regular t i j).comp (L.contDiff.add contDiff_const)
  measurable := fun Y i j => Q.measurable (L Y + a) i j
  metric := fun Y => Q.metric (L Y + a)
  budget := Q.budget
  budget_nonneg := Q.budget_nonneg
  derivative_bound := fun n hn t Y i j =>
    (finite_affine_derivative_norm_le (fun X => G t X i j) n
      ((Q.regular t i j).of_le (by simp)) L hL a Y).trans
      (Q.derivative_bound n hn t (L Y + a) i j)

end AVRegularity.EntryWeakProofs
end
end

section
/-! The geometric clamp has bounded positive jets, although the untouched phases remain unbounded. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

variable [FiniteDimensional ℝ X]

theorem independentProjectionClamp_positive_jet_budget (Q : X →L[ℝ] X) (hQ : ‖Q‖ ≤ 1) :
    ∃ B : ℕ → ℝ, (∀ n, 0 ≤ B n) ∧ ∀ n, 1 ≤ n → ∀ x,
      ‖iteratedFDeriv ℝ n (independentProjectionClamp Q) x‖ ≤ B n := by
  obtain ⟨B, hB, hb⟩ := independentProjectionBump_mul_jet_budget (X := X)
  let L := ContinuousLinearMap.id ℝ X - Q
  let f := fun y : X => (independentProjectionBump (X := X) : X → ℝ) y • y
  have hf : ContDiff ℝ (⊤ : ℕ∞) f :=
    (independentProjectionBump (X := X)).contDiff.smul contDiff_id
  have hL : ContDiff ℝ (⊤ : ℕ∞) (L : X → X) := L.contDiff
  have hcomp : ContDiff ℝ (⊤ : ℕ∞) (f ∘ Q) := hf.comp Q.contDiff
  refine ⟨fun n => ‖L‖ + B n, fun n => add_nonneg (norm_nonneg _) (hB n), ?_⟩
  intro n hn x
  change ‖iteratedFDeriv ℝ n ((L : X → X) + f ∘ Q) x‖ ≤ _
  rw [iteratedFDeriv_add_apply (hL.contDiffAt.of_le (by simp))
    (hcomp.contDiffAt.of_le (by simp))]
  apply (norm_add_le _ _).trans
  apply add_le_add (linear_positive_derivative_norm_le L n hn x)
  have hh := finite_affine_derivative_norm_le f n (hf.of_le (by simp)) Q hQ 0 x
  simp only [add_zero] at hh
  exact hh.trans (hb n (Q x))

end AVRegularity.EntryWeakProofs
end
end

section
/-! The literal relative shear and actual native transition retain cell periodicity. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

theorem weak_relative_displacement_periodic (D : OCData) (hΛ : 1 ≤ D.Λ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (u r : ℝ) :
    IsZ2Periodic (D.relDisp m slot u r) := by
  intro n z
  have hs : ocShearVel D.α D.q D.Λ m slot (D.eps m • (z + latticeShift n)) =
      ocShearVel D.α D.q D.Λ m slot (D.eps m • z) := by
    funext i
    have hh := CycleDamping.cell_shear_component_periodic (α := D.α) (q := D.q)
      (m := m) hΛ hp 0 i n z
    simpa only [zero_add, OCData.eps] using hh
  dsimp only [OCData.relDisp]
  rw [hs]

theorem weak_transfer_center_joint_fast_periodic (D : OCData) (hΛ : 1 ≤ D.Λ)
    (A : RealChain) (hl : A.WellSlotted) (hp : Odd A.slot) (slot : ℤ) (t : ℝ) (Y : Vec 2) :
    IsZ2Periodic (fun z => weakTransferCenterJoint D A slot t (z, Y)) := by
  intro n z
  rw [weak_transfer_center_joint_formula D A hl slot t
    (Construction.Stream.ocEpsilon_pos hΛ).ne']
  dsimp only
  have he : z + latticeShift n + Y = (z + Y) + latticeShift n := by abel
  rw [he, weak_relative_displacement_periodic D hΛ A.ctxLevel A.slot hp]

theorem weak_transfer_matrix_joint_fast_periodic (D : OCData) (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (A : RealChain) (hl : A.WellSlotted) (hp : Odd A.slot)
    (slot : ℤ) (t : ℝ) (Y : Vec 2) (a b : Fin 2) :
    IsZ2Periodic (fun z =>
      (childTransition D slot t (A.recenter D (D.eps A.ctxLevel • Y))
        (z + (D.eps A.ctxLevel)⁻¹ • (D.eps A.ctxLevel • Y)))⁻¹ a b) := by
  intro n z
  dsimp only
  rw [weak_transfer_matrix_inverse_eq_joint_slow_jacobian_inverse D hΛ hζ A hl slot t
      (z + latticeShift n, Y),
    weak_transfer_matrix_inverse_eq_joint_slow_jacobian_inverse D hΛ hζ A hl slot t (z, Y)]
  have he : (fun y => weakTransferCenterJoint D A slot t (z + latticeShift n, y)) =
      fun y => weakTransferCenterJoint D A slot t (z, y) :=
    funext (fun y => weak_transfer_center_joint_fast_periodic D hΛ A hl hp slot t y n z)
  rw [he]

end AVRegularity.EntryWeakProofs
end
end

section
/-! Integer shifts of a stored child phase leave its literal geometry unchanged. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.EntryWeakProofs

theorem childGeom_phase_lattice_shift (D : OCData) (hΛ : 1 ≤ D.Λ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (a : ℝ) (c : ChainChild) (g : ChainGeom) (n : Fin 2 → ℤ) :
    D.childGeom m slot a ⟨c.center, c.phase + latticeShift n⟩ g = D.childGeom m slot a c g := by
  apply Prod.ext
  · funext u x r
    dsimp only [OCData.childGeom]
    have he : (c.phase + latticeShift n) -
        (D.eps m)⁻¹ • (g.2.1 + c.center) =
        (c.phase - (D.eps m)⁻¹ • (g.2.1 + c.center)) + latticeShift n := by abel
    rw [he]
    have hs : (D.eps m)⁻¹ • g.1 g.2.2 x r +
        (c.phase - (D.eps m)⁻¹ • (g.2.1 + c.center) + latticeShift n) =
        ((D.eps m)⁻¹ • g.1 g.2.2 x r +
          (c.phase - (D.eps m)⁻¹ • (g.2.1 + c.center))) + latticeShift n := by abel
    rw [hs, weak_relative_displacement_periodic D hΛ m slot hp]
  · rfl

theorem childGeom_eq_of_phase_lattice (D : OCData) (hΛ : 1 ≤ D.Λ)
    (m : ℕ) (slot : ℤ) (hp : Odd slot) (a : ℝ) (c d : ChainChild) (g : ChainGeom)
    (hc : c.center = d.center) (n : Fin 2 → ℤ) (hphase : c.phase = d.phase + latticeShift n) :
    D.childGeom m slot a c g = D.childGeom m slot a d g := by
  have he : c = ⟨d.center, d.phase + latticeShift n⟩ := by
    cases c
    cases d
    simp_all
  rw [he]
  exact childGeom_phase_lattice_shift D hΛ m slot hp a d g n

end AVRegularity.EntryWeakProofs
end
end

section
/-! Extra fast and fine slow coordinates keep their identity jets under a stored-parameter clamp. -/
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs
variable {P V W : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup W] [NormedSpace ℝ W]

def independentParameterExtension (T : P → P) (Y : (V × P) × W) : (V × P) × W :=
  ((Y.1.1, T Y.1.2), Y.2)

theorem independentParameterExtension_contDiff (T : P → P) (hT : ContDiff ℝ (⊤ : ℕ∞) T) :
    ContDiff ℝ (⊤ : ℕ∞) (independentParameterExtension (V := V) (W := W) T) :=
  ((contDiff_fst.comp contDiff_fst).prodMk
    (hT.comp (contDiff_snd.comp contDiff_fst))).prodMk contDiff_snd

theorem independentParameterExtension_positive_jet_bound (T : P → P)
    (hT : ContDiff ℝ (⊤ : ℕ∞) T) (H n : ℕ) (hn : 1 ≤ n) (hnH : n ≤ H)
    (C : ℝ) (hC : 1 ≤ C)
    (hTC : ∀ j, 1 ≤ j → j ≤ H → ∀ Y, ‖iteratedFDeriv ℝ j T Y‖ ≤ C)
    (X : (V × P) × W) :
    ‖iteratedFDeriv ℝ n (independentParameterExtension (V := V) (W := W) T) X‖ ≤ C := by
  let A := (ContinuousLinearMap.fst ℝ V P).comp (ContinuousLinearMap.fst ℝ (V × P) W)
  let B := (ContinuousLinearMap.snd ℝ V P).comp (ContinuousLinearMap.fst ℝ (V × P) W)
  let E := ContinuousLinearMap.snd ℝ (V × P) W
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.1.1‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using (norm_fst_le Y.1).trans (norm_fst_le Y)
  have hB : ‖B‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.1.2‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using (norm_snd_le Y.1).trans (norm_fst_le Y)
  have hE : ‖E‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro Y
    change ‖Y.2‖ ≤ 1 * ‖Y‖
    simpa only [one_mul] using norm_snd_le Y
  have ha := (linear_positive_derivative_norm_le A n hn X).trans (hA.trans hC)
  have he := (linear_positive_derivative_norm_le E n hn X).trans (hE.trans hC)
  have hb := finite_affine_derivative_norm_le T n (hT.of_le (by simp)) B hB 0 X
  simp only [add_zero] at hb
  have hb' := hb.trans (hTC n hn hnH (B X))
  have hbt : ContDiff ℝ (n : ℕ∞) (T ∘ B) := (hT.comp B.contDiff).of_le (by simp)
  have hp := independent_joint_pair_jet_bound A (T ∘ B) n A.contDiff hbt X
  have hq := independent_joint_pair_jet_bound (fun Y => (A Y, T (B Y))) E n
    (A.contDiff.prodMk hbt) E.contDiff X
  exact hq.trans (max_le (hp.trans (max_le ha hb')) he)

end AVRegularity.EntryWeakProofs
end
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Genuine metric and drift bounds construct the molecular data used by local lift production. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def independentParameterMetricMolecularData {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G)
    (he : ∀ t Y (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    (v : ℝ → Vec 2 → Vec 2) (hm : Measurable (Function.uncurry v))
    (V : ℝ) (hv : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2) (Y : P) : MolecularData where
  G := fun t => G t Y
  v := v
  CG := Q.budget 0
  V := V
  metric_measurable i j := Q.measurable Y i j
  metric_bounded t i j := by
    simpa only [norm_iteratedFDeriv_zero, Real.norm_eq_abs]
      using Q.derivative_bound 0 (Nat.zero_le H) t Y i j
  metric_coercive t ξ := he t Y ξ
  drift_measurable := hm
  drift_bounded := hv

theorem independentParameterMetricMolecularData_coefficients {H : ℕ}
    {G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G)
    (he : ∀ t Y (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G t Y i j * ξ i * ξ j)
    (v : ℝ → Vec 2 → Vec 2) (hm : Measurable (Function.uncurry v))
    (V : ℝ) (hv : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2) (Y : P) :
    dataCoefficients (independentParameterMetricMolecularData Q he v hm V hv Y) =
      ⟨(fun t _ => G t Y), v, 0, 0⟩ := rfl

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Sampling the slow and fast variables at physical scales preserves the joint source budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]

def jointSourceDiagonalMap (ell : ℝ) : Vec 2 →L[ℝ] Vec 2 × Vec 2 :=
  (ContinuousLinearMap.id ℝ (Vec 2)).prod (ell • ContinuousLinearMap.id ℝ (Vec 2))

theorem jointSourceDiagonalMap_norm_le (ell : ℝ) (hell : |ell| ≤ 1) :
    ‖jointSourceDiagonalMap ell‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  change ‖(Y, ell • Y)‖ ≤ 1 * ‖Y‖
  rw [one_mul, Prod.norm_def, norm_smul, Real.norm_eq_abs]
  exact max_le le_rfl (mul_le_of_le_one_left (norm_nonneg Y) hell)

theorem JointSourceReserve.diagonal_contDiff {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (ell : ℝ) (t : ℝ) :
    ContDiff ℝ (H : ℕ∞) (fun Y => f t Y (ell • Y)) :=
  (Q.regular t).comp (jointSourceDiagonalMap ell).contDiff

theorem JointSourceReserve.diagonal_jet_le {H : ℕ} {f : ℝ → Vec 2 → Vec 2 → E}
    (Q : JointSourceReserve H f) (ell : ℝ) (hell : |ell| ≤ 1)
    (n : ℕ) (hn : n ≤ H) (t : ℝ) (Y : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun X => f t X (ell • X)) Y‖ ≤ Q.budget n := by
  have hh := finite_affine_derivative_norm_le
    (fun X : Vec 2 × Vec 2 => f t X.1 X.2) n
    ((Q.regular t).of_le (by exact_mod_cast hn))
    (jointSourceDiagonalMap ell) (jointSourceDiagonalMap_norm_le ell hell) 0 Y
  simp only [add_zero] at hh
  exact hh.trans (Q.derivative_bound n hn t (jointSourceDiagonalMap ell Y))

end AVRegularity.EntryWeakProofs
end
end
