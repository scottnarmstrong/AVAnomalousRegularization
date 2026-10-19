-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.NativeFamilyLiftUniqueness
import AVRegularity.EntryWeak.IndependentCovariantOperations
import AVRegularity.EntryWeakAssembly.WindowListL2Representative

@[expose] public noncomputable section

section
namespace AVRegularity.WeakEntryProofs

/-! Genuine source word reserves give the actual Hilbert source continuity. -/

section
open MeasureTheory Homogenization Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
variable {d H : ℕ}

theorem coordinate_source_word_Hilbert_memLp {f : ℝ → Vec 2 → Vec d → ℂ}
    (Q : IndependentParameterSourceReserve H f) (w : List (Fin d)) (hw : w.length ≤ H)
    (a b : ℝ) (Y : Vec d) :
    MemLp (coordinateWordHilbertSource f w Y) 2 (volume.restrict (Icc a b)) := by
  let q := Q.wordJet w.length 0 (by omega) (coordinateWordDirections w) (coordinateWordDirections_norm w)
  exact cellSourceSlice_memLp (Icc a b) _ (independent_source_window_memLp q a b Y)

theorem coordinate_source_word_Hilbert_energy_continuous {f : ℝ → Vec 2 → Vec d → ℂ}
    (Q : IndependentParameterSourceReserve H f) (w : List (Fin d)) (hw : w.length + 1 ≤ H)
    {a b : ℝ} (hab : a ≤ b) (Y : Vec d) :
    Tendsto (fun X => ∫ t in a..b,
      ‖coordinateWordHilbertSource f w X t - coordinateWordHilbertSource f w Y t‖ ^ 2)
      (𝓝 Y) (𝓝 0) := by
  let q := Q.wordJet w.length 1 hw (coordinateWordDirections w) (coordinateWordDirections_norm w)
  exact independent_source_slice_window_difference_energy_tendsto_zero q (by norm_num) hab Y
end

/-! Parameter differentiation preserves the genuine zero cell mean of a primitive source. -/

section
open Homogenization MeasureTheory
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
variable {d H : ℕ}

theorem coordinate_source_word_mean_zero {f : ℝ → Vec 2 → Vec d → ℂ}
    (Q : IndependentParameterSourceReserve H f)
    (hf : ∀ t Y, fieldCellMean (fun z => f t z Y) = 0)
    (w : List (Fin d)) (hw : w.length ≤ H) (t : ℝ) (Y : Vec d) :
    fieldCellMean (coordinateSourceWord f w Y t) = 0 := by
  change independentCoordinateMeanWord f t w Y = 0
  induction w generalizing Y with
  | nil =>
    rw [independentCoordinateMeanWord_nil]
    exact hf t Y
  | cons i w ih =>
    have hh := independent_coordinate_mean_word_derivative Q t w
      (by simpa only [List.length_cons] using hw) i Y
    have he : (fun h : ℝ => independentCoordinateMeanWord f t w (Y + h • basisVec i)) =
        fun _ => (0 : ℂ) := by
      funext h
      exact ih (by simp only [List.length_cons] at hw; omega) _
    rw [he] at hh
    exact hh.unique (hasDerivAt_const 0 (0 : ℂ))

theorem coordinate_source_word_Q0_eq_self {f : ℝ → Vec 2 → Vec d → ℂ}
    (Q : IndependentParameterSourceReserve H f)
    (hf : ∀ t Y, fieldCellMean (fun z => f t z Y) = 0)
    (w : List (Fin d)) (hw : w.length ≤ H) (t : ℝ) (Y : Vec d) :
    cellQ0 (coordinateSourceWord f w Y t) = coordinateSourceWord f w Y t :=
  cellQ0_eq_self_of_mean_zero _ (coordinate_source_word_mean_zero Q hf w hw t Y)
end

/-! Any actual real raw solution with a genuine higher carrier has the canonical scalar inverse readout. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE

theorem raw_higher_scalar_inverse {a b : ℝ} (hab : a ≤ b)
    (P : MolecularData) (hv : IsCellDrift P.v) (K r : ℕ) (hr : max r 1 + 2 ≤ K)
    (g : ℝ → Vec 2 → ℝ)
    (hg : MemLp (fun p : ℝ × Vec 2 => (g p.1 p.2 : ℂ)) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hgm : ∀ t, ∫ x in AVenhance.unitCube, g t x = 0)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P)
      (fun t x => (g t x : ℂ)) (fun _ _ => 0) D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (w : ℝ → TorusHk K ℂ)
    (hw : ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[
      volume.restrict AVenhance.unitCube] cellValue D t) :
    ∃ c : ℝ → Vec 2 → ℝ, IsCellFieldInverse P.G P.v r a b 0 g c ∧
      ∀ t ∈ Icc a b, c t = realClassicalLift K (mapTorusHk Complex.reCLM (w t)) := by
  have hcur := dataSolution_to_Hilbert hab P (fun t x => (g t x : ℂ)) (fun _ _ => 0)
    hg MemLp.zero D hD
  let U : C(Icc a b, ComplexCellL2) :=
    ⟨fun t => cellRawTrace D t, continuousOn_iff_continuous_domRestrict.mp hcur.trace⟩
  let u := extendCurve hab U
  have hext t (ht : t ∈ Icc a b) : u t = cellRawTrace D t := extendCurve_eq_of_mem hab U ht
  have he t (ht : t ∈ Icc a b) : (u t : Vec 2 → ℂ) =ᵐ[
      volume.restrict AVenhance.unitCube] cellValue D t := by
    rw [hext t ht]
    exact cellRawTrace_ae D t ((hD.2.2.1 t ht).1)
  have hcurve := cellWeakHilbert_trace_congr hcur hext
  have hrawreal := dataRaw_real_trace hab P g 0 hg D hD (by
      filter_upwards [hi] with x hx
      simpa only [Pi.zero_apply, Complex.ofReal_zero] using hx)
  have hreal t (ht : t ∈ Icc a b) : (fun x => ((u t x).re : ℂ)) =ᵐ[
      volume.restrict AVenhance.unitCube] u t := by
    filter_upwards [he t ht, hrawreal t ht] with x hx hy
    exact (congrArg (fun z : ℂ => (z.re : ℂ)) hx).trans (hy.trans hx.symm)
  have hread t (ht : t ∈ Icc a b) : torusHkValueCLM (w t) = u t :=
    Lp.ext ((hw t ht).trans (he t ht).symm)
  have hhigh t (ht : t ∈ Icc a b) : ∃ q : TorusHk K ℂ, torusHkValueCLM q = u t :=
    ⟨w t, hread t ht⟩
  obtain ⟨hc, hsol, hce⟩ := dataRegular_classical_solution P K (max r 1) hr
    (Nat.le_max_right _ _) (fun t x => (g t x : ℂ)) hg u (cellH1Slice D)
    (continuous_extendCurve hab U) hcurve hhigh hreal
  have hinit : (u a : Vec 2 → ℂ) =ᵐ[volume.restrict AVenhance.unitCube] 0 :=
    (he a ⟨le_rfl, hab⟩).trans hi
  have hmean := dataWeak_classical_mean_zero hab P hv g hg hgm u (cellH1Slice D) hcurve
    (by exact integral_eq_zero_of_ae hinit) (cellClassicalWindow a b u) hce
  refine ⟨cellClassicalWindow a b u, scalarFieldInverse_of_id hab P.G P.v r 0 g _
    (fun t _ => (hc t).of_le (by exact_mod_cast Nat.le_max_left r 1)) hsol hmean
    (by
      filter_upwards [(hce a ⟨le_rfl, hab⟩).symm.trans hinit] with x hx
      change (cellClassicalWindow a b u a x : ℂ) = (0 : ℂ)
      simpa only [Pi.zero_apply] using hx), ?_⟩
  intro t ht
  change (fun x => if t ∈ Icc a b then cellClassicalLift (u t) x else 0) = _
  simp only [ite_eq_left ht]
  exact cellClassicalLift_eq_real_high K (w t) (u t) (hread t ht) (hreal t ht)
end

/-! Primitive Taylor bounds construct the differentiated finite-window equation and identify its trace. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {A : Type*} [NormedAddCommGroup A] [NormedSpace ℝ A]

theorem molecular_parameter_variable_source_directional_tendsto
    {a b : ℝ} (hab : a ≤ b) (P : MolecularData)
    (S : A → ℝ → ComplexCellL2) (S₁ : ℝ → ComplexCellL2)
    (F : A → ℝ → Fin 2 → ComplexCellL2) (F₁ : ℝ → Fin 2 → ComplexCellL2)
    (G : A → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hr : ∀ t i j, ContDiff ℝ 2 (fun X => G X t i j))
    (hm : ∀ X i j, Measurable (fun t => G X t i j))
    (C₀ C₁ C₂ : ℝ) (hC₂ : 0 ≤ C₂)
    (hG : ∀ X t i j, |G X t i j| ≤ C₀)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G X t i j * ξ i * ξ j)
    (hD : ∀ t i j X, ‖fderiv ℝ (fun Y => G Y t i j) X‖ ≤ C₁)
    (hDD : ∀ t i j X, ‖fderiv ℝ (fderiv ℝ (fun Y => G Y t i j)) X‖ ≤ C₂)
    (u : A → ℝ → ComplexCellL2) (slice : A → ℝ → TorusHk 1 ℂ)
    (h : ∀ X, CellWeakHilbertCurve a b (u X) (slice X) (fun t => dataDualDerivative
      (molecularMetricReplacement P (G X) C₀ (hm X) (hG X) (he X)) t
        (slice X t) (S X t) (F X t)))
    (hi : ∀ X, u X a = 0) (Y v : A)
    (du : ℝ → ComplexCellL2) (dslice : ℝ → TorusHk 1 ℂ)
    (hd : CellWeakHilbertCurve a b du dslice (fun t => dataDualDerivative
        (molecularMetricReplacement P (G Y) C₀ (hm Y) (hG Y) (he Y)) t (dslice t)
        (S₁ t)
        (fun j => F₁ t j +
          molecularMetricHilbertFlux (Matrix.of (fun i k => fderiv ℝ (fun X => G X t i k) Y v))
            (slice Y t) j))) (hdi : du a = 0)
    (hSres : ∀ r : ℝ, MemLp (fun t => r⁻¹ • (S (Y + r • v) t - S Y t) - S₁ t)
      2 (volume.restrict (Icc a b)))
    (hFres : ∀ r : ℝ, ∀ j, MemLp (fun t => r⁻¹ • (F (Y + r • v) t j - F Y t j) - F₁ t j)
      2 (volume.restrict (Icc a b)))
    (htS : Tendsto (fun r : ℝ => ∫ t in a..b, ‖r⁻¹ • (S (Y + r • v) t - S Y t) - S₁ t‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0))
    (htF : ∀ j, Tendsto (fun r : ℝ => ∫ t in a..b,
      ‖r⁻¹ • (F (Y + r • v) t j - F Y t j) - F₁ t j‖ ^ 2) (𝓝[≠] 0) (𝓝 0)) :
    (∀ t ∈ Icc a b, Tendsto (fun r : ℝ => r⁻¹ • (u (Y + r • v) t - u Y t) - du t)
      (𝓝[≠] 0) (𝓝 0)) ∧
    Tendsto (fun r : ℝ => ∫ t in a..b, ∑ j,
      ‖cellDerivativeCLM j (r⁻¹ • (slice (Y + r • v) t - slice Y t) - dslice t)‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0) := by
  let Q := fun X => molecularMetricReplacement P (G X) C₀ (hm X) (hG X) (he X)
  let D := fun t => Matrix.of (fun i k => fderiv ℝ (fun X => G X t i k) Y v)
  let X := fun r : ℝ => Y + r • v
  let B := fun r : ℝ => ∫ s in a..b,
    ‖r⁻¹ • (S (X r) s - S Y s) - S₁ s‖ ^ 2 + 4 * ∑ j,
    ‖(r⁻¹ • (F (X r) s j - F Y s j) - F₁ s j) +
      molecularMetricHilbertFlux (r⁻¹ • (G (X r) s - G Y s) - D s) (slice Y s) j +
      molecularMetricHilbertFlux (G (X r) s - G Y s) (dslice s) j‖ ^ 2
  let T := fun r t j => molecularMetricHilbertFlux (r⁻¹ • (G (X r) t - G Y t) - D t) (slice Y t) j
  let U := fun r t j => molecularMetricHilbertFlux (G (X r) t - G Y t) (dslice t) j
  have hT r j : MemLp (fun t => T r t j) 2 (volume.restrict (Icc a b)) :=
    parameter_metric_quotient_flux_memLp (fun t X => G X t)
      (fun t i j => (hr t i j).of_le (by norm_num)) hm C₀ C₁
      (fun t X => hG X t) hD Y v r (slice Y) (h Y).state j
  have hU r j : MemLp (fun t => U r t j) 2 (volume.restrict (Icc a b)) :=
    parameter_metric_difference_flux_memLp (fun t X => G X t) hm C₀
      (fun t X => hG X t) Y (X r) dslice hd.state j
  have hflux r j := ((hFres r j).add (hT r j)).add (hU r j)
  have htT j := parameter_metric_window_quotient_flux_energy_tendsto_zero (fun t X => G X t)
    hr hm C₂ hC₂ hDD hab Y v (slice Y) (h Y).state j
  have hX : Tendsto X (𝓝[≠] 0) (𝓝 Y) := by
    have hc : Continuous X := continuous_const.add (continuous_id.smul continuous_const)
    simpa only [X, zero_smul, add_zero] using (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  have htU j := (parameter_metric_window_difference_flux_energy_tendsto_zero
    (fun t X => G X t) (fun t i j => (hr t i j).of_le (by norm_num)) hm C₁ hD
    hab Y dslice hd.state j).comp hX
  have hsmall : Tendsto B (𝓝[≠] 0) (𝓝 0) := by
    have hh := window_forcing_budget_tendsto_zero (𝓝[≠] 0) hab
      (fun _ : ℝ => (0 : ComplexCellL2)) (fun r t => r⁻¹ • (S (X r) t - S Y t) - S₁ t)
      (fun r t j => (r⁻¹ • (F (X r) t j - F Y t j) - F₁ t j) + T r t j + U r t j)
      hSres hflux
      (by simpa only [norm_zero] using (tendsto_const_nhds :
        Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[≠] 0) (𝓝 0))) htS
      (fun j => window_normSq_add_integral_tendsto_zero (𝓝[≠] 0) hab _ _
        (fun r => (hFres r j).add (hT r j)) (fun r => hU r j)
        (window_normSq_add_integral_tendsto_zero (𝓝[≠] 0) hab _ _
          (fun r => hFres r j) (fun r => hT r j) (htF j) (htT j)) (htU j))
    simpa only [norm_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add, T, U, B] using hh
  have hQ (r : ℝ) : molecularMetricReplacement (Q Y) (G (X r)) C₀
      (hm (X r)) (hG (X r)) (he (X r)) = Q (X r) := rfl
  have hQg : (Q Y).G = G Y := rfl
  have hbudget r : ‖r⁻¹ • (u (X r) a - u Y a) - du a‖ ^ 2 +
      ∫ t in a..b, ‖r⁻¹ • (S (X r) t - S Y t) - S₁ t‖ ^ 2 + 4 * ∑ j,
      ‖(r⁻¹ • (F (X r) t j - F Y t j) - F₁ t j) +
        molecularMetricHilbertFlux (r⁻¹ • (G (X r) t - (Q Y).G t) - D t) (slice Y t) j +
        molecularMetricHilbertFlux (G (X r) t - (Q Y).G t) (dslice t) j‖ ^ 2 ≤ B r := by
    rw [hQg, hi (X r), hi Y, hdi, sub_self, smul_zero, sub_zero, norm_zero,
      zero_pow (by norm_num : (2 : ℕ) ≠ 0), zero_add]
  have hfull r j : MemLp (fun t => (r⁻¹ • (F (X r) t j - F Y t j) - F₁ t j) +
      molecularMetricHilbertFlux (r⁻¹ • (G (X r) t - (Q Y).G t) - D t) (slice Y t) j +
      molecularMetricHilbertFlux (G (X r) t - (Q Y).G t) (dslice t) j) 2
      (volume.restrict (Icc a b)) := by
    rw [hQg]
    exact hflux r j
  refine ⟨?_, ?_⟩
  · intro t ht
    exact molecularWeak_metric_quotient_tendsto (𝓝[≠] 0) hab (Q Y)
      (fun r => G (X r)) (fun _ => C₀) (fun r => hm (X r))
      (fun r => hG (X r)) (fun r => he (X r)) (fun r : ℝ => r⁻¹) D
      (fun r => S (X r)) (S Y) S₁ (fun r => F (X r)) (F Y) F₁
      (fun r => u (X r)) (u Y) du (fun r => slice (X r)) (slice Y) dslice
      (fun r => by rw [hQ r]; exact h (X r)) (h Y) hd hSres hfull B
      (fun r => intervalIntegral.integral_nonneg hab (fun t _ => add_nonneg (sq_nonneg _)
        (mul_nonneg (by norm_num) (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))))
      hbudget hsmall t ht
  · exact molecularWeak_metric_quotient_gradient_tendsto (𝓝[≠] 0) hab (Q Y)
      (fun r => G (X r)) (fun _ => C₀) (fun r => hm (X r))
      (fun r => hG (X r)) (fun r => he (X r)) (fun r : ℝ => r⁻¹) D
      (fun r => S (X r)) (S Y) S₁ (fun r => F (X r)) (F Y) F₁
      (fun r => u (X r)) (u Y) du (fun r => slice (X r)) (slice Y) dslice
      (fun r => by rw [hQ r]; exact h (X r)) (h Y) hd hSres hfull B hbudget hsmall
end

/-! A finite predecessor rank admits one actual coefficient cutoff with all needed reserves. -/

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
variable {ι : Type*} [Fintype ι] {H : ℕ}
open scoped Classical

abbrev FullLiftPredecessorIndex (ι : Type*) (N hh n : ℕ) :=
  {i : (Σ _p : Fin (hh + 1), Σ q : Fin (N + 1), Σ m : Fin (q.val + 1),
    DerivativeWord2 m.val × ι × ι) //
    (i.1.val < hh ∨ (i.1.val = hh ∧ i.2.1.val < n)) ∧ 1 ≤ i.2.1.val}

theorem finite_full_lift_local_cutoff_reserves (a b : ℝ) (hab : a ≤ b)
    (Ω : Set (Vec 2)) (hΩ : IsOpen Ω) (Y₀ : Vec 2) (hYΩ : Y₀ ∈ Ω)
    (Cc : ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)) (N hh n : ℕ)
    (hz : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u Y, Y ∈ Ω →
        ∀ z, Cc p q m α a Y z v u 1 = 0)
    (hloc : ∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
      ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u,
        ∃ (U : Set (Vec 2)) (f' : ℝ → Vec 2 → Vec 2 → ℝ),
          IsOpen U ∧ Y₀ ∈ U ∧ Nonempty (IndependentParameterSourceReserve H
            (independentTimeWindowSource (Ioc a b) f')) ∧
          ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ z, f' t z Y = Cc p q m α t Y z v u 1) :
    ∃ χ : Vec 2 → ℝ, tsupport χ ⊆ Ω ∧ χ =ᶠ[𝓝 Y₀] 1 ∧
      Nonempty (∀ p q, p < hh ∨ (p = hh ∧ q < n) → 1 ≤ q → q ≤ N →
        ∀ m ≤ q, ∀ α : DerivativeWord2 m, ∀ v u, JointSourceReserve H
          (fun t z Y => fullLiftLocalCutoff χ a b Cc p q m α t Y z v u 1)) := by
  let I := FullLiftPredecessorIndex ι N hh n
  let f : I → ℝ → Vec 2 → Vec 2 → ℝ := fun i t z Y =>
    Cc i.val.1.val i.val.2.1.val i.val.2.2.1.val i.val.2.2.2.1
      t Y z i.val.2.2.2.2.1 i.val.2.2.2.2.2 1
  have hzero (i : I) (Y : Vec 2) (hY : Y ∈ Ω) (z : Vec 2) : f i a z Y = 0 :=
    hz _ _ i.property.1 i.property.2 (by omega) _ (by omega) _ _ _ Y hY z
  have hlocal (i : I) := hloc _ _ i.property.1 i.property.2
    (by omega) _ (by omega) i.val.2.2.2.1 i.val.2.2.2.2.1 i.val.2.2.2.2.2
  obtain ⟨χ, hs, hone, ⟨R⟩⟩ := finite_local_window_cutoff_reserves a b hab Ω hΩ Y₀ hYΩ f hzero hlocal
  refine ⟨χ, hs, hone, ⟨?_⟩⟩
  intro p q hpq hq hqN m hm α v u
  have hp : p ≤ hh := by rcases hpq with hp | ⟨rfl, _⟩ <;> omega
  let i : I := ⟨⟨⟨p, Nat.lt_succ_iff.mpr hp⟩, ⟨q, Nat.lt_succ_iff.mpr hqN⟩,
    ⟨m, Nat.lt_succ_iff.mpr hm⟩, α, v, u⟩, hpq, hq⟩
  refine (R i).congrSource ?_
  funext t z Y
  change χ Y • Cc p q m α (max a (min b t)) Y z v u 1 = _
  simp only [fullLiftLocalCutoff, ite_eq_right (by omega : q ≠ 0), smul_apply]
end

/-! Strict lower-word induction proves continuity of every actual ordered-word equation. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {d H : ℕ}

theorem molecular_primitive_word_Hilbert_family_continuous {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (hN : N + 1 ≤ H) (P : MolecularData)
    (G : List (Fin d) → Vec d → ℝ → Matrix (Fin 2) (Fin 2) ℝ) (B : List (Fin d) → ℝ)
    (hm : ∀ w X j k, Measurable (fun t => G w X t j k))
    (hb : ∀ w, w.length ≤ N → ∀ X t j k, |G w X t j k| ≤ B w)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G [] X t i j * ξ i * ξ j)
    (δ : List (Fin d) → Vec d → Vec d → ℝ)
    (hd : ∀ w, w.length ≤ N → ∀ X Y t j k,
      |G w X t j k - G w Y t j k| ≤ δ w Y X)
    (hδ : ∀ w, w.length ≤ N → ∀ Y, Tendsto (δ w Y) (𝓝 Y) (𝓝 0))
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : Fin 2 → ℝ → Vec 2 → Vec d → ℂ}
    (Qf : IndependentParameterSourceReserve H f)
    (QF : ∀ j, IndependentParameterSourceReserve H (F j))
    (u : List (Fin d) → Vec d → ℝ → ComplexCellL2) (slice : List (Fin d) → Vec d → ℝ → TorusHk 1 ℂ)
    (h : ∀ w, w.length ≤ N → ∀ X, CellWeakHilbertCurve a b (u w X) (slice w X)
      (fun t => dataDualDerivative
        (molecularMetricReplacement P (G [] X) (B []) (hm [] X) (hb [] (by simp) X) (he X)) t
        (slice w X t) (coordinateWordHilbertSource f w X t)
        (fun j => coordinateWordHilbertSource (F j) w X t + molecularWordHilbertFlux (fun p => G p X)
          (fun p => slice p X) w t j)))
    (hi : ∀ w, w.length ≤ N → ∀ X, u w X a = 0) :
    ∀ w, w.length ≤ N → ∀ Y,
      (∀ t ∈ Icc a b, Tendsto (fun X => u w X t - u w Y t) (𝓝 Y) (𝓝 0)) ∧
      Tendsto (fun X => ∫ t in a..b,
        ∑ j, ‖cellDerivativeCLM j (slice w X t - slice w Y t)‖ ^ 2) (𝓝 Y) (𝓝 0) := by
  exact molecular_word_Hilbert_family_continuous hab N P G B hm hb he δ hd hδ
    (coordinateWordHilbertSource f) (fun w X t j => coordinateWordHilbertSource (F j) w X t)
    (fun w hw X => coordinate_source_word_Hilbert_memLp Qf w (by omega) a b X)
    (fun w hw X j => coordinate_source_word_Hilbert_memLp (QF j) w (by omega) a b X)
    (fun w hw Y => coordinate_source_word_Hilbert_energy_continuous Qf w (by omega) hab Y)
    (fun w hw Y j => coordinate_source_word_Hilbert_energy_continuous (QF j) w (by omega) hab Y)
    u slice h hi
end

/-! The actual next ordered-word equation identifies both trace and gradient derivatives. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {d : ℕ}

theorem molecular_word_Hilbert_derivative_step {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (P : MolecularData)
    (G : List (Fin d) → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (C₀ C₁ C₂ : List (Fin d) → ℝ)
    (hC₂ : ∀ p, p.length ≤ N → 0 ≤ C₂ p)
    (hr : ∀ p, p.length ≤ N → ∀ t j k, ContDiff ℝ 2 (fun X => G p t X j k))
    (hm : ∀ p X j k, Measurable (fun t => G p t X j k))
    (hb : ∀ p, p.length ≤ N → ∀ t X j k, |G p t X j k| ≤ C₀ p)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G [] t X i j * ξ i * ξ j)
    (hD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fun Z => G p t Z j k) X‖ ≤ C₁ p)
    (hDD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fderiv ℝ (fun Z => G p t Z j k)) X‖ ≤ C₂ p)
    (hcons : ∀ p, p.length < N → ∀ i t Y,
      G (i :: p) t Y = Matrix.of (fun j k => fderiv ℝ (fun X => G p t X j k) Y (basisVec i)))
    (S : List (Fin d) → Vec d → ℝ → ComplexCellL2)
    (F : List (Fin d) → Vec d → ℝ → Fin 2 → ComplexCellL2)
    (u : List (Fin d) → Vec d → ℝ → ComplexCellL2)
    (slice : List (Fin d) → Vec d → ℝ → TorusHk 1 ℂ)
    (h : ∀ w, w.length ≤ N → ∀ X, CellWeakHilbertCurve a b (u w X) (slice w X)
      (fun t => dataDualDerivative
        (molecularMetricReplacement P (fun t => G [] t X) (C₀ []) (hm [] X)
          (fun t => hb [] (by simp) t X) (he X)) t (slice w X t) (S w X t)
        (fun j => F w X t j + molecularWordHilbertFlux (fun p t => G p t X)
          (fun p => slice p X) w t j)))
    (hi : ∀ w, w.length ≤ N → ∀ X, u w X a = 0)
    (w : List (Fin d)) (hw : w.length < N) (Y : Vec d) (i : Fin d)
    (hSres : ∀ r : ℝ, MemLp (fun t => r⁻¹ • (S w (Y + r • basisVec i) t - S w Y t) -
      S (i :: w) Y t) 2 (volume.restrict (Icc a b)))
    (hFres : ∀ r : ℝ, ∀ j, MemLp (fun t => r⁻¹ • (F w (Y + r • basisVec i) t j - F w Y t j) -
      F (i :: w) Y t j) 2 (volume.restrict (Icc a b)))
    (htS : Tendsto (fun r : ℝ => ∫ t in a..b,
      ‖r⁻¹ • (S w (Y + r • basisVec i) t - S w Y t) - S (i :: w) Y t‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0))
    (htF : ∀ j, Tendsto (fun r : ℝ => ∫ t in a..b,
      ‖r⁻¹ • (F w (Y + r • basisVec i) t j - F w Y t j) - F (i :: w) Y t j‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0))
    (hquot : ∀ p ∈ independentWordForcing w,
      Tendsto (fun r : ℝ => ∫ t in a..b, ∑ j,
        ‖cellDerivativeCLM j (r⁻¹ • (slice p.2 (Y + r • basisVec i) t - slice p.2 Y t) -
          slice (i :: p.2) Y t)‖ ^ 2) (𝓝[≠] 0) (𝓝 0)) :
    (∀ t ∈ Icc a b, Tendsto (fun r : ℝ => r⁻¹ • (u w (Y + r • basisVec i) t - u w Y t) -
      u (i :: w) Y t) (𝓝[≠] 0) (𝓝 0)) ∧
    Tendsto (fun r : ℝ => ∫ t in a..b, ∑ j,
      ‖cellDerivativeCLM j (r⁻¹ • (slice w (Y + r • basisVec i) t - slice w Y t) -
        slice (i :: w) Y t)‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have hn : (i :: w).length ≤ N := by simp only [List.length_cons]; omega
  let Q := fun X => molecularMetricReplacement P (fun t => G [] t X) (C₀ []) (hm [] X)
    (fun t => hb [] (by simp) t X) (he X)
  let L := fun X => molecularWordHilbertFlux (fun p t => G p t X) (fun p => slice p X) w
  let L₁ := molecularWordHilbertFluxDerivative (fun p t => G p t Y) (fun p => slice p Y) i w
  let VF := fun X t j => F w X t j + L X t j
  let VF₁ := fun t j => F (i :: w) Y t j + L₁ t j
  have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
  have hg p (hp : p ∈ independentWordForcing w) : p.1.length < N := by
    have hh := hl p hp
    omega
  have hc p (hp : p ∈ independentWordForcing w) : p.2.length < N := by
    have hh := hl p hp
    omega
  have hL X j : MemLp (fun t => L X t j) 2 (volume.restrict (Icc a b)) :=
    molecularWordHilbertFlux_memLp (a := a) (b := b) _ _ w C₀
      (fun p _ => hm p.1 X) (fun p hp t => hb p.1 (hg p hp).le t X)
      (fun p hp => (h p.2 (hc p hp).le X).state) j
  have hL₁ j : MemLp (fun t => L₁ t j) 2 (volume.restrict (Icc a b)) :=
    molecularWordHilbertFluxDerivative_memLp (a := a) (b := b) _ _ i w C₀
      (fun p _ => hm p.1 Y) (fun p _ => hm (i :: p.1) Y)
      (fun p hp t => hb p.1 (hg p hp).le t Y)
      (fun p hp t => hb (i :: p.1) (by simp only [List.length_cons]; have hh := hg p hp; omega) t Y)
      (fun p hp => (h p.2 (hc p hp).le Y).state)
      (fun p hp => (h (i :: p.2) (by simp only [List.length_cons]; have hh := hc p hp; omega) Y).state) j
  have hLres (r : ℝ) (j : Fin 2) := (((hL (Y + r • basisVec i) j).sub (hL Y j)).const_smul r⁻¹).sub (hL₁ j)
  have htL j := molecularWordHilbertFlux_directional_integral_tendsto_zero hab G slice w Y i C₀ C₁ C₂
    (fun p hp => hC₂ p.1 (hg p hp).le) (fun p hp => hr p.1 (hg p hp).le)
    (fun p _ => hm p.1) (fun p hp => hb p.1 (hg p hp).le)
    (fun p hp => hD p.1 (hg p hp).le) (fun p hp => hDD p.1 (hg p hp).le)
    (fun p hp t => hcons p.1 (hg p hp) i t Y)
    (fun p hp X => (h p.2 (hc p hp).le X).state)
    (fun p hp => (h (i :: p.2) (by simp only [List.length_cons]; have hh := hc p hp; omega) Y).state)
    hquot j
  have heq (r t : ℝ) (j : Fin 2) : r⁻¹ • (VF (Y + r • basisVec i) t j - VF Y t j) - VF₁ t j =
      (r⁻¹ • (F w (Y + r • basisVec i) t j - F w Y t j) - F (i :: w) Y t j) +
      (r⁻¹ • (L (Y + r • basisVec i) t j - L Y t j) - L₁ t j) := by
    dsimp only [VF, VF₁]
    rw [show F w (Y + r • basisVec i) t j + L (Y + r • basisVec i) t j -
      (F w Y t j + L Y t j) = (F w (Y + r • basisVec i) t j - F w Y t j) +
        (L (Y + r • basisVec i) t j - L Y t j) by abel, smul_add]
    abel
  have hVFres (r : ℝ) (j : Fin 2) : MemLp (fun t => r⁻¹ • (VF (Y + r • basisVec i) t j - VF Y t j) -
      VF₁ t j) 2 (volume.restrict (Icc a b)) := by
    simpa only [heq, Pi.add_apply] using! (hFres r j).add (hLres r j)
  have htVF j : Tendsto (fun r : ℝ => ∫ t in a..b,
      ‖r⁻¹ • (VF (Y + r • basisVec i) t j - VF Y t j) - VF₁ t j‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [heq, Pi.smul_apply, Pi.sub_apply] using window_normSq_add_integral_tendsto_zero (𝓝[≠] 0) hab _ _
      (fun r => hFres r j) (fun r => hLres r j) (htF j) (htL j)
  have hd : CellWeakHilbertCurve a b (u (i :: w) Y) (slice (i :: w) Y)
      (fun t => dataDualDerivative (Q Y) t (slice (i :: w) Y t) (S (i :: w) Y t)
        (fun j => VF₁ t j + molecularMetricHilbertFlux
          (Matrix.of (fun j k => fderiv ℝ (fun X => G [] t X j k) Y (basisVec i))) (slice w Y t) j)) := by
    apply (h (i :: w) hn Y).dual_congr
    exact Filter.Eventually.of_forall (fun t => by
      apply congrArg (dataDualDerivative (Q Y) t (slice (i :: w) Y t) (S (i :: w) Y t))
      funext j
      rw [molecularWordHilbertFlux_cons]
      change F (i :: w) Y t j + (molecularMetricHilbertFlux (G [i] t Y) (slice w Y t) j + L₁ t j) = _
      rw [hcons [] (by simp; omega) i t Y]
      dsimp only [VF₁]
      abel)
  exact molecular_parameter_variable_source_directional_tendsto hab P (S w) (S (i :: w) Y)
    VF VF₁ (fun X t => G [] t X) (hr [] (by simp)) (hm []) (C₀ []) (C₁ []) (C₂ [])
    (hC₂ [] (by simp)) (fun X t => hb [] (by simp) t X) he
    (hD [] (by simp)) (hDD [] (by simp)) (u w) (slice w)
    (h w hw.le) (hi w hw.le) Y (basisVec i) (u (i :: w) Y) (slice (i :: w) Y) hd
    (hi (i :: w) hn Y) hSres hVFres htS htVF
end

/-! Strict lower-word induction identifies every actual ordered-word derivative. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {d : ℕ}

theorem molecular_word_Hilbert_family_derivatives {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (P : MolecularData)
    (G : List (Fin d) → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (C₀ C₁ C₂ : List (Fin d) → ℝ)
    (hC₂ : ∀ p, p.length ≤ N → 0 ≤ C₂ p)
    (hr : ∀ p, p.length ≤ N → ∀ t j k, ContDiff ℝ 2 (fun X => G p t X j k))
    (hm : ∀ p X j k, Measurable (fun t => G p t X j k))
    (hb : ∀ p, p.length ≤ N → ∀ t X j k, |G p t X j k| ≤ C₀ p)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G [] t X i j * ξ i * ξ j)
    (hD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fun Z => G p t Z j k) X‖ ≤ C₁ p)
    (hDD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fderiv ℝ (fun Z => G p t Z j k)) X‖ ≤ C₂ p)
    (hcons : ∀ p, p.length < N → ∀ i t Y,
      G (i :: p) t Y = Matrix.of (fun j k => fderiv ℝ (fun X => G p t X j k) Y (basisVec i)))
    (S : List (Fin d) → Vec d → ℝ → ComplexCellL2)
    (F : List (Fin d) → Vec d → ℝ → Fin 2 → ComplexCellL2)
    (u : List (Fin d) → Vec d → ℝ → ComplexCellL2)
    (slice : List (Fin d) → Vec d → ℝ → TorusHk 1 ℂ)
    (h : ∀ w, w.length ≤ N → ∀ X, CellWeakHilbertCurve a b (u w X) (slice w X)
      (fun t => dataDualDerivative
        (molecularMetricReplacement P (fun t => G [] t X) (C₀ []) (hm [] X)
          (fun t => hb [] (by simp) t X) (he X)) t (slice w X t) (S w X t)
        (fun j => F w X t j + molecularWordHilbertFlux (fun p t => G p t X)
          (fun p => slice p X) w t j)))
    (hi : ∀ w, w.length ≤ N → ∀ X, u w X a = 0)
    (hSres : ∀ w : List (Fin d), w.length < N → ∀ Y i, ∀ r : ℝ, MemLp (fun t => r⁻¹ • (S w (Y + r • basisVec i) t - S w Y t) -
      S (i :: w) Y t) 2 (volume.restrict (Icc a b)))
    (hFres : ∀ w : List (Fin d), w.length < N → ∀ Y i, ∀ r : ℝ, ∀ j, MemLp (fun t => r⁻¹ • (F w (Y + r • basisVec i) t j - F w Y t j) -
      F (i :: w) Y t j) 2 (volume.restrict (Icc a b)))
    (htS : ∀ w : List (Fin d), w.length < N → ∀ Y i, Tendsto (fun r : ℝ => ∫ t in a..b,
      ‖r⁻¹ • (S w (Y + r • basisVec i) t - S w Y t) - S (i :: w) Y t‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0))
    (htF : ∀ w : List (Fin d), w.length < N → ∀ Y i, ∀ j, Tendsto (fun r : ℝ => ∫ t in a..b,
      ‖r⁻¹ • (F w (Y + r • basisVec i) t j - F w Y t j) - F (i :: w) Y t j‖ ^ 2)
      (𝓝[≠] 0) (𝓝 0)) :
    ∀ w : List (Fin d), w.length < N → ∀ Y i,
    (∀ t ∈ Icc a b, Tendsto (fun r : ℝ => r⁻¹ • (u w (Y + r • basisVec i) t - u w Y t) -
      u (i :: w) Y t) (𝓝[≠] 0) (𝓝 0)) ∧
    Tendsto (fun r : ℝ => ∫ t in a..b, ∑ j,
      ‖cellDerivativeCLM j (r⁻¹ • (slice w (Y + r • basisVec i) t - slice w Y t) -
        slice (i :: w) Y t)‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  intro w hw
  generalize hn : w.length = n
  induction n using Nat.strong_induction_on generalizing w with
  | h n ih =>
    intro Y i
    apply molecular_word_Hilbert_derivative_step hab N P G C₀ C₁ C₂ hC₂ hr hm hb he hD hDD
      hcons S F u slice h hi w hw Y i (hSres w hw Y i) (hFres w hw Y i)
      (htS w hw Y i) (htF w hw Y i)
    intro p hp
    have hl := (independentWordForcing_lengths w p hp).2.2
    exact (ih p.2.length (by omega) p.2 (by omega) rfl Y i).2
end

/-! Strict lower-word induction identifies every actual ordered-word derivative. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {d H : ℕ}

theorem molecular_primitive_word_Hilbert_family_derivatives {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (hN : N + 2 ≤ H) (P : MolecularData)
    (G : List (Fin d) → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (C₀ C₁ C₂ : List (Fin d) → ℝ)
    (hC₂ : ∀ p, p.length ≤ N → 0 ≤ C₂ p)
    (hr : ∀ p, p.length ≤ N → ∀ t j k, ContDiff ℝ 2 (fun X => G p t X j k))
    (hm : ∀ p X j k, Measurable (fun t => G p t X j k))
    (hb : ∀ p, p.length ≤ N → ∀ t X j k, |G p t X j k| ≤ C₀ p)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G [] t X i j * ξ i * ξ j)
    (hD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fun Z => G p t Z j k) X‖ ≤ C₁ p)
    (hDD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fderiv ℝ (fun Z => G p t Z j k)) X‖ ≤ C₂ p)
    (hcons : ∀ p, p.length < N → ∀ i t Y,
      G (i :: p) t Y = Matrix.of (fun j k => fderiv ℝ (fun X => G p t X j k) Y (basisVec i)))
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : Fin 2 → ℝ → Vec 2 → Vec d → ℂ}
    (Qf : IndependentParameterSourceReserve H f)
    (QF : ∀ j, IndependentParameterSourceReserve H (F j))
    (u : List (Fin d) → Vec d → ℝ → ComplexCellL2)
    (slice : List (Fin d) → Vec d → ℝ → TorusHk 1 ℂ)
    (h : ∀ w, w.length ≤ N → ∀ X, CellWeakHilbertCurve a b (u w X) (slice w X)
      (fun t => dataDualDerivative
        (molecularMetricReplacement P (fun t => G [] t X) (C₀ []) (hm [] X)
          (fun t => hb [] (by simp) t X) (he X)) t (slice w X t) (coordinateWordHilbertSource f w X t)
        (fun j => coordinateWordHilbertSource (F j) w X t + molecularWordHilbertFlux (fun p t => G p t X)
          (fun p => slice p X) w t j)))
    (hi : ∀ w, w.length ≤ N → ∀ X, u w X a = 0) :
    ∀ w : List (Fin d), w.length < N → ∀ Y i,
    (∀ t ∈ Icc a b, Tendsto (fun r : ℝ => r⁻¹ • (u w (Y + r • basisVec i) t - u w Y t) -
      u (i :: w) Y t) (𝓝[≠] 0) (𝓝 0)) ∧
    Tendsto (fun r : ℝ => ∫ t in a..b, ∑ j,
      ‖cellDerivativeCLM j (r⁻¹ • (slice w (Y + r • basisVec i) t - slice w Y t) -
        slice (i :: w) Y t)‖ ^ 2) (𝓝[≠] 0) (𝓝 0) := by
  have htS w (hw : w.length < N) Y i :=
    coordinate_source_word_slice_window_taylor Qf w (by omega) hab Y i
  have htF w (hw : w.length < N) Y i j :=
    coordinate_source_word_slice_window_taylor (QF j) w (by omega) hab Y i
  exact molecular_word_Hilbert_family_derivatives hab N P G C₀ C₁ C₂ hC₂ hr hm hb he hD hDD
    hcons (coordinateWordHilbertSource f) (fun w X t j => coordinateWordHilbertSource (F j) w X t)
    u slice h hi (fun w hw Y i => (htS w hw Y i).1)
    (fun w hw Y i r j => (htF w hw Y i j).1 r)
    (fun w hw Y i => (htS w hw Y i).2) (fun w hw Y i j => (htF w hw Y i j).2)
end

end AVRegularity.WeakEntryProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.WeakEntryProofs

/-! Uniform genuine primitive budgets produce higher carriers for every finite ordered inverse word. -/

open AVRegularity.EntryWeakProofs
variable {I Y : Type*}

theorem uniform_word_finite_window_carrier {a b : ℝ} (hab : a < b)
    (N H : ℕ) (P : Y → MolecularData)
    (G : Y → List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (src : Y → List I → ℝ → Vec 2 → ℂ)
    (F : Y → List I → ℝ → Vec 2 → ComplexCellVector)
    (c : Y → List I → ℝ → RawJet2 1 ℂ)
    (Cv : ℕ → ℝ) (hCv : ∀ K, 0 ≤ Cv K)
    (hv : ∀ y K, K ≤ H → ∀ t, ContDiff ℝ (K : ℕ∞) ((P y).v t))
    (hp : ∀ y t, AVenhance.IsZ2Periodic ((P y).v t))
    (hb : ∀ y K, K ≤ H → ∀ t j, j ≤ K → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun z => (P y).v t z k) x‖ ≤ Cv K)
    (Q : ∀ y w, w.length ≤ N → ∀ K, K + w.length ≤ H →
      HigherSourceCarrierData (Icc a b) K (src y w) (F y w))
    (Ns Nf : List I → ℕ → ℝ)
    (hQs : ∀ y w hw K hK, (Q y w hw K hK).Ns ≤ Ns w K)
    (hQf : ∀ y w hw K hK, (Q y w hw K hK).Nf ≤ Nf w K)
    (B : List I → ℝ) (hB : ∀ w, w.length ≤ N → 0 ≤ B w)
    (hGb : ∀ y w, w.length ≤ N → ∀ t i j, |G y w t i j| ≤ B w)
    (hGm : ∀ y w, w.length ≤ N → ∀ i j, Measurable (fun t => G y w t i j))
    (hsol : ∀ y w, w.length ≤ N → IsCellSolution (Icc a b) (dataCoefficients (P y)) (src y w)
      (F y w + independentWordMetricFlux (fun p t _ => G y p t) (c y) w) (c y w))
    (hi : ∀ y w, w.length ≤ N → cellValue (c y w) a =ᵐ[volume.restrict AVenhance.unitCube] 0)
    (w : List I) (hw : w.length ≤ N) (K : ℕ) (hK : K + w.length ≤ H) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk K ℂ,
      StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (c y w) t := by
  classical
  have main (n : ℕ) : ∀ w : List I, w.length = n → w.length ≤ N → ∀ K,
      K + w.length ≤ H → ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk K ℂ,
        StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (c y w) t := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro w hn hw K hK
      have hall (p : List I) : ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ u : ℝ → TorusHk (K + 1) ℂ,
          StronglyMeasurable u ∧ (∀ t, ‖u t‖ ≤ R) ∧
          (p.length < w.length → ∀ t ∈ Icc a b,
            torusHkValueCLM (u t) =ᵐ[volume.restrict AVenhance.unitCube] cellValue (c y p) t) := by
        by_cases hp : p.length < w.length
        · obtain ⟨R, hR, hh⟩ := ih p.length (by omega) p rfl (by omega) (K + 1) (by omega)
          refine ⟨R, hR, fun y => ?_⟩
          obtain ⟨u, hum, hub, hue⟩ := hh y
          exact ⟨u, hum, hub, fun _ => hue⟩
        · exact ⟨0, le_rfl, fun _ => ⟨0, stronglyMeasurable_const,
            (fun _ => by simp), fun h => (hp h).elim⟩⟩
      choose R hR u hum hub hue using hall
      let r := ((independentWordForcing w).map
        (fun p => B p.1 * metricGradientCarrierConstant K * R p.2)).sum
      have hr : 0 ≤ r := by
        apply List.sum_nonneg
        intro x hx
        obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
        have hl := independentWordForcing_lengths w p hp
        exact mul_nonneg (mul_nonneg (hB p.1 (by omega)) (metricGradientCarrierConstant_nonneg K)) (hR p.2)
      let Rbound := higherSourceWindowTraceBound a b K (Cv K) (Ns w K) (Nf w K + r)
      refine ⟨Rbound, Real.sqrt_nonneg _, ?_⟩
      intro y
      let Qbase := Q y w hw K hK
      have hl p (hp : p ∈ independentWordForcing w) := independentWordForcing_lengths w p hp
      obtain ⟨Qnext, hs, hf⟩ := Qbase.metricFluxList_exists (independentWordForcing w)
        (fun p => G y p.1) (fun p => c y p.2) (fun p => u p.2 y)
        (fun p => B p.1) (fun p => R p.2)
        (fun p hp => hB p.1 (by have hh := hl p hp; omega))
        (fun p _ => hR p.2)
        (fun p hp => hGm y p.1 (by have hh := hl p hp; omega))
        (fun p hp => hGb y p.1 (by have hh := hl p hp; omega))
        (fun p _ => hum p.2 y) (fun p _ => hub p.2 y)
        (fun p hp => (hsol y p.2 (by have hh := hl p hp; omega)).2.1)
        (fun p hp => ae_restrict_of_forall_mem measurableSet_Icc
          (hue p.2 y (hl p hp).2.2))
        (fun p hp => cell_window_metric_flux_memLp hab.le _
          (Measurable.of_eval (fun i => Measurable.of_eval (fun j =>
            (hGm y p.1 (by have hh := hl p hp; omega) i j).comp measurable_fst)))
          (B p.1) (hB p.1 (by have hh := hl p hp; omega))
          (fun t _ => hGb y p.1 (by have hh := hl p hp; omega) t)
          (hsol y p.2 (by have hh := hl p hp; omega)))
      obtain ⟨v, hvm, hvb, hve⟩ := higher_source_window_carrier_exists hab Qnext
        (Cv K) (hCv K) (hv y K (by omega)) (hp y) (hb y K (by omega))
        (c y w) (hsol y w hw) (hi y w hw)
      refine ⟨v, hvm, fun t => (hvb t).trans ?_, hve⟩
      change higherSourceWindowTraceBound a b K (Cv K) Qnext.Ns Qnext.Nf ≤ Rbound
      apply higherSourceWindowTraceBound_mono hab.le K (Cv K)
        Qnext.scalar_budget_nonneg Qnext.flux_budget_nonneg
      · rw [hs]
        exact hQs y w hw K hK
      · rw [hf]
        exact add_le_add (hQf y w hw K hK) (le_refl r)

  exact main w.length w rfl hw K hK

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Strict lower-word induction identifies every actual ordered-word derivative. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set Filter Topology
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
variable {d H : ℕ}

theorem molecular_primitive_word_Hilbert_family_contDiff {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (hN : N + 2 ≤ H) (P : MolecularData)
    (G : List (Fin d) → ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (C₀ C₁ C₂ : List (Fin d) → ℝ)
    (hC₂ : ∀ p, p.length ≤ N → 0 ≤ C₂ p)
    (hr : ∀ p, p.length ≤ N → ∀ t j k, ContDiff ℝ 2 (fun X => G p t X j k))
    (hm : ∀ p X j k, Measurable (fun t => G p t X j k))
    (hb : ∀ p, p.length ≤ N → ∀ t X j k, |G p t X j k| ≤ C₀ p)
    (he : ∀ X t (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤
      ∑ i, ∑ j, G [] t X i j * ξ i * ξ j)
    (hD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fun Z => G p t Z j k) X‖ ≤ C₁ p)
    (hDD : ∀ p, p.length ≤ N → ∀ t j k X,
      ‖fderiv ℝ (fderiv ℝ (fun Z => G p t Z j k)) X‖ ≤ C₂ p)
    (hcons : ∀ p, p.length < N → ∀ i t Y,
      G (i :: p) t Y = Matrix.of (fun j k => fderiv ℝ (fun X => G p t X j k) Y (basisVec i)))
    {f : ℝ → Vec 2 → Vec d → ℂ} {F : Fin 2 → ℝ → Vec 2 → Vec d → ℂ}
    (Qf : IndependentParameterSourceReserve H f)
    (QF : ∀ j, IndependentParameterSourceReserve H (F j))
    (u : List (Fin d) → Vec d → ℝ → ComplexCellL2)
    (slice : List (Fin d) → Vec d → ℝ → TorusHk 1 ℂ)
    (h : ∀ w, w.length ≤ N → ∀ X, CellWeakHilbertCurve a b (u w X) (slice w X)
      (fun t => dataDualDerivative
        (molecularMetricReplacement P (fun t => G [] t X) (C₀ []) (hm [] X)
          (fun t => hb [] (by simp) t X) (he X)) t (slice w X t) (coordinateWordHilbertSource f w X t)
        (fun j => coordinateWordHilbertSource (F j) w X t + molecularWordHilbertFlux (fun p t => G p t X)
          (fun p => slice p X) w t j)))
    (hi : ∀ w, w.length ≤ N → ∀ X, u w X a = 0) :
    ∀ w : List (Fin d), ∀ r : ℕ, w.length + r ≤ N → ∀ t ∈ Icc a b,
      ContDiff ℝ (r : ℕ∞) (fun Y => u w Y t) := by
  let δ := fun (w : List (Fin d)) (Y X : Vec d) => C₁ w * ‖X - Y‖
  have hd w (hw : w.length ≤ N) (X Y : Vec d) (t : ℝ) (j k : Fin 2) :
      |G w t X j k - G w t Y j k| ≤ δ w Y X :=
    independent_parameter_lipschitz (fun Z => G w t Z j k)
      ((hr w hw t j k).of_le (by norm_num)) (C₁ w) (hD w hw t j k) Y X
  have hδ w (_hw : w.length ≤ N) (Y : Vec d) : Tendsto (δ w Y) (𝓝 Y) (𝓝 0) := by
    have hc : Continuous (δ w Y) := continuous_const.mul (continuous_id.sub continuous_const).norm
    simpa only [δ, sub_self, norm_zero, mul_zero] using hc.tendsto Y
  have hc := molecular_primitive_word_Hilbert_family_continuous hab N (by omega) P
    (fun w Y t => G w t Y) C₀ (fun w Y => hm w Y)
    (fun w hw Y t => hb w hw t Y) he δ hd hδ Qf QF u slice h hi
  have hder := molecular_primitive_word_Hilbert_family_derivatives hab N hN P G C₀ C₁ C₂
    hC₂ hr hm hb he hD hDD hcons Qf QF u slice h hi
  intro w r hwr t ht
  apply finite_coordinate_word_family_contDiff d N (fun p Y => u p Y t) _ _ w r hwr
  · intro p hp
    apply continuous_iff_continuousAt.mpr
    intro Y
    exact tendsto_sub_nhds_zero_iff.mp ((hc p hp Y).1 t ht)
  · intro p hp i Y
    rw [hasDerivAt_iff_tendsto_slope_zero]
    simpa only [zero_add, zero_smul, add_zero] using
      tendsto_sub_nhds_zero_iff.mp ((hder p hp Y i).1 t ht)
end

/-! Genuine primitive coordinate words produce their actual finite-window raw equations. -/

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution
open scoped ContDiff
variable {d H : ℕ}

theorem coordinate_word_window_family_exists {a b : ℝ} (hab : a ≤ b)
    (K : ℕ) (hK : K ≤ H) (P : Vec d → MolecularData)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F) :
    ∃ c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ, ∀ Y w, w.length ≤ K →
      IsCellSolution (Icc a b) (dataCoefficients (P Y))
        (fun t => cellQ0 (coordinateSourceWord f w Y t))
        (coordinateSourceWord F w Y + independentWordMetricFlux
          (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y) ∧
      cellValue (c w Y) a =ᵐ[volume.restrict AVenhance.unitCube] (fun _ => 0) := by
  classical
  have hex (Y : Vec d) := word_window_inverse_family_exists hab K (P Y)
    (fun w t => independentMetricWordJet G w.length (coordinateWordDirections w) Y t)
    (fun w => B w.length) (fun w t => cellQ0 (coordinateSourceWord f w Y t))
    (fun w => coordinateSourceWord F w Y) (fun w hw => by
      let Q := coordinateWordHigherSourceData Qf QF w 0 (by omega) a b Y
      exact ⟨hB _, general_metric_word_entry_measurable hr hm _ _ Y,
        general_metric_word_entry_bound hr B hb _ (hw.trans hK) _
          (coordinateWordDirections_norm w) Y, Q.scalar_memLp, Q.flux_memLp⟩)
  choose c hc using hex
  exact ⟨fun w Y => c Y w, fun Y w hw => hc Y w hw⟩
end

end AVRegularity.WeakEntryProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.WeakEntryProofs

/-! The exact triangular parameter difference equations produce uniform higher quotient carriers. -/

open AVRegularity.EntryWeakProofs

theorem uniform_word_window_difference_higher_carrier_exists {Y I : Type*}
    {a b : ℝ} (hab : a < b) (N Hmax : ℕ) (P : Y → MolecularData)
    (G H : Y → List I → ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (hP : ∀ y, dataCoefficients (P y) = ⟨fun t _ => G y [] t, (P y).v, 0, 0⟩)
    (f g : Y → List I → ℝ → Vec 2 → ℂ)
    (F F' : Y → List I → ℝ → Vec 2 → ComplexCellVector)
    (D E : Y → List I → ℝ → RawJet2 1 ℂ) (r : Y → ℝ)
    (hGsym : ∀ y t, (G y [] t).IsSymm) (hHsym : ∀ y t, (H y [] t).IsSymm)
    (hD : ∀ y (α : List I), α.length ≤ N →
      IsCellSolution (Icc a b) (dataCoefficients (P y)) (f y α)
        (F y α + independentWordMetricFlux (fun β t _ => G y β t) (D y) α) (D y α))
    (hE : ∀ y (α : List I), α.length ≤ N →
      IsCellSolution (Icc a b) ⟨fun t _ => H y [] t, (P y).v, 0, 0⟩ (g y α)
        (F' y α + independentWordMetricFlux (fun β t _ => H y β t) (E y) α) (E y α))
    (Cv : ℕ → ℝ) (hCv : ∀ K, 0 ≤ Cv K)
    (hv : ∀ y K, K ≤ Hmax → ∀ t, ContDiff ℝ (K : ℕ∞) ((P y).v t))
    (hp : ∀ y t, AVenhance.IsZ2Periodic ((P y).v t))
    (hvb : ∀ y K, K ≤ Hmax → ∀ t j, j ≤ K → ∀ k x,
      ‖iteratedFDeriv ℝ j (fun z => (P y).v t z k) x‖ ≤ Cv K)
    (Q : ∀ y (α : List I), α.length ≤ N → ∀ K, K ≤ Hmax →
      HigherSourceCarrierData (Icc a b) K (r y • (g y α - f y α)) (r y • (F' y α - F y α)))
    (Ns Nf : List I → ℕ → ℝ)
    (hNs : ∀ α K, 0 ≤ Ns α K) (hNf : ∀ α K, 0 ≤ Nf α K)
    (hQs : ∀ y α hα K hK, (Q y α hα K hK).Ns ≤ Ns α K)
    (hQf : ∀ y α hα K hK, (Q y α hα K hK).Nf ≤ Nf α K)
    (B Bδ : List I → ℝ)
    (hB : ∀ α : List I, α.length ≤ N → 0 ≤ B α)
    (hBδ : ∀ α : List I, α.length ≤ N → 0 ≤ Bδ α)
    (hb : ∀ y (α : List I), α.length ≤ N → ∀ t i j, |G y α t i j| ≤ B α)
    (hm : ∀ y (α : List I), α.length ≤ N → ∀ i j, Measurable (fun t => G y α t i j))
    (hbδ : ∀ y (α : List I), α.length ≤ N → ∀ t i j,
      |r y * (H y α t i j - G y α t i j)| ≤ Bδ α)
    (hmδ : ∀ y (α : List I), α.length ≤ N → ∀ i j,
      Measurable (fun t => r y * (H y α t i j - G y α t i j)))
    (hcarrier : ∀ α : List I, α.length ≤ N → ∀ K, K ≤ Hmax + 1 →
      ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ w : ℝ → TorusHk K ℂ,
        StronglyMeasurable w ∧ (∀ t, ‖w t‖ ≤ R) ∧
        ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube]
          cellValue (E y α) t)
    (hiD : ∀ y (α : List I), α.length ≤ N → cellValue (D y α) a =ᵐ[
      volume.restrict AVenhance.unitCube] 0)
    (hiE : ∀ y (α : List I), α.length ≤ N → cellValue (E y α) a =ᵐ[
      volume.restrict AVenhance.unitCube] 0)
    (α : List I) (hα : α.length ≤ N) (K : ℕ) (hK : K + α.length ≤ Hmax) :
    ∃ R : ℝ, 0 ≤ R ∧ ∀ y, ∃ w : ℝ → TorusHk K ℂ,
      StronglyMeasurable w ∧ (∀ t, ‖w t‖ ≤ R) ∧
      ∀ t ∈ Icc a b, torusHkValueCLM (w t) =ᵐ[volume.restrict AVenhance.unitCube]
        cellValue (r y • (E y α - D y α)) t := by
  let A := fun y β t => r y • (H y β t - G y β t)
  let q := fun y β => r y • (E y β - D y β)
  let src := fun y β => r y • (g y β - f y β)
  let flux := fun y β => (r y • (F' y β - F y β) +
    independentWordMetricFlux (fun γ t _ => A y γ t) (E y) β) +
      cellMetricFlux (fun t _ => A y [] t) (E y β)
  have hAb (y : Y) (β : List I) (hβ : β.length ≤ N) :
      ∀ t i j, |A y β t i j| ≤ Bδ β := hbδ y β hβ
  have hAm (y : Y) (β : List I) (hβ : β.length ≤ N) :
      ∀ i j, Measurable (fun t => A y β t i j) := hmδ y β hβ
  have hprod (β : List I) (hβ : β.length ≤ N) (L : ℕ) (hL : L ≤ Hmax) :
      ∃ Rs Rf : ℝ, 0 ≤ Rs ∧ 0 ≤ Rf ∧ ∀ y,
        ∃ Q' : HigherSourceCarrierData (Icc a b) L (src y β) (flux y β),
          Q'.Ns ≤ Rs ∧ Q'.Nf ≤ Rf := by
    exact uniform_word_window_perturbed_higher_source_exists a b hab.le N L A E
      (fun y => ⟨fun t _ => H y [] t, (P y).v, 0, 0⟩) g
      (fun y γ => F' y γ + independentWordMetricFlux (fun δ t _ => H y δ t) (E y) γ)
      hE Bδ hBδ hAb hAm β hβ
      (fun γ hγ => hcarrier γ (by omega) (L + 1) (by omega))
      (fun y => src y β) (fun y => r y • (F' y β - F y β))
      (fun y => Q y β hβ L hL) (Ns β L) (Nf β L) (hNs β L) (hNf β L)
      (fun y => hQs y β hβ L hL) (fun y => hQf y β hβ L hL)
  obtain ⟨Rs, Rf, _hRs, _hRf, Q', hQ's, hQ'f⟩ :=
    uniform_word_higher_source_selection (Icc a b) N Hmax src flux
      (fun β hβ L hL => hprod β hβ L (by omega))
  have hq (y : Y) (β : List I) (hβ : β.length ≤ N) :
      IsCellSolution (Icc a b) (dataCoefficients (P y)) (src y β)
        (flux y β + independentWordMetricFlux (fun γ t _ => G y γ t) (q y) β) (q y β) :=
    by
      have hd := hD y β hβ
      rw [hP y] at hd ⊢
      exact independent_word_window_difference_solution (Icc a b)
        (fun γ t _ => G y γ t) (fun γ t _ => H y γ t) (P y).v
        (f y) (g y) (F y) (F' y) (D y) (E y) β (r y)
        (fun t _ => hGsym y t) (fun t _ => hHsym y t) hd (hE y β hβ)
  apply uniform_word_finite_window_carrier hab N Hmax P G src flux q
    Cv hCv hv hp hvb (fun y β hβ L hL => Q' y β hβ L (by omega))
    Rs Rf (fun y β hβ L hL => hQ's y β hβ L (by omega))
    (fun y β hβ L hL => hQ'f y β hβ L (by omega)) B hB hb hm hq
  · intro y β hβ
    filter_upwards [hiD y β hβ, hiE y β hβ] with z hzD hzE
    change r y • (E y β a (valueIndex2 1) z - D y β a (valueIndex2 1) z) = 0
    simp only [cellValue] at hzD hzE
    rw [hzD, hzE, sub_self, smul_zero]
  · exact hα
  · exact hK

end AVRegularity.WeakEntryProofs
end

section
namespace AVRegularity.WeakEntryProofs

/-! Canonical traces of the actual raw coordinate words obey the primitive Hilbert equations. -/

open MeasureTheory Homogenization AVRegularity.Sobolev Set
open AVRegularity.EntryWeakProofs AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open scoped ContDiff
variable {d H : ℕ}

theorem coordinate_word_raw_Hilbert_curves {a b : ℝ} (hab : a ≤ b)
    (N : ℕ) (hN : N ≤ H) (P : Vec d → MolecularData)
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    (hr : ∀ t i j, ContDiff ℝ ∞ (fun X => G t X i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (hs : ∀ t Y, (G t Y).IsSymm)
    (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n)
    (hb : ∀ n, n ≤ H → ∀ t Y i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n)
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    (hf : ∀ t Y, fieldCellMean (fun z => f t z Y) = 0)
    (c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ)
    (hsol : ∀ Y w, w.length ≤ N → IsCellSolution (Icc a b) (dataCoefficients (P Y))
      (fun t => cellQ0 (coordinateSourceWord f w Y t))
      (coordinateSourceWord F w Y + independentWordMetricFlux
        (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y))
    (hi : ∀ Y w, w.length ≤ N →
      cellValue (c w Y) a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ w, w.length ≤ N → ∀ Y,
      CellWeakHilbertCurve a b (cellRawTrace (c w Y)) (cellH1Slice (c w Y))
        (fun t => dataDualDerivative (P Y) t (cellH1Slice (c w Y) t)
          (coordinateWordHilbertSource f w Y t)
          (fun j => coordinateWordHilbertSource (fun s z X => F s z X j) w Y t +
            molecularWordHilbertFlux
              (fun p t => independentMetricWordJet G p.length (coordinateWordDirections p) Y t)
              (fun p => cellH1Slice (c p Y)) w t j)) ∧ cellRawTrace (c w Y) a = 0 := by
  have hq (w : List (Fin d)) (hw : w.length ≤ N) Y :
      (fun t => cellQ0 (coordinateSourceWord f w Y t)) = coordinateSourceWord f w Y :=
    funext (fun t => coordinate_source_word_Q0_eq_self Qf hf w (hw.trans hN) t Y)
  have hraw (Y : Vec d) (w : List (Fin d)) (hw : w.length ≤ N) :
      IsCellSolution (Icc a b) (dataCoefficients (P Y)) (coordinateSourceWord f w Y)
        (coordinateSourceWord F w Y + independentWordMetricFlux
          (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y) := by
    have hh := hsol Y w hw
    rw [hq w hw Y] at hh
    exact hh
  have hmem {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
      {f : ℝ → Vec 2 → Vec d → E} (Q : IndependentParameterSourceReserve H f)
      (w : List (Fin d)) (hw : w.length ≤ N) Y :
      MemLp (Function.uncurry (coordinateSourceWord f w Y)) 2
        ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)) :=
    independent_source_window_memLp (Q.wordJet w.length 0 (by omega)
      (coordinateWordDirections w) (coordinateWordDirections_norm w)) a b Y
  intro w hw Y
  have hc := word_window_raw_to_Hilbert hab N (P Y)
    (fun p t => independentMetricWordJet G p.length (coordinateWordDirections p) Y t)
    (fun p => B p.length) (fun p => coordinateSourceWord f p Y)
    (fun p => coordinateSourceWord F p Y) (fun p => c p Y)
    (fun _ _ => hB _) (fun p _ => general_metric_word_entry_measurable hr hm _ _ Y)
    (fun p hp => general_metric_word_entry_bound hr B hb _ (hp.trans hN) _
      (coordinateWordDirections_norm p) Y)
    (fun p hp => hmem Qf p hp Y) (fun p hp => by simpa only using! hmem QF p hp Y)
    (hraw Y) w hw
  have htranspose : (fun p t => (independentMetricWordJet G p.length
      (coordinateWordDirections p) Y t).transpose) =
      fun p t => independentMetricWordJet G p.length (coordinateWordDirections p) Y t :=
    funext (fun p => funext (fun t => coordinate_metric_word_symm G hs p Y t))
  rw [htranspose] at hc
  have hproj (j : Fin 2) : (fun s z => coordinateSourceWord F w Y s z j) =
      coordinateSourceWord (fun s z X => F s z X j) w Y := by
    funext s z
    exact (coordinate_source_word_map QF (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j)
      w (hw.trans hN) Y s z).symm
  simp_rw [hproj] at hc
  refine ⟨hc, ?_⟩
  apply Lp.ext
  exact (cellRawTrace_ae (c w Y) a ((hraw Y w hw).2.2.1 a ⟨le_rfl, hab⟩).1).trans
    ((hi Y w hw).trans (by simpa only using! (Lp.coeFn_zero ℂ 2
      (volume.restrict AVenhance.unitCube)).symm))

end AVRegularity.WeakEntryProofs
end
