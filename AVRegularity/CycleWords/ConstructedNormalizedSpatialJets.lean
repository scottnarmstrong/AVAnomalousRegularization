-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.WeightedSmoothPullbackSequence
import AVRegularity.CycleDamping.ReferenceJetRegularity
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellLimitMoments
public import AVRegularity.CycleReference.ChartTestTransport
import AVRegularity.CycleReference.CorrectorMeanGeometry
import AVRegularity.CycleReference.SingleModeFlux
import AVRegularity.CycleWords.CellComplexH1Separability
import Mathlib.Algebra.Order.Star.Real

@[expose] public noncomputable section

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Literal time-window Taylor remainders keep their small factor and polynomial moment degree. -/

def slowRemainderTimeCoefficient (K : ℕ) (f : ℝ → Vec 2 → Vec 2 → ℝ)
    (a b : ℝ) (X0 : Vec 2) (δ : ℝ) (t : ℝ) (z : Vec 2) : ℝ :=
  if t ∈ Set.Icc a b then f t (X0 + δ • z) z -
    taylorSlow 0 K (fun X => f t X z) X0 (δ • z) else 0

theorem slowRemainder_time_coefficient_budget (K Nmax : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N ≤ Nmax, ∀ (f : ℝ → Vec 2 → Vec 2 → ℝ)
      (a b : ℝ) (X0 : Vec 2) (ϖ ρ δ ζ B : ℝ),
      (∀ X z, Measurable (fun t => f t X z)) →
      (∀ t ∈ Set.Icc a b, ContDiff ℝ (N + (K + 1) : ℕ) (Function.uncurry (f t))) →
      0 < ϖ → 0 < ρ → ρ * ϖ ≤ 1 → 0 ≤ ζ → 0 ≤ B → δ = ζ * ϖ →
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ r j : ℕ, r + j ≤ N → ∀ X z,
        ρ ^ (r + j) * |δ| ^ r *
          ‖iteratedFDeriv ℝ (K + 1 + r) (fun X' => iteratedFDeriv ℝ j (f t X') z) X‖ ≤ B) →
      (∀ z, Measurable (fun t => slowRemainderTimeCoefficient K f a b X0 δ t z)) ∧
      (∀ t, ContDiff ℝ (N : ℕ) (slowRemainderTimeCoefficient K f a b X0 δ t)) ∧
      (∀ᵐ t ∂volume.restrict (Set.Icc a b), ∀ j ≤ N, ∀ z,
        ρ ^ j * ‖iteratedFDeriv ℝ j (slowRemainderTimeCoefficient K f a b X0 δ t) z‖ ≤
          C * B * ζ ^ (K + 1) * polynomialMomentRoot ϖ z ^ (K + 1)) := by
  obtain ⟨C, hC, hb⟩ := slowRemainder_uniform_reserved_budget K Nmax
  refine ⟨C, hC, ?_⟩
  intro N hN f a b X0 ϖ ρ δ ζ B hm hf hϖ hρ hscale hζ hB hδ hjet
  refine ⟨?_, ?_, ?_⟩
  · intro z
    have hfs : ∀ t ∈ Set.Icc a b, ∀ z, ContDiff ℝ (K : ℕ) (fun X => f t X z) := by
      intro t ht z
      exact ((hf t ht).comp (contDiff_id.prodMk (contDiff_const (c := z)))).of_le
        (by exact_mod_cast (by omega : K ≤ N + (K + 1)))
    have hTaylor := Weighted.taylorSlow_time_window_measurable (Set.Icc a b) measurableSet_Icc
      0 K f hm hfs X0 δ z
    have hactual : Measurable (fun t => if t ∈ Set.Icc a b then f t (X0 + δ • z) z else 0) :=
      (hm (X0 + δ • z) z).piecewise measurableSet_Icc (measurable_const (a := (0 : ℝ)))
    convert hactual.sub hTaylor using 1
    funext t
    by_cases ht : t ∈ Set.Icc a b
    · simp only [slowRemainderTimeCoefficient, Pi.sub_apply, ite_eq_left ht]
    · simp only [slowRemainderTimeCoefficient, Pi.sub_apply, ite_eq_right ht, sub_self]
  · intro t
    by_cases ht : t ∈ Set.Icc a b
    · have heq : slowRemainderTimeCoefficient K f a b X0 δ t =
          (fun z => f t (X0 + δ • z) z - taylorSlow 0 K (fun X => f t X z) X0 (δ • z)) := by
        funext z
        simp only [slowRemainderTimeCoefficient, ite_eq_left ht]
      rw [heq]
      have hactual : ContDiff ℝ (N : ℕ) (fun z => f t (X0 + δ • z) z) :=
        ((hf t ht).comp
          (((contDiff_const (c := X0)).add (contDiff_id.const_smul δ)).prodMk contDiff_id)).of_le
            (by exact_mod_cast Nat.le_add_right N (K + 1))
      have hTaylor := Weighted.taylorSlow_spatial_contDiff 0 K N (f t)
        ((hf t ht).of_le (by exact_mod_cast (show K + N ≤ N + (K + 1) by omega))) X0 δ
      exact hactual.sub hTaylor
    · have heq : slowRemainderTimeCoefficient K f a b X0 δ t = (fun _ : Vec 2 => (0 : ℝ)) := by
        funext z
        simp only [slowRemainderTimeCoefficient, ite_eq_right ht]
      rw [heq]
      exact contDiff_const
  · filter_upwards [hjet, ae_restrict_mem measurableSet_Icc] with t ht htI
    have heq : slowRemainderTimeCoefficient K f a b X0 δ t =
        (fun z => f t (X0 + δ • z) z - taylorSlow 0 K (fun X => f t X z) X0 (δ • z)) := by
      funext z
      simp only [slowRemainderTimeCoefficient, ite_eq_left htI]
    rw [heq]
    exact hb N hN (f t) (hf t htI) ϖ ρ δ ζ B hϖ hρ hscale hζ hB hδ ht X0

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The literal actual geometry coupling flux is linear on the native
carrier readouts, including finite response sums. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem geometryActualFlux_eq_native_ordered (D : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (edge : ConstituentEdges D h)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin 1 → ι → ℕ)
    (U : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) (z : Vec 2) :
    geometryActualFlux D G edge X0 δ κ U i t z =
      nativeCoupledOrderFlux D (fun p => κ p.1 p.2)
        (fun i u d z => planeChainCoefficient (geometryActualData G edge X0 δ) κ i u d t z) U i z := by
  unfold geometryActualFlux nativeCoupledOrderFlux
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  congr 2
  funext w
  have hd := (Finset.mem_filter.mp d.property).2
  dsimp only at hd
  exact congrFun (planeJetOrder_eq_stored (show d.val - 1 ≤ κ u.1 u.2 + 1 by omega) (U u) w).symm z

theorem geometryActualFlux_sub_sum_ae {L : Type*} [Fintype L] (D : ℕ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (edge : ConstituentEdges D h)
    (X0 : Vec 2) (δ : ℝ) (κ : Fin 1 → ι → ℕ)
    (U : ∀ p : Fin 1 × ι, PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (Z : ∀ (_ : L) (p : Fin 1 × ι), PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (i : Fin 1 × ι) (t : ℝ) :
    geometryActualFlux D G edge X0 δ κ (fun u => U u - ∑ j, Z j u) i t =ᵐ[volume]
      (fun z => geometryActualFlux D G edge X0 δ κ U i t z -
        ∑ j, geometryActualFlux D G edge X0 δ κ (Z j) i t z) := by
  have hh := nativeCoupledOrderFlux_sub_sum_ae D (fun p => κ p.1 p.2)
    (fun i u d z => planeChainCoefficient (geometryActualData G edge X0 δ) κ i u d t z) U Z i
  filter_upwards [hh] with z hz
  simpa only [geometryActualFlux_eq_native_ordered] using hz

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Construction of the chart weights from the literal future-memory coordinates. -/

def adjointChartWeights {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {ν B T C : ℝ}
    (hν : 0 < ν) (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C)
    (he : ν + ocEpsilon q Λ m ^ (2 * (1 + α)) / ν ≤ C * B)
    (hellT : ocEll q Λ m ν ^ 2 ≤ T) (K : ℝ) (hK : 0 ≤ K)
    (hb : ∀ k t, |deriv (ocCutoff α q Λ m k) t| ≤ K / ocTau α q Λ m)
    (hdur : Real.sqrt T * ocEll q Λ m ν / ocTau α q Λ m *
      Real.exp (-Real.pi ^ 2 * ocTau α q Λ m / (3 * ocEll q Λ m ν ^ 2)) ≤ 1)
    (yc : Vec 2) (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ k j, ContDiff ℝ 1 (fun p : ℝ × Vec 2 => G p.1 p.2 k j))
    (hGsym : ∀ t z, (G t z).IsSymm) (g : ℝ) (hg : g ≤ 1 / 4)
    (t₀ : ℝ) (hGn : IsMetricNearIdentityOn (Set.Icc t₀ (t₀ + T / ocEll q Λ m ν ^ 2)) G g) (M : ℕ) :
    ChartWeights G (ocCellDrift α q Λ ζ m ν yc) t₀ (T / ocEll q Λ m ν ^ 2)
      (ocEpsilon q Λ m / Real.sqrt (B * T)) 0 M (adjointWeightConstant C K) := by
  let W := adjointCellPolynomialWeight α q Λ ζ m ν B T yc
  have hWp : ∀ n t z, 0 < W n t z := fun n t z =>
    adjointCellPolynomialWeight_pos α q Λ ζ m ν B T yc n t z
  have hWs : ∀ n, ContDiff ℝ 2 (fun p : ℝ × Vec 2 => W n p.1 p.2) := fun n =>
    adjointCellPolynomialWeight_joint_contDiff hΛ hζ ν B T yc n 2
  have hGs : ∀ t k j, Differentiable ℝ (fun z => G t z k j) := fun t k j =>
    ((hG k j).comp (contDiff_const.prodMk contDiff_id)).differentiable (by norm_num)
  have hellp : 0 < ocEll q Λ m ν ^ 2 := by
    have hep := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
    unfold ocEll
    positivity
  refine {
    W := W
    Phi := fun n t z k => metricCorrectionFlux (W n t) (G t) z k
    lam := fun n => adjointWeightRate C K n * (ocEll q Λ m ν ^ 2 / T)
    smooth := ?_
    pos := ?_
    comparable := ?_
    defect := ?_
    bound := ?_
    lam_bound := ?_ }
  · intro n _
    exact ⟨hWs n, metricCorrectionFlux_joint_contDiff (W n) (hWs n) G hG⟩
  · intro n _ t z
    exact hWp n t z
  · intro n _ t _ z
    have hh := adjointCellPolynomialWeight_comparable hΛ hζ hν hB hT hC he
      (by simpa only [CycleReference.ocEll_sq_eq hν] using hellT) yc n t z
    have hcomp := adjointWeightConstant_comparison hC hK n
    have hp := adjointWeightComparison_pos C n
    have hU : 0 ≤ (1 + (ocEpsilon q Λ m / Real.sqrt (B * T)) ^ 2 *
        (z 0 ^ 2 + z 1 ^ 2)) ^ n := by positivity
    have hew := weight_comparison_enlarge hU hp hcomp
      (show (adjointWeightComparison C n)⁻¹ * _ ≤ W n t z from hh.1)
      (show W n t z ≤ adjointWeightComparison C n * _ from hh.2)
    simpa only [Pi.zero_apply, sub_zero] using hew
  · intro n _ t _ z
    exact adjointPolynomial_metric_defect hΛ hζ hν hB hT hC he K hK hb hdur yc G hGs n t z
  · intro n _ t ht z
    exact adjointPolynomial_metric_gradient hΛ hζ hν hB hT hC hK he yc G n t z
      (fun i j => nearIdentityOn_entry_abs_le G hg hGn ht z (hGsym t z) i j)
  · intro n _
    refine ⟨mul_nonneg (adjointWeightRate_nonneg hC hK n) (div_pos hellp hT).le, ?_⟩
    have hi : adjointWeightRate C K n * (ocEll q Λ m ν ^ 2 / T) =
        adjointWeightRate C K n / (T / ocEll q Λ m ν ^ 2) := by field_simp
    rw [hi]
    exact div_le_div_of_nonneg_right (adjointWeightConstant_rate hC hK n)
      (div_pos hT hellp).le

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! Actual cell H1 fields of real plane H1 data, with exact physical readouts. -/

def centeredPlaneBlochRealH1Field
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) :
    Lp CellComplexH1 2 centeredPlaneFrequencyMeasure :=
  (centeredPlaneBlochRealH1_memLp f g hfg).toLp
    (planeBlochRealH1 centeredPlaneFrequencyBase f g)

theorem centeredPlaneBlochRealH1Field_jet_ae
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) :
    ∀ᵐ θ ∂centeredPlaneFrequencyMeasure,
      (centeredPlaneBlochRealH1Field f g hfg θ).val =
        planeBlochRealCellJet centeredPlaneFrequencyBase f g θ := by
  filter_upwards [(centeredPlaneBlochRealH1_memLp f g hfg).coeFn_toLp,
    planeBlochRealH1_val_ae centeredPlaneFrequencyBase f g hfg] with θ hθ hj
  exact (congrArg Subtype.val hθ).trans hj

theorem centeredPlaneBlochRealH1Field_value
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) :
    centeredCellBlochValueField (centeredPlaneBlochRealH1Field f g hfg) =
      planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume f) := by
  apply Lp.ext
  filter_upwards [cellComplexH1ValueCLM.coeFn_compLp (centeredPlaneBlochRealH1Field f g hfg),
    centeredPlaneBlochRealH1Field_jet_ae f g hfg,
    planeCellBlochTransform_ae centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume f)]
    with θ hv hj hp
  change cellComplexH1ValueCLM.compLp (centeredPlaneBlochRealH1Field f g hfg) θ = _
  rw [hv, hp]
  exact cellFirstJet_value_readout _ _ _ hj

theorem centeredPlaneBlochRealH1Field_gradient
    (f : Lp ℝ 2 (volume : Measure (Vec 2)))
    (g : Fin 2 → Lp ℝ 2 (volume : Measure (Vec 2)))
    (hfg : ∀ i, HasWeakPartialDerivOn Set.univ i f (g i)) (i : Fin 2) :
    centeredCellBlochGradientField (centeredPlaneBlochRealH1Field f g hfg) i =
      planeCellBlochTransform centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume (g i)) := by
  apply Lp.ext
  filter_upwards [(centeredCellBlochGradient_memLp (centeredPlaneBlochRealH1Field f g hfg) i).coeFn_toLp,
    centeredPlaneBlochRealH1Field_jet_ae f g hfg,
    planeCellBlochTransform_ae centeredPlaneFrequencyBase 1 (by norm_num) (ofRealL2 volume (g i))]
    with θ hd hj hp
  change centeredCellBlochGradientField (centeredPlaneBlochRealH1Field f g hfg) i θ =
    cellShiftedDerivativeCLM (planePhysicalBlochShift θ) i
      (cellComplexH1RealEquiv (centeredPlaneBlochRealH1Field f g hfg θ)) at hd
  rw [hd, hp]
  exact cellFirstJet_physical_readout _ _ _ _ hj i

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A native realization of the preceding-letter flux gives the actual scalar equation at one word level. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {D N : ℕ}

theorem wordChain_scalar_component_redistribution (hD : 2 ≤ D)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (letters : Fin N → CycleLetter ι h D) (X0 : Vec 2) (δ : ℝ)
    (κ : Fin (N + 1) → ι → ℕ) (a b : ℝ)
    (v : ℝ → Vec 2 → Vec 2) (hvm : ∀ t k, Measurable (fun x => v t x k))
    (M : ℝ) (hvb : ∀ t k x, ‖v t x k‖ ≤ M)
    (f : ∀ p : Fin (N + 1) × ι, PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (U : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2) (h p.2))
    (Uw : ∀ p : Fin (N + 1) × ι, ℝ → PlaneHk Set.univ (κ p.1 p.2 + 1) (h p.2))
    (hsol : IsPlaneChainFrom (wordChainData G letters X0 δ) κ a b v
      (fun j x => f (j, x)) (fun _ _ _ => 0)
      (fun j x => U (j, x)) (fun j x => Uw (j, x)))
    (i : Fin (N + 1) × ι)
    (V : ℝ → PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2)))
    (hV : ∀ᵐ t ∂volume.restrict (Set.Icc a b), planeValue (V t) =ᵐ[volume]
      wordChainPreviousFlux letters X0 δ κ (fun p => Uw p t) i t) :
    IsPlaneChainFrom (h := fun _ : Unit => h i.2) (geometryScalarData D (fun t _ => G t))
      (fun _ _ => κ i.1 i.2) a b v (fun _ _ => f i) (fun _ _ => V)
      (fun _ _ => U i) (fun _ _ => Uw i) := by
  refine ⟨(fun _ => hsol.1 i), (fun _ => hsol.2.1 i),
    (fun _ => hsol.2.2.1 i), (fun _ => hsol.2.2.2.1 i), ?_⟩
  intro q t ht ψ
  rcases q with ⟨j0, u⟩
  cases u
  have hj := Fin.eq_zero j0
  subst j0
  have hs := hsol.2.2.2.2 i t ht ψ
  simp only [Measure.restrict_univ] at hs ⊢
  let du := fun r k => (Uw i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => k⟩
  let fzero := fun _ : ℝ =>
    (0 : PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2))).toFunction.jet
      (valueIndex2 (κ i.1 i.2))
  let fnew := fun r => (V r).toFunction.jet (valueIndex2 (κ i.1 i.2))
  let gzero := fun _ : ℝ => (0 : PlaneHk Set.univ (κ i.1 i.2) (h i.2)).toFunction.jet
    (valueIndex2 (κ i.1 i.2))
  let A := fun r => wordChainRawFlux G letters X0 δ κ (fun p => Uw p r) i r
  let A' := fun r => geometryScalarFlux D (h := fun _ : Unit => h i.2) (fun t _ => G t)
    (fun _ _ => κ i.1 i.2) (fun _ => Uw i r) (0, ()) r
  change CoupledWeakIdentity volume 1 a t v _ _ _ _ du A fzero gzero at hs
  change CoupledWeakIdentity volume 1 a t v _ _ _ _ du A' fnew gzero
  have hsub : Set.Ioc a t ⊆ Set.Icc a b := fun r hr => ⟨hr.1.le, hr.2.trans ht.2⟩
  apply coupledWeakIdentity_flux_ae_time_congr volume 1 a t v _ _ _ _ du A fzero A' fnew gzero hs
  · have hv := ae_restrict_of_ae_restrict_of_subset hsub hV
    filter_upwards [hv] with r hr
    have hz := planeValue_zero_ae (E := PiLp 2 (fun _ : Fin 2 => h i.2)) (κ i.1 i.2)
    rw [planeValue_eq_stored] at hr hz
    filter_upwards [hr, hz] with z hrz hzz
    change A r z + fzero r z = A' r z + fnew r z
    dsimp only [A, fzero, fnew]
    rw [wordChainRawFlux_split hD]
    have hm : WithLp.toLp 2 (fun k : Fin 2 => ∑ l : Fin 2, (G r - 1) k l •
        (Uw i r).toFunction.jet ⟨⟨1, by omega⟩, fun _ : Fin 1 => l⟩ z) = A' r z := by
      apply PiLp.ext
      intro k
      dsimp only [A']
      rw [geometryScalarFlux_eq D hD]
    change (0 : PlaneHk Set.univ (κ i.1 i.2) (PiLp 2 (fun _ : Fin 2 => h i.2))).toFunction.jet
      (valueIndex2 (κ i.1 i.2)) z = 0 at hzz
    change (V r).toFunction.jet (valueIndex2 (κ i.1 i.2)) z = _ at hrz
    rw [hm, hzz, add_zero, hrz]
  · intro r _
    have hi := planeScalarRawRhs_integrable_measurable (κ i.1 i.2) (v r)
      (hvm r) M (hvb r) (G r) (Uw i r) (V r) ψ
    unfold Weighted.planeScalarRawRhs at hi
    simpa only [du, A', fnew, gzero, geometryScalarFlux_eq D hD, one_mul] using hi

end AVRegularity.CycleWords
end

section
open MeasureTheory Set AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Genuine time-indexed frequency H1 states obtained by Bochner transposition. -/

local instance cellEnergyTimeFrequencyRealInner : InnerProductSpace ℝ CellComplexH1 :=
  InnerProductSpace.complexToReal

local instance cellEnergyTimeFrequencyTimeSecondCountable (a b : ℝ) :
    SecondCountableTopology (Lp CellComplexH1 2 (volume.restrict (Icc a b))) :=
  cellComplexH1LpSecondCountable _

local instance cellEnergyTimeFrequencyCellSecondCountable :
    SecondCountableTopology (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) :=
  cellComplexH1LpSecondCountable _

def cellEnergyTimeFrequencyState {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    Lp (Lp CellComplexH1 2 centeredPlaneFrequencyMeasure) 2 (volume.restrict (Icc a b)) :=
  bochnerL2Transpose centeredPlaneFrequencyMeasure (volume.restrict (Icc a b))
    (cellEnergyFrequencyTimeState centeredPlaneFrequencyMeasure hab F)

theorem cellEnergyTimeFrequencyState_slices {a b : ℝ} (hab : a ≤ b)
    (F : Lp (CellEnergySpace a b) 2 centeredPlaneFrequencyMeasure) :
    ∀ᵐ t ∂volume.restrict (Icc a b),
      (cellEnergyTimeFrequencyState hab F t : Homogenization.Vec 2 → CellComplexH1) =ᵐ[
        centeredPlaneFrequencyMeasure] fun θ =>
          bochnerL2Joint centeredPlaneFrequencyMeasure (volume.restrict (Icc a b))
            (cellEnergyFrequencyTimeState centeredPlaneFrequencyMeasure hab F) (θ, t) :=
  bochnerL2Transpose_slices _ _ _

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Exact spatial form on every active pulse, including its nonstationary shoulders. -/

 theorem ocCellDrift_active_horizontal {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    {k : ℤ} (hk : Odd k) (h1 : k % 4 = 1) (t : ℝ)
    (hp : ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0)
    (z : Vec 2) (i : Fin 2) :
    ocCellDrift α q Λ ζ m ν y₀ t z i =
      if i = 1 then
        (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
          (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)) *
          CycleDamping.cellCosine 0 (y₀ 0 / ocEpsilon q Λ m) z else 0 := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
    CycleReference.ocShearVel_horizontal h1, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · norm_num
  · norm_num
    have hc := CycleDamping.scaled_cell_cosine_eq (ocEpsilon q Λ m) he.ne' y₀ z (0 : Fin 2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    change Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
      (y₀ 0 + ocEpsilon q Λ m * z 0)) =
      CycleDamping.cellCosine 0 (y₀ 0 / ocEpsilon q Λ m) z at hc
    rw [hc]
    rw [show ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
        (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
        ((2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹) *
        CycleDamping.cellCosine 0 (y₀ 0 / ocEpsilon q Λ m) z)) =
        ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
        ((ocEll q Λ m ν ^ 2 / ocEpsilon q Λ m *
        (2 * Real.pi * ocEpsilon q Λ m ^ (1 + α) * (ocEpsilon q Λ m)⁻¹)) *
        CycleDamping.cellCosine 0 (y₀ 0 / ocEpsilon q Λ m) z) by ring]
    rw [CycleDamping.shear_cell_amplitude_identity hΛ]
    ring

 theorem ocCellDrift_active_vertical {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    {k : ℤ} (hk : Odd k) (h3 : k % 4 = 3) (t : ℝ)
    (hp : ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0)
    (z : Vec 2) (i : Fin 2) :
    ocCellDrift α q Λ ζ m ν y₀ t z i =
      if i = 0 then
        -(ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
          (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)) *
          CycleDamping.cellCosine 1 (y₀ 1 / ocEpsilon q Λ m) z else 0 := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_active hΛ hζ hk hp,
    CycleReference.ocShearVel_vertical h3, Pi.smul_apply, smul_eq_mul]
  fin_cases i
  · norm_num
    have hc := CycleDamping.scaled_cell_cosine_eq (ocEpsilon q Λ m) he.ne' y₀ z (1 : Fin 2)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at hc
    change Real.cos (2 * Real.pi * (ocEpsilon q Λ m)⁻¹ *
      (y₀ 1 + ocEpsilon q Λ m * z 1)) =
      CycleDamping.cellCosine 1 (y₀ 1 / ocEpsilon q Λ m) z at hc
    rw [hc]
    have ha := CycleDamping.shear_cell_amplitude_identity (m := m) (q := q) (α := α) hΛ ν
    linear_combination (ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
      CycleDamping.cellCosine 1 (y₀ 1 / ocEpsilon q Λ m) z) * ha
  · norm_num

 theorem ocCellDrift_quiet_zero {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (ν : ℝ) (y₀ : Vec 2) (t : ℝ)
    (hp : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0) :
    ocCellDrift α q Λ ζ m ν y₀ t = 0 := by
  funext z
  simp only [ocCellDrift, CycleReference.pulseStreamVel_eq_zero_of_quiet hp, smul_zero, Pi.zero_apply]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergyPlane.Fourier
namespace AVRegularity.CycleWords

/-! On the original window the clamped full Sobolev sources have the prescribed scalar RHS. -/

open AVRegularity.Weighted

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem cellMetric_scalarSobolevSource_pair_eq_raw {K Kmax : ℕ} {ta tb : ℝ}
    (hK : K ≤ Kmax) (hab : ta ≤ tb)
    (v : ℝ → Vec 2 → Vec 2) (hv : ∀ t ∈ Set.Icc ta tb, ContDiff ℝ (⊤ : ℕ∞) (v t))
    (V strain B lam : ℝ) (hbv : ∀ t ∈ Set.Icc ta tb, ∀ x, ‖v t x‖ ≤ V)
    (hjets : ∀ t ∈ Set.Icc ta tb, ∀ l, 1 ≤ l → l ≤ Kmax → ∀ x,
      ‖coefficientDerivativeArray (driftCoefficient (v t)) l x‖ ≤
        strain * B ^ l * (l.factorial : ℝ) * lam ^ ((1 : ℤ) - l))
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ t ∈ Set.Icc ta tb, ∀ k j, ContDiff ℝ (K : ℕ) (fun x => G t x k j))
    (M : Fin (K + 1) → ℝ)
    (hb : ∀ t ∈ Set.Icc ta tb, ∀ (l : Fin (K + 1)) x k j,
      ‖iteratedFDeriv ℝ l.val (fun y => G t y k j) x‖ ≤ M l)
    (hCell : IsCellMetric G)
    (W : ℝ → PlaneHk Set.univ (K + 1) E)
    (F : ℝ → PlaneHk Set.univ K (PiLp 2 (fun _ : Fin 2 => E)))
    (t : ℝ) (ht : t ∈ Set.Icc ta tb) (Z : PlaneHk Set.univ 1 E) :
    inner ℝ (planeHkValueOperator K
      (scalarSobolevTransportSource hK hab v hv V strain B lam hbv hjets W t))
      (planeHkValueOperator 1 Z) -
      inner ℝ (planeFluxValueOperator K (scalarSobolevMetricSource hab G hG M hb W F t))
        (planeH1GradientOperator Z) = ∫ x, planeScalarRawRhs K (v t) (G t) (W t) (F t) Z x := by
  let τ := Set.projIcc ta tb hab t
  have hh := scalarCarrierSource_pair_eq_raw hK
    (planeIntervalCoefficient ta tb hab v t) (hv τ τ.property) V (hbv τ τ.property)
    strain B lam (hjets τ τ.property)
    (fun k => (continuous_apply k).comp (hv τ τ.property).continuous)
    (max V 0) (le_max_right _ _)
    (planeIntervalVelocity_bound ta tb hab v V hbv t)
    (planeIntervalCoefficient ta tb hab G t) (hG τ τ.property) M (hb τ τ.property)
    (fun k j => (hG τ τ.property k j).continuous) 2 (by norm_num)
    (cellMetricInterval_entry_bound ta tb hab G hCell t) (W t) (F t) Z
  refine hh.trans ?_
  rw [planeIntervalCoefficient_of_mem ta tb hab v t ht,
    planeIntervalCoefficient_of_mem ta tb hab G t ht]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Transverse projection preserves the original weak cell evolution and its invariant states. -/

theorem cellActualWeak_transverse_projection {a b : ℝ}
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (hv : IsCellDrift v) (V : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (e : Fin 2) (ht : ∀ (t : ℝ) (z : Vec 2) (s : ℝ), v t (z + s • basisVec e) = v t z)
    (src : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t (slice t) (src t) (F t))) :
    CellWeakHilbertCurve a b (fun t => cellTransverseProjection e (u t))
      (fun t => cellTransverseH1Projection e (slice t))
      (fun t => cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t
        (cellTransverseH1Projection e (slice t)) (cellTransverseProjection e (src t))
        (fun j => cellTransverseProjection e (F t j))) := by
  apply (cellWeakHilbertCurve_transverse_projection h e).dual_congr
  exact Filter.Eventually.of_forall (fun t =>
    cellTransverseH1Projection_dualDerivative G hG v θ κ hv V hb e ht t (slice t) (src t) (F t))

theorem cellActualWeak_transverse_invariant {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (θ : Fin 2 → ℂ) (κ : ℝ → ℂ)
    (hv : IsCellDrift v) (V k : ℝ) (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hκ : ∀ t, ‖κ t‖ ≤ k)
    (e : Fin 2) (ht : ∀ (t : ℝ) (z : Vec 2) (s : ℝ), v t (z + s • basisVec e) = v t z)
    (src : ℝ → ComplexCellL2) (F : ℝ → Fin 2 → ComplexCellL2)
    (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t =>
      cellDualDerivative ⟨fun t _ => G t, v, θ, κ⟩ hG V hv.1 hb t (slice t) (src t) (F t)))
    (hs : ∀ t, cellTransverseProjection e (src t) = src t)
    (hF : ∀ t j, cellTransverseProjection e (F t j) = F t j)
    (hi : cellTransverseProjection e (u a) = u a) :
    ∀ t ∈ Icc a b, cellTransverseProjection e (u t) = u t := by
  have hp := cellActualWeak_transverse_projection G hG v θ κ hv V hb e ht src F u slice h
  simp only [hs, hF] at hp
  exact cellActualWeak_unique hab ⟨fun t _ => G t, v, θ, κ⟩ hG V k hv.1 hb hκ src F
    (fun t => cellTransverseProjection e (u t)) u
    (fun t => cellTransverseH1Projection e (slice t)) slice hp h hi

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
open AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The genuine quiet fibre mean solves the original measurable scalar metric equation. -/

theorem cellBlochDriftMean_at_quiet_time (η Cw : ℝ) (hCw : 0 ≤ Cw)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (t : ℝ) (hquiet : ∀ x, v t x = 0) (u : ComplexCellL2) :
    cellBlochDriftMeanCLM η Cw hCw hv hw ξ t u = 0 := by
  rw [cellBlochDriftMeanCLM_apply]
  have he : (fun x => fibreDriftCoupling η v ξ t x * u x) = (fun _ => (0 : ℂ)) := by
    funext x
    simp only [fibreDriftCoupling, hquiet x, Pi.zero_apply, Complex.ofReal_zero,
      mul_zero, Finset.sum_const_zero, zero_mul]
  rw [he, cellMean, integral_zero]

theorem cellWeak_quiet_mean_strongTime {a b : ℝ} (hab : a ≤ b)
    (η Cw : ℝ) (hη : 0 ≤ η) (hCw : 0 ≤ Cw)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (hw : ∀ t x, Real.sqrt η * Real.sqrt (∑ i, v t x i ^ 2) ≤ Cw)
    (ξ : Fin 2 → ℂ) (u : ℝ → ComplexCellL2) (slice : ℝ → TorusHk 1 ℂ)
    (h : CellWeakHilbertCurve a b u slice (fun t => cellDualDerivative
      ⟨fun t _ => G t, v, fun j => (Real.sqrt η : ℂ) * ξ j, 0⟩ hG V hv.1 hb t (slice t) 0 0))
    (hquiet : ∀ t ∈ Icc a b, ∀ x, v t x = 0) :
    StrongTimeRegularity a b (fun t => cellMean (u t))
      (fun t => (-(η : ℂ) * fibreQuad (G t) ξ) * cellMean (u t)) := by
  have hs := cellWeakBloch_mean_strongTime hab G hG hv V hb
    (fun j => (Real.sqrt η : ℂ) * ξ j) 0 u slice 0 0 h
  refine ⟨hs.ac, ?_⟩
  have hd := hs.derivative
  rw [uIcc_of_le hab] at hd ⊢
  filter_upwards [hd, h.agrees, ae_restrict_mem measurableSet_Icc] with t ht ha hmem
  have hz : cellMean (0 : ComplexCellL2) = 0 := by
    rw [← cellMeanCLM_apply (0 : ComplexCellL2), map_zero]
  rw [cellBlochLinearSourceClass_mean η Cw hη hCw G hv hw V hb ξ t (slice t),
    cellBlochDriftMean_at_quiet_time η Cw hCw hv hw ξ t (hquiet t hmem),
    ← ha] at ht
  simpa only [Pi.zero_apply, mul_zero, zero_mul, hz, Finset.sum_const_zero, zero_sub,
    zero_add, add_zero, neg_mul] using ht

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! All-time component jet bounds for the actual constructed drift. -/

 theorem constructed_spatial_component_cosine {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) (t : ℝ) (i : Fin 2) :
    ∃ j : Fin 2, ∃ phase A : ℝ,
      |A| ≤ |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| ∧
      (fun z => ocCellDrift α q Λ ζ m ν y₀ t z i) =
        fun z => A * CycleDamping.cellCosine j phase z := by
  classical
  by_cases hp : ∃ k : ℤ, Odd k ∧ ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) ≠ 0
  · obtain ⟨k, hk, hp⟩ := hp
    have hpbound := CycleReference.ocPulse_range (α := α) (q := q) (Λ := Λ) (m := m)
      hζ k (ocEll q Λ m ν ^ 2 * t)
    have hprice : |ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
        (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)| ≤
        |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| := by
      rw [abs_mul, abs_of_nonneg hpbound.1]
      exact mul_le_of_le_one_left (abs_nonneg _) hpbound.2
    rcases CycleReference.odd_int_mod_four hk with h1 | h3
    · by_cases hi : i = 1
      · refine ⟨0, y₀ 0 / ocEpsilon q Λ m,
          ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
            (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2), hprice, ?_⟩
        funext z
        simp only [ocCellDrift_active_horizontal hΛ hζ ν y₀ hk h1 t hp z i, ite_eq_left hi]
      · refine ⟨0, 0, 0, (by simpa only [abs_zero] using abs_nonneg (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)), ?_⟩
        funext z
        simp only [ocCellDrift_active_horizontal hΛ hζ ν y₀ hk h1 t hp z i,
          ite_eq_right hi, zero_mul]
    · by_cases hi : i = 0
      · refine ⟨1, y₀ 1 / ocEpsilon q Λ m,
          -(ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) *
            (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)), ?_, ?_⟩
        · simpa only [abs_neg] using hprice
        · funext z
          simp only [ocCellDrift_active_vertical hΛ hζ ν y₀ hk h3 t hp z i, ite_eq_left hi]
      · refine ⟨0, 0, 0, (by simpa only [abs_zero] using abs_nonneg (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)), ?_⟩
        funext z
        simp only [ocCellDrift_active_vertical hΛ hζ ν y₀ hk h3 t hp z i,
          ite_eq_right hi, zero_mul]
  · have hp0 : ∀ k : ℤ, Odd k → ocPulse α q Λ ζ m k (ocEll q Λ m ν ^ 2 * t) = 0 := by
      intro k hk
      by_contra hne
      exact hp ⟨k, hk, hne⟩
    refine ⟨0, 0, 0, (by simpa only [abs_zero] using abs_nonneg (2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2)), ?_⟩
    funext z
    simp only [ocCellDrift_quiet_zero ν y₀ t hp0, Pi.zero_apply, zero_mul]

 theorem constructed_spatial_contDiff {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2) (t : ℝ) :
    ContDiff ℝ (↑(⊤ : ℕ∞)) (ocCellDrift α q Λ ζ m ν y₀ t) := by
  apply contDiff_pi.mpr
  intro i
  obtain ⟨j, phase, A, _, he⟩ := constructed_spatial_component_cosine hΛ hζ ν y₀ t i
  rw [he]
  exact contDiff_const.mul (CycleDamping.cellCosine_smooth j phase)

 theorem constructed_spatial_component_jet_bound {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}
    (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (ν : ℝ) (y₀ : Vec 2)
    (t : ℝ) (i : Fin 2) (n : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun x => ocCellDrift α q Λ ζ m ν y₀ t x i) z‖ ≤
      |2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| * (2 * Real.pi) ^ n := by
  obtain ⟨j, phase, A, hA, he⟩ := constructed_spatial_component_cosine hΛ hζ ν y₀ t i
  rw [he]
  exact (cellCosine_scalar_jet_bound j phase A n z).trans
    (mul_le_mul_of_nonneg_right hA (by positivity))

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CoupledEnergy.Galerkin AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! Actual constant metric diffusion is compatible with every native reserve. -/

 theorem torusHigherStrongDiffusionCLM_truncate {K L : ℕ} (hKL : K ≤ L)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (θ : Fin 2 → ℂ) (t : ℝ)
    (U : TorusHk (L + 2) ℂ) :
    truncateTorusHk hKL (torusHigherStrongDiffusionCLM L G θ t U) =
      torusHigherStrongDiffusionCLM K G θ t
        (truncateTorusHk (by omega : K + 2 ≤ L + 2) U) := by
  apply TorusHk.ext_value
  change torusHkValueCLM (torusHigherStrongDiffusionCLM L G θ t U) =
    torusHkValueCLM (torusHigherStrongDiffusionCLM K G θ t
      (truncateTorusHk (by omega : K + 2 ≤ L + 2) U))
  rw [torusHigherStrongDiffusionCLM_value, torusHigherStrongDiffusionCLM_value,
    torusHigher_truncate_comp]

 theorem finiteSmoothPeriodicHk_truncate {K L : ℕ} (hKL : K ≤ L)
    (f : Vec 2 → ℂ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    truncateTorusHk hKL (finiteSmoothPeriodicHk L f (hf.of_le (by simp)) hp) =
      finiteSmoothPeriodicHk K f (hf.of_le (by simp)) hp := by
  apply TorusHk.ext_value
  apply Lp.ext
  have hl := finiteSmoothPeriodicHk_jet_ae L f (hf.of_le (by simp)) hp (valueIndex2 L)
  have hr := finiteSmoothPeriodicHk_jet_ae K f (hf.of_le (by simp)) hp (valueIndex2 K)
  exact hl.trans hr.symm

 theorem finiteSmoothPeriodicHk_ordered_truncated_H1 {r L : ℕ} (hr : 1 + r ≤ L)
    (w : DerivativeWord2 r) (f : Vec 2 → ℂ)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hp : AVenhance.IsZ2Periodic f) :
    derivativeTorusHk (K := 1) w
      (truncateTorusHk hr (finiteSmoothPeriodicHk L f (hf.of_le (by simp)) hp)) =
      cellH2BaseCLM (finiteSmoothPeriodicHk 2 (orderedDerivative w f)
        (orderedDerivative_contDiff w 2 f (hf.of_le (by simp)))
        (orderedDerivative_periodic w f (hf.of_le (by simp)) hp)) :=
  (congrArg (derivativeTorusHk (K := 1) w)
    (finiteSmoothPeriodicHk_truncate hr f hf hp)).trans
    (finiteSmoothPeriodicHk_ordered_H2_base w f hf hp).symm

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Weighted native plane data have a single compact smooth approximation in all reserved jets. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem exists_weighted_compact_smooth_approximation {K : ℕ} (U : PlaneHk Set.univ K E)
    (q : Vec 2 → ℝ) (hq : Continuous q)
    (hw : JetMemL2On Set.univ (fun a x => q x • U.toFunction.jet a x)) :
    ∃ UN : ℕ → PlaneHk Set.univ K E, ∃ fN : ℕ → Vec 2 → E,
      (∀ n, ContDiff ℝ (⊤ : ℕ∞) (fN n) ∧ HasCompactSupport (fN n)) ∧
      (∀ n, planeValue (UN n) =ᵐ[volume] fN n) ∧
      ∀ a : JetIndex2 K,
        ∃ hmem : ∀ n, MemLp (fun x => q x • (UN n).toFunction.jet a x) 2 volume,
        ∃ hU : MemLp (fun x => q x • U.toFunction.jet a x) 2 volume,
          Tendsto (fun n => (hmem n).toLp (fun x => q x • (UN n).toFunction.jet a x))
            atTop (𝓝 (hU.toLp (fun x => q x • U.toFunction.jet a x))) := by
  classical
  obtain ⟨A, hA, hb, hb0⟩ := exists_expandingPlaneCoefficient_budget (E := E) K
  let base n := expandingCutoffPlaneHk U n A (hb n)
  have happrox (n : ℕ) := exists_compact_smooth_weighted_jet_approximation
    (base n) (tsupport (expandingPlaneCutoff n)) (expandingPlaneCutoff_hasCompactSupport n)
    (expandingCutoffPlaneHk_supported U n A (hb n)) q hq
  choose T fT _htT hdT hvT hjT using happrox
  choose hmT hmBase hconv using hjT
  have hwv (a : JetIndex2 K) : MemLp (fun x => q x • U.toFunction.jet a x) 2 volume := by
    simpa only [Measure.restrict_univ] using hw a
  let u (a : JetIndex2 K) := (hwv a).toLp (fun x => q x • U.toFunction.jet a x)
  let b (n : ℕ) (a : JetIndex2 K) :=
    (hmBase n a).toLp (fun x => q x • (base n).toFunction.jet a x)
  let s (n m : ℕ) (a : JetIndex2 K) :=
    (hmT n a m).toLp (fun x => q x • (T n m).toFunction.jet a x)
  have hbconv (a : JetIndex2 K) : Tendsto (fun n => b n a) atTop (𝓝 (u a)) :=
    expandingCutoff_volume_jet_limit U q hw A hA hb hb0 a (fun n => hmBase n a) (hwv a)
  have hsconv (n : ℕ) (a : JetIndex2 K) : Tendsto (fun m => s n m a) atTop (𝓝 (b n a)) :=
    hconv n a
  obtain ⟨m, hdiag⟩ := exists_finite_diagonal_approximation b s u hbconv hsconv
  refine ⟨fun n => T n (m n), fun n => fT n (m n), fun n => hdT n (m n),
    fun n => hvT n (m n), ?_⟩
  intro a
  exact ⟨fun n => hmT n a (m n), hwv a, hdiag a⟩

end AVRegularity.CycleWords
end

section
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! The genuine mean-free cell projection is orthogonal and contracts the L2 norm. -/

theorem cellQ0CLM_norm_sq_decomposition (u : ComplexCellL2) :
    ‖u‖ ^ 2 = ‖cellQ0CLM u‖ ^ 2 + ‖cellMean u‖ ^ 2 := by
  let q := cellQ0CLM u
  let c := cellConstantCLM (cellMean u)
  have hm : cellMean q = 0 := cellQ0CLM_mean_zero u
  have hp := cellMeanZero_constant_pair_zero (cellMean u) q hm
  rw [cellScalarCLM_constant_one] at hp
  have ho : inner ℝ q c = 0 := by
    have he := congrArg Complex.re hp
    rw [cellComplexPair_re, Complex.zero_re, real_inner_comm] at he
    exact he
  have he : u = q + c := by
    change u = (u - cellConstantCLM (cellMeanCLM u)) + cellConstantCLM (cellMean u)
    rw [cellMeanCLM_apply]
    abel
  calc
    ‖u‖ ^ 2 = ‖q + c‖ ^ 2 := congrArg (fun z => ‖z‖ ^ 2) he
    _ = ‖q‖ ^ 2 + ‖c‖ ^ 2 := by rw [norm_add_sq_real, ho, mul_zero, add_zero]
    _ = _ := by rw [cellConstantCLM_norm]

theorem cellQ0CLM_norm_le_one (u : ComplexCellL2) : ‖cellQ0CLM u‖ ≤ ‖u‖ := by
  have he := cellQ0CLM_norm_sq_decomposition u
  have hq := norm_nonneg (cellQ0CLM u)
  have hu := norm_nonneg u
  nlinarith only [he, hq, hu, sq_nonneg ‖cellMean u‖]

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A finite, radius-independent bound on the full renewal density. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def pullbackSquareOrderBudget (B : ℕ → ℝ) (n : ℕ) : ℝ :=
  (Fintype.card (Σ c : OrderedFinpartition n, DerivativeWord2 c.length) : ℝ) *
    ∑ a : (Σ c : OrderedFinpartition n, DerivativeWord2 c.length),
      (∏ i : Fin a.1.length, B (a.1.partSize i)) ^ 2

def pullbackSquareBudget (B : ℕ → ℝ) (K : ℕ) : ℝ :=
  ∑ a : JetIndex2 K, pullbackSquareOrderBudget B a.1.val

theorem planeSobolev_pullback_word_density_bound {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) (n : ℕ) (hn : n ≤ K)
    (w : DerivativeWord2 n) :
    ∀ᵐ z ∂volume, factorialWeight r n * ‖planeJetOrder V n w z‖ ^ 2 ≤
      pullbackSquareOrderBudget B n * planeFactorialDensity r U (X z) := by
  filter_upwards [planeSobolev_pullback_weighted_word_budget U V X hX hμ B hb hv r hr hr1 n hn w]
    with z hz
  apply hz.trans
  unfold pullbackSquareOrderBudget
  rw [mul_assoc]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro a _
  exact mul_le_mul_of_nonneg_left
    (planeFactorialDensity_term_le (a.1.length_le.trans hn) r U a.2 (X z)) (sq_nonneg _)

theorem planeSobolev_pullback_density_bound {K : ℕ} (U V : PlaneHk Set.univ K E)
    (X : Vec 2 → Vec 2) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume) (B : ℕ → ℝ)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j)
    (hv : planeValue V =ᵐ[volume] planeValue U ∘ X)
    (r : ℝ) (hr : 0 ≤ r) (hr1 : r ≤ 1) :
    ∀ᵐ z ∂volume, planeFactorialDensity r V z ≤
      pullbackSquareBudget B K * planeFactorialDensity r U (X z) := by
  have hh : ∀ᵐ z ∂volume, ∀ a : JetIndex2 K,
      factorialWeight r a.1.val * ‖planeJetOrder V a.1.val a.2 z‖ ^ 2 ≤
        pullbackSquareOrderBudget B a.1.val * planeFactorialDensity r U (X z) :=
    (ae_all_iff).mpr (fun a => planeSobolev_pullback_word_density_bound U V X hX hμ B hb hv
      r hr hr1 a.1.val (Nat.le_of_lt_succ a.1.isLt) a.2)
  filter_upwards [hh] with z hz
  unfold planeFactorialDensity pullbackSquareBudget
  rw [Finset.sum_mul]
  exact Finset.sum_le_sum (fun a _ => hz a)

end AVRegularity.CycleWords
end

section
open MeasureTheory Set Filter Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin AVenhance.Infra.ODE
open scoped Topology
namespace AVRegularity.CycleWords

/-! Full homogeneous finite moments converge at every time to the actual weak cell trace. -/

theorem cellRawSourceFunctional_zero_apply (θ : Fin 2 → ℂ) (t : ℝ) (z : TorusHk 1 ℂ) :
    cellRawSourceFunctional θ 0 0 t z = 0 := by
  simp only [cellRawSourceFunctional, Pi.zero_apply, Pi.zero_def, PiLp.zero_apply, cellSourceSlice_zero,
    ContinuousLinearMap.coe_coe, cellSourceFunctional_zero]

theorem cellFullGalerkin_trace_moments_tendsto {a b : ℝ} (hab : a ≤ b)
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V k : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t x, ∑ i, C.v t x i ^ 2 ≤ V ^ 2)
    (hκ : Measurable C.κ) (hκb : ∀ t, ‖C.κ t‖ ≤ k)
    (initial : ComplexCellL2) (D : CellGalerkinLimitData a b hab C hG V hv hb 0 0 initial)
    (U : ℝ → ComplexCellL2)
    (hU : CellWeakHilbertCurve a b U D.limit
      (fun t => cellDualDerivative C hG V hv hb t (D.limit t) 0 0))
    (hinitial : U a = initial) (z : TorusHk 1 ℂ) (t : ℝ) (ht : t ∈ Icc a b) :
    Tendsto (fun n => inner ℝ
      (cellGalerkinValue (D.subsequence n) (extendCurve hab (D.curve (D.subsequence n)) t))
      (torusHkValueCLM z)) atTop (𝓝 (inner ℝ (U t) (torusHkValueCLM z))) := by
  have he := hU.increment a ⟨le_rfl, hab⟩ t ht ht.1 z
  rw [hinitial] at he
  simp only [cellDualDerivative_pairing] at he
  have hz : cellSourceFunctional C.θ 0 0 z = 0 := cellSourceFunctional_zero C.θ z
  simp only [hz, add_zero] at he
  have hm := D.moment_primitive_tendsto k hκ hκb (by apply MemLp.zero) (by apply MemLp.zero) z t ht
  simp only [cellRawSourceFunctional_zero_apply, add_zero] at hm
  have hv0 : inner ℝ (U t) (torusHkValueCLM z) =
      inner ℝ initial (torusHkValueCLM z) + ∫ r in a..t, cellGeneratorForm C hG V hv hb r (D.limit r) z := by
    linarith only [he]
  rw [hv0]
  exact hm

end AVRegularity.CycleWords
end

section
open Homogenization
namespace AVRegularity.CycleWords

/-! The remainder growth root shifts the literal polynomial moment by its degree. -/

theorem polynomialMomentRoot_continuous (ϖ : ℝ) : Continuous (polynomialMomentRoot ϖ) := by
  unfold polynomialMomentRoot
  fun_prop

theorem polynomialMomentRoot_pow_sq (ϖ : ℝ) (z : Vec 2) (p : ℕ) :
    (polynomialMomentRoot ϖ z ^ p) ^ 2 = Weighted.planeMomentPolynomial p ϖ 0 z := by
  rw [← pow_mul, Nat.mul_comm p 2, pow_mul]
  unfold polynomialMomentRoot Weighted.planeMomentPolynomial
  rw [Real.sq_sqrt (by positivity)]
  simp only [Pi.zero_apply, sub_zero]

theorem polynomialMomentRoot_weight_shift (ϖ : ℝ) (z : Vec 2) (n p : ℕ) :
    Weighted.planeMomentPolynomial n ϖ 0 z * (polynomialMomentRoot ϖ z ^ p) ^ 2 =
      Weighted.planeMomentPolynomial (n + p) ϖ 0 z := by
  rw [polynomialMomentRoot_pow_sq]
  unfold Weighted.planeMomentPolynomial
  rw [pow_add]

end AVRegularity.CycleWords
end

section
namespace AVRegularity.CycleWords

/-! Uniform finite slot bounds for the renewal constants. -/

theorem pullbackSquareBudget_nonneg (B : ℕ → ℝ) (K : ℕ) : 0 ≤ pullbackSquareBudget B K := by
  unfold pullbackSquareBudget pullbackSquareOrderBudget
  exact Finset.sum_nonneg (fun _ _ => mul_nonneg (Nat.cast_nonneg _)
    (Finset.sum_nonneg (fun _ _ => sq_nonneg _)))

def uniformPullbackSquareBudget (B : ℕ → ℝ) (Kmax : ℕ) : ℝ :=
  ∑ K ∈ Finset.range (Kmax + 1), pullbackSquareBudget B K

theorem uniformPullbackSquareBudget_nonneg (B : ℕ → ℝ) (Kmax : ℕ) :
    0 ≤ uniformPullbackSquareBudget B Kmax :=
  Finset.sum_nonneg (fun K _ => pullbackSquareBudget_nonneg B K)

theorem pullbackSquareBudget_le_uniform (B : ℕ → ℝ) {K Kmax : ℕ} (hK : K ≤ Kmax) :
    pullbackSquareBudget B K ≤ uniformPullbackSquareBudget B Kmax := by
  exact Finset.single_le_sum (fun j _ => pullbackSquareBudget_nonneg B j)
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hK))

end AVRegularity.CycleWords
end

section
open AVRegularity.Sobolev AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleWords

/-! The finite lift of a native datum is its literal native Fourier cutoff. -/

theorem cellGalerkinHigherInitial_eq (N q : ℕ) (U : TorusHk q ℂ) :
    truncateTorusHk (by omega : q ≤ q + 1)
      (cellGalerkinHigherStateCLM N q (cellGalerkinL2Initial N (torusHkValueCLM U))) =
      galerkinProj N U := by
  apply TorusHk.ext_value
  change torusHkValueCLM (truncateTorusHk (by omega : q ≤ q + 1)
    (cellGalerkinHigherStateCLM N q (cellGalerkinL2Initial N (torusHkValueCLM U)))) =
      torusHkValueCLM (galerkinProj N U)
  rw [torusHigher_truncate_value, cellGalerkinHigherStateCLM_value, cellGalerkinL2Initial_eq_fourier,
    cellL2FourierState_value]
  rfl

theorem cellGalerkinHigherInitial_norm_le (N q : ℕ) (U : TorusHk q ℂ) :
    ‖truncateTorusHk (by omega : q ≤ q + 1)
      (cellGalerkinHigherStateCLM N q (cellGalerkinL2Initial N (torusHkValueCLM U)))‖ ≤ ‖U‖ := by
  rw [cellGalerkinHigherInitial_eq]
  exact galerkinProj_norm_le N U

end AVRegularity.CycleWords
end

section
open Homogenization AVenhance
namespace AVRegularity.CycleWords

/-! Enhanced-normalized spatial jets have a price fixed before the band and metric. -/

 def constructedSpatialJetPrice (n : ℕ) : ℝ :=
    (2 * Real.pi * Real.sqrt (2 / ((1 - Real.exp (-2)) / 96))) * (2 * Real.pi) ^ n

 theorem constructedSpatialJetPrice_nonneg (n : ℕ) : 0 ≤ constructedSpatialJetPrice n := by
  unfold constructedSpatialJetPrice
  positivity

 theorem constructed_normalized_spatial_component_jet_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (t : ℝ) (i : Fin 2) (n : ℕ) (z : Vec 2) :
    Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
      ‖iteratedFDeriv ℝ n (fun x => ocCellDrift α q Λ ζ m ν y₀ t x i) z‖ ≤
      constructedSpatialJetPrice n := by
  have he := AVRegularity.Construction.Stream.ocEpsilon_pos (q := q) (n := m) hΛ
  have ha : 0 ≤ 2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2 := by
    unfold ocA
    positivity
  have hab := CycleDamping.corrector_amplitude_bound (α := α) (q := q) (m := m) hΛ hζ hν hr
  calc
    _ ≤ Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) *
        (|2 * Real.pi * ocA α q Λ m * ocEll q Λ m ν ^ 2| * (2 * Real.pi) ^ n) :=
      mul_le_mul_of_nonneg_left
        (constructed_spatial_component_jet_bound hΛ hζ ν y₀ t i n z) (Real.sqrt_nonneg _)
    _ = (2 * Real.pi *
        (Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) * ocA α q Λ m * ocEll q Λ m ν ^ 2)) *
        (2 * Real.pi) ^ n := by rw [abs_of_nonneg ha]; ring
    _ ≤ constructedSpatialJetPrice n := by
      unfold constructedSpatialJetPrice
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hab (by positivity)) (by positivity)

 theorem vec2_iteratedFDeriv_bound_of_components (f : Vec 2 → Vec 2) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ) f) (z : Vec 2) (M : ℝ) (hM : 0 ≤ M)
    (hb : ∀ i : Fin 2, ‖iteratedFDeriv ℝ n (fun x => f x i) z‖ ≤ M) :
    ‖iteratedFDeriv ℝ n f z‖ ≤ M := by
  apply ContinuousMultilinearMap.opNorm_le_bound hM
  intro w
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hM (by positivity))).mpr
  intro i
  have he := (ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ).iteratedFDeriv_comp_left
    (hf.contDiffAt (x := z)) le_rfl
  have hp := (iteratedFDeriv ℝ n (fun x => f x i) z).le_opNorm w
  change ‖iteratedFDeriv ℝ n ((ContinuousLinearMap.proj i : Vec 2 →L[ℝ] ℝ) ∘ f) z w‖ ≤ _ at hp
  rw [he] at hp
  exact hp.trans (mul_le_mul_of_nonneg_right (hb i) (by positivity))

 theorem constructed_normalized_spatial_jet_bound
    {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {ν : ℝ} (hν : 0 < ν) (hr : 6 ≤ ocMu q Λ m ν * ocTau α q Λ m)
    (y₀ : Vec 2) (t : ℝ) (n : ℕ) (z : Vec 2) :
    ‖iteratedFDeriv ℝ n (fun x => Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) •
      ocCellDrift α q Λ ζ m ν y₀ t x) z‖ ≤ constructedSpatialJetPrice n := by
  have hv : ContDiff ℝ (n : ℕ) (ocCellDrift α q Λ ζ m ν y₀ t) :=
    (constructed_spatial_contDiff hΛ hζ ν y₀ t).of_le (by simp)
  let f : Vec 2 → Vec 2 := fun x => Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) •
    ocCellDrift α q Λ ζ m ν y₀ t x
  have hf : ContDiff ℝ (n : ℕ) f := by
    dsimp [f]
    exact (contDiff_const : ContDiff ℝ (n : ℕ)
      (fun _ : Vec 2 => Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν))).smul hv
  apply vec2_iteratedFDeriv_bound_of_components f n hf z (constructedSpatialJetPrice n)
    (constructedSpatialJetPrice_nonneg n)
  intro i
  change ‖iteratedFDeriv ℝ n (fun x => Real.sqrt (ν / ocMeanFlux α q Λ ζ m ν) •
    ocCellDrift α q Λ ζ m ν y₀ t x i) z‖ ≤ _
  have hi : ContDiff ℝ (n : ℕ) (fun x => ocCellDrift α q Λ ζ m ν y₀ t x i) := by
    simpa only [Function.comp_def] using (contDiff_apply ℝ ℝ i).comp hv
  rw [iteratedFDeriv_const_smul_apply' (hi.contDiffAt (x := z)),
    norm_smul, Real.norm_of_nonneg (Real.sqrt_nonneg _)]
  exact constructed_normalized_spatial_component_jet_bound hΛ hζ hν hr y₀ t i n z

end AVRegularity.CycleWords
end
