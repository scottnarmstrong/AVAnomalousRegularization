-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.CellScalarSourceSeries
import AVRegularity.CycleComparison.Lift.ProfileModeHilbertJets
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Residual.QuietMean.SourceMean
public import AVRegularity.CycleComparison.Lift.MixedJetEnergyBound
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Pointwise slow-jet grading allows exponential tests without a global bound on the tests. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem covariantListCoefficient_mixed_grading_at_slow_point (η : ℝ) (hη : η ≤ 1)
    (δ : ℕ) (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C) (X : Vec 2) (w : List (Fin 2)) :
    ∀ p q j, j ≤ w.length → ∀ (f : Vec 2 → Vec 2 → E),
      IsBoxSmooth (p + j) (q + w.length - j) f →
      (∀ a ≤ p + j, ∀ b ≤ q + w.length - j, ∀ z,
        ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a)) →
      ∀ z, ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
        (covariantListCoefficients η w f j Y) z) X‖ ≤
        (2 ^ w.length * C) * lam ^ (δ + j + p) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro p q j hj f hf hb z
    have hj0 : j = 0 := by simpa only [List.length_nil, Nat.le_zero] using hj
    subst j
    simpa only [covariantListCoefficients_nil, ite_true, List.length_nil,
      Nat.add_zero, Nat.sub_zero, pow_zero, one_mul] using hb p le_rfl q (by simp) z
  | append_singleton w k ih =>
    intro p q j hj f hf hb z
    have hlen : (w ++ [k]).length = w.length + 1 := by simp
    have hjlen : j ≤ w.length + 1 := by simpa only [hlen] using hj
    have hfast : IsBoxSmooth p (q + 1) (covariantListCoefficients η w f j) := by
      by_cases hja : j ≤ w.length
      · apply covariantListCoefficient_box_reserve η w j p (q + 1) f hja
        exact hf.mono le_rfl (by rw [hlen]; omega)
      · rw [covariantListCoefficients_above_degree η w f j (by omega)]
        exact IsBoxSmooth.zero
    have hfast_bound : ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ (q + 1)
        (covariantListCoefficients η w f j Y) z) X‖ ≤
        (2 ^ w.length * C) * lam ^ (δ + j + p) := by
      by_cases hja : j ≤ w.length
      · apply ih p (q + 1) j hja f (hf.mono le_rfl (by rw [hlen]; omega))
        intro a ha b hb' y
        exact hb a ha b (by rw [hlen]; omega) y
      · rw [covariantListCoefficients_above_degree η w f j (by omega)]
        simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero]
        positivity
    rw [covariantListCoefficients_append_singleton]
    by_cases hj0 : j = 0
    · subst j
      apply (norm_mixed_covariantCoefficientStep_zero_le η k
        (covariantListCoefficients η w f) hfast X z).trans
      apply hfast_bound.trans
      have hn : 0 ≤ (2 ^ w.length * C) * lam ^ (δ + 0 + p) := by positivity
      rw [hlen, pow_succ]
      nlinarith
    · have hslow : IsBoxSmooth (p + 1) q
          (covariantListCoefficients η w f (j - 1)) := by
        apply covariantListCoefficient_box_reserve η w (j - 1) (p + 1) q f (by omega)
        exact hf.mono (by omega) (by rw [hlen]; omega)
      have hslow_bound : ‖iteratedFDeriv ℝ (p + 1) (fun Y => iteratedFDeriv ℝ q
          (covariantListCoefficients η w f (j - 1) Y) z) X‖ ≤
          (2 ^ w.length * C) * lam ^ (δ + (j - 1) + (p + 1)) := by
        apply ih (p + 1) q (j - 1) (by omega) f
          (hf.mono (by omega) (by rw [hlen]; omega))
        intro a ha b hb' y
        exact hb a (by omega) b (by rw [hlen]; omega) y
      have hh := norm_mixed_covariantCoefficientStep_graded_le hj0 η hη k
        (covariantListCoefficients η w f) hfast hslow X z δ lam
        (2 ^ w.length * C) (2 ^ w.length * C) hfast_bound hslow_bound
      have he : (2 ^ w.length * C + 2 ^ w.length * C) * lam ^ (δ + j + p) =
          (2 ^ (w ++ [k]).length * C) * lam ^ (δ + j + p) := by
        rw [hlen, pow_succ]
        ring
      rwa [he] at hh

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every diagonal mean of degree at least three is the exact drift divergence, with automatic cutoff. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem liftMean_diagonal_ge_three_of_predecessor_fields
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (_hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hΦ : GoodField 2 (liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t))
    (hΨ : CoefField True 2 (liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t)) :
    liftMean Q Cc (fun _ => f) 0 n t X =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z q) •
          liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t Y z)) X (basisVec q) := by
  let Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t
  have hG := setting_metric_contDiff_one P t ht
  have hw := setting_normalized_drift_contDiff_one P t ht
  have hB2 := cellB2_centField Q.η Q.G t hG hΨ
  have hB1 := cellB1_continuous_slice Q.η Q.G Q.v t hG
    (fun q => (hw q).continuous) Φ hΦ X
  have he : liftMean Q Cc (fun _ => f) 0 n t X =
      fieldCellMean (fun z => cellB1 Q.η Q.G Q.v t Φ X z + cellB2 Q.η Q.G t Ψ X z) := by
    simp only [liftMean, liftA, Φ, Ψ, show 2 ≤ n by omega, ite_true, sub_zero]
  rw [he, AVRegularity.fieldCellMean_add hB1 (hB2.1.continuous_slice X),
    hB2.2 trivial X, add_zero]
  exact fieldCellMean_cellB1_formula Q.η Q.G Q.v t hG hw Φ hΦ X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Averaging preserves the base slow grading and spends no parameter reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

local instance gradedCellMeanJetBoundProbCube : IsProbabilityMeasure (volume.restrict AVenhance.unitCube) :=
  ⟨by simpa only [Measure.restrict_apply_univ] using AVRegularity.CycleEvolution.cellCube_volume_one⟩

theorem fieldCellMean_graded_jet_bound (p q sZ δ : ℕ) (hq : q ≤ p)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p sZ f)
    (C : ℕ → ℝ) (lam : ℝ)
    (hb : ∀ j ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => f Y z) X‖ ≤ C j * lam ^ (δ + j)) :
    ContDiff ℝ (p : ℕ∞) (fun X => fieldCellMean (f X)) ∧
      ∀ X, ‖iteratedFDeriv ℝ q (fun Y => fieldCellMean (f Y)) X‖ ≤
        ((2 : ℝ) ^ q * C q) * lam ^ (δ + q) := by
  let F := fun z X => f X z
  have hm : ∀ X, Measurable (fun z => F z X) := fun X => (hf.1 X).continuous.measurable
  have hs : ∀ z, ContDiff ℝ (p : ℕ∞) (F z) := boxSmooth_slow_contDiff hf
  have hb' : ∀ j ≤ p, ∀ z X,
      ‖iteratedFDeriv ℝ j (F z) X‖ ≤ C j * lam ^ (δ + j) := fun j hj z X => hb j hj X z
  refine ⟨parameter_integral_contDiff (volume.restrict AVenhance.unitCube) p F hm hs
    (fun j => C j * lam ^ (δ + j)) hb', ?_⟩
  intro X
  have hh := parameter_integral_iteratedFDeriv_norm_le
    (volume.restrict AVenhance.unitCube) p F hm hs (fun j => C j * lam ^ (δ + j)) hb' q hq X
  simpa only [Measure.real, measure_univ, ENNReal.toReal_one, mul_one, mul_assoc,
    fieldCellMean, F] using! hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit source coefficients apply one outer covariant step to the finite flux vector. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

def sourceCoefficientArray (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (j : ℕ) : Vec 2 → Vec 2 → ∀ i, h i :=
  fun X z => ∑ k : Fin 2,
    covariantCoefficientStep η k (sourceFluxCoefficientArray edge η t Φ k) j X z

theorem sourceOp_polynomial_identity (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η ε t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : GoodField D Φ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z)) (X z : Vec 2) :
    sourceOp edge η ε t Φ X z = ∑ j ∈ Finset.range (D + 1),
      ε ^ j • sourceCoefficientArray edge η t Φ j X z := by
  have hflux (k : Fin 2) : sourceFlux edge η ε t Φ k =
      fun Y y => ∑ i ∈ Finset.range ((D - 1) + 1),
        ε ^ i • sourceFluxCoefficientArray edge η t Φ k i Y y := by
    funext Y y
    simpa only [Nat.sub_add_cancel hD] using
      sourceFlux_polynomial_identity edge η ε t Φ hΦ k Y y
  change (∑ k : Fin 2, dEps η ε k (sourceFlux edge η ε t Φ k) X z) = _
  simp_rw [hflux]
  have hstep (k : Fin 2) := dEps_finite_polynomial_expand (D - 1)
    (sourceFluxCoefficientArray edge η t Φ k)
    (sourceFluxCoefficientArray_good edge hD η t Φ hΦ hΓ k)
    (sourceFluxCoefficientArray_above_degree edge η t Φ k) η ε k X z
  simp_rw [hstep]
  have hlen : D - 1 + 2 = D + 1 := by omega
  simp only [hlen]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  simp only [sourceCoefficientArray, Finset.smul_sum, covariantCoefficientStep]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The finite literal flux coefficient array is measurable in time at its ambient word reserve. -/

variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] {D : ℕ}

theorem sourceFluxCoefficientArray_component_parameter_measurable
    (edge : ConstituentEdges D h) (η : ℝ) (τ : T → ℝ)
    (Φ : T → Vec 2 → Vec 2 → ∀ i, h i)
    (hm : ∀ X z, Measurable (fun t => Φ t X z))
    (hf : ∀ t, IsBoxSmooth D D (Φ t))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z,
      Measurable (fun t => γ.coeff α (τ t) X z))
    (k : Fin 2) (j : ℕ) (X z : Vec 2) (v : ι) :
    Measurable (fun t => sourceFluxCoefficientArray edge η (τ t) (Φ t) k j X z v) := by
  classical
  unfold sourceFluxCoefficientArray
  apply Finset.measurable_sum
  intro u _
  apply Finset.measurable_sum
  intro d _
  have hc (γ : Constituent d.1 (h u) (h v)) (hγ : γ ∈ edge v u d) :
      Measurable (fun t => ∑ α : DerivativeWord2 (d.1 - 1),
        γ.coeff α (τ t) X z k • γ.map
          (covariantListCoefficients η (List.ofFn α) (Φ t) j X z u)) := by
    apply Finset.measurable_sum
    intro α _
    have hw := covariantListCoefficient_parameter_measurable η (List.ofFn α) Φ hm
      (fun t => (hf t).mono (by simp only [List.length_ofFn]; have hd := (Finset.mem_Icc.mp d.2).2; omega)
        (by simp only [List.length_ofFn]; have hd := (Finset.mem_Icc.mp d.2).2; omega)) j X z
    exact ((measurable_pi_apply k).comp (hΓ v u d γ hγ α X z)).smul
      (γ.map.continuous.measurable.comp ((measurable_pi_apply u).comp hw))
  have hl := List.measurable_fun_sum
    ((edge v u d).map fun γ => fun t => ∑ α : DerivativeWord2 (d.1 - 1),
      γ.coeff α (τ t) X z k • γ.map
        (covariantListCoefficients η (List.ofFn α) (Φ t) j X z u))
    (by intro f hf'; obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hf'; exact hc γ hγ)
  simpa only [List.map_map, Function.comp_def] using hl

theorem sourceFluxCoefficientArray_parameter_measurable
    (edge : ConstituentEdges D h) (η : ℝ) (τ : T → ℝ)
    (Φ : T → Vec 2 → Vec 2 → ∀ i, h i)
    (hm : ∀ X z, Measurable (fun t => Φ t X z))
    (hf : ∀ t, IsBoxSmooth D D (Φ t))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z,
      Measurable (fun t => γ.coeff α (τ t) X z))
    (k : Fin 2) (j : ℕ) (X z : Vec 2) :
    Measurable (fun t => sourceFluxCoefficientArray edge η (τ t) (Φ t) k j X z) :=
  Measurable.of_eval (fun v => sourceFluxCoefficientArray_component_parameter_measurable
    edge η τ Φ hm hf hΓ k j X z v)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The source-flux coefficient of degree j uses exactly j slow choices inside its covariant word. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxCoefficientArray_box_reserve (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (p q j : ℕ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth p q (fun X z => γ.coeff α t X z))
    (hΦ : IsBoxSmooth (p + j) (q + (D - 1) - j) Φ) :
    IsBoxSmooth p q (sourceFluxCoefficientArray edge η t Φ k j) := by
  have he : sourceFluxCoefficientArray edge η t Φ k j =
      fun X z v => ∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      γ.coeff α t X z k • γ.map
        (covariantListCoefficients η (List.ofFn α) Φ j X z u)).sum := rfl
  rw [he]
  apply isBoxSmooth_pi
  intro v
  apply IsBoxSmooth.sum
  intro u _
  apply IsBoxSmooth.sum
  intro d _
  apply isBoxSmooth_list_sum
  intro γ hγ
  apply IsBoxSmooth.sum
  intro α _
  by_cases hja : j ≤ d.1 - 1
  · have hw : IsBoxSmooth p q (covariantListCoefficients η (List.ofFn α) Φ j) := by
      apply covariantListCoefficient_box_reserve
      · simpa only [List.length_ofFn] using hja
      · have hd := (Finset.mem_Icc.mp d.2).2
        exact hΦ.mono le_rfl (by simp only [List.length_ofFn]; omega)
    have hscalar := (hΓ v u d γ hγ α).clm_comp (ContinuousLinearMap.proj k)
    have hvector := hw.clm_comp (γ.map.comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) u))
    simpa only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] using!
      isBoxSmooth_bilinear hscalar hvector
        (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)
  · have hz := covariantListCoefficients_above_degree η (List.ofFn α) Φ j
      (by simp only [List.length_ofFn]; omega)
    simp only [hz, Pi.zero_apply, map_zero, smul_zero]
    exact IsBoxSmooth.zero
end

/-! Source-flux coefficients can be computed component by component under their exact reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceFluxComponentCoefficient (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (j : ℕ) (v : ι) :
    Vec 2 → Vec 2 → h v := fun X z =>
  ∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      γ.coeff α t X z k • γ.map
        (covariantListCoefficients η (List.ofFn α) (fun Y y => Φ Y y u) j X z)).sum

theorem sourceFluxCoefficientArray_component_eq (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (j : ℕ)
    (hΦ : IsBoxSmooth j ((D - 1) - j) Φ) (v : ι) :
    (fun X z => sourceFluxCoefficientArray edge η t Φ k j X z v) =
      sourceFluxComponentCoefficient edge η t Φ k j v := by
  funext X z
  unfold sourceFluxCoefficientArray sourceFluxComponentCoefficient
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  apply congrArg List.sum
  apply List.map_congr_left
  intro γ _
  apply Finset.sum_congr rfl
  intro α _
  by_cases hj : j ≤ d.val - 1
  · have hw : IsBoxSmooth j ((List.ofFn α).length - j) Φ :=
      hΦ.mono le_rfl (by
        have hd := (Finset.mem_Icc.mp d.2).2
        simp only [List.length_ofFn]
        omega)
    have he := covariantListCoefficients_postcomposition η (List.ofFn α) j
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) u) Φ
      (by simpa only [List.length_ofFn] using hj) hw
    have hp := congrFun (congrFun he X) z
    simpa only [ContinuousLinearMap.proj_apply] using congrArg
      (fun x => γ.coeff α t X z k • γ.map x) hp.symm
  · rw [covariantListCoefficients_above_degree η (List.ofFn α) Φ j
        (by simp only [List.length_ofFn]; omega),
      covariantListCoefficients_above_degree η (List.ofFn α) (fun Y y => Φ Y y u) j
        (by simp only [List.length_ofFn]; omega)]
    simp only [Pi.zero_apply]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A constituent product needs only slow-jet majorants at the test point. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem covariantCoefficientProduct_mixed_grading_at_slow_point (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (lam A C : ℝ) (hlam : 0 ≤ lam) (hA : 0 ≤ A) (hC : 0 ≤ C)
    (w : List (Fin 2)) (hj : j ≤ w.length)
    (γ : Vec 2 → Vec 2 → ℝ) (f : Vec 2 → Vec 2 → E) (M : E →L[ℝ] F) (X : Vec 2)
    (hγ : IsBoxSmooth p q γ) (hf : IsBoxSmooth (p + j) (q + w.length - j) f)
    (hbγ : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (γ Y) z) X‖ ≤ A * lam ^ a)
    (hbf : ∀ a ≤ p + j, ∀ b ≤ q + w.length - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => γ Y y • M (covariantListCoefficients η w f j Y y)) z) X‖ ≤
      (2 ^ (p + 2 * q) * A * (‖M‖ * (2 ^ w.length * C))) * lam ^ (δ + j + p) := by
  let c := covariantListCoefficients η w f j
  have hc : IsBoxSmooth p q c := covariantListCoefficient_box_reserve η w j p q f hj hf
  have hmc := hc.clm_comp M
  have hbm : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Z => iteratedFDeriv ℝ b (fun z => M (c Z z)) y) X‖ ≤
        (‖M‖ * (2 ^ w.length * C)) * lam ^ ((δ + j) + a) := by
    intro a ha b hb y
    have hh := norm_mixed_jet_postcomposition_le p q a b ha hb c hc.1 (hc.2.1 b hb) M X y
    have hword := covariantListCoefficient_mixed_grading_at_slow_point η hη δ lam C hlam hC X w a b j hj f
      (hf.mono (by omega) (by omega))
      (fun r hr s hs z => hbf r (by omega) s (by omega) z) y
    apply hh.trans
    calc
      _ ≤ ‖M‖ * ((2 ^ w.length * C) * lam ^ (δ + j + a)) :=
        mul_le_mul_of_nonneg_left hword (norm_nonneg _)
      _ = _ := (mul_assoc _ _ _).symm
  have hh := norm_mixed_bilinear_graded_le_at_slow_point p 0 (δ + j) lam A
    (‖M‖ * (2 ^ w.length * C)) hlam hA (by positivity)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
    ContinuousLinearMap.opNorm_lsmul_le X q γ (fun Y y => M (c Y y)) hγ hmc
    (by simpa only [Nat.zero_add] using hbγ) hbm z
  simpa only [Nat.zero_add] using! hh

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Every diagonal mean of degree at least three is the exact drift divergence, with automatic cutoff. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem liftMean_diagonal_ge_three (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (hn : 3 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) 0 n t X =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z q) •
          liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t Y z)) X (basisVec q) := by
  let Φ := liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t
  let Ψ := liftApply (n - 2) (Cc 0 (n - 2)) (fun _ => f) t
  have hG := setting_metric_contDiff_one P t ht
  have hw := setting_normalized_drift_contDiff_one P t ht
  have hΦ : GoodField 2 Φ := liftApply_goodField_of_seq Q hseq hX hZ (Nat.zero_le H) _ hf ht
  have hΨ : CoefField True 2 Ψ :=
    liftApply_centField_of_seq Q hseq hX hZ (Nat.zero_le H) (Or.inl (by omega)) hf ht
  have hB2 := cellB2_centField Q.η Q.G t hG hΨ
  have hB1 := cellB1_continuous_slice Q.η Q.G Q.v t hG
    (fun q => (hw q).continuous) Φ hΦ X
  have he : liftMean Q Cc (fun _ => f) 0 n t X =
      fieldCellMean (fun z => cellB1 Q.η Q.G Q.v t Φ X z + cellB2 Q.η Q.G t Ψ X z) := by
    simp only [liftMean, liftA, Φ, Ψ, show 2 ≤ n by omega, ite_true, sub_zero]
  rw [he, AVRegularity.fieldCellMean_add hB1 (hB2.1.continuous_slice X),
    hB2.2 trivial X, add_zero]
  exact fieldCellMean_cellB1_formula Q.η Q.G Q.v t hG hw Φ hΦ X

include P in
theorem liftMean_diagonal_above_cutoff (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (n : ℕ) (hn : N + 2 ≤ n) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) 0 n t X = 0 := by
  have hthree : 3 ≤ n := by have hN := P.N_ge; omega
  rw [liftMean_diagonal_ge_three P sX sZ hX hZ Cc hseq f hf n hthree t ht X]
  have he : liftApply (n - 1) (Cc 0 (n - 1)) (fun _ => f) t = 0 := by
    exact congrFun (liftApply_above_cutoff Q sX sZ a b N H Cc hseq
      0 (Nat.zero_le H) (n - 1) (by omega) (fun _ => f)) t
  rw [he]
  simp [fieldCellMean]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Normalized cell means retain the source degree through the full slow reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem normalized_fieldCellMean_graded_jet_bound (p q sZ δ : ℕ) (hq : q ≤ p)
    (A : Vec 2 →L[ℝ] ℝ) (lam C : ℝ) (hlam : 0 ≤ lam) (hC : 0 ≤ C)
    (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p sZ (fun X z => (Real.exp ((lam • A) X))⁻¹ • f X z))
    (hb : ∀ j ≤ p, ∀ X z,
      ‖iteratedFDeriv ℝ j (fun Y => (Real.exp ((lam • A) Y))⁻¹ • f Y z) X‖ ≤
        C * lam ^ (δ + j)) :
    ContDiff ℝ (p : ℕ∞)
        (fun X => (Real.exp ((lam • A) X))⁻¹ • fieldCellMean (f X)) ∧
      ∀ X, ‖iteratedFDeriv ℝ q
        (fun Y => (Real.exp ((lam • A) Y))⁻¹ • fieldCellMean (f Y)) X‖ ≤
          ((2 : ℝ) ^ p * C) * lam ^ (δ + q) := by
  have he (X : Vec 2) :
      fieldCellMean (fun z => (Real.exp ((lam • A) X))⁻¹ • f X z) =
        (Real.exp ((lam • A) X))⁻¹ • fieldCellMean (f X) :=
    AVRegularity.fieldCellMean_smul _ _
  have hm := fieldCellMean_graded_jet_bound p q sZ δ hq
    (fun X z => (Real.exp ((lam • A) X))⁻¹ • f X z) hf (fun _ => C) lam hb
  simp_rw [he] at hm
  refine ⟨hm.1, fun X => (hm.2 X).trans ?_⟩
  have hpow : (2 : ℝ) ^ q ≤ 2 ^ p := pow_le_pow_right₀ (by norm_num) hq
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hpow hC)
    (pow_nonneg hlam _)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleComparison.Lift

/-! Clamping the primitive endpoint supplies a uniform slow-jet budget on the centering window. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

def clampedIntervalPrimitive (f : ℝ → Vec 2 → E) (s : ℝ) (X : Vec 2) : E :=
  ∫ y in (0 : ℝ)..(projIcc 0 1 (by norm_num) s : ℝ), f y X

omit [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] in
theorem clampedIntervalPrimitive_continuous_endpoint (f : ℝ → Vec 2 → E)
    (hf : ∀ X, Continuous (fun y => f y X)) (X : Vec 2) :
    Continuous (fun s => clampedIntervalPrimitive f s X) :=
  (intervalPrimitive_continuous _ (hf X)).comp
    (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := by norm_num)).subtype_val

omit [CompleteSpace E] in
theorem clampedIntervalPrimitive_contDiff (n : ℕ) (f : ℝ → Vec 2 → E)
    (hm : ∀ X, Measurable (fun y => f y X))
    (hs : ∀ y, ContDiff ℝ (n : ℕ∞) (f y))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ y X, ‖iteratedFDeriv ℝ j (f y) X‖ ≤ C j)
    (s : ℝ) : ContDiff ℝ (n : ℕ∞) (clampedIntervalPrimitive f s) :=
  parameter_intervalIntegral_contDiff n f hm hs C hb 0 _

omit [CompleteSpace E] in
theorem clampedIntervalPrimitive_iteratedFDeriv_norm_le (n : ℕ) (f : ℝ → Vec 2 → E)
    (hm : ∀ X, Measurable (fun y => f y X))
    (hs : ∀ y, ContDiff ℝ (n : ℕ∞) (f y))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ y X, ‖iteratedFDeriv ℝ j (f y) X‖ ≤ C j)
    (j : ℕ) (hj : j ≤ n) (s : ℝ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ j (clampedIntervalPrimitive f s) X‖ ≤ (2 : ℝ) ^ j * C j := by
  let r := projIcc (0 : ℝ) 1 (by norm_num) s
  have hC : 0 ≤ C j := (norm_nonneg _).trans (hb j hj 0 0)
  have hh := parameter_intervalIntegral_iteratedFDeriv_norm_le n f hm hs C hb j hj X
    0 (r : ℝ) r.2.1
  have he : (2 : ℝ) ^ j * (C j * ((r : ℝ) - 0)) ≤ (2 : ℝ) ^ j * C j := by
    simp only [sub_zero]
    exact mul_le_mul_of_nonneg_left
      ((mul_le_mul_of_nonneg_left r.2.2 hC).trans_eq (mul_one _)) (by positivity)
  exact hh.trans he

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Scalar Fourier coefficient integrals preserve the slow source reserve. -/

theorem unitProfileFourierCoeff_parameter_contDiff (p : ℕ) (f : Vec 2 → ℝ → ℂ)
    (hm : ∀ X, Measurable (f X))
    (hs : ∀ z, ContDiff ℝ (p : ℕ∞) (fun X => f X z))
    (C : ℕ → ℝ) (hb : ∀ r ≤ p, ∀ z X,
      ‖iteratedFDeriv ℝ r (fun Y => f Y z) X‖ ≤ C r) (m : ℤ) :
    ContDiff ℝ (p : ℕ∞) (fun X => unitProfileFourierCoeff (f X) m) := by
  have he : (fun X => unitProfileFourierCoeff (f X) m) =
      fun X => ∫ z in (0 : ℝ)..1, fourier (-m) (z : AddCircle ((1 : ℝ) - 0)) * f X z := by
    funext X
    simp only [unitProfileFourierCoeff, fourierCoeffOn_eq_integral, sub_zero, div_one,
      one_smul, smul_eq_mul]
  rw [he]
  refine parameter_intervalIntegral_contDiff p _ ?_ ?_ C ?_ 0 1
  · intro X
    simpa only [Function.comp_def, Pi.mul_apply] using!
      (((fourier (-m)).continuous.comp (AddCircle.continuous_mk' ((1 : ℝ) - 0))).measurable).mul (hm X)
  · intro z
    exact unit_complex_mul_contDiff p _ (hs z) _
  · intro r hr z X
    exact (norm_iteratedFDeriv_unit_complex_mul_le p r hr _ (hs z) _
      (by simp only [fourier_apply, Circle.norm_coe]) X).trans (hb r hr z X)

theorem unitProfileFourierCoeff_parameter_jet_norm_le (p q : ℕ) (hq : q ≤ p)
    (f : Vec 2 → ℝ → ℂ) (hm : ∀ X, Measurable (f X))
    (hs : ∀ z, ContDiff ℝ (p : ℕ∞) (fun X => f X z))
    (C : ℕ → ℝ) (hb : ∀ r ≤ p, ∀ z X,
      ‖iteratedFDeriv ℝ r (fun Y => f Y z) X‖ ≤ C r) (m : ℤ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y => unitProfileFourierCoeff (f Y) m) X‖ ≤ (2 : ℝ) ^ q * C q := by
  have he : (fun X => unitProfileFourierCoeff (f X) m) =
      fun X => ∫ z in (0 : ℝ)..1, fourier (-m) (z : AddCircle ((1 : ℝ) - 0)) * f X z := by
    funext X
    simp only [unitProfileFourierCoeff, fourierCoeffOn_eq_integral, sub_zero, div_one,
      one_smul, smul_eq_mul]
  rw [he]
  have hh := parameter_intervalIntegral_iteratedFDeriv_norm_le p
    (fun z Y => fourier (-m) (z : AddCircle ((1 : ℝ) - 0)) * f Y z)
    (fun Y => by simpa only [Function.comp_def, Pi.mul_apply] using!
      (((fourier (-m)).continuous.comp (AddCircle.continuous_mk' ((1 : ℝ) - 0))).measurable).mul (hm Y))
    (fun z => unit_complex_mul_contDiff p _ (hs z) _) C
    (fun r hr z Y => (norm_iteratedFDeriv_unit_complex_mul_le p r hr _ (hs z) _
      (by simp only [fourier_apply, Circle.norm_coe]) Y).trans (hb r hr z Y)) q hq X 0 1 (by norm_num)
  simpa only [sub_zero, mul_one] using hh

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The full source convolution has zero constant degree in the original setting. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_liftSourceConvolution_zero
    (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) :
    liftSourceConvolution Q Cc (fun _ => f) hh 0 t X z = 0 := by
  classical
  simp only [liftSourceConvolution, min_zero, Finset.sum_range_succ,
    Finset.sum_range_zero, zero_add, Nat.zero_sub]
  by_cases hh0 : hh = 0
  · subst hh
    have he : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y := by
      funext Y y
      exact hseq.1 f hf t ht Y y
    rw [he]
    exact sourceCoeff_zero_independent Q.edge Q.η t f (hf.of_le (by simp))
      (setting_source_fast_contDiff_one P t ht) (setting_source_slow_contDiff_one P t ht) X z
  · have he := congrFun (liftApply_positive_grade_zero_degree Q sX sZ a b N H Cc hseq
      hh (by omega) hhh (fun _ => f)) t
    rw [he]
    change sourceCoeff Q.edge Q.η 0 t 0 X z = 0
    rw [sourceCoeff_zero_input]
    rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! The integrated metric perturbation retains its smallness factor in every slow jet. -/

def transverseMetricDifferenceExponent (rate : ℝ) (d : ℝ → Vec 2 → ℝ)
    (a b : ℝ) (X : Vec 2) : ℝ := -rate * ∫ t in a..b, d t X

theorem transverseMetricDifferenceExponent_contDiff
    (p : ℕ) (d : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => d t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (d t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (d t) X‖ ≤ C j)
    (rate a b : ℝ) : ContDiff ℝ (p : ℕ∞) (transverseMetricDifferenceExponent rate d a b) :=
  (parameter_intervalIntegral_contDiff p d hm hs C hb a b).const_smul (-rate)

theorem transverseMetricDifferenceExponent_scaled_jet_le
    (p : ℕ) (d : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => d t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (d t))
    (M eps lam rate a b : ℝ) (hM : 0 ≤ M) (heps : 0 ≤ eps) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hab : a ≤ b)
    (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (d t) X‖ ≤ M * eps * lam ^ j)
    (r : ℕ) (hr : r ≤ p) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (transverseMetricDifferenceExponent rate d a b) X‖ ≤
      ((2 : ℝ) ^ p * M * eps * rate * (b - a)) * lam ^ r := by
  let I := fun Y => ∫ t in a..b, d t Y
  let A : ℝ →L[ℝ] ℝ := (-rate) • ContinuousLinearMap.id ℝ ℝ
  have hi : ContDiff ℝ (p : ℕ∞) I :=
    parameter_intervalIntegral_contDiff p d hm hs (fun j => M * eps * lam ^ j) hb a b
  have hA : ‖A‖ = rate := by
    simp only [A, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hrate,
      ContinuousLinearMap.norm_id, mul_one]
  have he := A.norm_iteratedFDeriv_comp_left (x := X) hi.contDiffAt
    (n := r) (by exact_mod_cast hr)
  change ‖iteratedFDeriv ℝ r (A ∘ I) X‖ ≤ _
  apply he.trans
  rw [hA]
  have hbI := parameter_intervalIntegral_iteratedFDeriv_norm_le p d hm hs
    (fun j => M * eps * lam ^ j) hb r hr X a b hab
  calc
    _ ≤ rate * ((2 : ℝ) ^ r * ((M * eps * lam ^ r) * (b - a))) :=
      mul_le_mul_of_nonneg_left hbI hrate
    _ ≤ rate * ((2 : ℝ) ^ p * ((M * eps * lam ^ r) * (b - a))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right
        (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) hr)
        (mul_nonneg (mul_nonneg (mul_nonneg hM heps) (pow_nonneg hlam _))
          (sub_nonneg.mpr hab))) hrate
    _ = _ := by ring

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleComparison.Lift

/-! The centering integral is unchanged by clamping its endpoint to the unit interval. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem centeredIntervalPrimitive_eq_clamped (f : ℝ → Vec 2 → E) (r : ℝ) (X : Vec 2) :
    centeredIntervalPrimitive (fun y => f y X) r =
      (∫ y in (0 : ℝ)..r, f y X) - ∫ s in (0 : ℝ)..1, clampedIntervalPrimitive f s X := by
  unfold centeredIntervalPrimitive
  congr 1
  apply intervalIntegral.integral_congr
  intro s hs
  have hmem : s ∈ Icc (0 : ℝ) 1 := by
    simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
  simp only [clampedIntervalPrimitive, projIcc_of_mem (by norm_num) hmem]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The second diagonal mean includes the molecular metric flux. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftMean_diagonal_second_of_predecessor_fields
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2)
    (hid : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y)
    (hΦ : GoodField 2 (liftApply 1 (Cc 0 1) (fun _ => f) t)) :
    liftMean Q Cc (fun _ => f) 0 2 t X =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z q) • liftApply 1 (Cc 0 1) (fun _ => f) t Y z) -
          Q.η • ∑ j : Fin 2, Q.G t Y q j • fderiv ℝ f Y (basisVec j)) X (basisVec q) := by
  have he : liftMean Q Cc (fun _ => f) 0 2 t X =
      fieldCellMean (fun z =>
        cellB1 Q.η Q.G Q.v t (liftApply 1 (Cc 0 1) (fun _ => f) t) X z +
        cellB2 Q.η Q.G t (fun Y _ => f Y) X z) := by
    simp only [liftMean, liftA, show 2 ≤ (2 : ℕ) by omega, ite_true, sub_zero]
    norm_num only
    rw [hid]
  rw [he]
  exact fieldCellMean_diagonal_second_cross Q.η Q.G Q.v t
    (setting_metric_contDiff_one P t ht) (setting_normalized_drift_contDiff_one P t ht)
    _ hΦ
    f (hf.of_le (by simp)) X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The outer source divergence raises degree with its slow derivative and preserves normalized grading. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_normalized_covariantStep_le (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hj : j ≠ 0) (lam U V : ℝ)
    (hlam : 0 ≤ lam) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (A : Vec 2 →L[ℝ] ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p (q + 1) (P j)) (hs : IsBoxSmooth (p + 1) q (P (j - 1)))
    (X : Vec 2)
    (hbf : ∀ a ≤ p, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (P j Y) z) X‖ ≤
        (Real.exp ((lam • A) X) * U) * lam ^ (δ + j + a))
    (hbs : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (P (j - 1) Y) z) X‖ ≤
        (Real.exp ((lam • A) X) * V) * lam ^ (δ + (j - 1) + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • covariantCoefficientStep η k P j Y y) z) X‖ ≤
      (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p * (U + V)) * lam ^ (δ + j + p) := by
  have hbox := covariantCoefficientStep_box_reserve p q j η k P hf (fun _ => hs)
  have hb : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (covariantCoefficientStep η k P j Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * (U + V)) * lam ^ ((δ + j) + a) := by
    intro a ha b hb y
    have hf' := hf.mono ha (show b + 1 ≤ q + 1 by omega)
    have hs' := hs.mono (show a + 1 ≤ p + 1 by omega) hb
    have hh := norm_mixed_covariantCoefficientStep_graded_le hj η hη k P hf' hs' X y δ lam
      (Real.exp ((lam • A) X) * U) (Real.exp ((lam • A) X) * V) (hbf a ha (b + 1) (by omega) y)
      (hbs (a + 1) (by omega) b hb y)
    apply hh.trans_eq
    ring
  exact norm_mixed_exponential_normalized_le p q (δ + j) A lam (U + V) hlam
    (add_nonneg hU hV) (covariantCoefficientStep η k P j) hbox X hb z
end

/-! The normalized degree-zero divergence needs fast jets only. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_normalized_covariantStep_zero_le (η : ℝ) (p q δ : ℕ)
    (lam U : ℝ) (hlam : 0 ≤ lam) (hU : 0 ≤ U)
    (A : Vec 2 →L[ℝ] ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p (q + 1) (P 0)) (X : Vec 2)
    (hbf : ∀ a ≤ p, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (P 0 Y) z) X‖ ≤
        (Real.exp ((lam • A) X) * U) * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • covariantCoefficientStep η k P 0 Y y) z) X‖ ≤
      (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p * U) * lam ^ (δ + p) := by
  have hbox := covariantCoefficientStep_box_reserve p q 0 η k P hf
    (fun hn => False.elim (hn rfl))
  have hb : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (covariantCoefficientStep η k P 0 Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * U) * lam ^ (δ + a) := by
    intro a ha b hb y
    exact (norm_mixed_covariantCoefficientStep_zero_le η k P
      (hf.mono ha (by omega)) X y).trans (hbf a ha (b + 1) (by omega) y)
  exact norm_mixed_exponential_normalized_le p q δ A lam U hlam hU
    (covariantCoefficientStep η k P 0) hbox X hb z
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleComparison.Lift

/-! Centering a periodic primitive preserves the full available slow regularity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_centeredIntervalPrimitive_contDiff (n : ℕ) (f : ℝ → Vec 2 → E)
    (hf : ∀ X, Continuous (fun y => f y X))
    (hs : ∀ y, ContDiff ℝ (n : ℕ∞) (f y))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ y X, ‖iteratedFDeriv ℝ j (f y) X‖ ≤ C j)
    (r : ℝ) : ContDiff ℝ (n : ℕ∞) (fun X => centeredIntervalPrimitive (fun y => f y X) r) := by
  have hm := fun X => (hf X).measurable
  have hanchor := parameter_intervalIntegral_contDiff n f hm hs C hb 0 r
  have hcenter := parameter_intervalIntegral_contDiff n (clampedIntervalPrimitive f)
    (fun X => (clampedIntervalPrimitive_continuous_endpoint f hf X).measurable)
    (clampedIntervalPrimitive_contDiff n f hm hs C hb)
    (fun j => (2 : ℝ) ^ j * C j)
    (fun j hj s X => clampedIntervalPrimitive_iteratedFDeriv_norm_le n f hm hs C hb j hj s X)
    0 1
  have he (X : Vec 2) : (∫ s in (0 : ℝ)..1, clampedIntervalPrimitive f s X) =
      ∫ s in (0 : ℝ)..1, ∫ y in (0 : ℝ)..s, f y X := by
    apply intervalIntegral.integral_congr
    intro s hs
    have hmem : s ∈ Icc (0 : ℝ) 1 := by simpa only [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using hs
    simp only [clampedIntervalPrimitive, projIcc_of_mem (by norm_num) hmem]
  have hefun : (fun X => centeredIntervalPrimitive (fun y => f y X) r) =
      fun X => (∫ y in (0 : ℝ)..r, f y X) - ∫ s in (0 : ℝ)..1, clampedIntervalPrimitive f s X := by
    funext X
    rw [he]
    rfl
  rw [hefun]
  exact hanchor.sub hcenter

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Weighted source modes consume fast jets without spending additional slow reserve. -/

theorem weightedProfileFourierCoeff_parameter_data (p q j : ℕ) (hq : q ≤ p)
    (f : Vec 2 → ℝ → ℂ) (hf : ∀ X, ContDiff ℝ (j : ℕ∞) (f X))
    (hper : ∀ X, Function.Periodic (f X) 1)
    (hs : ∀ z, ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (f X) z))
    (C : ℕ → ℝ) (hb : ∀ r ≤ p, ∀ z X,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedDeriv j (f Y) z) X‖ ≤ C r)
    (hcenter : ∀ X, unitProfileFourierCoeff (f X) 0 = 0) (m : ℤ) :
    ContDiff ℝ (p : ℕ∞) (fun X => profileFourierFrequency m ^ j * unitProfileFourierCoeff (f X) m) ∧
    ∀ X, ‖iteratedFDeriv ℝ q
      (fun Y => profileFourierFrequency m ^ j * unitProfileFourierCoeff (f Y) m) X‖ ≤
      (2 : ℝ) ^ q * C q := by
  by_cases hm0 : m = 0
  · subst m
    have he : (fun X => profileFourierFrequency 0 ^ j * unitProfileFourierCoeff (f X) 0) = 0 := by
      funext X
      simp only [hcenter, mul_zero, Pi.zero_apply]
    rw [he]
    refine ⟨contDiff_const, fun X => ?_⟩
    have hC : 0 ≤ C q := (norm_nonneg _).trans (hb q hq 0 X)
    simpa using mul_nonneg (pow_nonneg (by norm_num : (0 : ℝ) ≤ 2) q) hC
  · have he : (fun X => profileFourierFrequency m ^ j * unitProfileFourierCoeff (f X) m) =
        fun X => unitProfileFourierCoeff (iteratedDeriv j (f X)) m := by
      funext X
      simpa only [profileFourierFrequency] using
        (unitProfileFourierCoeff_iteratedDeriv j (f X) (hf X) (hper X) m hm0).symm
    rw [he]
    have hm : ∀ X, Measurable (iteratedDeriv j (f X)) :=
      fun X => ((hf X).continuous_iteratedDeriv j le_rfl).measurable
    exact ⟨unitProfileFourierCoeff_parameter_contDiff p _ hm hs C hb m,
      fun X => unitProfileFourierCoeff_parameter_jet_norm_le p q hq _ hm hs C hb m X⟩

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Slow propagator jets retain both their scale power and the exact damping kernel. -/

theorem transverseModeKernel_parameter_scaled_jet (n q : ℕ) (hq : q ≤ n)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (M lam rate a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hab : a ≤ b)
    (hb : ∀ j ≤ n, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (X : Vec 2) :
    ‖iteratedFDeriv ℝ q
      (fun Y => transverseModeKernel rate (fun t => g t Y) a b) X‖ ≤
      q.factorial * transverseModeKernel rate (fun t => g t X) a b *
        (max 1 ((2 : ℝ) ^ n * M * rate * (b - a))) ^ q * lam ^ q := by
  let I := fun Y => ∫ t in a..b, g t Y
  let A : ℝ →L[ℝ] ℝ := (-rate) • ContinuousLinearMap.id ℝ ℝ
  have hi : ContDiff ℝ (n : ℕ∞) I :=
    parameter_intervalIntegral_contDiff n g hm hs (fun j => M * lam ^ j) hb a b
  have hA : ‖A‖ = rate := by
    simp only [A, norm_smul, norm_neg, Real.norm_eq_abs, abs_of_nonneg hrate,
      ContinuousLinearMap.norm_id, mul_one]
  have hu : ContDiff ℝ (q : ℕ∞) (A ∘ I) :=
    (A.contDiff.comp hi).of_le (by exact_mod_cast hq)
  have hj : ∀ j, 1 ≤ j → j ≤ q → ‖iteratedFDeriv ℝ j (A ∘ I) X‖ ≤
      ((2 : ℝ) ^ n * M * rate * (b - a)) * lam ^ j := by
    intro j _ hjq
    have hij := parameter_intervalIntegral_iteratedFDeriv_norm_le n g hm hs
      (fun j => M * lam ^ j) hb j (hjq.trans hq) X a b hab
    have ha := A.norm_iteratedFDeriv_comp_left (x := X) hi.contDiffAt
      (n := j) (by exact_mod_cast hjq.trans hq)
    apply ha.trans
    rw [hA]
    calc
      rate * ‖iteratedFDeriv ℝ j I X‖ ≤
          rate * ((2 : ℝ) ^ j * ((M * lam ^ j) * (b - a))) :=
        mul_le_mul_of_nonneg_left hij hrate
      _ ≤ rate * ((2 : ℝ) ^ n * ((M * lam ^ j) * (b - a))) := by
        gcongr
        · norm_num
        · exact hjq.trans hq
      _ = _ := by ring
  simpa only [A, I, Function.comp_def, smul_apply,
    ContinuousLinearMap.id_apply, smul_eq_mul, transverseModeKernel] using
    norm_iteratedFDeriv_exp_scaled_le q (A ∘ I) hu X lam
      ((2 : ℝ) ^ n * M * rate * (b - a)) hlam hj

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit source coefficients preserve the transverse profile class at every parameter degree. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxCoefficientArray_transverse (par : Fin 2) (I : Set ℝ)
    (edge : ConstituentEdges D h) (η : ℝ)
    (Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (hΦ : IsTransverseOn par I Φ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsTransverseOn par I (γ.coeff α))
    (k : Fin 2) (j : ℕ) :
    IsTransverseOn par I (fun t => sourceFluxCoefficientArray edge η t (Φ t) k j) := by
  intro t ht X z s
  ext v
  simp only [sourceFluxCoefficientArray]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro d _
  apply congrArg List.sum
  apply List.map_congr_left
  intro γ hm
  apply Finset.sum_congr rfl
  intro α _
  have hw := covariantListCoefficients_transverse par I η (List.ofFn α) Φ hΦ j
  have hwEq : covariantListCoefficients η (List.ofFn α) (Φ t) j X (z + s • basisVec par) =
      covariantListCoefficients η (List.ofFn α) (Φ t) j X z := hw t ht X z s
  rw [hΓ v u d γ hm α t ht X z s, hwEq]

theorem sourceCoefficientArray_transverse (par : Fin 2) (I : Set ℝ)
    (edge : ConstituentEdges D h) (η : ℝ)
    (Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (hΦ : IsTransverseOn par I Φ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsTransverseOn par I (γ.coeff α))
    (j : ℕ) : IsTransverseOn par I (fun t => sourceCoefficientArray edge η t (Φ t) j) := by
  apply transverse_finset_sum Finset.univ
  intro k _
  exact covariantCoefficientStep_transverse par k I η
    (fun i t => sourceFluxCoefficientArray edge η t (Φ t) k i)
    (fun i => sourceFluxCoefficientArray_transverse par I edge η Φ hΦ hΓ k i) j
end

/-! The second diagonal mean includes the molecular metric flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftMean_diagonal_second (sX sZ : ℕ) (hX : 2 ≤ sX) (hZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    liftMean Q Cc (fun _ => f) 0 2 t X =
      ∑ q : Fin 2, fderiv ℝ (fun Y => fieldCellMean (fun z =>
        (Real.sqrt Q.η * Q.v t z q) • liftApply 1 (Cc 0 1) (fun _ => f) t Y z) -
          Q.η • ∑ j : Fin 2, Q.G t Y q j • fderiv ℝ f Y (basisVec j)) X (basisVec q) := by
  have hid : liftApply 0 (Cc 0 0) (fun _ => f) t = fun Y _ => f Y := by
    funext Y z
    exact hseq.1 f hf t ht Y z
  have he : liftMean Q Cc (fun _ => f) 0 2 t X =
      fieldCellMean (fun z =>
        cellB1 Q.η Q.G Q.v t (liftApply 1 (Cc 0 1) (fun _ => f) t) X z +
        cellB2 Q.η Q.G t (fun Y _ => f Y) X z) := by
    simp only [liftMean, liftA, show 2 ≤ (2 : ℕ) by omega, ite_true, sub_zero]
    norm_num only
    rw [hid]
  rw [he]
  exact fieldCellMean_diagonal_second_cross Q.η Q.G Q.v t
    (setting_metric_contDiff_one P t ht) (setting_normalized_drift_contDiff_one P t ht)
    _ (liftApply_goodField_of_seq Q hseq hX hZ (Nat.zero_le H) 1 hf ht)
    f (hf.of_le (by simp)) X
end

end AVRegularity.CycleComparison.Lift
end
