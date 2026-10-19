-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.CovariantPolynomialMean
import AVRegularity.CycleComparison.Lift.ProfileModeHilbertJets
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Lift.MixedJetEnergyBound
public import AVRegularity.CycleComparison.Lift.NormalizedCellB1ScaledDriftMixedGrading
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Bounds

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The zeroth coefficient step consumes a fast jet and no slow jet. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_covariantCoefficientStep_zero_le {r q : ℕ}
    (η : ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth r (q + 1) (P 0)) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (covariantCoefficientStep η k P 0 Y) z) X‖ ≤
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (P 0 Y) z) X‖ := by
  have he : covariantCoefficientStep η k P 0 =
      fun Y y => fderiv ℝ (P 0 Y) y (basisVec k) := by
    funext Y y
    simp only [covariantCoefficientStep, ite_true, add_zero]
    rfl
  rw [he]
  simpa only [norm_basisVec, one_mul] using norm_mixed_fast_direction_le hf (basisVec k) X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Padding the finite coefficient vector to a larger degree does not change the literal word. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem dEpsWord_polynomial_with_degree {q : ℕ} (α : DerivativeWord2 q)
    (Q : ℕ) (hq : q ≤ Q) (f : Vec 2 → Vec 2 → E) (hf : GoodField q f)
    (η ε : ℝ) (X z : Vec 2) :
    dEpsWord η ε α f X z = ∑ i ∈ Finset.range (Q + 1),
      ε ^ i • covariantListCoefficients η (List.ofFn α) f i X z := by
  have he := covariantList_polynomial_identity η (List.ofFn α) f
    (by simpa only [List.length_ofFn] using hf) ε X z
  change dEpsWord η ε α f X z = _
  have he' : dEpsWord η ε α f X z = ∑ i ∈ Finset.range (q + 1),
      ε ^ i • covariantListCoefficients η (List.ofFn α) f i X z := by
    simpa only [dEpsWord, List.length_ofFn] using he
  rw [he']
  apply Finset.sum_subset (Finset.range_mono (by omega))
  intro i _ hi
  have hqi : q < i := by
    have hh : ¬ i < q + 1 := fun h => hi (Finset.mem_range.mpr h)
    omega
  have hz := covariantListCoefficients_above_degree η (List.ofFn α) f i
    (by simpa only [List.length_ofFn] using hqi)
  rw [hz, smul_zero]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Reserved ordered slow derivatives commute with measurable time integration. -/

section
variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem orderedDerivative_parameter_integral (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) :
    orderedDerivative α (fun x => ∫ t, f t x ∂μ) =
      fun x => ∫ t, orderedDerivative α (f t) x ∂μ := by
  induction q with
  | zero => simp [orderedDerivative]
  | succ q ih =>
    let β : DerivativeWord2 q := fun i => α i.castSucc
    have hh := ih (by omega) β
    have hf : ∀ t, ContDiff ℝ (1 : ℕ∞) (orderedDerivative β (f t)) := by
      intro t
      exact contDiff_orderedDerivative β ((hs t).of_le
        (by exact_mod_cast (show 1 + q ≤ n by omega)))
    have hme : ∀ x, Measurable (fun t => orderedDerivative β (f t) x) :=
      fun x => orderedDerivative_parameter_measurable f n hm hs q (by omega) β x
    have h₀ : ∀ t x, ‖orderedDerivative β (f t) x‖ ≤ C q := by
      intro t x
      exact (norm_orderedDerivative_le ((hs t).of_le (by exact_mod_cast (show q ≤ n by omega)))
        β x).trans (hb q (by omega) t x)
    have h₁ : ∀ t x, ‖fderiv ℝ (orderedDerivative β (f t)) x‖ ≤ C (q + 1) := by
      intro t x
      have hl := norm_iteratedFDeriv_orderedDerivative_le (p := 1) β
        ((hs t).of_le (by exact_mod_cast (show 1 + q ≤ n by omega))) x
      simpa only [norm_iteratedFDeriv_one, Nat.add_comm 1 q] using
        hl.trans (hb (1 + q) (by omega) t x)
    have hd := parameter_integral_hasFDerivAt μ
      (fun t x => orderedDerivative β (f t) x) hme
      (fun t => (hf t).differentiable one_ne_zero) (C q) (C (q + 1)) h₀ h₁
    rw [orderedDerivative_succ, hh]
    funext x
    rw [(hd x).fderiv]
    have hi : Integrable (fun t => fderiv ℝ (orderedDerivative β (f t)) x) μ :=
      (integrable_const (C (q + 1))).mono'
        (fderiv_parameter_stronglyMeasurable _ hme
          (fun t => (hf t).differentiable one_ne_zero) x).aestronglyMeasurable
        (ae_of_all μ (fun t => h₁ t x))
    rw [ContinuousLinearMap.integral_apply hi]
    apply integral_congr_ae
    exact ae_of_all μ (fun t => (congrFun (orderedDerivative_succ α (f t)) x).symm)
end

/-! The original lift reserves discharge the source-coefficient regularity used in its means. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_source_fast_reserve : D ≤ qf := by
  rw [P.qf_eq]
  omega

include P in
theorem setting_source_slow_reserve : 1 ≤ qs := by
  have hn := P.N_ge
  have hd := P.D_ge
  have hpos : 0 < 4 * (H + 1) * (N + D) ^ 2 := by positivity
  rw [P.qs_eq]
  omega

include P in
theorem setting_source_fast_contDiff (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X, ContDiff ℝ (D : ℕ∞) (γ.coeff α t X) := by
  intro v u d γ hγ α X
  exact ((P.coeff_smooth v u d γ hγ α t ht).1 X).of_le
    (by exact_mod_cast setting_source_fast_reserve P)

include P in
theorem setting_source_fast_contDiff_one (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α X, ContDiff ℝ 1 (γ.coeff α t X) := by
  intro v u d γ hγ α X
  exact (setting_source_fast_contDiff P t ht v u d γ hγ α X).of_le
    (by exact_mod_cast (show 1 ≤ D by have hh := P.D_ge; omega))

include P in
theorem setting_source_slow_contDiff_one (t : ℝ) (ht : t ∈ Set.Icc a b) :
    ∀ v u d, ∀ γ ∈ Q.edge v u d, ∀ α z,
      ContDiff ℝ 1 (fun X => γ.coeff α t X z) := by
  intro v u d γ hγ α z
  exact (boxSmooth_slow_contDiff (P.coeff_smooth v u d γ hγ α t ht) z).of_le
    (by exact_mod_cast setting_source_slow_reserve P)

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

include P in
theorem setting_first_source_mean (f : Vec 2 → ∀ i, h i)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) :
    fieldCellMean (fun z => sourceCoeff Q.edge Q.η 1 t (fun X _ => f X) X z) = 0 := by
  exact fieldCellMean_sourceCoeff_one_independent Q.edge Q.η t f (hf.of_le (by simp))
    (setting_source_fast_contDiff_one P t ht) (setting_source_slow_contDiff_one P t ht) X
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Rectangular reserves suffice to commute each covariant word coefficient with a fixed output map. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem covariantListCoefficients_postcomposition (η : ℝ) (w : List (Fin 2))
    (j : ℕ) (L : E →L[ℝ] F) (f : Vec 2 → Vec 2 → E)
    (hj : j ≤ w.length) (hf : IsBoxSmooth j (w.length - j) f) :
    covariantListCoefficients η w (fun Y y => L (f Y y)) j =
      fun X z => L (covariantListCoefficients η w f j X z) := by
  induction w using List.reverseRecOn generalizing j with
  | nil =>
    have hj0 : j = 0 := by simpa using hj
    subst j
    simp only [covariantListCoefficients_nil, ite_true]
  | append_singleton w k ih =>
    have hj' : j ≤ w.length + 1 := by simpa using hj
    have hf' : IsBoxSmooth j (w.length + 1 - j) f := by simpa using hf
    have hfast : IsBoxSmooth 0 1 (covariantListCoefficients η w f j) := by
      by_cases hle : j ≤ w.length
      · apply covariantListCoefficient_box_reserve η w j 0 1 f hle
        simpa only [Nat.zero_add] using hf'.mono le_rfl (by omega)
      · rw [covariantListCoefficients_above_degree η w f j (by omega)]
        exact IsBoxSmooth.zero
    have hslow : j ≠ 0 → IsBoxSmooth 1 0 (covariantListCoefficients η w f (j - 1)) := by
      intro hn
      apply covariantListCoefficient_box_reserve η w (j - 1) 1 0 f (by omega)
      exact hf'.mono (by omega) (by omega)
    have he (i : ℕ) (hi : i = j ∨ i = j - 1) :
        covariantListCoefficients η w (fun Y y => L (f Y y)) i =
          fun X z => L (covariantListCoefficients η w f i X z) := by
      by_cases hle : i ≤ w.length
      · apply ih i hle
        rcases hi with rfl | rfl
        · exact hf'.mono le_rfl (by omega)
        · exact hf'.mono (by omega) (by omega)
      · rw [covariantListCoefficients_above_degree η w _ i (by omega),
          covariantListCoefficients_above_degree η w f i (by omega)]
        simp only [map_zero]
    rw [covariantListCoefficients_append_singleton, covariantListCoefficients_append_singleton]
    funext X z
    change fastPartial k (covariantListCoefficients η w (fun Y y => L (f Y y)) j) X z +
      (if j = 0 then 0 else Real.sqrt η • slowPartial k
        (covariantListCoefficients η w (fun Y y => L (f Y y)) (j - 1)) X z) = _
    rw [he j (Or.inl rfl), he (j - 1) (Or.inr rfl)]
    exact covariantCoefficientStep_postcomposition η k (covariantListCoefficients η w f) j L
      hfast hslow X z

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The original reserves discharge the classical cross-operator coefficient regularity at every pulse time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_metric_contDiff_one (t : ℝ) (ht : t ∈ Set.Icc a b) (i j : Fin 2) :
    ContDiff ℝ (1 : ℕ∞) (fun X => Q.G t X i j) :=
  (P.G_smooth t ht i j).of_le (by exact_mod_cast setting_source_slow_reserve P)

include P in
theorem setting_normalized_drift_contDiff_upto (r : ℕ) (hr : r ≤ qf)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i : Fin 2) :
    ContDiff ℝ (r : ℕ∞) (fun z => Real.sqrt Q.η * Q.v t z i) := by
  have he : (fun z => Real.sqrt Q.η * Q.v t z i) =
      fun z => Real.sqrt Q.η * (V t (z par.rev) * basisVec par i) := by
    funext z
    rw [P.v_shear t z]
    rfl
  rw [he]
  have hV : ContDiff ℝ (r : ℕ∞) (V t) :=
    (P.V_smooth t ht).of_le (by exact_mod_cast hr)
  exact contDiff_const.mul ((hV.comp
    (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ).contDiff).mul contDiff_const)

include P in
theorem setting_normalized_drift_contDiff_one (t : ℝ) (ht : t ∈ Set.Icc a b) (i : Fin 2) :
    ContDiff ℝ (1 : ℕ∞) (fun z => Real.sqrt Q.η * Q.v t z i) := by
  have hq : 1 ≤ qf := by rw [P.qf_eq]; omega
  exact setting_normalized_drift_contDiff_upto P 1 hq t ht i
end

/-! Slow regularity is parameterized by the available reserve rather than fixed to the target order. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_output_supported : K + N + D ≤ qs := by
  have hd := P.D_ge
  have hn := P.N_ge
  have hsq : N + D ≤ (N + D) ^ 2 := le_self_pow₀ (by omega) (by decide)
  have hmul : (N + D) ^ 2 ≤ (H + 1) * (N + D) ^ 2 :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [P.qs_eq]
  simp only [Nat.mul_assoc]
  omega

include P in
theorem setting_tail_ambient_supported : (K + N + D + 2) + N + D ≤ qs := by
  have hd := P.D_ge
  have hn := P.N_ge
  have hsq : N + D ≤ (N + D) ^ 2 := le_self_pow₀ (by omega) (by decide)
  have hmul : (N + D) ^ 2 ≤ (H + 1) * (N + D) ^ 2 :=
    Nat.le_mul_of_pos_left _ (by omega)
  rw [P.qs_eq]
  simp only [Nat.mul_assoc]
  omega
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit finite source-flux coefficients, before the outer covariant divergence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceFluxCoefficientArray (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (j : ℕ) :
    Vec 2 → Vec 2 → ∀ i, h i := fun X z v =>
  ∑ u : ι, ∑ d : Finset.Icc 2 D,
    ((edge v u d).map fun γ => ∑ α : DerivativeWord2 (d.1 - 1),
      γ.coeff α t X z k • γ.map
        (covariantListCoefficients η (List.ofFn α) Φ j X z u)).sum

theorem sourceFluxCoefficientArray_above_degree (edge : ConstituentEdges D h) (η t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) (j : ℕ) (hj : D - 1 < j) :
    sourceFluxCoefficientArray edge η t Φ k j = fun _ _ => 0 := by
  funext X z v
  simp only [sourceFluxCoefficientArray]
  apply Finset.sum_eq_zero
  intro u _
  apply Finset.sum_eq_zero
  intro d _
  apply List.sum_eq_zero
  intro a ha
  obtain ⟨γ, _, rfl⟩ := List.mem_map.mp ha
  apply Finset.sum_eq_zero
  intro α _
  have hd := (Finset.mem_Icc.mp d.2).2
  have hz := covariantListCoefficients_above_degree η (List.ofFn α) Φ j
    (by simp only [List.length_ofFn]; omega)
  rw [hz]
  simp only [Pi.zero_apply, map_zero, smul_zero]

theorem sourceFlux_polynomial_identity (edge : ConstituentEdges D h) (η ε t : ℝ)
    (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : GoodField D Φ)
    (k : Fin 2) (X z : Vec 2) :
    sourceFlux edge η ε t Φ k X z = ∑ j ∈ Finset.range D,
      ε ^ j • sourceFluxCoefficientArray edge η t Φ k j X z := by
  classical
  funext v
  have hw : ∀ d : Finset.Icc 2 D, ∀ α : DerivativeWord2 (d.1 - 1),
      dEpsWord η ε α Φ X z = ∑ j ∈ Finset.range D,
        ε ^ j • covariantListCoefficients η (List.ofFn α) Φ j X z := by
    intro d α
    have hd := Finset.mem_Icc.mp d.2
    have hD : D - 1 + 1 = D := by omega
    simpa only [hD] using dEpsWord_polynomial_with_degree α (D - 1)
      (by omega) Φ (hΦ.mono (by omega)) η ε X z
  simp only [sourceFlux, Finset.sum_apply, Pi.smul_apply, sourceFluxCoefficientArray]
  simp_rw [hw]
  simp only [Finset.sum_apply, Pi.smul_apply, map_sum, map_smul,
    Finset.smul_sum, List.smul_sum, List.map_map, Function.comp_def]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro d _
  have hcomm (l : List (Constituent d.1 (h u) (h v)))
      (s : Finset ℕ) (f : Constituent d.1 (h u) (h v) → ℕ → h v) :
      (l.map fun a => ∑ j ∈ s, f a j).sum = ∑ j ∈ s, (l.map fun a => f a j).sum := by
    induction l with
    | nil => simp
    | cons a l ih => simp only [List.map_cons, List.sum_cons, Finset.sum_add_distrib, ih]
  have hγ : ∀ γ ∈ edge v u d,
      (∑ α : DerivativeWord2 (d.1 - 1), ∑ j ∈ Finset.range D,
        γ.coeff α t X z k • (ε ^ j • γ.map (covariantListCoefficients η (List.ofFn α) Φ j X z u))) =
      ∑ j ∈ Finset.range D, ∑ α : DerivativeWord2 (d.1 - 1),
        ε ^ j • (γ.coeff α t X z k • γ.map (covariantListCoefficients η (List.ofFn α) Φ j X z u)) := by
    intro γ _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro α _
    exact smul_comm (γ.coeff α t X z k) (ε ^ j) _
  have hm := List.map_congr_left hγ
  rw [hm]
  exact hcomm (edge v u d) (Finset.range D) _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Clamped interpolation supplies a globally measurable integration parameter without changing the kernel difference. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

def clampedMetricInterpolationParameter (θ : ℝ) : ℝ := Set.projIcc (0 : ℝ) 1 zero_le_one θ

theorem clampedMetricInterpolationParameter_mem (θ : ℝ) :
    clampedMetricInterpolationParameter θ ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one θ).2

theorem clampedMetricInterpolationParameter_continuous : Continuous clampedMetricInterpolationParameter :=
  (continuous_projIcc (a := (0 : ℝ)) (b := 1) (h := zero_le_one)).subtype_val

theorem transverseModeKernel_interpolation_formula (rate : ℝ) (g : ℝ → ℝ)
    (s t θ : ℝ) (hi : IntervalIntegrable g volume s t) :
    transverseModeKernel rate (fun r => (1 - θ) + θ * g r) s t =
      Real.exp (-rate * ((1 - θ) * (t - s) + θ * ∫ r in s..t, g r)) := by
  unfold transverseModeKernel
  congr 1
  congr 1
  rw [intervalIntegral.integral_add (intervalIntegrable_const (μ := volume)) (hi.const_mul θ),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const]
  simp only [smul_eq_mul]
  ring

omit [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E] in
theorem transverseModeKernel_clamped_interpolation_continuous (rate : ℝ) (g : ℝ → ℝ)
    (s t : ℝ) (hi : IntervalIntegrable g volume s t) :
    Continuous (fun θ => transverseModeKernel rate
      (fun r => (1 - clampedMetricInterpolationParameter θ) + clampedMetricInterpolationParameter θ * g r) s t) := by
  simp_rw [transverseModeKernel_interpolation_formula rate g s t _ hi]
  have hc := clampedMetricInterpolationParameter_continuous
  fun_prop

theorem transverseModeKernel_difference_source_eq_integral (rate : ℝ) (g : ℝ → Vec 2 → ℝ)
    (s t : ℝ) (hi : ∀ X, IntervalIntegrable (fun r => g r X) volume s t) (f : Vec 2 → E) :
    (fun X => (transverseModeKernel rate (fun r => g r X) s t -
      transverseModeKernel rate (fun _ => 1) s t) • f X) =
    fun X => ∫ θ in (0 : ℝ)..1,
      transverseModeKernel rate (fun r => scalarMetricInterpolation
        (clampedMetricInterpolationParameter θ) g r X) s t •
        ((-rate * ∫ r in s..t, g r X - 1) • f X) := by
  funext X
  rw [transverseModeKernel_metric_difference_integral rate (fun r => g r X) s t (hi X)]
  rw [← intervalIntegral.integral_smul_const]
  apply intervalIntegral.integral_congr
  intro θ hθ
  have hθ' : θ ∈ Set.Icc (0 : ℝ) 1 := by simpa only [Set.uIcc_of_le zero_le_one] using hθ
  have he : clampedMetricInterpolationParameter θ = θ := congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hθ')
  dsimp only
  rw [he]
  exact mul_smul _ _ _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Quantitative mixed jets follow the same separate fast and slow branches as the coefficient recursion. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_covariantCoefficientStep_le {r q j : ℕ} (hj : j ≠ 0)
    (η : ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth r (q + 1) (P j))
    (hs : IsBoxSmooth (r + 1) q (P (j - 1))) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (covariantCoefficientStep η k P j Y) z) X‖ ≤
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (P j Y) z) X‖ +
      Real.sqrt η * ‖iteratedFDeriv ℝ (r + 1)
        (fun Y => iteratedFDeriv ℝ q (P (j - 1) Y) z) X‖ := by
  have he : covariantCoefficientStep η k P j = fun Y y =>
      fastPartial k (P j) Y y + Real.sqrt η • slowPartial k (P (j - 1)) Y y := by
    funext Y y
    simp only [covariantCoefficientStep, hj, ite_false]
  have hslow : IsBoxSmooth r q (slowPartial k (P (j - 1))) :=
    isBoxSmooth_slow_direction hs (basisVec k)
  have hfast := hf.fastPartial k
  rw [he]
  apply (norm_mixed_jet_add_le hfast (hslow.const_smul (Real.sqrt η)) X z).trans
  rw [norm_mixed_jet_const_smul hslow, abs_of_nonneg (Real.sqrt_nonneg η)]
  apply add_le_add
  · simpa only [fastPartial, norm_basisVec, one_mul] using! norm_mixed_fast_direction_le hf (basisVec k) X z
  · apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg η)
    simpa only [slowPartial, norm_basisVec, one_mul] using! norm_mixed_slow_direction_le hs (basisVec k) X z

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit covariant word coefficients are measurable in time using a finite ambient reserve. -/

variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem covariantListCoefficient_parameter_measurable (η : ℝ) (w : List (Fin 2)) :
    ∀ (f : T → Vec 2 → Vec 2 → E),
      (∀ X z, Measurable (fun t => f t X z)) →
      (∀ t, IsBoxSmooth w.length w.length (f t)) →
      ∀ j X z, Measurable (fun t => covariantListCoefficients η w (f t) j X z) := by
  induction w using List.reverseRecOn with
  | nil =>
    intro f hm _ j X z
    simp only [covariantListCoefficients_nil]
    split_ifs
    · exact hm X z
    · exact measurable_const
  | append_singleton w k ih =>
    intro f hm hf j X z
    have hlen : (w ++ [k]).length = w.length + 1 := by simp
    have hm' (i : ℕ) (Y y : Vec 2) :
        Measurable (fun t => covariantListCoefficients η w (f t) i Y y) :=
      ih f hm (fun t => (hf t).mono (by omega) (by omega)) i Y y
    have hb (i : ℕ) (t : T) : IsBoxSmooth 1 1 (covariantListCoefficients η w (f t) i) := by
      by_cases hi : i ≤ w.length
      · apply covariantListCoefficient_box_reserve η w i 1 1 (f t) hi
        exact (hf t).mono (by omega) (by omega)
      · rw [covariantListCoefficients_above_degree η w (f t) i (by omega)]
        exact IsBoxSmooth.zero
    simp only [covariantListCoefficients_append_singleton, covariantCoefficientStep]
    apply Measurable.add
    · exact fastPartial_parameter_measurable _ (hm' j)
        (fun t Y => ((hb j t).1 Y).differentiable one_ne_zero) k X z
    · by_cases hj : j = 0
      · simp only [hj, ite_true]
        exact measurable_const
      · simp only [hj, ite_false]
        exact (slowPartial_parameter_measurable _ (hm' (j - 1))
          (fun t y => (boxSmooth_slow_contDiff (hb (j - 1) t) y).differentiable one_ne_zero)
          k X z).const_smul (Real.sqrt η)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit uniform slow-jet bounds after integration over a finite time measure. -/

variable {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_integral_orderedDerivative_norm_le (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) (x : Vec 2) :
    ‖orderedDerivative α (fun x => ∫ t, f t x ∂μ) x‖ ≤ C q * μ.real Set.univ := by
  rw [orderedDerivative_parameter_integral μ n f hm hs C hb q hq α]
  apply norm_integral_le_of_norm_le_const
  exact ae_of_all μ (fun t => (norm_orderedDerivative_le
    ((hs t).of_le (by exact_mod_cast hq)) α x).trans (hb q hq t x))

theorem parameter_integral_iteratedFDeriv_norm_le (μ : Measure T) [IsFiniteMeasure μ]
    (n : ℕ) (f : T → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j)
    (q : ℕ) (hq : q ≤ n) (x : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun x => ∫ t, f t x ∂μ) x‖ ≤
      (2 : ℝ) ^ q * (C q * μ.real Set.univ) := by
  have hi : ContDiff ℝ (q : ℕ∞) (fun x => ∫ t, f t x ∂μ) :=
    (parameter_integral_contDiff μ n f hm hs C hb).of_le
    (by exact_mod_cast hq)
  apply (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words hi x).trans
  calc
    _ ≤ ∑ α : DerivativeWord2 q, C q * μ.real Set.univ :=
      Finset.sum_le_sum (fun α _ =>
        parameter_integral_orderedDerivative_norm_le μ n f hm hs C hb q hq α x)
    _ = _ := by simp

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleComparison.Lift

/-! Reserved ordered slow derivatives commute with oriented finite interval integration. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem orderedDerivative_parameter_intervalIntegral
    (n : ℕ) (f : ℝ → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j)
    (a b : ℝ) (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) :
    orderedDerivative α (fun x => ∫ t in a..b, f t x) =
      fun x => ∫ t in a..b, orderedDerivative α (f t) x := by
  have h₁ := parameter_integral_contDiff (volume.restrict (Ioc a b)) n f hm hs C hb
  have h₂ := parameter_integral_contDiff (volume.restrict (Ioc b a)) n f hm hs C hb
  simp only [intervalIntegral]
  rw [AVRegularity.orderedDerivative_sub α
    (h₁.of_le (by exact_mod_cast hq)) (h₂.of_le (by exact_mod_cast hq)),
    orderedDerivative_parameter_integral (volume.restrict (Ioc a b)) n f hm hs C hb q hq α,
    orderedDerivative_parameter_integral (volume.restrict (Ioc b a)) n f hm hs C hb q hq α]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original metric envelope bounds each scalar matrix-entry jet. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_metric_entry_jet_bound (r : ℕ) (hr : r ≤ qs)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun Y => Q.G t Y i j) X‖ ≤ max (CG r * lam ^ r) 0 := by
  let A : (Fin 2 → Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Vec 2) →L[ℝ] Vec 2)
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro M
    rw [one_mul]
    exact (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
  have hs : ContDiff ℝ (qs : ℕ∞) (fun Y (i j : Fin 2) => Q.G t Y i j) :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => P.G_smooth t ht i j))
  have he := A.norm_iteratedFDeriv_comp_left
    (f := fun Y (i j : Fin 2) => Q.G t Y i j) (x := X)
    (N := (qs : ℕ∞)) hs.contDiffAt (n := r) (by exact_mod_cast hr)
  have hb : ‖iteratedFDeriv ℝ r (Q.G t) X‖ ≤ max (CG r * lam ^ r) 0 := by
    apply (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp
    rw [ofReal_norm]
    have hh := (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le X le_rfl))).trans
      (P.G_jets r hr)
    exact hh.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  change ‖iteratedFDeriv ℝ r (A ∘ Q.G t) X‖ ≤ _
  apply he.trans
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ r (Q.G t) X‖ :=
      mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact hb

include P in
theorem setting_metric_entry_scaled_jet_bound (r : ℕ) (hr : r ≤ qs)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X : Vec 2) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun Y => Q.G t Y i j) X‖ ≤ max (CG r) 0 * lam ^ r := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hh := setting_metric_entry_jet_bound P r hr t ht X i j
  rw [max_mul_of_nonneg (CG r) 0 (pow_nonneg hlam r), zero_mul]
  exact hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The source operator's positive polynomial coefficients average to the exact slow flux divergence. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D p : ℕ}

theorem source_family_coefficient_mean (edge : ConstituentEdges D h) (η t : ℝ)
    (hcoeff : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z))
    {Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (hΦ : EpsPoly False p D Φ)
    (j : ℕ) (hj : 1 ≤ j) (X : Vec 2) :
    fieldCellMean (fun z => ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε => sourceOp edge η ε t (Φ ε) X z) 0) =
      Real.sqrt η • ∑ k : Fin 2, fderiv ℝ (fun Y =>
        fieldCellMean (sourceFluxCoeff edge η (j - 1) t Φ k Y)) X (basisVec k) := by
  simpa only [sourceOp, sourceFluxCoeff] using!
    covariant_flux_family_coefficient_mean (p + (D - 1)) j hj
      (fun k ε => sourceFlux edge η ε t (Φ ε) k)
      (sourceFlux_family_epsPoly_good edge η t hcoeff hΦ) η X

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The slow branch adds one derivative and one parameter degree with exactly the same scale power. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_covariantCoefficientStep_graded_le {r q j : ℕ} (hj : j ≠ 0)
    (η : ℝ) (hη : η ≤ 1) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth r (q + 1) (P j))
    (hs : IsBoxSmooth (r + 1) q (P (j - 1))) (X z : Vec 2)
    (δ : ℕ) (lam A B : ℝ)
    (hA : ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (P j Y) z) X‖ ≤
      A * lam ^ (δ + j + r))
    (hB : ‖iteratedFDeriv ℝ (r + 1)
      (fun Y => iteratedFDeriv ℝ q (P (j - 1) Y) z) X‖ ≤
      B * lam ^ (δ + (j - 1) + (r + 1))) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ q
      (covariantCoefficientStep η k P j Y) z) X‖ ≤
      (A + B) * lam ^ (δ + j + r) := by
  have hgrade : δ + (j - 1) + (r + 1) = δ + j + r := by omega
  rw [hgrade] at hB
  have hsqrt : Real.sqrt η ≤ 1 := by
    simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt hη
  apply (norm_mixed_covariantCoefficientStep_le hj η k P hf hs X z).trans
  calc
    _ ≤ ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ (q + 1) (P j Y) z) X‖ +
        ‖iteratedFDeriv ℝ (r + 1) (fun Y => iteratedFDeriv ℝ q (P (j - 1) Y) z) X‖ := by
      apply add_le_add le_rfl
      simpa only [one_mul] using mul_le_mul_of_nonneg_right hsqrt (norm_nonneg _)
    _ ≤ A * lam ^ (δ + j + r) + B * lam ^ (δ + j + r) := add_le_add hA hB
    _ = _ := (add_mul A B _).symm
end

/-! An identity metric has scale-graded jets with an order-only enlarged metric budget. -/

def identityMetricJetBudget (CG : ℕ → ℝ) (r : ℕ) : ℝ := max (CG r) 1

theorem identityMatrix_norm_le_one :
    ‖(fun i j : Fin 2 => if i = j then (1 : ℝ) else 0)‖ ≤ 1 := by
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro i
  apply (pi_norm_le_iff_of_nonneg zero_le_one).mpr
  intro j
  split_ifs <;> norm_num

theorem identityMetric_scaled_jet_bound (CG : ℕ → ℝ) (lam : ℝ) (hlam : 0 ≤ lam)
    (r : ℕ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun _ : Vec 2 => fun i j : Fin 2 =>
      if i = j then (1 : ℝ) else 0) X‖ ≤ identityMetricJetBudget CG r * lam ^ r := by
  cases r with
  | zero =>
    rw [norm_iteratedFDeriv_zero, pow_zero, mul_one]
    exact identityMatrix_norm_le_one.trans (le_max_right _ _)
  | succ r =>
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    exact mul_nonneg (zero_le_one.trans (le_max_right _ _)) (pow_nonneg hlam _)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The exact metric perturbation premise controls all reserved scalar entry jets. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_metric_difference_entry_scaled_jet_bound
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (r : ℕ) (hr : r ≤ qs) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (X : Vec 2) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun Y => Q.G t Y i j - (if i = j then 1 else 0)) X‖ ≤
      max (CGI r) 0 * g * lam ^ r := by
  let F := fun Y => fun i j : Fin 2 => Q.G t Y i j - (if i = j then 1 else 0)
  let A : (Fin 2 → Vec 2) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj j : Vec 2 →L[ℝ] ℝ).comp
      (ContinuousLinearMap.proj i : (Fin 2 → Vec 2) →L[ℝ] Vec 2)
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro M
    rw [one_mul]
    exact (norm_le_pi_norm (M i) j).trans (norm_le_pi_norm M i)
  have hs : ContDiff ℝ (qs : ℕ∞) F :=
    contDiff_pi.mpr (fun i => contDiff_pi.mpr (fun j => (P.G_smooth t ht i j).sub contDiff_const))
  have he := A.norm_iteratedFDeriv_comp_left (f := F) (x := X)
    (N := (qs : ℕ∞)) hs.contDiffAt (n := r) (by exact_mod_cast hr)
  have hb : ‖iteratedFDeriv ℝ r F X‖ ≤ max (CGI r * g * lam ^ r) 0 := by
    apply (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp
    rw [ofReal_norm]
    have hh := (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le X le_rfl))).trans (hGI r hr)
    exact hh.trans (ENNReal.ofReal_le_ofReal (le_max_left _ _))
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hb' : ‖iteratedFDeriv ℝ r F X‖ ≤ max (CGI r) 0 * g * lam ^ r := by
    simpa only [max_mul_of_nonneg _ _ (pow_nonneg hlam r),
      max_mul_of_nonneg _ _ hg, zero_mul] using hb
  change ‖iteratedFDeriv ℝ r (A ∘ F) X‖ ≤ _
  exact he.trans ((mul_le_mul_of_nonneg_right hA (norm_nonneg _)).trans
    (by rw [one_mul]; exact hb'))

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleComparison.Lift

/-! Quantitative slow-jet bounds for an ordered finite time window. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem parameter_intervalIntegral_iteratedFDeriv_norm_le (n : ℕ) (f : ℝ → Vec 2 → E)
    (hm : ∀ x, Measurable (fun t => f t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (f t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (f t) x‖ ≤ C j)
    (q : ℕ) (hq : q ≤ n) (x : Vec 2) (a b : ℝ) (hab : a ≤ b) :
    ‖iteratedFDeriv ℝ q (fun x => ∫ t in a..b, f t x) x‖ ≤
      (2 : ℝ) ^ q * (C q * (b - a)) := by
  have he : (fun x => ∫ t in a..b, f t x) =
      fun x => ∫ t, f t x ∂volume.restrict (Ioc a b) := by
    funext x
    exact intervalIntegral.integral_of_le hab
  rw [he]
  have hh := parameter_integral_iteratedFDeriv_norm_le
    (volume.restrict (Ioc a b)) n f hm hs C hb q hq x
  simpa [Measure.real, Measure.restrict_apply_univ, Real.volume_Ioc,
    ENNReal.toReal_ofReal (sub_nonneg.mpr hab)] using hh

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The identity-metric comparison preserves drift and history with a fixed enlarged budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_identity_metric :
    IsLiftSetting (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf
      (identityMetricJetBudget CG) Cw Cj edge Θ := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  refine { P with G_symm := ?_, G_meas := ?_, G_smooth := ?_, G_ellip := ?_, G_jets := ?_ }
  · intro t X i j
    simp only [eq_comm]
  · exact fun _ _ _ => measurable_const
  · exact fun _ _ _ _ => contDiff_const
  · intro t ht X ξ
    have he : (∑ i : Fin 2, ∑ j : Fin 2, (if i = j then (1 : ℝ) else 0) * ξ i * ξ j) =
        ∑ i, ξ i ^ 2 := by
      apply Finset.sum_congr rfl
      intro i _
      simp [sq]
    rw [he]
    have hn : 0 ≤ ∑ i : Fin 2, ξ i ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg (ξ i)
    constructor <;> linarith
  · intro r hr
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    apply iSup_le
    intro X
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (identityMetric_scaled_jet_bound CG lam hlam r X)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The explicit flux vector is the actual Taylor vector and inherits its periodic good-field regularity. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] in
theorem sourceFluxCoefficientArray_normalized (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : GoodField D Φ)
    (k : Fin 2) (j : ℕ) (X z : Vec 2) :
    ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε => sourceFlux edge η ε t Φ k X z) 0 =
      sourceFluxCoefficientArray edge η t Φ k j X z := by
  have he : (fun ε => sourceFlux edge η ε t Φ k X z) =
      fun ε => ∑ i ∈ Finset.range ((D - 1) + 1),
        ε ^ i • sourceFluxCoefficientArray edge η t Φ k i X z := by
    funext ε
    simpa only [Nat.sub_add_cancel hD] using
      sourceFlux_polynomial_identity edge η ε t Φ hΦ k X z
  rw [he]
  exact normalized_polynomial_coefficient (D - 1) j _ (fun i hi => by
    rw [sourceFluxCoefficientArray_above_degree edge η t Φ k i hi])

theorem sourceFluxCoefficientArray_good (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (Φ : Vec 2 → Vec 2 → ∀ i, h i) (hΦ : GoodField D Φ)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z)) (k : Fin 2) (j : ℕ) :
    GoodField 1 (sourceFluxCoefficientArray edge η t Φ k j) := by
  obtain ⟨P, hP, hz, he⟩ := sourceFlux_epsPoly_good edge η t hΓ hΦ k
  have hc : sourceFluxCoefficientArray edge η t Φ k j = P j := by
    funext X z
    rw [← sourceFluxCoefficientArray_normalized edge hD η t Φ hΦ k j X z]
    have he' : (fun ε => sourceFlux edge η ε t Φ k X z) =
        fun ε => ∑ i ∈ Finset.range ((D - 1) + 1), ε ^ i • P i X z :=
      funext fun ε => he ε X z
    rw [he']
    exact normalized_polynomial_coefficient (D - 1) j _ (fun i hi => hz i hi X z)
  rw [hc]
  exact (hP j).1

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Uniform normalized-shear profile jets are bounded directly by the original drift envelope. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_normalized_drift_jet_bound (j : ℕ) (hj : j ≤ qf)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j (fun y => Real.sqrt Q.η • Q.v t y) z‖ ≤ max (Cw j) 0 := by
  apply (ENNReal.ofReal_le_ofReal_iff (le_max_right _ _)).mp
  rw [ofReal_norm]
  have hh := (le_iSup_of_le t (le_iSup_of_le ht (le_iSup_of_le z le_rfl))).trans
    (P.w_jets j hj)
  have hb := hh.trans (ENNReal.ofReal_le_ofReal (le_max_left (Cw j) 0))
  simpa using! hb

include P in
theorem setting_normalized_drift_profile_jets_bounded
    (line : ℝ →L[ℝ] Vec 2) (A : Vec 2 →L[ℝ] ℂ) :
    ∃ C : ℕ → ℝ, (∀ j ≤ qf, 0 ≤ C j) ∧
      ∀ j ≤ qf, ∀ t ∈ Set.Icc a b, ∀ x : ℝ,
        ‖iteratedDeriv j (fun y => A (Real.sqrt Q.η • Q.v t (line y))) x‖ ≤ C j := by
  refine ⟨fun j => ‖A‖ * (max (Cw j) 0 * ‖line‖ ^ j), ?_, ?_⟩
  · intro j _
    positivity
  · intro j hj t ht x
    have hw : ContDiff ℝ (qf : ℕ∞) (fun z => Real.sqrt Q.η • Q.v t z) :=
      contDiff_pi.mpr (fun i => setting_normalized_drift_contDiff_upto P qf le_rfl t ht i)
    have hb := norm_iteratedDeriv_dual_linear_profile_le
      (fun z => Real.sqrt Q.η • Q.v t z) qf j hw hj line A x
    apply hb.trans
    exact mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right (setting_normalized_drift_jet_bound P j hj t ht (line x))
        (pow_nonneg (norm_nonneg line) j)) (norm_nonneg A)

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal lift mean on physical input equals the restored divergence action. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)



include P in
theorem setting_physical_mean_action (Cc : ℕ → ℕ → LiftCoeff ι h) (hh n : ℕ)
    (b₀ : MeanCoeff ι h)
    (hact : ∀ f : Vec 2 → ∀ i, h i, ContDiff ℝ (⊤ : ℕ∞) f → ∀ t ∈ Set.Icc a b, ∀ X,
      liftMean Q Cc (fun _ => f) hh n t X = meanApply n b₀ (fun _ => f) t X)
    (ap : ℝ → Vec 2 → ∀ i, h i) (hf : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (ap t))
    (t : ℝ) (ht : t ∈ Set.Icc (ℓ ^ 2 * a) (ℓ ^ 2 * b)) (x : Vec 2) :
    ((ℓ ^ 2)⁻¹ * εc ^ n) • liftMean Q Cc (fun s X => ap (ℓ ^ 2 * s) (ρ • X)) hh n
        (t / ℓ ^ 2) (ρ⁻¹ • x) =
      meanApply n (scaledMeanCoefficient ((ℓ ^ 2)⁻¹ * εc ^ n) ρ (fun s => s / ℓ ^ 2) b₀) ap t x := by
  have hℓ : ℓ ^ 2 ≠ 0 := pow_ne_zero _ (ne_of_gt (setting_length_pos P))
  have hdate : ℓ ^ 2 * (t / ℓ ^ 2) = t := by rw [mul_div_cancel₀ t hℓ]
  have he := liftMean_congr_time_input Q Cc (fun s X => ap (ℓ ^ 2 * s) (ρ • X))
    (fun _ X => ap t (ρ • X)) hh n (t / ℓ ^ 2) (by funext X; rw [hdate])
  rw [he, hact (fun X => ap t (ρ • X)) ((hf t).comp (contDiff_const_smul ρ))
    (t / ℓ ^ 2) (setting_physical_time_mem P t ht)]
  exact (scaledMeanCoefficient_meanApply n ((ℓ ^ 2)⁻¹ * εc ^ n) ρ (ne_of_gt P.ρ_pos)
    (fun s => s / ℓ ^ 2) b₀ (ap t) (hf t) t x).symm

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Fixed component projections commute with both cross operators under their exact reserves. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cellB1_postcomposition (L : E →L[ℝ] F) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 1 1 f)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB1 η G v t (fun Y y => L (f Y y)) X z = L (cellB1 η G v t f X z) := by
  have hs k Y y := slowPartial_postcomposition L f (hf.mono le_rfl (by omega)) k Y y
  have hz k Y y := fastPartial_postcomposition L f (hf.mono (by omega) le_rfl) k Y y
  have hfs i j Y y : fastPartial i (slowPartial j (fun Z w => L (f Z w))) Y y =
      L (fastPartial i (slowPartial j f) Y y) := by
    have he : slowPartial j (fun Z w => L (f Z w)) = fun Z w => L (slowPartial j f Z w) :=
      funext fun Z => funext fun w => hs j Z w
    rw [he]
    exact fastPartial_postcomposition L (slowPartial j f) (hf.slowPartial j) i Y y
  have hdiv i j Y y :
      slowPartial i (fun Z w => G t Z i j • fastPartial j (fun U a => L (f U a)) Z w) Y y =
        L (slowPartial i (fun Z w => G t Z i j • fastPartial j f Z w) Y y) := by
    have hb := isBoxSmooth_bilinear (hG i j) (hf.fastPartial j)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    have he : (fun Z w => G t Z i j • fastPartial j (fun U a => L (f U a)) Z w) =
        fun Z w => L (G t Z i j • fastPartial j f Z w) := by
      funext Z w
      rw [hz, map_smul]
    rw [he]
    exact slowPartial_postcomposition L _ hb i Y y
  simp only [cellB1, hs, hfs, hdiv, map_sub, map_sum, map_smul, map_add]

theorem cellB2_postcomposition (L : E →L[ℝ] F) (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth 2 0 f)
    (hG : ∀ i j, IsBoxSmooth 1 0 (fun X (_ : Vec 2) => G t X i j)) (X z : Vec 2) :
    cellB2 η G t (fun Y y => L (f Y y)) X z = L (cellB2 η G t f X z) := by
  have hs k Y y := slowPartial_postcomposition L f (hf.mono (by omega) le_rfl) k Y y
  have hdiv i j Y y :
      slowPartial i (fun Z w => G t Z i j • slowPartial j (fun U a => L (f U a)) Z w) Y y =
        L (slowPartial i (fun Z w => G t Z i j • slowPartial j f Z w) Y y) := by
    have hb := isBoxSmooth_bilinear (hG i j) (hf.slowPartial j)
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
    have he : (fun Z w => G t Z i j • slowPartial j (fun U a => L (f U a)) Z w) =
        fun Z w => L (G t Z i j • slowPartial j f Z w) := by
      funext Z w
      rw [hs, map_smul]
    rw [he]
    exact slowPartial_postcomposition L _ hb i Y y
  simp only [cellB2, hdiv, map_neg, map_smul, map_sum]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The actual scalar-forced Riesz cell derivative commutes with absolute state and source sums. -/

theorem cellDualDerivative_scalar_source_tsum {J : Type*}
    (C : CellCoefficients) (hG : IsCellMetric C.G) (V : ℝ)
    (hv : Measurable (fun p : ℝ × Vec 2 => C.v p.1 p.2))
    (hb : ∀ t z, ∑ i, C.v t z i ^ 2 ≤ V ^ 2) (t : ℝ)
    (u : J → TorusHk 1 ℂ) (S : J → ComplexCellL2)
    (hu : Summable u) (hS : Summable S) :
    cellDualDerivative C hG V hv hb t (∑' j, u j) (∑' j, S j) (fun _ => 0) =
      ∑' j, cellDualDerivative C hG V hv hb t (u j) (S j) (fun _ => 0) := by
  rw [cellDualDerivative_scalar_source, (cellGeneratorDualCLM C hG V hv hb t).map_tsum hu,
    cellPivotDualCLM.map_tsum hS]
  simp_rw [cellDualDerivative_scalar_source]
  exact ((cellGeneratorDualCLM C hG V hv hb t).summable hu).tsum_add
    (cellPivotDualCLM.summable hS) |>.symm

end AVRegularity.CycleComparison.Lift
end
