-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.DiagonalSecondMean
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Lift.LiftApplyFiniteVectorSynthesis
import AVRegularity.CycleComparison.Lift.ProfileModeHilbertJets
public import AVRegularity.CycleComparison.Lift.NormalizedCompositionPowerGrading
import AVRegularity.CycleEvolution.CellEnergySpaceRawJetCauchyBound
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Every source constituent on an exponential test has a uniform local exponential majorant. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_mixed_exponential_covariant_product_le (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (lam S C : ℝ) (hlam : 0 ≤ lam) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (w : List (Fin 2)) (hj : j ≤ w.length) (A : Vec 2 →L[ℝ] ℝ)
    (γ : Vec 2 → Vec 2 → ℝ) (f : Vec 2 → Vec 2 → E) (M : E →L[ℝ] F)
    (hγ : IsBoxSmooth p q γ) (hf : IsBoxSmooth (p + j) (q + w.length - j) f) (X : Vec 2)
    (hbγ : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (γ Y) z) X‖ ≤ S * lam ^ a)
    (hbf : ∀ a ≤ p + j, ∀ b ≤ q + w.length - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (a b : ℕ) (ha : a ≤ p) (hb : b ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => γ Y y •
      M (covariantListCoefficients η w (fun Z y => Real.exp ((lam • A) Z) • f Z y) j Y y)) z) X‖ ≤
      (Real.exp ((lam • A) X) *
        (2 ^ (p + 2 * q) * S * (‖M‖ * (2 ^ w.length *
          (2 ^ ((p + j) + 2 * (q + w.length - j)) * (max 1 ‖A‖) ^ (p + j) * C))))) *
        lam ^ (δ + j + a) := by
  let K := 2 ^ ((p + j) + 2 * (q + w.length - j)) * (max 1 ‖A‖) ^ (p + j) * C
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  have hK : 0 ≤ K := by positivity
  have hΦ : IsBoxSmooth (p + j) (q + w.length - j) Φ :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field _ _ _
      (Real.contDiff_exp.comp (lam • A).contDiff)) hf
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hΦb : ∀ r ≤ p + j, ∀ s ≤ q + w.length - j, ∀ y,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (Φ Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * K) * lam ^ (δ + r) := by
    intro r hr s hs y
    exact norm_mixed_exponential_smul_graded_le (p + j) (q + w.length - j) δ A
      lam C hlam hC f hf X hbf r s hr hs y
  have hh := covariantCoefficientProduct_mixed_grading_at_slow_point η hη δ a b j lam S
    (Real.exp ((lam • A) X) * K) hlam hS (by positivity) w hj γ Φ M X
    (hγ.mono ha hb) (hΦ.mono (by omega) (by omega))
    (fun r hr s hs y => hbγ r (hr.trans ha) s (hs.trans hb) y)
    (fun r hr s hs y => hΦb r (by omega) s (by omega) y) z
  apply hh.trans
  calc
    _ ≤ (2 ^ (p + 2 * q) * S * (‖M‖ * (2 ^ w.length *
        (Real.exp ((lam • A) X) * K)))) * lam ^ (δ + j + a) := by
      gcongr
      · norm_num
    _ = _ := by dsimp only [K]; ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Multiplying the integrated perturbation by a source preserves one perturbation factor. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def metricDifferenceSourceBudget (p : ℕ) (M : ℝ) (S : ℕ → ℝ) (q : ℕ) : ℝ :=
  (2 : ℝ) ^ p * M * ∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * S (q - j)

theorem metricDifferenceSourceBudget_nonneg (p q : ℕ) (M : ℝ) (S : ℕ → ℝ)
    (hM : 0 ≤ M) (hS : ∀ j ≤ q, 0 ≤ S j) :
    0 ≤ metricDifferenceSourceBudget p M S q :=
  mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hM)
    (Finset.sum_nonneg fun j _ => mul_nonneg (Nat.cast_nonneg _) (hS (q - j) (Nat.sub_le _ _)))

theorem transverseMetricDifferenceExponent_source_scaled_jet_le
    (p : ℕ) (d : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => d t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (d t))
    (M eps lam rate a b : ℝ) (hM : 0 ≤ M) (heps : 0 ≤ eps) (hlam : 0 ≤ lam)
    (hrate : 0 ≤ rate) (hab : a ≤ b)
    (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (d t) X‖ ≤ M * eps * lam ^ j)
    (f : Vec 2 → E) (hf : ContDiff ℝ (p : ℕ∞) f) (S : ℕ → ℝ)
    (hS : ∀ j ≤ p, 0 ≤ S j) (hfB : ∀ j ≤ p, ∀ X, ‖iteratedFDeriv ℝ j f X‖ ≤ S j * lam ^ j)
    (q : ℕ) (hq : q ≤ p) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y => transverseMetricDifferenceExponent rate d a b Y • f Y) X‖ ≤
      (metricDifferenceSourceBudget p M S q * eps * rate * (b - a)) * lam ^ q := by
  have hd := transverseMetricDifferenceExponent_contDiff p d hm hs
    (fun j => M * eps * lam ^ j) hb rate a b
  have hD : 0 ≤ (2 : ℝ) ^ p * M * eps * rate * (b - a) :=
    mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (pow_nonneg (by norm_num) _) hM) heps) hrate)
      (sub_nonneg.mpr hab)
  have he := norm_iteratedFDeriv_smul_scaled_le q
    (transverseMetricDifferenceExponent rate d a b) f
    (hd.of_le (by exact_mod_cast hq)) (hf.of_le (by exact_mod_cast hq)) X lam hlam
    (fun _ => (2 : ℝ) ^ p * M * eps * rate * (b - a)) S
    (fun _ _ => hD) (fun j hj => hS j (hj.trans hq))
    (fun j hj => transverseMetricDifferenceExponent_scaled_jet_le p d hm hs M eps lam rate a b
      hM heps hlam hrate hab hb j (hj.trans hq) X)
    (fun j hj => hfB j (hj.trans hq) X)
  apply he.trans_eq
  unfold metricDifferenceSourceBudget
  simp only [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Set
namespace AVRegularity.CycleComparison.Lift

/-! The centered periodic primitive commutes with every reserved ordered slow word. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem orderedDerivative_parameter_centeredIntervalPrimitive
    (n : ℕ) (f : ℝ → Vec 2 → E)
    (hf : ∀ X, Continuous (fun y => f y X))
    (hs : ∀ y, ContDiff ℝ (n : ℕ∞) (f y))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ y X, ‖iteratedFDeriv ℝ j (f y) X‖ ≤ C j)
    (q : ℕ) (hq : q ≤ n) (α : DerivativeWord2 q) (r : ℝ) :
    orderedDerivative α (fun X => centeredIntervalPrimitive (fun y => f y X) r) =
      fun X => centeredIntervalPrimitive (fun y => orderedDerivative α (f y) X) r := by
  have hm := fun X => (hf X).measurable
  let F := clampedIntervalPrimitive f
  have hFm := fun X => (clampedIntervalPrimitive_continuous_endpoint f hf X).measurable
  have hFs := clampedIntervalPrimitive_contDiff n f hm hs C hb
  have hFb := fun j hj s X => clampedIntervalPrimitive_iteratedFDeriv_norm_le n f hm hs C hb j hj s X
  have hanchor := parameter_intervalIntegral_contDiff n f hm hs C hb 0 r
  have hcenter := parameter_intervalIntegral_contDiff n F hFm hFs
    (fun j => (2 : ℝ) ^ j * C j) hFb 0 1
  simp_rw [centeredIntervalPrimitive_eq_clamped]
  rw [AVRegularity.orderedDerivative_sub α
    (hanchor.of_le (by exact_mod_cast hq)) (hcenter.of_le (by exact_mod_cast hq)),
    orderedDerivative_parameter_intervalIntegral n f hm hs C hb 0 r q hq α,
    orderedDerivative_parameter_intervalIntegral n F hFm hFs
      (fun j => (2 : ℝ) ^ j * C j) hFb 0 1 q hq α]
  funext X
  congr 1
  apply intervalIntegral.integral_congr
  intro s _
  exact congrFun (orderedDerivative_parameter_intervalIntegral n f hm hs C hb
    0 (projIcc 0 1 (by norm_num) s : ℝ) q hq α) X

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization Set
namespace AVRegularity.CycleComparison.Lift

/-! Joint slow-position and endpoint continuity follows from a fixed-window primitive integral. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [MeasurableSpace E] [BorelSpace E] in
theorem parameter_intervalPrimitive_joint_continuous (f : ℝ → Vec 2 → E)
    (hf : Continuous (Function.uncurry f)) (C : ℝ) (hb : ∀ y X, ‖f y X‖ ≤ C) :
    Continuous (fun p : Vec 2 × ℝ => ∫ y in (0 : ℝ)..p.2, f y p.1) := by
  let H := fun p : Vec 2 × ℝ => ∫ s in (0 : ℝ)..1, f (p.2 * s) p.1
  have hH : Continuous H := by
    apply intervalIntegral.continuous_of_dominated_interval (bound := fun _ => C)
    · intro p
      exact (hf.comp ((continuous_const.mul continuous_id).prodMk continuous_const)).stronglyMeasurable.aestronglyMeasurable
    · intro p
      exact ae_of_all volume (fun s _ => hb (p.2 * s) p.1)
    · exact intervalIntegrable_const
    · exact ae_of_all volume (fun s _ =>
        hf.comp ((continuous_snd.mul continuous_const).prodMk continuous_fst))
  have he (p : Vec 2 × ℝ) : p.2 • H p = ∫ y in (0 : ℝ)..p.2, f y p.1 := by
    simpa only [H, mul_zero, mul_one] using
      intervalIntegral.smul_integral_comp_mul_left (f := fun y => f y p.1)
        (a := (0 : ℝ)) (b := 1) p.2
  exact (continuous_snd.smul hH).congr he

variable [CompleteSpace E]

theorem parameter_centeredIntervalPrimitive_joint_continuous (f : ℝ → Vec 2 → E)
    (hf : Continuous (Function.uncurry f)) (C : ℝ) (hb : ∀ y X, ‖f y X‖ ≤ C) :
    Continuous (fun p : Vec 2 × ℝ => centeredIntervalPrimitive (fun y => f y p.1) p.2) := by
  have hfast (X : Vec 2) : Continuous (fun y => f y X) :=
    hf.comp (continuous_id.prodMk continuous_const)
  have hslow (y : ℝ) : ContDiff ℝ (0 : ℕ∞) (f y) :=
    contDiff_zero.mpr (hf.comp (continuous_const.prodMk continuous_id))
  have hbound : ∀ j ≤ 0, ∀ y X, ‖iteratedFDeriv ℝ j (f y) X‖ ≤ C := by
    intro j hj y X
    have hj0 : j = 0 := by omega
    subst j
    simpa only [norm_iteratedFDeriv_zero] using hb y X
  have hcenter := (parameter_centeredIntervalPrimitive_contDiff 0 f hfast hslow
    (fun _ => C) hbound 0).continuous
  have hanchor := parameter_intervalPrimitive_joint_continuous f hf C hb
  apply (hanchor.add (hcenter.comp continuous_fst)).congr
  intro p
  simp only [Pi.add_apply, Function.comp_apply, centeredIntervalPrimitive,
    intervalIntegral.integral_same, sub_eq_add_neg, zero_add]

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The molecular first-order flux has a diagonal block slow-jet budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_metric_flux_coefficient_difference_jet_le
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (r : ℕ) (hr : r ≤ qs) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (k₀ : Fin 2) (α : DerivativeWord2 1) (X z : Vec 2) (v u : ι) :
    ‖iteratedFDeriv ℝ r (fun Y => metricFluxCoefficient (h := h) Q.η Q.G k₀ 1 α t Y z v u -
      metricFluxCoefficient Q.η (fun _ _ i j => if i = j then 1 else 0) k₀ 1 α t Y z v u) X‖ ≤
      (max (CGI r) 0 * g * lam ^ r) * (if v = u then (1 : ℝ) else 0) := by
  have hG : ContDiff ℝ (r : ℕ∞) (fun Y => Q.G t Y k₀ (α 0) - (if k₀ = α 0 then 1 else 0)) :=
    ((P.G_smooth t ht k₀ (α 0)).sub contDiff_const).of_le (by exact_mod_cast hr)
  have hη0 : 0 ≤ Q.η := by rw [P.η_eq]; exact (div_pos P.ν_pos P.B_pos).le
  have hηnorm : ‖-Q.η‖ ≤ 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hη0]
    exact P.η_le
  let d := fun Y => -Q.η * (Q.G t Y k₀ (α 0) - (if k₀ = α 0 then 1 else 0))
  have hd : ContDiff ℝ (r : ℕ∞) d := contDiff_const.mul hG
  have hgn : ‖iteratedFDeriv ℝ r d X‖ ≤ max (CGI r) 0 * g * lam ^ r := by
    change ‖iteratedFDeriv ℝ r (fun Y => (-Q.η) • (Q.G t Y k₀ (α 0) - (if k₀ = α 0 then 1 else 0))) X‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hG.contDiffAt, norm_smul]
    apply le_trans (mul_le_mul_of_nonneg_right hηnorm (norm_nonneg _))
    simpa only [one_mul] using setting_metric_difference_entry_scaled_jet_bound P g hg CGI hGI r hr t ht X k₀ (α 0)
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hK : 0 ≤ max (CGI r) 0 * g * lam ^ r := mul_nonneg (mul_nonneg (le_max_right _ _) hg) (pow_nonneg hlam r)
  have he (Y : Vec 2) :
      metricFluxCoefficient (h := h) Q.η Q.G k₀ 1 α t Y z v u -
        metricFluxCoefficient Q.η (fun _ _ i j => if i = j then 1 else 0) k₀ 1 α t Y z v u =
      d Y • blockIdentityEntry h v u := by
    simp only [metricFluxCoefficient_one, ← sub_smul]
    congr 1
    dsimp only [d]
    ring
  simp_rw [he]
  apply (norm_iteratedFDeriv_smul_const_le r d hd (blockIdentityEntry h v u) X).trans
  exact mul_le_mul hgn (blockIdentityEntry_norm_le h v u) (norm_nonneg _) hK

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The molecular first-order flux has a diagonal block slow-jet budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_metric_flux_coefficient_jet_le
    (r : ℕ) (hr : r ≤ qs) (t : ℝ) (ht : t ∈ Set.Icc a b)
    (k₀ : Fin 2) (α : DerivativeWord2 1) (X z : Vec 2) (v u : ι) :
    ‖iteratedFDeriv ℝ r (fun Y => metricFluxCoefficient (h := h) Q.η Q.G k₀ 1 α t Y z v u) X‖ ≤
      (max (CG r) 0 * lam ^ r) * (if v = u then (1 : ℝ) else 0) := by
  have hG : ContDiff ℝ (r : ℕ∞) (fun Y => Q.G t Y k₀ (α 0)) :=
    (P.G_smooth t ht k₀ (α 0)).of_le (by exact_mod_cast hr)
  have hη0 : 0 ≤ Q.η := by rw [P.η_eq]; exact (div_pos P.ν_pos P.B_pos).le
  have hηnorm : ‖-Q.η‖ ≤ 1 := by
    rw [norm_neg, Real.norm_eq_abs, abs_of_nonneg hη0]
    exact P.η_le
  let g := fun Y => -Q.η * Q.G t Y k₀ (α 0)
  have hg : ContDiff ℝ (r : ℕ∞) g := contDiff_const.mul hG
  have hgn : ‖iteratedFDeriv ℝ r g X‖ ≤ max (CG r) 0 * lam ^ r := by
    change ‖iteratedFDeriv ℝ r (fun Y => (-Q.η) • Q.G t Y k₀ (α 0)) X‖ ≤ _
    rw [iteratedFDeriv_const_smul_apply' hG.contDiffAt, norm_smul]
    apply le_trans (mul_le_mul_of_nonneg_right hηnorm (norm_nonneg _))
    simpa only [one_mul] using setting_metric_entry_scaled_jet_bound P r hr t ht X k₀ (α 0)
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hK : 0 ≤ max (CG r) 0 * lam ^ r := mul_nonneg (le_max_right _ _) (pow_nonneg hlam r)
  simp only [metricFluxCoefficient_one]
  apply (norm_iteratedFDeriv_smul_const_le r g hg (blockIdentityEntry h v u) X).trans
  exact mul_le_mul hgn (blockIdentityEntry_norm_le h v u) (norm_nonneg _) hK

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The literal source divergence and Taylor coefficient are time measurable at the original ambient word reserve. -/

variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] {D : ℕ}

theorem sourceCoefficientArray_parameter_measurable
    (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η : ℝ) (τ : T → ℝ)
    (Φ : T → Vec 2 → Vec 2 → ∀ i, h i)
    (hm : ∀ X z, Measurable (fun t => Φ t X z))
    (hf : ∀ t, IsBoxSmooth D D (Φ t))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z,
      Measurable (fun t => γ.coeff α (τ t) X z))
    (hΓbox : ∀ t v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth 1 1 (γ.coeff α (τ t)))
    (j : ℕ) (X z : Vec 2) :
    Measurable (fun t => sourceCoefficientArray edge η (τ t) (Φ t) j X z) := by
  change Measurable (fun t => ∑ k : Fin 2,
    covariantCoefficientStep η k (sourceFluxCoefficientArray edge η (τ t) (Φ t) k) j X z)
  apply Finset.measurable_sum
  intro k _
  have hm' (i : ℕ) (Y y : Vec 2) :=
    sourceFluxCoefficientArray_parameter_measurable edge η τ Φ hm hf hΓ k i Y y
  have hb (i : ℕ) (t : T) :
      IsBoxSmooth 1 1 (sourceFluxCoefficientArray edge η (τ t) (Φ t) k i) := by
    by_cases hi : i ≤ D - 1
    · apply sourceFluxCoefficientArray_box_reserve edge η (τ t) (Φ t) k 1 1 i
        (hΓbox t)
      exact (hf t).mono (by omega) (by omega)
    · rw [sourceFluxCoefficientArray_above_degree edge η (τ t) (Φ t) k i (by omega)]
      exact IsBoxSmooth.zero
  change Measurable (fun t =>
    fastPartial k (sourceFluxCoefficientArray edge η (τ t) (Φ t) k j) X z +
      if j = 0 then 0 else Real.sqrt η •
        slowPartial k (sourceFluxCoefficientArray edge η (τ t) (Φ t) k (j - 1)) X z)
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
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The actual outer divergence preserves grading directly from normalized flux bounds. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_covariantStep_from_normalized_bounds_le (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (hj : j ≠ 0) (lam U V : ℝ)
    (hlam : 0 ≤ lam) (hU : 0 ≤ U) (hV : 0 ≤ V)
    (A : Vec 2 →L[ℝ] ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p (q + 1) (P j)) (hs : IsBoxSmooth (p + 1) q (P (j - 1)))
    (X : Vec 2)
    (hbf : ∀ a ≤ p, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • P j Y y) z) X‖ ≤
        U * lam ^ (δ + j + a))
    (hbs : ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • P (j - 1) Y y) z) X‖ ≤
        V * lam ^ (δ + (j - 1) + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • covariantCoefficientStep η k P j Y y) z) X‖ ≤
      (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p *
        (2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p * U +
          2 ^ ((p + 1) + 2 * q) * (max 1 ‖A‖) ^ (p + 1) * V)) *
        lam ^ (δ + j + p) := by
  let U' := 2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p * U
  let V' := 2 ^ ((p + 1) + 2 * q) * (max 1 ‖A‖) ^ (p + 1) * V
  apply norm_mixed_normalized_covariantStep_le η hη δ p q j hj lam U' V'
    hlam (by dsimp only [U']; positivity) (by dsimp only [V']; positivity) A k P hf hs X
  · intro a ha b hb y
    exact norm_mixed_exponential_denormalized_le p (q + 1) (δ + j) A lam U hlam hU
      (P j) hf X hbf a b ha hb y
  · intro a ha b hb y
    exact norm_mixed_exponential_denormalized_le (p + 1) q (δ + (j - 1)) A lam V hlam hV
      (P (j - 1)) hs X hbs a b ha hb y
end

/-! Degree-zero outer divergence transfers normalized flux bounds without spending slow reserve. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem norm_mixed_covariantStep_zero_from_normalized_bounds_le
    (η : ℝ) (p q δ : ℕ) (lam U : ℝ) (hlam : 0 ≤ lam) (hU : 0 ≤ U)
    (A : Vec 2 →L[ℝ] ℝ) (k : Fin 2) (P : ℕ → Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth p (q + 1) (P 0)) (X : Vec 2)
    (hbf : ∀ a ≤ p, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun y => (Real.exp ((lam • A) Y))⁻¹ • P 0 Y y) z) X‖ ≤
        U * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • covariantCoefficientStep η k P 0 Y y) z) X‖ ≤
      (2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p *
        (2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p * U)) * lam ^ (δ + p) := by
  let U' := 2 ^ (p + 2 * (q + 1)) * (max 1 ‖A‖) ^ p * U
  apply norm_mixed_normalized_covariantStep_zero_le η p q δ lam U' hlam
    (by dsimp only [U']; positivity) A k P hf X
  intro a ha b hb y
  exact norm_mixed_exponential_denormalized_le p (q + 1) δ A lam U hlam hU
    (P 0) hf X hbf a b ha hb y
end

/-! Normalized source constituents have constants fixed solely by the finite orders and test direction. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def normalizedCovariantProductConstant (p q j : ℕ) (w : List (Fin 2))
    (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p *
    (2 ^ (p + 2 * q) * 2 ^ w.length *
      (2 ^ ((p + j) + 2 * (q + w.length - j)) * (max 1 ‖A‖) ^ (p + j)))

theorem normalizedCovariantProductConstant_nonneg (p q j : ℕ) (w : List (Fin 2))
    (A : Vec 2 →L[ℝ] ℝ) : 0 ≤ normalizedCovariantProductConstant p q j w A := by
  unfold normalizedCovariantProductConstant
  positivity

theorem norm_mixed_normalized_covariant_product_le (η : ℝ) (hη : η ≤ 1)
    (δ p q j : ℕ) (lam S C : ℝ) (hlam : 0 ≤ lam) (hS : 0 ≤ S) (hC : 0 ≤ C)
    (w : List (Fin 2)) (hj : j ≤ w.length) (A : Vec 2 →L[ℝ] ℝ)
    (γ : Vec 2 → Vec 2 → ℝ) (f : Vec 2 → Vec 2 → E) (M : E →L[ℝ] F)
    (hγ : IsBoxSmooth p q γ) (hf : IsBoxSmooth (p + j) (q + w.length - j) f) (X : Vec 2)
    (hbγ : ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (γ Y) z) X‖ ≤ S * lam ^ a)
    (hbf : ∀ a ≤ p + j, ∀ b ≤ q + w.length - j, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • (γ Y y •
        M (covariantListCoefficients η w (fun Z y => Real.exp ((lam • A) Z) • f Z y) j Y y))) z) X‖ ≤
      (normalizedCovariantProductConstant p q j w A * S * ‖M‖ * C) * lam ^ (δ + j + p) := by
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  let Tfield := fun Y y => γ Y y • M (covariantListCoefficients η w Φ j Y y)
  let K := 2 ^ (p + 2 * q) * S * (‖M‖ * (2 ^ w.length *
    (2 ^ ((p + j) + 2 * (q + w.length - j)) * (max 1 ‖A‖) ^ (p + j) * C)))
  have hΦ : IsBoxSmooth (p + j) (q + w.length - j) Φ :=
    isBoxSmooth_bilinear (isBoxSmooth_slow_field _ _ _
      (Real.contDiff_exp.comp (lam • A).contDiff)) hf
      (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] E →L[ℝ] E)
  have hword := covariantListCoefficient_box_reserve η w j p q Φ hj hΦ
  have hF : IsBoxSmooth p q Tfield := isBoxSmooth_bilinear hγ (hword.clm_comp M)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] F →L[ℝ] F)
  have hK : 0 ≤ K := by positivity
  have hFb : ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (Tfield Y) y) X‖ ≤
        (Real.exp ((lam • A) X) * K) * lam ^ ((δ + j) + a) := by
    intro a ha b hb y
    exact norm_mixed_exponential_covariant_product_le η hη δ p q j lam S C hlam hS hC
      w hj A γ f M hγ hf X hbγ hbf a b ha hb y
  have hh := norm_mixed_exponential_normalized_le p q (δ + j) A lam K hlam hK Tfield hF X hFb z
  apply hh.trans_eq
  dsimp only [K, normalizedCovariantProductConstant]
  ring
end

/-! A single finite-order constant bounds all constituent word lengths before the family is chosen. -/

def normalizedSourceOrderConstant (D p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  ∑ m ∈ Finset.range D, normalizedCovariantProductConstant p q j (List.replicate m 0) A

theorem normalizedSourceOrderConstant_nonneg (D p q j : ℕ) (A : Vec 2 →L[ℝ] ℝ) :
    0 ≤ normalizedSourceOrderConstant D p q j A := by
  exact Finset.sum_nonneg fun m _ => normalizedCovariantProductConstant_nonneg p q j _ A

theorem normalizedCovariantProductConstant_le_sourceOrderConstant
    (D p q j : ℕ) (w : List (Fin 2)) (hw : w.length < D) (A : Vec 2 →L[ℝ] ℝ) :
    normalizedCovariantProductConstant p q j w A ≤ normalizedSourceOrderConstant D p q j A := by
  have he : normalizedCovariantProductConstant p q j w A =
      normalizedCovariantProductConstant p q j (List.replicate w.length 0) A := by
    simp only [normalizedCovariantProductConstant, List.length_replicate]
  rw [he]
  unfold normalizedSourceOrderConstant
  exact Finset.single_le_sum
    (f := fun m => normalizedCovariantProductConstant p q j (List.replicate m 0) A)
    (fun m _ => normalizedCovariantProductConstant_nonneg p q j _ A) (Finset.mem_range.mpr hw)

/-! Componentwise normalized cross bounds keep the original component budget. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB2_component_uniform_mixed_grading (p q δ : ℕ) (η lam M C : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → ∀ i, h i) (i₀ : ι) (hf : IsBoxSmooth (p + 2) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => f Y y i₀) z) X‖ ≤ C * lam ^ (δ + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • (cellB2 η G t
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y i₀)) z) X‖ ≤
      (normalizedCellB2UniformConstant p q A M * C) * lam ^ ((δ + 2) + r) := by
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  have hΦ : IsBoxSmooth (p + 2) (q + 0) Φ := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hf
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (∀ i, h i) →L[ℝ] (∀ i, h i))
  have he (Y y : Vec 2) := cellB2_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀) η G t Φ
    (hΦ.mono (by omega) (by omega))
    (fun i j => (hG i j).mono (by omega) (by omega)) Y y
  change ∀ Y y, cellB2 η G t (fun Z w => Φ Z w i₀) Y y =
    cellB2 η G t Φ Y y i₀ at he
  change ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
    (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t Φ Y y i₀) z) X‖ ≤ _
  simp_rw [← he]
  have hc := hf.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀)
  exact normalizedCellB2_uniform_mixed_grading_at_slow_point p q δ η lam M C
    hη0 hη1 hlam hM hC A G t
    (fun Y y => f Y y i₀) hc hG  X hbG  hbf r s hr hs z
end

/-! Componentwise normalized cross bounds keep the original component budget. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalizedCellB1_scaled_drift_component_uniform_grading (p q δ : ℕ) (η lam M W C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → ∀ i, h i) (i₀ : ι) (hf : IsBoxSmooth (p + 1) (q + 1) f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => v t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * v t y k) z) X‖ ≤ W * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (fun y => f Y y i₀) z) X‖ ≤ C * lam ^ (δ + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • (cellB1 η G v t
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y i₀)) z) X‖ ≤
      (normalizedCellB1UniformConstant p q A M W * C) * lam ^ ((δ + 1) + r) := by
  let Φ := fun Y y => Real.exp ((lam • A) Y) • f Y y
  have hΦ : IsBoxSmooth (p + 1) (q + 1) Φ := isBoxSmooth_bilinear
    (isBoxSmooth_slow_field _ _ _ (Real.contDiff_exp.comp (lam • A).contDiff)) hf
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] (∀ i, h i) →L[ℝ] (∀ i, h i))
  have he (Y y : Vec 2) := cellB1_postcomposition
    (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀) η G v t Φ
    (hΦ.mono (by omega) (by omega))
    (fun i j => (hG i j).mono (by omega) (by omega)) Y y
  change ∀ Y y, cellB1 η G v t (fun Z w => Φ Z w i₀) Y y =
    cellB1 η G v t Φ Y y i₀ at he
  change ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
    (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G v t Φ Y y i₀) z) X‖ ≤ _
  simp_rw [← he]
  have hc := hf.clm_comp (ContinuousLinearMap.proj (R := ℝ) (φ := h) i₀)
  exact normalizedCellB1_scaled_drift_uniform_mixed_grading_at_slow_point p q δ η lam M W C
    hη hlam hM hW hC A G v t
    (fun Y y => f Y y i₀) hc hG hv X hbG hbv hbf r s hr hs z
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Zero initial state and zero source determine the classical cell inverse. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [CompleteSpace E]

omit [CompleteSpace E] in
theorem cellFieldInverse_zero (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (sZ : ℕ) (a b : ℝ) (hab : a ≤ b)
    (hG : IsCellMetric (fun t _ => G t))
    (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2))
    (V : ℝ) (hV : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b (fun _ => 0) (fun _ _ => 0) c) :
    ∀ t ∈ Set.Icc a b, ∀ x, c t x = 0 := by
  intro t ht x
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro l
  have hsol : IsCellSolution (Set.Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
      (fun _ _ => 0) (fun _ _ => 0) (cellJetOfField l c) := by
    simpa only [map_zero, Complex.ofReal_zero] using (hc.2 l).1
  have hz : IsCellSolution (Set.Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
      (fun _ _ => 0) (fun _ _ => 0) (0 : ℝ → RawJet2 1 ℂ) := by
    simpa only [zero_smul] using! cellSolution_complex_smul hsol (0 : ℂ)
  have hi : cellValue (cellJetOfField l c) a =ᵐ[volume.restrict AVenhance.unitCube]
      cellValue (0 : ℝ → RawJet2 1 ℂ) a := by
    simpa only [map_zero, Complex.ofReal_zero] using! (hc.2 l).2.2.1
  have he := cellActual_unique_raw hab ⟨fun t _ => G t, v, 0, 0⟩ hG V 0 hv hV
    measurable_const (fun _ => by simp) (fun _ _ => 0) (fun _ _ => 0)
    (MemLp.zero) (MemLp.zero) (cellJetOfField l c) 0 hsol hz hi t ht
  have hae : (fun z => ((l (c t z) : ℝ) : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube] 0 := by
    change (fun z => ((l (c t z) : ℝ) : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube] 0 at he
    exact he
  have hper : AVenhance.IsZ2Periodic (fun z => ((l (c t z) : ℝ) : ℂ)) := by
    change AVenhance.IsZ2Periodic (cellValue (cellJetOfField l c) t)
    exact (hsol.2.2.1 t ht).2
  have hpoint := periodicContinuous_zero_of_cell_ae _
    (Complex.ofRealCLM.continuous.comp (l.continuous.comp (hc.1 t ht).continuous)) hper hae
  have heq := congrFun hpoint x
  exact Complex.ofReal_injective (by simpa using heq)

end AVRegularity.CycleComparison.Lift
end
