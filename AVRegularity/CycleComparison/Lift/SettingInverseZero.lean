-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.CellB1LeftTerms
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence
import AVRegularity.CycleEvolution.FibreCoefficientWeightedForcing
import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! Centered parameter-dependent mode forcing retains the summable inverse-rate gain. -/

def parameterizedModeJetConstant (p q : ℕ) (M lam κ : ℝ) (S : ℕ → ℝ) : ℝ :=
  (2 : ℝ) ^ q * (duhamelSlowJetMajorant p M κ S q * lam ^ q * (2 / κ))

theorem parameterizedModeResponse_jet_bound (p q : ℕ) (hq : q ≤ p)
    (g : ℝ → Vec 2 → ℝ) (hm : ∀ X, Measurable (fun t => g t X))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M lam κ a b : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ) (hab : a ≤ b)
    (hb : ∀ r ≤ p, ∀ t X, ‖iteratedFDeriv ℝ r (g t) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ g t X)
    (U : ℤ → ℝ → Vec 2 → ℂ) (hUm : ∀ m X, Measurable (fun t => U m t X))
    (hUs : ∀ m t, ContDiff ℝ (p : ℕ∞) (U m t))
    (S : ℕ → ℝ) (hS : ∀ r ≤ p, 0 ≤ S r)
    (hUb : ∀ r ≤ p, ∀ m t X, ‖iteratedFDeriv ℝ r (U m t) X‖ ≤ S r * lam ^ r)
    (hU0 : ∀ t X, U 0 t X = 0) (m : ℤ) (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y => transverseModeResponse (‖profileFourierFrequency m‖ ^ 2)
      (fun t => g t Y) (fun t => U m t Y) a b) X‖ ≤
      profileJetMajorant (parameterizedModeJetConstant p q M lam κ S) 0 m := by
  by_cases hm0 : m = 0
  · subst m
    have he : (fun Y => transverseModeResponse (‖profileFourierFrequency 0‖ ^ 2)
        (fun t => g t Y) (fun t => U 0 t Y) a b) = 0 := by
      funext Y
      simp only [transverseModeResponse, hU0, smul_zero, intervalIntegral.integral_zero, Pi.zero_apply]
    rw [he]
    simp [profileJetMajorant]
  · have hr : 0 < ‖profileFourierFrequency m‖ ^ 2 :=
      sq_pos_of_pos (norm_pos_iff.mpr (profileFourierFrequency_ne_zero m hm0))
    have hh := transverseModeResponse_iteratedFDeriv_parameter_norm_le p g hm hs
      M lam (‖profileFourierFrequency m‖ ^ 2) κ a b hM hlam hr hκ hab hb hgl
      (U m) (hUm m) (hUs m) S hS (fun r hr => hUb r hr m) q hq X
    apply hh.trans_eq
    simp only [profileJetMajorant, ite_eq_right hm0, parameterizedModeJetConstant,
      profileFourierFrequency_norm_sq]
    field_simp

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Metric perturbation cross inputs keep the original slow scale and one linear perturbation factor. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_metric_difference_mixed_uniform_bound (p r s : ℕ) (hp : p ≤ qs) (hr : r ≤ p)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun (_ : Vec 2) => Q.G t Y i j - (if i = j then 1 else 0)) z) X‖ ≤ (metricParameterBudget p CGI * g) * lam ^ r := by
  apply (norm_mixed_slow_field_le r s (fun Y => Q.G t Y i j - (if i = j then 1 else 0)) X z).trans
  apply (setting_metric_difference_entry_scaled_jet_bound P g hg CGI hGI r (hr.trans hp) t ht X i j).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by
    rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le) r)
  apply mul_le_mul_of_nonneg_right _ hg
  exact Finset.single_le_sum (fun j _ => le_max_right (CGI j) 0)
    (Finset.mem_range.mpr (by omega))
end

/-! Metric cross inputs have fixed rectangular budgets independent of the fast order. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_metric_entry_box (p q : ℕ) (hp : p ≤ qs)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i j : Fin 2) :
    IsBoxSmooth p q (fun X (_ : Vec 2) => Q.G t X i j) :=
  isBoxSmooth_slow_field p q _ ((P.G_smooth t ht i j).of_le (by exact_mod_cast hp))

include P in
theorem setting_metric_mixed_uniform_bound (p r s : ℕ) (hp : p ≤ qs) (hr : r ≤ p)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (i j : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun (_ : Vec 2) => Q.G t Y i j) z) X‖ ≤ metricParameterBudget p CG * lam ^ r := by
  apply (norm_mixed_slow_field_le r s (fun Y => Q.G t Y i j) X z).trans
  apply (setting_metric_entry_scaled_jet_bound P r (hr.trans hp) t ht X i j).trans
  apply mul_le_mul_of_nonneg_right _ (pow_nonneg (by
    rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le) r)
  exact Finset.single_le_sum (fun j _ => le_max_right (CG j) 0)
    (Finset.mem_range.mpr (by omega))
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Coarse-test calibration identifies full operator-valued coefficient box regularity. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]

theorem symmetric_lift_coefficient_box_of_tests (c : LiftCoeff ι h) (n m p q : ℕ) (hm : m ≤ n)
    (hc : ∀ β (σ : Equiv.Perm (Fin m)), c m (β ∘ σ) = c m β)
    (α : DerivativeWord2 m) (lam : ℝ) (hlam : lam ≠ 0)
    (u v : ι) (t : ℝ)
    (hbox : ∀ (ξ : h u) (A : Vec 2 →L[ℝ] ℝ),
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t)) :
    IsBoxSmooth p q (fun X z => c m α t X z v u) := by
  apply isBoxSmooth_clm_of_apply
  intro ξ
  have he : (fun X z => c m α t X z v u ξ) =
      calibratedLiftCoefficientEntry c n m α lam u v ξ t := by
    funext X z
    exact (calibratedLiftCoefficientEntry_eq c n m hm hc α lam hlam u v ξ t X z).symm
  rw [he]
  exact calibratedLiftCoefficientEntry_box c n m p q α lam u v ξ t (hbox ξ)

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The actual transverse inverse difference keeps its reciprocal-rate gain and scale-graded smallness. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem transverseModeResponse_metric_difference_jet_bound
    (p q : ℕ) (hq : q ≤ p) (g : ℝ → Vec 2 → ℝ)
    (hm : ∀ X, Measurable (fun t => g t X)) (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (g t))
    (M Md eps lam rate κ a b : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hrate : 0 < rate) (hκ : 0 < κ) (hκ1 : κ ≤ 1) (hab : a ≤ b)
    (hb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (g t) X‖ ≤ M * lam ^ j)
    (hdb : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (fun Y => g t Y - 1) X‖ ≤ Md * eps * lam ^ j)
    (hgl : ∀ t X, κ ≤ g t X)
    (f : ℝ → Vec 2 → E) (hmf : ∀ X, Measurable (fun t => f t X))
    (hf : ∀ t, ContDiff ℝ (p : ℕ∞) (f t)) (S : ℕ → ℝ)
    (hS : ∀ j ≤ p, 0 ≤ S j) (hfB : ∀ j ≤ p, ∀ t X, ‖iteratedFDeriv ℝ j (f t) X‖ ≤ S j * lam ^ j)
    (X : Vec 2) :
    ‖iteratedFDeriv ℝ q (fun Y =>
      transverseModeResponse rate (fun t => g t Y) (fun t => f t Y) a b -
        transverseModeResponse rate (fun _ => 1) (fun t => f t Y) a b) X‖ ≤
      ((2 : ℝ) ^ q * ((2 : ℝ) ^ q * metricDifferenceKernelSourceConstant p q M Md κ S)) *
        eps * lam ^ q * (4 / (rate * κ)) := by
  let μ := volume.restrict (Ioc a b)
  let F := clampedMetricDifferenceField rate g f a b hab
  let C := fun j => (duhamelSlowJetMajorant p M κ S j + duhamelSlowJetMajorant p 1 κ S j) * lam ^ j
  let B := ((2 : ℝ) ^ q * metricDifferenceKernelSourceConstant p q M Md κ S) * eps * lam ^ q
  have hB : 0 ≤ B := mul_nonneg (mul_nonneg
    (mul_nonneg (pow_nonneg (by norm_num) _)
      (metricDifferenceKernelSourceConstant_nonneg p q M Md κ S hM hMd hκ (fun j hj => hS j (hj.trans hq))))
    heps) (pow_nonneg hlam _)
  have hd := clamped_metric_difference_reserve_data p g hm hs M lam rate κ a b hM hlam hrate.le hκ hκ1 hab
    hb hgl f hmf hf S hS hfB
  have hreg : ContDiff ℝ (q : ℕ∞) (fun Y => ∫ s, F s Y ∂μ) :=
    (parameter_integral_contDiff μ p F hd.1 hd.2.1 C hd.2.2.1).of_le (by exact_mod_cast hq)
  have hw (α : DerivativeWord2 q) :
      ‖orderedDerivative α (fun Y => ∫ s, F s Y ∂μ) X‖ ≤ B * (4 / (rate * κ)) := by
    rw [orderedDerivative_parameter_integral μ p F hd.1 hd.2.1 C hd.2.2.1 q hq α]
    have hc : Continuous (fun s : ℝ => B * Real.exp (-(rate * κ / 4) * (b - s))) := by fun_prop
    have hi : Integrable (fun s => B * Real.exp (-(rate * κ / 4) * (b - s))) μ :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).mp (hc.intervalIntegrable a b)
    have hbound : ∀ᵐ s ∂μ, ‖orderedDerivative α (F s) X‖ ≤
        B * Real.exp (-(rate * κ / 4) * (b - s)) := by
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hsmem
      have hsmem' : s ∈ Icc a b := ⟨hsmem.1.le, hsmem.2⟩
      have he : F s = fun Y =>
          (transverseModeKernel rate (fun t => g t Y) s b - transverseModeKernel rate (fun _ => 1) s b) • f s Y := by
        funext Y
        dsimp [F, clampedMetricDifferenceField, clampedDuhamelField]
        rw [projIcc_of_mem hab hsmem']
        exact (sub_smul _ _ _).symm
      apply (norm_orderedDerivative_le ((hd.2.1 s).of_le (by exact_mod_cast hq)) α X).trans
      change ‖iteratedFDeriv ℝ q (F s) X‖ ≤ _
      rw [he]
      exact (transverseModeKernel_metric_difference_source_jet_bound p q hq g hm hs M Md eps lam rate κ s b
        hM hMd heps hlam hrate.le hκ hκ1 hsmem.2 hb hdb hgl (f s) (hf s) S hS
        (fun j hj Y => hfB j hj s Y) X).trans_eq (by dsimp [B]; ring)
    calc
      _ ≤ ∫ s, B * Real.exp (-(rate * κ / 4) * (b - s)) ∂μ := norm_integral_le_of_norm_le hi hbound
      _ = ∫ s in a..b, B * Real.exp (-(rate * κ / 4) * (b - s)) :=
        (intervalIntegral.integral_of_le hab).symm
      _ = B * ∫ s in a..b, Real.exp (-(rate * κ / 4) * (b - s)) := intervalIntegral.integral_const_mul _ _
      _ ≤ B * (1 / (rate * κ / 4)) := mul_le_mul_of_nonneg_left
        (integral_decayKernel_le _ (by positivity) a b) hB
      _ = _ := by ring
  rw [hd.2.2.2]
  apply (AVRegularity.ChartTransport.norm_iteratedFDeriv_le_sum_words hreg X).trans
  calc
    _ ≤ ∑ _α : DerivativeWord2 q, B * (4 / (rate * κ)) := Finset.sum_le_sum (fun α _ => hw α)
    _ = _ := by
      rw [Finset.sum_const, AVRegularity.ChartTransport.card_derivativeWord2]
      simp only [nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]
      dsimp [B]
      ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite calibration preserves actual normalized coarse-test jet majorants. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem calibratedLiftCoefficientEntry_mixed_bound
    (c : LiftCoeff ι h) (n m p q : ℕ) (α : DerivativeWord2 m)
    (lam : ℝ) (u v : ι) (ξ : h u) (t : ℝ)
    (K : (Vec 2 →L[ℝ] ℝ) → ℝ) (M : ℝ)
    (hbox : ∀ A : Vec 2 →L[ℝ] ℝ,
      IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t))
    (hb : ∀ A : Vec 2 →L[ℝ] ℝ, ∀ r ≤ p, ∀ s ≤ q, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
        (normalizedLiftTestField c n (lam • A) u v ξ t Y) z) X‖ ≤
          (K A * M * ‖ξ‖) * lam ^ (n + r))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (calibratedLiftCoefficientEntry c n m α lam u v ξ t Y) z) X‖ ≤
      (∑ j : Fin (m + 1) × Fin (n + 1), |liftCalibrationWeight n m α lam j| *
        K ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))) * M * ‖ξ‖ * lam ^ (n + r) := by
  unfold calibratedLiftCoefficientEntry
  apply (norm_mixed_jet_finset_sum_le Finset.univ r s _
    (fun j _ => ((hbox ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))).mono hr hs).const_smul _) X z).trans
  rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [norm_mixed_jet_const_smul
    ((hbox ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ))).mono hr hs)]
  have hh := mul_le_mul_of_nonneg_left
    (hb ((j.2 : ℝ) • coordinateSymbolDirection (j.1 : ℝ)) r hr s hs X z)
    (abs_nonneg (liftCalibrationWeight n m α lam j))
  simpa only [mul_assoc] using hh

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! The inverse majorant is linear in source size and preserves its base slow grade. -/

theorem duhamelSlowJetMajorant_source_mul (p q : ℕ) (M κ c : ℝ) (S : ℕ → ℝ) :
    duhamelSlowJetMajorant p M κ (fun r => S r * c) q =
      duhamelSlowJetMajorant p M κ S q * c := by
  unfold duhamelSlowJetMajorant
  have he : (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * (S (q - j) * c)) =
      (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j)) * c := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [he]
  ring

theorem parameterizedModeJetConstant_base_grade (p q δ : ℕ) (M lam κ : ℝ) (S : ℕ → ℝ) :
    parameterizedModeJetConstant p q M lam κ (fun r => S r * lam ^ δ) =
      parameterizedModeJetConstant p q M 1 κ S * lam ^ (δ + q) := by
  unfold parameterizedModeJetConstant
  rw [duhamelSlowJetMajorant_source_mul, pow_add]
  simp only [one_pow, mul_one]
  ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! Actual scaled drift components use fixed sums of the original w-jet constants. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_scaled_drift_component_jet_bound (j : ℕ) (hj : j ≤ qf)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (z : Vec 2) (i : Fin 2) :
    ‖iteratedFDeriv ℝ j (fun y => Real.sqrt Q.η * Q.v t y i) z‖ ≤ max (Cw j) 0 := by
  let W := fun y => Real.sqrt Q.η • Q.v t y
  let A : Vec 2 →L[ℝ] ℝ := ContinuousLinearMap.proj i
  have hA : ‖A‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    change ‖x i‖ ≤ 1 * ‖x‖
    simpa only [one_mul] using norm_le_pi_norm x i
  have hW : ContDiff ℝ (qf : ℕ∞) W :=
    contDiff_pi.mpr (fun i => setting_normalized_drift_contDiff_upto P qf le_rfl t ht i)
  have he := A.norm_iteratedFDeriv_comp_left (f := W) (x := z)
    (N := (qf : ℕ∞)) hW.contDiffAt (n := j) (by exact_mod_cast hj)
  change ‖iteratedFDeriv ℝ j (A ∘ W) z‖ ≤ _
  apply he.trans
  calc
    _ ≤ 1 * ‖iteratedFDeriv ℝ j W z‖ := mul_le_mul_of_nonneg_right hA (norm_nonneg _)
    _ ≤ _ := by rw [one_mul]; exact setting_normalized_drift_jet_bound P j hj t ht z

include P in
theorem setting_scaled_drift_mixed_uniform_bound (q r s : ℕ) (hq : q ≤ qf) (hs : s ≤ q)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (i : Fin 2) :
    ‖iteratedFDeriv ℝ r (fun _ : Vec 2 => iteratedFDeriv ℝ s
      (fun y => Real.sqrt Q.η * Q.v t y i) z) X‖ ≤ metricParameterBudget q Cw * lam ^ r := by
  cases r with
  | zero =>
    simp only [norm_iteratedFDeriv_zero, pow_zero, mul_one]
    apply (setting_scaled_drift_component_jet_bound P s (hs.trans hq) t ht z i).trans
    exact Finset.single_le_sum (fun j _ => le_max_right (Cw j) 0)
      (Finset.mem_range.mpr (by omega))
  | succ r =>
    simp only [iteratedFDeriv_succ_const, Pi.zero_apply, norm_zero]
    apply mul_nonneg (metricParameterBudget_nonneg q Cw)
    rw [P.lam_eq]
    exact pow_nonneg (div_pos P.ρ_pos P.E_pos).le _

include P in
theorem setting_raw_drift_fast_box (p q : ℕ) (hq : q ≤ qf)
    (t : ℝ) (ht : t ∈ Set.Icc a b) (i : Fin 2) :
    IsBoxSmooth p q (fun (_ : Vec 2) z => Q.v t z i) := by
  apply isBoxSmooth_fast_field
  have he : (fun z => Q.v t z i) = fun z => V t (z par.rev) * basisVec par i := by
    funext z
    rw [P.v_shear t z]
    rfl
  rw [he]
  exact (((P.V_smooth t ht).of_le (by exact_mod_cast hq)).comp
    (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ).contDiff).mul contDiff_const

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Explicit finite differential terms for the actual component source flux. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def sourceFluxLeftTerms (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : LiftCoeff ι h) (k : Fin 2) (j : ℕ) (v : ι) :
    List (LeftTerm (∀ i, h i) (h v)) :=
  (Finset.univ.toList : List ι).flatMap fun u =>
    (Finset.univ.toList : List (Finset.Icc 2 D)).flatMap fun d =>
      (edge v u d).flatMap fun γ =>
        (Finset.univ.toList : List (DerivativeWord2 (d.val - 1))).flatMap fun α =>
          constituentLeftTerms η (List.ofFn α) j (liftComponentLeftTerms n c t u)
            γ.map (fun X z => γ.coeff α t X z k)
end

/-! The actual source acting on a lift polynomial has the recurrence's finite convolution. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem source_polynomial_input_coefficient (edge : ConstituentEdges D h) (hD : 1 ≤ D)
    (η t : ℝ) (N j : ℕ) (P : ℕ → Vec 2 → Vec 2 → ∀ i, h i)
    (hP : ∀ i, GoodField D (P i)) (hz : ∀ i, N < i → P i = fun _ _ => 0)
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α,
      GoodField 1 (fun X z => γ.coeff α t X z)) (X z : Vec 2) :
    ((j.factorial : ℝ)⁻¹) • iteratedDeriv j
      (fun ε : ℝ => sourceOp edge η ε t
        (fun Y y => ∑ i ∈ Finset.range (N + 1), ε ^ i • P i Y y) X z) 0 =
      ∑ l ∈ Finset.range (min D j + 1), sourceCoeff edge η l t (P (j - l)) X z := by
  have he : (fun ε : ℝ => sourceOp edge η ε t
      (fun Y y => ∑ i ∈ Finset.range (N + 1), ε ^ i • P i Y y) X z) =
      fun ε => ∑ i ∈ Finset.range (N + 1), ∑ l ∈ Finset.range (D + 1),
        ε ^ (i + l) • sourceCoefficientArray edge η t (P i) l X z := by
    funext ε
    rw [congrFun (congrFun (sourceOp_finset_sum_smul edge η ε t hΓ
      (Finset.range (N + 1)) (fun i => ε ^ i) P (fun i _ => hP i)) X) z]
    simp_rw [sourceOp_polynomial_identity edge hD η ε t _ (hP _) hΓ]
    simp only [Finset.smul_sum, smul_smul, pow_add]
  rw [he, normalized_polynomial_convolution N D j]
  · apply Finset.sum_congr rfl
    intro l _
    rw [sourceCoeff_eq_sourceCoefficientArray edge hD η t _ (hP _) hΓ]
  · intro i hi l
    rw [← sourceCoeff_eq_sourceCoefficientArray edge hD η t _ (hP i) hΓ,
      hz i hi]
    change sourceCoeff edge η l t (0 : Vec 2 → Vec 2 → ∀ i, h i) X z = 0
    rw [sourceCoeff_zero_input]
    rfl
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Identify the measurable finite source array with the literal normalized Taylor coefficient. -/

variable {ι T : Type*} [Fintype ι] [MeasurableSpace T] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, SecondCountableTopology (h i)] {D : ℕ}

variable [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]

theorem sourceCoeff_parameter_measurable_of_ambient_inputs
    (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η : ℝ) (τ : T → ℝ)
    (Φ : T → Vec 2 → Vec 2 → ∀ i, h i)
    (hm : ∀ X z, Measurable (fun t => Φ t X z))
    (hf : ∀ t, IsBoxSmooth D D (Φ t))
    (hper : ∀ t X, AVenhance.IsZ2Periodic (Φ t X))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α X z,
      Measurable (fun t => γ.coeff α (τ t) X z))
    (hΓbox : ∀ t v u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth 1 1 (γ.coeff α (τ t)))
    (j : ℕ) (X z : Vec 2) :
    Measurable (fun t => sourceCoeff edge η j (τ t) (Φ t) X z) := by
  have he (t : T) : sourceCoeff edge η j (τ t) (Φ t) =
      sourceCoefficientArray edge η (τ t) (Φ t) j := by
    apply sourceCoeff_eq_sourceCoefficientArray edge hD η (τ t) (Φ t)
      ⟨(hf t).contDiff_uncurry le_rfl le_rfl, hper t⟩
    intro v u d γ hγ α
    exact ⟨(hΓbox t v u d γ hγ α).contDiff_uncurry le_rfl le_rfl,
      γ.periodic α (τ t)⟩
  simp_rw [he]
  exact sourceCoefficientArray_parameter_measurable edge hD η τ Φ hm hf hΓ hΓbox j X z

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public section
namespace AVRegularity.CycleComparison.Lift

/-! Inverse constants are positive and linear in the source majorant. -/

theorem parameterizedModeJetConstant_nonneg (p q : ℕ) (M lam κ : ℝ) (S : ℕ → ℝ)
    (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ) (hS : ∀ r ≤ q, 0 ≤ S r) :
    0 ≤ parameterizedModeJetConstant p q M lam κ S := by
  unfold parameterizedModeJetConstant
  exact mul_nonneg (by positivity) (mul_nonneg
    (mul_nonneg (duhamelSlowJetMajorant_nonneg p q M κ S hM hκ hS) (pow_nonneg hlam q))
    (by positivity))

theorem parameterizedModeJetConstant_source_mul (p q : ℕ) (M lam κ c : ℝ) (S : ℕ → ℝ) :
    parameterizedModeJetConstant p q M lam κ (fun r => S r * c) =
      parameterizedModeJetConstant p q M lam κ S * c := by
  unfold parameterizedModeJetConstant
  rw [duhamelSlowJetMajorant_source_mul]
  ring

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Covariant source flux spends exactly its coefficient degree in tested slow order. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxLeftTerms_order (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : LiftCoeff ι h) (k : Fin 2) (j : ℕ) (v : ι)
    (e : LeftTerm (∀ i, h i) (h v)) (he : e ∈ sourceFluxLeftTerms edge η t n c k j v) :
    e.order ≤ n + j := by
  obtain ⟨u, hu, d, hd, γ, hγ, α, hα, he⟩ := by
    simpa only [sourceFluxLeftTerms, List.mem_flatMap] using he
  obtain ⟨b, hb, rfl⟩ := List.mem_map.mp he
  obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hb
  exact covariantLeftTermList_order η (List.ofFn α) (liftComponentLeftTerms n c t u) n
    (liftComponentLeftTerms_order n c t u) j a ha
end

/-! Literal normalized source derivatives retain the profile geometry of actual reserved inputs. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)] {D : ℕ}

theorem sourceCoeff_transverse_of_reserved_inputs (par : Fin 2) (I : Set ℝ)
    (edge : ConstituentEdges D h) (hD : 1 ≤ D) (η : ℝ)
    (Φ : ℝ → Vec 2 → Vec 2 → ∀ i, h i) (hΦ : IsTransverseOn par I Φ)
    (hgood : ∀ t ∈ I, GoodField D (Φ t))
    (hΓ : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, IsTransverseOn par I (γ.coeff α))
    (hΓgood : ∀ v u d, ∀ γ ∈ edge v u d, ∀ α, ∀ t ∈ I,
      GoodField 1 (fun X z => γ.coeff α t X z))
    (j : ℕ) : IsTransverseOn par I (fun t => sourceCoeff edge η j t (Φ t)) := by
  intro t ht X z s
  have he := sourceCoeff_eq_sourceCoefficientArray edge hD η t (Φ t) (hgood t ht)
    (fun v u d γ hm α => hΓgood v u d γ hm α t ht) j
  change sourceCoeff edge η j t (Φ t) X (z + s • basisVec par) = sourceCoeff edge η j t (Φ t) X z
  rw [he]
  exact sourceCoefficientArray_transverse par I edge η Φ hΦ hΓ j t ht X z s
end

/-! The second cross action commutes with the explicit component synthesis. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem cellB2_liftComponentLeftTerms_apply (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (n : ℕ) (c : LiftCoeff ι h) (t : ℝ)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsBoxSmooth 2 0 (fun X z => c m α t X z v u))
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => G t X i j))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) (v : ι) :
    leftTermsApply (cellB2LeftTerms η (G t) (liftComponentLeftTerms n c t v)) f X z =
      cellB2 η G t (liftApply n c (fun _ => f) t) X z v := by
  rw [cellB2LeftTerms_apply η G t _ hG
    (liftComponentLeftTerms_box n c t v 2 0 (fun m hm α u => hc m hm α v u)) f hf X z]
  have he : leftTermsApply (liftComponentLeftTerms n c t v) f =
      fun Y y => liftApply n c (fun _ => f) t Y y v := by
    funext Y y
    exact liftComponentLeftTerms_apply n c t v f Y y
  rw [he]
  have hb : IsBoxSmooth 2 0 (liftApply n c (fun _ => f) t) :=
    liftApply_box_reserve n 2 0 c (fun _ => f) t (hf.of_le (by simp)) hc
  exact cellB2_postcomposition (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) η G t
    (liftApply n c (fun _ => f) t) hb
    (fun i j => isBoxSmooth_slow_field 1 0 (fun Y => G t Y i j) (hG i j)) X z
end

/-! Explicit source-flux coefficients retain the exact rectangular reserve. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxLeftTerms_box (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : LiftCoeff ι h) (k : Fin 2) (j p q : ℕ) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth (p + j) (q + (D - 1) - j) (fun X z => c m α t X z u u'))
    (hΓ : ∀ u d, ∀ γ ∈ edge v u d, ∀ α,
      IsBoxSmooth p q (fun X z => γ.coeff α t X z k))
    (e : LeftTerm (∀ i, h i) (h v)) (he : e ∈ sourceFluxLeftTerms edge η t n c k j v) :
    IsBoxSmooth p q e.coeff := by
  obtain ⟨u, hu, d, hd, γ, hγ, α, hα, he⟩ := by
    simpa only [sourceFluxLeftTerms, List.mem_flatMap] using he
  by_cases hj : j ≤ (List.ofFn α).length
  · apply constituentLeftTerms_box η (List.ofFn α) j p q hj
      (liftComponentLeftTerms n c t u) γ.map (fun X z => γ.coeff α t X z k)
      _ (hΓ u d γ hγ α) e he
    intro b hb
    apply (liftComponentLeftTerms_box n c t u (p + j) (q + (D - 1) - j)
      (fun m hm β u' => hc m hm β u u') b hb).mono le_rfl
    have hdD := (Finset.mem_Icc.mp d.property).2
    simp only [List.length_ofFn]
    omega
  · have hz := covariantLeftTermList_above_degree η (List.ofFn α)
      (liftComponentLeftTerms n c t u) j (by omega)
    simp only [constituentLeftTerms, hz, List.map_nil, List.not_mem_nil] at he
end

/-! The first cross action commutes with the explicit component synthesis. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem cellB1_liftComponentLeftTerms_apply (η : ℝ)
    (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (n : ℕ) (c : LiftCoeff ι h) (vdrift : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      IsBoxSmooth 1 1 (fun X z => c m α t X z v u))
    (hG : ∀ i j, ContDiff ℝ 1 (fun X => G t X i j))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) (v : ι) :
    leftTermsApply (cellB1LeftTerms η (G t) (vdrift t) (liftComponentLeftTerms n c t v)) f X z =
      cellB1 η G vdrift t (liftApply n c (fun _ => f) t) X z v := by
  rw [cellB1LeftTerms_apply η G vdrift t _ hG
    (liftComponentLeftTerms_box n c t v 1 1 (fun m hm α u => hc m hm α v u)) f hf X z]
  have he : leftTermsApply (liftComponentLeftTerms n c t v) f =
      fun Y y => liftApply n c (fun _ => f) t Y y v := by
    funext Y y
    exact liftComponentLeftTerms_apply n c t v f Y y
  rw [he]
  have hb : IsBoxSmooth 1 1 (liftApply n c (fun _ => f) t) :=
    liftApply_box_reserve n 1 1 c (fun _ => f) t (hf.of_le (by simp)) hc
  exact cellB1_postcomposition (ContinuousLinearMap.proj (R := ℝ) (φ := h) v) η G vdrift t
    (liftApply n c (fun _ => f) t) hb
    (fun i j => isBoxSmooth_slow_field 1 0 (fun Y => G t Y i j) (hG i j)) X z
end

/-! Divergence of the actual fast-independent mean flux coefficients is a finite Pi-valued differential action. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def meanFluxLeftTerms (n : ℕ) (C : Fin 2 → LiftCoeff ι h) (t : ℝ) :
    List (LeftTerm (∀ i, h i) (∀ i, h i)) :=
  (Finset.univ.toList : List (Fin 2)).flatMap fun k =>
    leftTermsSlowPartial k (liftPiLeftTerms (n - 1) (fun m α s X _ => C k m α s X 0) t)

theorem meanFluxLeftTerms_order (n : ℕ) (hn : 1 ≤ n) (C : Fin 2 → LiftCoeff ι h) (t : ℝ)
    (d : LeftTerm (∀ i, h i) (∀ i, h i)) (hd : d ∈ meanFluxLeftTerms n C t) : d.order ≤ n := by
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hd
  have he := leftTermsSlowPartial_order k _ (n - 1)
    (liftPiLeftTerms_order (n - 1) _ t) d hk
  omega

theorem meanFluxLeftTerms_box (n : ℕ) (C : Fin 2 → LiftCoeff ι h) (t : ℝ) (p q : ℕ)
    (hc : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      ContDiff ℝ ((p + 1 : ℕ) : ℕ∞) (fun X => C k m α t X 0 v u))
    (d : LeftTerm (∀ i, h i) (∀ i, h i)) (hd : d ∈ meanFluxLeftTerms n C t) : IsBoxSmooth p q d.coeff := by
  obtain ⟨k, _, hk⟩ := List.mem_flatMap.mp hd
  apply leftTermsSlowPartial_box k _ p q ?_ d hk
  intro e he
  exact liftPiLeftTerms_box (n - 1) (fun m α s X _ => C k m α s X 0) t (p + 1) q
    (fun m hm α v u => isBoxSmooth_slow_field (p + 1) q
      (fun Y => C k m α t Y 0 v u) (hc k m hm α v u)) e he

theorem meanFluxLeftTerms_apply (n : ℕ) (C : Fin 2 → LiftCoeff ι h) (t : ℝ)
    (hc : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      ContDiff ℝ 1 (fun X => C k m α t X 0 v u))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (meanFluxLeftTerms n C t) f X z =
      ∑ k : Fin 2, fderiv ℝ (fun Y => liftApply (n - 1) (C k) (fun _ => f) t Y 0) X (basisVec k) := by
  unfold meanFluxLeftTerms
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro k _
  have hcoeff (e : LeftTerm (∀ i, h i) (∀ i, h i))
      (he : e ∈ liftPiLeftTerms (n - 1) (fun m α s X _ => C k m α s X 0) t) :
      IsBoxSmooth 1 0 e.coeff :=
    liftPiLeftTerms_box (n - 1) (fun m α s X _ => C k m α s X 0) t 1 0
      (fun m hm α v u => isBoxSmooth_slow_field 1 0 (fun Y => C k m α t Y 0 v u)
        ((hc k m hm α v u).of_le (by norm_num))) e he
  rw [leftTermsSlowPartial_apply k _ hcoeff f hf]
  change fderiv ℝ (fun Y => leftTermsApply
    (liftPiLeftTerms (n - 1) (fun m α s X _ => C k m α s X 0) t) f Y z) X (basisVec k) = _
  have he : (fun Y => leftTermsApply
      (liftPiLeftTerms (n - 1) (fun m α s X _ => C k m α s X 0) t) f Y z) =
      fun Y => liftApply (n - 1) (C k) (fun _ => f) t Y 0 := by
    funext Y
    rw [liftPiLeftTerms_apply]
    rfl
  rw [he]
end

/-! The explicit source-flux terms act as the literal covariant component coefficient. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

theorem sourceFluxLeftTerms_apply (edge : ConstituentEdges D h) (η t : ℝ)
    (n : ℕ) (c : LiftCoeff ι h) (k : Fin 2) (j : ℕ) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u u',
      IsBoxSmooth j ((D - 1) - j) (fun X z => c m α t X z u u'))
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (sourceFluxLeftTerms edge η t n c k j v) f X z =
      sourceFluxComponentCoefficient edge η t (liftApply n c (fun _ => f) t) k j v X z := by
  classical
  unfold sourceFluxLeftTerms sourceFluxComponentCoefficient
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro u hu
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro d hd
  rw [leftTermsApply_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro γ hγ
  rw [leftTermsApply_finset_flatMap]
  apply Finset.sum_congr rfl
  intro α hα
  have hb : ∀ e ∈ liftComponentLeftTerms n c t u,
      IsBoxSmooth j ((List.ofFn α).length - j) e.coeff := by
    intro e he
    apply (liftComponentLeftTerms_box n c t u j ((D - 1) - j)
      (fun m hm β u' => hc m hm β u u') e he).mono le_rfl
    have hdD := (Finset.mem_Icc.mp d.property).2
    simp only [List.length_ofFn]
    omega
  have ha := constituentLeftTerms_apply η (List.ofFn α) j
    (liftComponentLeftTerms n c t u) γ.map (fun X z => γ.coeff α t X z k) hb f hf
  have he : leftTermsApply (liftComponentLeftTerms n c t u) f =
      fun X z => liftApply n c (fun _ => f) t X z u := by
    funext X z
    exact liftComponentLeftTerms_apply n c t u f X z
  rw [he] at ha
  exact congrFun (congrFun ha X) z
end

/-! The finite mean-flux terms give exactly the existing divergence-form mean action. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem meanFluxLeftTerms_meanApply (n : ℕ) (hn : 2 ≤ n) (C : Fin 2 → LiftCoeff ι h) (t : ℝ)
    (hc : ∀ k m, m ≤ n - 1 → ∀ α : DerivativeWord2 m, ∀ v u,
      ContDiff ℝ 1 (fun X => C k m α t X 0 v u))
    (hzero : ∀ k (α : DerivativeWord2 0) X v u, C k 0 α t X 0 v u = 0)
    (f : Vec 2 → ∀ i, h i) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (X z : Vec 2) :
    leftTermsApply (meanFluxLeftTerms n C t) f X z =
      meanApply n (fun d α s Y k => C k (d - 1) α s Y 0) (fun _ => f) t X := by
  rw [meanFluxLeftTerms_apply n C t hc f hf X z]
  apply meanApply_of_flux_coefficients n hn C (fun _ => f) t X hzero
  intro m hm α k
  apply (coefficient_word_action_contDiff 1 m α (C k) t 0 _ f hf).differentiable (by norm_num)
  exact fun v u => hc k m hm α v u
end

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Uniqueness at zero for a cell inverse with only local coefficient bounds. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem localCellFieldInverse_zero (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (sZ : ℕ) (a b : ℝ) (hab : a ≤ b)
    (hmG : ∀ i j, Measurable (fun t => G t i j))
    (hsG : ∀ t ∈ Set.Icc a b, (G t).IsSymm)
    (heG : ∀ t ∈ Set.Icc a b, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, ξ i * G t i j * ξ j ∧
      (∑ i, ∑ j, ξ i * G t i j * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (hcv : ∀ t ∈ Set.Icc a b, Continuous (v t))
    (hmv : ∀ z, Measurable (fun t => v t z))
    (V : ℝ) (hV : ∀ t ∈ Set.Icc a b, ∀ x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b (fun _ => 0) (fun _ _ => 0) c) :
    ∀ t ∈ Set.Icc a b, ∀ x, c t x = 0 := by
  let G' := fun t => G (Set.projIcc a b hab t)
  let v' := localCellDrift a b hab v
  have hc' : IsCellFieldInverse G' v' sZ a b (fun _ => 0) (fun _ _ => 0) c := by
    refine ⟨hc.1, ?_⟩
    intro l
    refine ⟨?_, (hc.2 l).2⟩
    exact cellSolution_coefficients_congr (fun t _ => G t) (fun t _ => G' t) v v'
      (fun t ht => localCellMetric_eq a b hab G t ht)
      (fun t ht => localCellDrift_eq a b hab v t ht) _ _ _ (hc.2 l).1
  exact cellFieldInverse_zero G' v' sZ a b hab
    (localCellMetric_admissible a b hab G hmG hsG heG)
    (localCellDrift_measurable a b hab v hcv hmv) V
    (fun t x => hV _ (Set.projIcc a b hab t).2 x) c hc'

 theorem cellFieldInverse_source_congr_on (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ)
    (v : ℝ → Vec 2 → Vec 2) (sZ : ℕ) (a b : ℝ)
    (c0 : Vec 2 → E) (g g' c : ℝ → Vec 2 → E)
    (hg : ∀ t ∈ Set.Icc a b, g t = g' t)
    (hc : IsCellFieldInverse G v sZ a b c0 g c) :
    IsCellFieldInverse G v sZ a b c0 g' c := by
  refine ⟨hc.1, ?_⟩
  intro l
  refine ⟨?_, (hc.2 l).2⟩
  apply AVRegularity.CycleEvolution.cellSolution_source_congr_sections
    (Set.Icc a b) ⟨fun t _ => G t, v, 0, 0⟩
    (fun t x => ((l (g t x) : ℝ) : ℂ)) (fun t x => ((l (g' t x) : ℝ) : ℂ))
    (fun _ _ => 0) (fun _ _ => 0) (cellJetOfField l c)
    ?_ (Filter.Eventually.of_forall (fun _ => Filter.EventuallyEq.rfl)) (hc.2 l).1
  filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
  exact Filter.EventuallyEq.of_eq (congrArg (fun q : Vec 2 → E => fun x => ((l (q x) : ℝ) : ℂ)) (hg t ht))

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! A window-restricted transverse source is exactly its clamped one-dimensional profile in the weak inverse. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E]

theorem cellFieldInverse_clamped_transverse_source
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (par : Fin 2)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hf : IsTransverseOn par (Set.Icc a b) f)
    (X : Vec 2) (c0 : Vec 2 → E) (c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b c0 (fun t z => f t X z) c) :
    IsCellFieldInverse G v sZ a b c0
      (fun t z => f (Set.projIcc a b hab t) X (z par.rev • basisVec par.rev)) c := by
  apply cellFieldInverse_source_congr_on G v sZ a b c0 _ _ c _ hc
  intro t ht
  funext z
  rw [Set.projIcc_of_mem hab ht]
  exact transverse_profile_representation par (Set.Icc a b) f hf t ht X z

end AVRegularity.CycleComparison.Lift
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! A lift recursion with zero constant-input source has zero constant-input output. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem liftConstant_zero_of_source_zero (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (c0 : ∀ i, h i) (hh n : ℕ) (hhh : hh ≤ H) (hn : 1 ≤ n) (hnN : n ≤ N)
    (hg : ∀ t ∈ Set.Icc a b, ∀ X z, liftCellSource Q Cc (fun _ _ => c0) hh n t X z = 0) :
    ∀ t ∈ Set.Icc a b, ∀ X z, liftApply n (Cc hh n) (fun _ _ => c0) t X z = 0 := by
  obtain ⟨W, hW⟩ := setting_drift_bound P
  intro t ht X z
  have hc := hseq.2.2.2.2.2.2 hh hhh n hn hnN (fun _ => c0) contDiff_const X
  have hzero := cellFieldInverse_source_congr_on (fun t => Matrix.of (Q.G t X)) Q.v sZ a b
    (fun _ => 0) (fun t z => liftCellSource Q Cc (fun _ _ => c0) hh n t X z) (fun _ _ => 0)
    (fun t z => liftApply n (Cc hh n) (fun _ _ => c0) t X z)
    (fun t ht => funext (fun z => hg t ht X z)) hc
  apply localCellFieldInverse_zero (fun t => Matrix.of (Q.G t X)) Q.v sZ a b P.window
    (fun i j => P.G_meas X i j) ?_ ?_ (setting_drift_continuous P) P.v_meas W hW _ hzero t ht z
  · intro r hr
    ext i j
    exact P.G_symm r X j i
  · intro r hr ξ
    simpa only [Matrix.of_apply, mul_assoc, mul_left_comm, mul_comm] using P.G_ellip r hr X ξ

end AVRegularity.CycleComparison.Lift
end
end
