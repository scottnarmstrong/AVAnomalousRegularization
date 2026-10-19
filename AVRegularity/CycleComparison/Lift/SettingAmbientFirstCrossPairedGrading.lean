-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingAmbientSourceTestPeriodicOfCoefficients
public import AVRegularity.CycleComparison.Lift.CellB1LeftTerms

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original metric premise controls the actual paired second-cross term from predecessor states. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_second_cross_paired_lift_bound
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs)
    (hp' : p + 2 ≤ p') (hq' : q ≤ q')
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (c ci : LiftCoeff ι h) (M Mi Md : ι → ι → ℝ) (hMd : ∀ v u, 0 ≤ Md v u)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (datai : AmbientLiftCoefficientData par a b P.window lam n p' q' ci Mi)
    (datad : AmbientLiftCoefficientData par a b P.window lam n p' q'
      (fun m α t X z v u => c m α t X z v u - ci m α t X z v u)
      (fun v u => Md v u * g))
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 Q.η Q.G t
          (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • cellB2 Q.η
          (fun _ _ i j => if i = j then 1 else 0) t
          (liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      ((normalizedCellB2UniformConstant p q A (metricParameterBudget (p + 1) CG) * Md v u +
        normalizedCellB2UniformConstant p q A (metricParameterBudget (p + 1) CGI) * Mi v u) *
        finiteLiftSymbolBudget n A * ‖ξ‖) * g * lam ^ ((n + 2) + r) := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hη : 0 ≤ Q.η := by rw [P.η_eq]; exact (div_pos P.ν_pos P.B_pos).le
  have hh := normalizedCellB2_paired_lift_test_grading n p q Q.η lam
    (metricParameterBudget (p + 1) CG) (metricParameterBudget (p + 1) CGI)
    g (Mi v u) (Md v u)
    hη P.η_le hlam (metricParameterBudget_nonneg (p + 1) CG)
    (metricParameterBudget_nonneg (p + 1) CGI)
    hg (datai.nonneg v u) (hMd v u) A Q.G
    (fun _ _ i j => if i = j then 1 else 0) t c ci v u ξ
    (fun m hm α v' u' => (data.box m hm α v' u' t ht).mono hp' hq')
    (fun m hm α v' u' => (datai.box m hm α v' u' t ht).mono hp' hq')
    (fun _ _ => isBoxSmooth_slow_field (p + 1) q _ contDiff_const)
    (fun i j => setting_metric_entry_box P (p + 1) q hp t ht i j)
    X
    (fun i j a ha b _ y => setting_metric_mixed_uniform_bound P (p + 1) a b hp ha t ht X y i j)
    (fun i j a ha b _ y => setting_metric_difference_mixed_uniform_bound P
      (p + 1) a b hp ha g hg CGI hGI t ht X y i j)
    (fun m hm α a ha b hb y => datai.bound m hm α v u a (ha.trans hp') b (hb.trans hq') t ht X y)
    (fun m hm α a ha b hb y => datad.bound m hm α v u a (ha.trans hp') b (hb.trans hq') t ht X y)
    r s hr hs z
  exact hh.trans_eq (by ring)
end

/-! The original metric premise controls the actual paired first-cross term from predecessor states. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_first_cross_paired_lift_bound
    (n p q p' q' : ℕ) (hp : p + 1 ≤ qs) (hq : q ≤ qf)
    (hp' : p + 1 ≤ p') (hq' : q + 1 ≤ q')
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (c ci : LiftCoeff ι h) (M Mi Md : ι → ι → ℝ) (hMd : ∀ v u, 0 ≤ Md v u)
    (data : AmbientLiftCoefficientData par a b P.window lam n p' q' c M)
    (datai : AmbientLiftCoefficientData par a b P.window lam n p' q' ci Mi)
    (datad : AmbientLiftCoefficientData par a b P.window lam n p' q'
      (fun m α t X z v u => c m α t X z v u - ci m α t X z v u)
      (fun v u => Md v u * g))
    (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (ht : t ∈ Set.Icc a b) (v u : ι) (ξ : h u)
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 Q.η Q.G Q.v t
          (liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v -
        (Real.exp ((lam • A) Y))⁻¹ • cellB1 Q.η
          (fun _ _ i j => if i = j then 1 else 0) Q.v t
          (liftApply n ci (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t) Y y v) z) X‖ ≤
      ((normalizedCellB1UniformConstant p q A (metricParameterBudget (p + 1) CG)
          (metricParameterBudget q Cw) * Md v u +
        normalizedCellB1UniformConstant p q A (metricParameterBudget (p + 1) CGI) 0 * Mi v u) *
        finiteLiftSymbolBudget n A * ‖ξ‖) * g * lam ^ ((n + 1) + r) := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hh := normalizedCellB1_paired_lift_test_grading n p q Q.η lam
    (metricParameterBudget (p + 1) CG) (metricParameterBudget (p + 1) CGI)
    (metricParameterBudget q Cw) g (Mi v u) (Md v u)
    P.η_le hlam (metricParameterBudget_nonneg (p + 1) CG)
    (metricParameterBudget_nonneg (p + 1) CGI) (metricParameterBudget_nonneg q Cw)
    hg (datai.nonneg v u) (hMd v u) A Q.G
    (fun _ _ i j => if i = j then 1 else 0) Q.v t c ci v u ξ
    (fun m hm α v' u' => (data.box m hm α v' u' t ht).mono hp' hq')
    (fun m hm α v' u' => (datai.box m hm α v' u' t ht).mono hp' hq')
    (fun _ _ => isBoxSmooth_slow_field (p + 1) q _ contDiff_const)
    (fun i j => setting_metric_entry_box P (p + 1) q hp t ht i j)
    (fun i => setting_raw_drift_fast_box P p q hq t ht i) X
    (fun i j a ha b _ y => setting_metric_mixed_uniform_bound P (p + 1) a b hp ha t ht X y i j)
    (fun i j a ha b _ y => setting_metric_difference_mixed_uniform_bound P
      (p + 1) a b hp ha g hg CGI hGI t ht X y i j)
    (fun i a _ b hb y => setting_scaled_drift_mixed_uniform_bound P q a b hq hb t ht X y i)
    (fun m hm α a ha b hb y => datai.bound m hm α v u a (ha.trans hp') b (hb.trans hq') t ht X y)
    (fun m hm α a ha b hb y => datad.bound m hm α v u a (ha.trans hp') b (hb.trans hq') t ht X y)
    r s hr hs z
  exact hh.trans_eq (by ring)
end

end AVRegularity.CycleComparison.Lift
end
