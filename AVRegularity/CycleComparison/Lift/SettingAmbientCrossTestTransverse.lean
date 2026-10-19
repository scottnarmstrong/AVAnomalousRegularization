-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.ProfileCellInitial
import AVRegularity.CycleComparison.Lift.FirstDiagonalSource
public import AVRegularity.CycleComparison.Lift.SettingDimensionalScales

@[expose] public noncomputable section

section
open MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! The fast derivative identity uses only the original fast source jets. -/

theorem profileCellResponse_fast_jet_identity (g : ℝ → ℝ) (f : ℝ → ℝ → ℂ)
    (a b κ : ℝ) (hab : a ≤ b) (hκ : 0 < κ) (hi : IntegrableOn g (Icc a b))
    (hg : ∀ t ∈ Icc a b, κ ≤ g t) (j : ℕ) (C : ℕ → ℝ)
    (hC : ∀ r ≤ j, 0 ≤ C r) (hf : ∀ t ∈ Icc a b, ContDiff ℝ (j : ℕ∞) (f t))
    (hp : ∀ t ∈ Icc a b, Function.Periodic (f t) 1)
    (hb : ∀ r ≤ j, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv r (f t) x‖ ≤ C r) (z : ℝ) :
    iteratedDeriv j (profileCellResponse g f a b) z = profileWeightedResponse g f a b z j := by
  have hsum : ∀ r ≤ j, Summable (fun m => profileFourierFrequency m ^ r * profileModeResponse g f a b m) := by
    intro r hr
    apply profileFourier_jet_summable _ r (C r / κ)
    intro m hm
    exact profileModeResponse_frequency_weight_bound g f a b κ hab hκ hi hg r (C r) (hC r hr)
      (fun t ht => (hf t ht).of_le (by exact_mod_cast hr)) hp (hb r hr) m hm
  change iteratedDeriv j (profileFourierSeries (profileModeResponse g f a b)) z = _
  rw [profileFourierSeries_iteratedDeriv j _ hsum]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The measurable-metric propagator has the reserved slow parameter regularity. -/

theorem transverseModeKernel_parameter_contDiff (n : ℕ) (g : ℝ → Vec 2 → ℝ)
    (hm : ∀ x, Measurable (fun t => g t x))
    (hs : ∀ t, ContDiff ℝ (n : ℕ∞) (g t))
    (C : ℕ → ℝ) (hb : ∀ j ≤ n, ∀ t x, ‖iteratedFDeriv ℝ j (g t) x‖ ≤ C j)
    (rate a b : ℝ) :
    ContDiff ℝ (n : ℕ∞) (fun x => transverseModeKernel rate (fun t => g t x) a b) := by
  have hi := parameter_intervalIntegral_contDiff n g hm hs C hb a b
  simpa only [transverseModeKernel, smul_eq_mul] using (hi.const_smul (-rate)).exp

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The actual shear and both cross tests preserve the parallel fast invariance. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] [DecidableEq ι]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
omit [DecidableEq ι] in
theorem setting_drift_transverse :
    IsTransverseOn par (Set.Icc a b) (fun t (_ : Vec 2) z => Q.v t z) := by
  intro t _ X z s
  change Q.v t (z + s • basisVec par) = Q.v t z
  rw [P.v_shear, P.v_shear]
  have hne : par.rev ≠ par := by
    have hh : ∀ p : Fin 2, p.rev ≠ p := by decide
    exact hh par
  simp only [Pi.add_apply, Pi.smul_apply, basisVec_apply, ite_eq_right hne, smul_zero, add_zero]

include P in
theorem setting_first_cross_test_transverse (n p q : ℕ) (c : LiftCoeff ι h)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q c M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) :
    IsTransverseOn par (Set.Icc a b) (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      cellB1 Q.η Q.G Q.v t (liftApply n c
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  have hΦ := liftApply_transverse par (Set.Icc a b) n c
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) data.transverse
  have hb := cellB1_transverse par (Set.Icc a b) Q.η Q.G Q.v _ hΦ (setting_drift_transverse P)
  intro t ht X z s
  exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hb t ht X z s)

theorem setting_second_cross_test_transverse (n p q : ℕ) (c : LiftCoeff ι h)
    (M : ι → ι → ℝ)
    (data : AmbientLiftCoefficientData par a b P.window lam n p q c M)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) :
    IsTransverseOn par (Set.Icc a b) (fun t X z => (Real.exp ((lam • A) X))⁻¹ •
      cellB2 Q.η Q.G t (liftApply n c
        (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) X z v) := by
  have hΦ := liftApply_transverse par (Set.Icc a b) n c
    (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) data.transverse
  have hb := cellB2_transverse par (Set.Icc a b) Q.η Q.G _ hΦ
  intro t ht X z s
  exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hb t ht X z s)

end AVRegularity.CycleComparison.Lift
end
