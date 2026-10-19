-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.SettingTransverseFieldInverseExistence
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
public import AVRegularity.CycleComparison.Lift.DiagonalMeanLeftTermsActionOfCoefficients
import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The explicit response to clamped bounded transverse sources solves the original cell equation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace] [CompleteSpace Wspace]

include P in
theorem setting_transverse_field_response_inverse
    (q : ℕ) (hq : 2 ≤ q) (f : ℝ → Vec 2 → Vec 2 → Wspace)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (X : Vec 2) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => f t X z)
      (fun t z => finiteProfileResponse
        (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
        (fun s x => f (Set.projIcc a b P.window s) X (x • basisVec par.rev))
        a t (z par.rev)) := by
  let F : ℝ → ℝ → Wspace := fun t x => f t X (x • basisVec par.rev)
  have hc := setting_profile_response_inverse P q hq X F
    (fun l j => S j * ‖l‖) (fun l j hj => mul_nonneg (hS j hj) (norm_nonneg l))
    (fun l => clamped_linear_profile_joint_measurable_from_window 0 q a b P.window par.rev f hf hfm l X)
    (fun l t ht => by
      simpa only [F, Set.projIcc_of_mem P.window ht] using!
        clamped_linear_profile_fast_reserve 0 q a b P.window par.rev f hf l t X)
    (fun l t ht x => congrArg (fun y => ((l y : ℝ) : ℂ))
      (cell_periodic_linear_profile par.rev (f t X) (hper t ht X) x))
    (fun l j hj t ht x _ => by
      have hm := clamped_linear_profile_mixed_bound 0 q 0 j 0 (Nat.zero_le 0) hj
        a b P.window par.rev f hf (S j) 1
        (fun t ht X z => by simpa using hb j hj t ht X z) l t x X
      simpa only [Set.projIcc_of_mem P.window ht, norm_iteratedFDeriv_zero,
        Nat.zero_add, pow_zero, mul_one] using hm)
    (fun l t ht => transverse_profile_fourier_centered par (Icc a b) f hft t ht X
      ((hf t ht).1 X).continuous (hcenter t ht X) l)
  apply cellFieldInverse_source_congr_on _ Q.v q a b 0
    (fun t z => F t (z par.rev)) (fun t z => f t X z) _ _ hc
  intro t ht
  funext z
  exact (transverse_profile_representation par (Icc a b) f hft t ht X z).symm
end

/-! Actual bounded transverse cell sources possess a finite-past inverse in the original setting. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace] [CompleteSpace Wspace]

include P in
theorem setting_window_transverse_field_inverse_exists
    (q : ℕ) (hq : 2 ≤ q) (f : ℝ → Vec 2 → Vec 2 → Wspace)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (X : Vec 2) :
    ∃ c : ℝ → Vec 2 → Wspace,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
        (fun t z => f t X z) c := by
  let fc := fun t X z => f (Set.projIcc a b P.window t) X z
  have hf' : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (fc t) := by
    intro t ht
    simpa only [fc, Set.projIcc_of_mem P.window ht] using hf t ht
  obtain ⟨c, hc⟩ := setting_transverse_field_inverse_exists P q hq fc hf'
    (fun t ht X z s => hft _ (Set.projIcc a b P.window t).2 X z s) hfm
    (fun t _ X n z => hper _ (Set.projIcc a b P.window t).2 X n z)
    (fun t _ X => hcenter _ (Set.projIcc a b P.window t).2 X)
    S hS (fun j hj t _ X z => hb j hj _ (Set.projIcc a b P.window t).2 X z) X
  refine ⟨c, cellFieldInverse_source_congr_on _ Q.v q a b 0
    (fun t z => fc t X z) (fun t z => f t X z) c ?_ hc⟩
  intro t ht
  funext z
  simp only [fc, Set.projIcc_of_mem P.window ht]
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Identity, zero height, and truncation match the fixed scalar-power majorant exactly. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

theorem liftSequence_degree_zero_scalar_power_data (Qdata : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Qdata sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H)
    (par : Fin 2) (lam : ℝ) (hlam : 0 ≤ lam) (P Q R p q : ℕ)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (F : ι → ι → ℝ) :
    AmbientLiftCoefficientData par a b hab lam 0 p q (Cc hh 0)
      (fun v u => ambientCoefficientScalarBudget P Q D H R N hh 0 CG Cw Cj *
        finiteMatrixPower F hh v u) := by
  rw [ambientCoefficientScalarBudget_zero]
  by_cases hh0 : hh = 0
  · subst hh
    simp only [ite_true, finiteMatrixPower_zero, one_mul]
    exact liftSequence_identity_ambient_data Qdata sX sZ a b hab N H Cc hseq par lam hlam p q
  · simp only [ite_eq_right hh0, zero_mul]
    exact liftSequence_positive_height_zero_ambient_data Qdata sX sZ a b hab N H Cc hseq
      hh (by omega) hhh par lam p q

theorem liftSequence_cutoff_scalar_power_data (Qdata : LiftOperatorData ι h D)
    (sX sZ : ℕ) (a b : ℝ) (hab : a ≤ b) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Qdata sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H)
    (n : ℕ) (hN : N < n) (par : Fin 2) (lam : ℝ) (P Q R p q : ℕ) (hn : n ≤ R)
    (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (F : ι → ι → ℝ) :
    AmbientLiftCoefficientData par a b hab lam n p q (Cc hh n)
      (fun v u => ambientCoefficientScalarBudget P Q D H R N hh n CG Cw Cj *
        finiteMatrixPower F hh v u) := by
  rw [ambientCoefficientScalarBudget_cutoff P Q D H R N hh n hn hN]
  simp only [zero_mul]
  exact liftSequence_truncated_ambient_data Qdata sX sZ a b hab N H Cc hseq hh hhh n hN
    par lam p q

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual weak cell inverses inherit box reserves from source reserves only on the original window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_window_source_box_reserve (p q sZ : ℕ) (hq : 2 ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → Vec 2 → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M lam κ : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (S : ℕ → ℕ → ℝ)
    (hS : ∀ r, r ≤ p → ∀ j ≤ q, 0 ≤ S r j)
    (hfb : ∀ r, r ≤ p → ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤
        S r j * lam ^ r)
    (t : ℝ) (ht : t ∈ Icc a b) : IsBoxSmooth p q (c t) := by
  let F : ℝ → Vec 2 → ℝ → E := fun t X x =>
    f (Set.projIcc a b hab t) X (x • basisVec par.rev)
  have hc' : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => F t X (z par.rev)) (fun t z => c t X z) := by
    intro X
    exact cellFieldInverse_clamped_transverse_source (fun t => G t X) v sZ a b hab
      par f hft X 0 (fun t z => c t X z) (hc X)
  apply cellFieldInverse_ambient_box_reserve p q sZ hq G hG v W hv hvb
    par htrans F c a b hab hc' hm hs M lam κ hM hlam hκ hb hgl
    (fun l X => clamped_linear_profile_joint_measurable p q a b hab par.rev f hf hfm l X)
    (fun l t X => clamped_linear_profile_fast_reserve p q a b hab par.rev f hf l t X)
    (fun t X => cell_periodic_linear_profile par.rev _
      (hper _ (Set.projIcc a b hab t).2 X))
    (fun l i hi t z => clamped_linear_profile_slow_reserve p q i hi a b hab par.rev
      f hf l t z) (fun l s i => S s i * ‖l‖)
    (fun l s hs i hi => mul_nonneg (hS s hs i hi) (norm_nonneg l))
    (fun l s hs i hi t z X => by
      simpa only [Nat.zero_add] using
        clamped_linear_profile_mixed_bound p q s i 0 hs hi
          a b hab par.rev f hf (S s i) lam
          (by simpa only [Nat.zero_add] using hfb s hs i hi) l t z X)
    ?_ t ht
  intro l t X
  exact transverse_profile_fourier_centered par (Icc a b) f hft _
    (Set.projIcc a b hab t).2 X ((hf _ (Set.projIcc a b hab t).2).1 X).continuous
    (hcenter _ (Set.projIcc a b hab t).2 X) l
end

/-! Actual weak cell inverses inherit grading from source reserves only on the original window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_window_source_graded_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → Vec 2 → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M lam κ : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (S : ℕ → ℕ → ℝ)
    (hS : ∀ r, r ≤ p → ∀ j ≤ q, 0 ≤ S r j)
    (hfb : ∀ r, r ≤ p → ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤
        S r j * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (c t Y) z) X‖ ≤
      (parameterizedModeJetConstant p r M 1 κ (fun s => (2 : ℝ) ^ s * S s j) *
        centeredProfileJetConstant) * lam ^ (δ + r) := by
  let F : ℝ → Vec 2 → ℝ → E := fun t X x =>
    f (Set.projIcc a b hab t) X (x • basisVec par.rev)
  have hc' : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => F t X (z par.rev)) (fun t z => c t X z) := by
    intro X
    exact cellFieldInverse_clamped_transverse_source (fun t => G t X) v sZ a b hab
      par f hft X 0 (fun t z => c t X z) (hc X)
  apply cellFieldInverse_graded_mixed_bound p q sZ δ r j hq hr hj G hG v W hv hvb
    par htrans F c a b hab hc' hm hs M lam κ hM hlam hκ hb hgl
    (fun l X => clamped_linear_profile_joint_measurable p q a b hab par.rev f hf hfm l X)
    (fun l t X => clamped_linear_profile_fast_reserve p q a b hab par.rev f hf l t X)
    (fun t X => cell_periodic_linear_profile par.rev _
      (hper _ (Set.projIcc a b hab t).2 X))
    (fun l i hi t z => clamped_linear_profile_slow_reserve p q i hi a b hab par.rev
      f hf l t z) S hS
    (fun l s hs i hi t z X => clamped_linear_profile_mixed_bound p q s i δ hs hi
      a b hab par.rev f hf (S s i) lam (hfb s hs i hi) l t z X)
    ?_ t ht X z
  intro l t X
  exact transverse_profile_fourier_centered par (Icc a b) f hft _
    (Set.projIcc a b hab t).2 X ((hf _ (Set.projIcc a b hab t).2).1 X).continuous
    (hcenter _ (Set.projIcc a b hab t).2 X) l
end

/-! The actual inverse is linear in a common source budget and preserves its degree at all reserved orders. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_window_source_uniform_graded_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → Vec 2 → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M lam κ : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r, r ≤ p → ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤
        C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (c t Y) z) X‖ ≤
      (ambientInverseUniformConstant p M κ * C) * lam ^ (δ + r) := by
  have hh := cellFieldInverse_window_source_graded_mixed_bound p q sZ δ r j hq hr hj
    G hG v W hv hvb par htrans f c a b hab hc hm hs M lam κ hM hlam hκ hb hgl
    hf hft hfm hper hcenter (fun _ _ => C) (fun _ _ _ _ => hC) hfb t ht X z
  rw [parameterizedModeJetConstant_source_mul] at hh
  apply hh.trans
  have hh' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right (ambientInverseUniformConstant_entry_le p r hr M κ hM hκ) hC)
    (pow_nonneg hlam (δ + r))
  convert hh' using 1
  ring
end

/-! A short parameter-data interface separates coefficient admissibility from the inverse estimate. -/

section
structure CellInverseParameterData (p : ℕ) (par : Fin 2) (lam M κ W : ℝ)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (drift : ℝ → Vec 2 → Vec 2) : Prop where
  metric : ∀ X, IsCellMetric (fun t _ => G t X)
  drift_measurable : Measurable (fun x : ℝ × Vec 2 => drift x.1 x.2)
  drift_bound : ∀ t z, ∑ i, drift t z i ^ 2 ≤ W ^ 2
  transverse : ∀ t z, drift t z par.rev = 0
  M_nonneg : 0 ≤ M
  lam_nonneg : 0 ≤ lam
  kappa_pos : 0 < κ
  diagonal_measurable : ∀ X, Measurable (fun t => G t X par.rev par.rev)
  diagonal_smooth : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev)
  diagonal_bound : ∀ r ≤ p, ∀ t X,
    ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r
  diagonal_lower : ∀ t X, κ ≤ G t X par.rev par.rev

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem CellInverseParameterData.window_graded_bound {p : ℕ} {par : Fin 2} {lam M κ W : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {drift : ℝ → Vec 2 → Vec 2}
    (data : CellInverseParameterData p par lam M κ W G drift)
    (q sZ δ r j : ℕ) (hq : 2 ≤ q) (hr : r ≤ p) (hj : j ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → E) (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (c t Y) z) X‖ ≤
      (ambientInverseUniformConstant p M κ * C) * lam ^ (δ + r) :=
  cellFieldInverse_window_source_uniform_graded_mixed_bound p q sZ δ r j hq hr hj
    G data.metric drift W data.drift_measurable data.drift_bound par data.transverse
    f c a b hab hc data.diagonal_measurable data.diagonal_smooth M lam κ
    data.M_nonneg data.lam_nonneg data.kappa_pos data.diagonal_bound data.diagonal_lower
    hf hft hfm hper hcenter C hC hfb t ht X z
end

/-! The actual scalar-dual representative is measurable after clamping time to its cell window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem CellInverseParameterData.profile_dual_clamped_measurable
    {p : ℕ} {par : Fin 2} {lam M κ W : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {drift : ℝ → Vec 2 → Vec 2}
    (data : CellInverseParameterData p par lam M κ W G drift)
    (sZ q : ℕ) (hq : 2 ≤ q) (a b : ℝ) (hab : a ≤ b)
    (f : ℝ → Vec 2 → ℝ → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => c t X z))
    (l : E →L[ℝ] ℝ) (X z : Vec 2)
    (hfm : Measurable (fun tx : ℝ × ℝ => ((l (f tx.1 X tx.2) : ℝ) : ℂ)))
    (hf : ∀ t ∈ Icc a b, ContDiff ℝ q (fun x => ((l (f t X x) : ℝ) : ℂ)))
    (hper : ∀ t ∈ Icc a b, Function.Periodic (fun x => ((l (f t X x) : ℝ) : ℂ)) 1)
    (C : ℕ → ℝ) (hC : ∀ j ≤ q, 0 ≤ C j)
    (hfb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t X y) : ℝ) : ℂ)) x‖ ≤ C j) :
    Measurable (fun t => l (c (Set.projIcc a b hab t) X z)) := by
  let g := fun t => G t X par.rev par.rev
  let F := fun t x => ((l (f t X x) : ℝ) : ℂ)
  have hgb t : |g t| ≤ M := by
    simpa only [g, norm_iteratedFDeriv_zero, pow_zero, mul_one, Real.norm_eq_abs] using
      data.diagonal_bound 0 (Nat.zero_le p) t X
  have hi : IntegrableOn g (Icc a b) := by
    apply (integrable_const M).mono' (data.diagonal_measurable X).aestronglyMeasurable
    exact ae_of_all _ (fun t => (by simpa only [Real.norm_eq_abs] using hgb t))
  have hcont := profileCellResponse_iteratedDeriv_time_continuousOn g F a b κ M hab
    data.kappa_pos hi (fun t _ => data.diagonal_lower t X) data.M_nonneg
    (data.diagonal_measurable X).aestronglyMeasurable hgb hfm q C hC hf hper hfb
    0 (Nat.zero_le q) (z par.rev)
  simp only [iteratedDeriv_zero] at hcont
  have hm := (hcont.comp_continuous
    (continuous_projIcc (a := a) (b := b) (h := hab)).subtype_val
    (fun t => (Set.projIcc a b hab t).2)).measurable
  have he : (fun t => ((l (c (Set.projIcc a b hab t) X z) : ℝ) : ℂ)) =
      fun t => profileCellResponse g F a (Set.projIcc a b hab t) (z par.rev) := by
    funext t
    exact congrFun (cellFieldInverse_dual_eq_profileResponse (fun t => G t X) (data.metric X)
      drift W data.drift_measurable data.drift_bound par data.transverse (fun t => f t X)
      (fun t => c t X) sZ a b hab (hc X) l hfm q hq C hC hf hper hfb
      _ (Set.projIcc a b hab t).2) z
  change Measurable (fun t => profileCellResponse g F a (Set.projIcc a b hab t) (z par.rev)) at hm
  rw [← he] at hm
  have hr := Complex.reCLM.continuous.measurable.comp hm
  change Measurable (fun t => (((l (c (Set.projIcc a b hab t) X z) : ℝ) : ℂ)).re) at hr
  simpa only [Complex.ofReal_re] using hr
end

/-! A genuine graded source supplies rectangular regularity through the short inverse-data interface. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem CellInverseParameterData.window_box_reserve {p : ℕ} {par : Fin 2} {lam M κ W : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {drift : ℝ → Vec 2 → Vec 2}
    (data : CellInverseParameterData p par lam M κ W G drift)
    (q sZ δ : ℕ) (hq : 2 ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → E) (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) : IsBoxSmooth p q (c t) := by
  apply cellFieldInverse_window_source_box_reserve p q sZ hq
    G data.metric drift W data.drift_measurable data.drift_bound par data.transverse
    f c a b hab hc data.diagonal_measurable data.diagonal_smooth M lam κ
    data.M_nonneg data.lam_nonneg data.kappa_pos data.diagonal_bound data.diagonal_lower
    hf hft hfm hper hcenter (fun _ _ => C * lam ^ δ)
    (fun _ _ _ _ => mul_nonneg hC (pow_nonneg data.lam_nonneg _)) _ t ht
  intro r hr j hj t ht X z
  simpa only [pow_add, mul_assoc] using hfb r hr j hj t ht X z
end

/-! Window-only source regularity gives measurable clamped representatives of the actual inverse. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem CellInverseParameterData.window_clamped_dual_measurable
    {p : ℕ} {par : Fin 2} {lam M κ W : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {drift : ℝ → Vec 2 → Vec 2}
    (data : CellInverseParameterData p par lam M κ W G drift)
    (sZ q : ℕ) (hq : 2 ≤ q) (a b : ℝ) (hab : a ≤ b)
    (f c : ℝ → Vec 2 → Vec 2 → E)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b hab t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (l : E →L[ℝ] ℝ) (X z : Vec 2) :
    Measurable (fun t => l (c (Set.projIcc a b hab t) X z)) := by
  let F : ℝ → Vec 2 → ℝ → E := fun t X x => f (Set.projIcc a b hab t) X (x • basisVec par.rev)
  have hi (X : Vec 2) : IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => F t X (z par.rev)) (fun t z => c t X z) :=
    cellFieldInverse_clamped_transverse_source (fun t => G t X) drift sZ a b hab
      par f hft X 0 (fun t z => c t X z) (hc X)
  have hfast t : ContDiff ℝ (q : ℕ∞) (fun x => ((l (F t X x) : ℝ) : ℂ)) :=
    clamped_linear_profile_fast_reserve 0 q a b hab par.rev f hf l t X
  have hm x : Measurable (fun t => ((l (F t X x) : ℝ) : ℂ)) :=
    Complex.ofRealCLM.continuous.measurable.comp (hfm l X (x • basisVec par.rev))
  have hmeas := profile_iteratedDeriv_joint_measurable (fun t x => ((l (F t X x) : ℝ) : ℂ))
    hm q hfast 0 (Nat.zero_le q)
  simp only [iteratedDeriv_zero] at hmeas
  have hp' (t : ℝ) (_ : t ∈ Icc a b) : Function.Periodic (fun x => ((l (F t X x) : ℝ) : ℂ)) 1 := by
    intro x
    exact congrArg (fun y => ((l y : ℝ) : ℂ))
      (cell_periodic_linear_profile par.rev _ (hper _ (Set.projIcc a b hab t).2 X) x)
  apply data.profile_dual_clamped_measurable sZ q hq a b hab F c hi l X z hmeas
    (fun t _ => hfast t) hp' (fun j => S j * ‖l‖)
    (fun j hj => mul_nonneg (hS j hj) (norm_nonneg l))
  intro j hj t _ x _
  have hh := clamped_linear_profile_mixed_bound 0 q 0 j 0 (Nat.zero_le 0) hj
      a b hab par.rev f hf (S j) 1
      (fun t ht X z => by simpa only [norm_iteratedFDeriv_zero, one_pow, mul_one] using hb j hj t ht X z)
      l t x X
  simpa only [norm_iteratedFDeriv_zero, one_pow, mul_one] using hh
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Construct the short inverse-data interface entirely from the original lift setting. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_inverse_parameter_data (p : ℕ) (hp : p ≤ qs) (W : ℝ)
    (hW : ∀ t ∈ Set.Icc a b, ∀ z, ∑ i, Q.v t z i ^ 2 ≤ W ^ 2) :
    CellInverseParameterData p par lam (metricParameterBudget p CG) (3 / 4) W
      (fun t X => Matrix.of (Q.G (Set.projIcc a b P.window t) X))
      (localCellDrift a b P.window Q.v) := by
  have hdata := setting_clamped_diagonal_metric_fixed_data P p hp par.rev
  dsimp only at hdata
  refine ⟨setting_cell_metric P,
    localCellDrift_measurable a b P.window Q.v (setting_drift_continuous P) P.v_meas,
    fun t z => hW _ (Set.projIcc a b P.window t).2 z,
    fun t z => setting_transverse_drift_zero P _ z,
    hdata.1, ?_, by norm_num, hdata.2.1, hdata.2.2.1, hdata.2.2.2.1, hdata.2.2.2.2⟩
  rw [P.lam_eq]
  exact (div_pos P.ρ_pos P.E_pos).le

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Original setting data give a fixed inverse constant for genuine window-source grading. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_uniform_graded_bound (p q sZ δ r j : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hr : r ≤ p) (hj : j ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (c t Y) z) X‖ ≤
      (ambientInverseUniformConstant p (metricParameterBudget p CG) (3 / 4) * C) * lam ^ (δ + r) := by
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have data := setting_inverse_parameter_data P p hp W hW
  have hlocal (X : Vec 2) : IsCellFieldInverse
      (fun t => Matrix.of (Q.G (Set.projIcc a b P.window t) X))
      (localCellDrift a b P.window Q.v) sZ a b (0 : Vec 2 → Wspace)
      (fun t z => f t X z) (fun t z => c t X z) :=
    cellFieldInverse_local_coefficients (E := Wspace)
      (fun t => Matrix.of (Q.G t X)) Q.v sZ a b P.window (0 : Vec 2 → Wspace)
      (fun t z => f t X z) (fun t z => c t X z) (hc X)
  exact data.window_graded_bound q sZ δ r j hq hr hj f c a b P.window hlocal
    hf hft hfm hper hcenter C hC hfb t ht X z
end

/-! Only the clamped source must be measurable; arbitrary values outside the window play no role. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_clamped_source_graded_bound (p q sZ δ r j : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q) (hr : r ≤ p) (hj : j ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (c t Y) z) X‖ ≤
      (ambientInverseUniformConstant p (metricParameterBudget p CG) (3 / 4) * C) * lam ^ (δ + r) := by
  let F := fun t X z => f (Set.projIcc a b P.window t) X z
  have hlocal (X : Vec 2) : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => F t X z) (fun t z => c t X z) := by
    apply cellFieldInverse_source_congr_on (E := Wspace) (fun t => Matrix.of (Q.G t X)) Q.v
      sZ a b 0 (fun t z => f t X z) (fun t z => F t X z) (fun t z => c t X z) _ (hc X)
    intro t ht
    dsimp only [F]
    rw [Set.projIcc_of_mem P.window ht]
  have htrans : IsTransverseOn par (Icc a b) F := by
    intro t _ X z s
    exact hft _ (Set.projIcc a b P.window t).2 X z s
  exact setting_window_inverse_uniform_graded_bound P p q sZ δ r j hp hq hr hj F c hlocal
    (fun t _ => hf _ (Set.projIcc a b P.window t).2) htrans hfm
    (fun t _ X n z => hper _ (Set.projIcc a b P.window t).2 X n z)
    (fun t _ X => hcenter _ (Set.projIcc a b P.window t).2 X) C hC
    (fun r hr j hj t _ X z => hfb r hr j hj _ (Set.projIcc a b P.window t).2 X z) t ht X z
end

/-! Original setting data give ambient rectangular regularity for genuine graded sources. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_box_reserve (p q sZ δ : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) : IsBoxSmooth p q (c t) := by
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have data := setting_inverse_parameter_data P p hp W hW
  have hlocal (X : Vec 2) : IsCellFieldInverse
      (fun t => Matrix.of (Q.G (Set.projIcc a b P.window t) X))
      (localCellDrift a b P.window Q.v) sZ a b (0 : Vec 2 → Wspace)
      (fun t z => f t X z) (fun t z => c t X z) :=
    cellFieldInverse_local_coefficients (E := Wspace)
      (fun t => Matrix.of (Q.G t X)) Q.v sZ a b P.window (0 : Vec 2 → Wspace)
      (fun t z => f t X z) (fun t z => c t X z) (hc X)
  exact data.window_box_reserve q sZ δ hq f c a b P.window hlocal
    hf hft hfm hper hcenter C hC hfb t ht
end

/-! Window-only source regularity preserves transverse geometry of the actual inverse. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem CellInverseParameterData.window_clamped_transverse
    {p : ℕ} {par : Fin 2} {lam M κ W : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {drift : ℝ → Vec 2 → Vec 2}
    (data : CellInverseParameterData p par lam M κ W G drift)
    (sZ q : ℕ) (hq : 2 ≤ q) (a b : ℝ) (hab : a ≤ b)
    (f c : ℝ → Vec 2 → Vec 2 → E)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b hab t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j) :
    IsTransverseOn par (Icc a b) c := by
  let F := fun t X z => f (Set.projIcc a b hab t) X z
  have hi (X : Vec 2) : IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => F t X z) (fun t z => c t X z) := by
    apply cellFieldInverse_source_congr_on (E := E) (fun t => G t X) drift sZ a b 0
      (fun t z => f t X z) (fun t z => F t X z) (fun t z => c t X z) _ (hc X)
    intro t ht
    dsimp only [F]
    rw [Set.projIcc_of_mem hab ht]
  apply cellFieldInverse_window_source_transverse 0 q sZ hq G data.metric drift W
    data.drift_measurable data.drift_bound par data.transverse F c a b hab hi 1
    (fun t _ => hf _ (Set.projIcc a b hab t).2)
    (fun t _ X z s => hft _ (Set.projIcc a b hab t).2 X z s)
    hfm (fun t _ X n z => hper _ (Set.projIcc a b hab t).2 X n z)
    (fun _ j => S j) (fun _ _ j hj => hS j hj)
  intro r hr j hj t _ X z
  have hr0 : r = 0 := by omega
  subst r
  simpa only [norm_iteratedFDeriv_zero, pow_zero, mul_one] using
    hb j hj _ (Set.projIcc a b hab t).2 X z
end

/-! Original window data give measurable clamped representatives of genuine inverse fields. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_clamped_dual_measurable (q sZ : ℕ) (hq : 2 ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (l : Wspace →L[ℝ] ℝ) (X z : Vec 2) :
    Measurable (fun t => l (c (Set.projIcc a b P.window t) X z)) := by
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have data := setting_inverse_parameter_data P 0 (Nat.zero_le qs) W hW
  have hlocal (Y : Vec 2) : IsCellFieldInverse
      (fun t => Matrix.of (Q.G (Set.projIcc a b P.window t) Y))
      (localCellDrift a b P.window Q.v) sZ a b (0 : Vec 2 → Wspace)
      (fun t z => f t Y z) (fun t z => c t Y z) :=
    cellFieldInverse_local_coefficients (E := Wspace)
      (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b P.window (0 : Vec 2 → Wspace)
      (fun t z => f t Y z) (fun t z => c t Y z) (hc Y)
  exact data.window_clamped_dual_measurable sZ q hq a b P.window f c hlocal
    hf hft hfm hper S hS hb l X z
end

/-! Only the clamped source must be measurable; arbitrary values outside the window play no role. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_clamped_source_box_reserve (p q sZ δ : ℕ)
    (hp : p ≤ qs) (hq : 2 ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r ≤ p, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤ C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) : IsBoxSmooth p q (c t) := by
  let F := fun t X z => f (Set.projIcc a b P.window t) X z
  have hlocal (X : Vec 2) : IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => F t X z) (fun t z => c t X z) := by
    apply cellFieldInverse_source_congr_on (E := Wspace) (fun t => Matrix.of (Q.G t X)) Q.v
      sZ a b 0 (fun t z => f t X z) (fun t z => F t X z) (fun t z => c t X z) _ (hc X)
    intro t ht
    dsimp only [F]
    rw [Set.projIcc_of_mem P.window ht]
  have htrans : IsTransverseOn par (Icc a b) F := by
    intro t _ X z s
    exact hft _ (Set.projIcc a b P.window t).2 X z s
  exact setting_window_inverse_box_reserve P p q sZ δ hp hq F c hlocal
    (fun t _ => hf _ (Set.projIcc a b P.window t).2) htrans hfm
    (fun t _ X n z => hper _ (Set.projIcc a b P.window t).2 X n z)
    (fun t _ X => hcenter _ (Set.projIcc a b P.window t).2 X) C hC
    (fun r hr j hj t _ X z => hfb r hr j hj _ (Set.projIcc a b P.window t).2 X z) t ht
end

/-! Actual weak cell inverses inherit grading from source reserves only on the original window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_window_source_metric_difference_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → Vec 2 → E) (c ci : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) v sZ a b 0
      (fun t z => f t X z) (fun t z => ci t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M Md eps lam κ : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hdb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev - 1) X‖ ≤ Md * eps * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (S : ℕ → ℕ → ℝ)
    (hS : ∀ r, r ≤ p → ∀ j ≤ q, 0 ≤ S r j)
    (hfb : ∀ r, r ≤ p → ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤
        S r j * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (fun y => c t Y y - ci t Y y) z) X‖ ≤
      (metricDifferenceModeJetConstant p r M Md κ (fun s => (2 : ℝ) ^ s * S s j) *
        centeredProfileJetConstant) * eps * lam ^ (δ + r) := by
  let F : ℝ → Vec 2 → ℝ → E := fun t X x =>
    f (Set.projIcc a b hab t) X (x • basisVec par.rev)
  have hc' : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => F t X (z par.rev)) (fun t z => c t X z) := by
    intro X
    exact cellFieldInverse_clamped_transverse_source (fun t => G t X) v sZ a b hab
      par f hft X 0 (fun t z => c t X z) (hc X)
  have hci' : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) v sZ a b 0
      (fun t z => F t X (z par.rev)) (fun t z => ci t X z) := by
    intro X
    exact cellFieldInverse_clamped_transverse_source (fun _ i j => if i = j then 1 else 0)
      v sZ a b hab par f hft X 0 (fun t z => ci t X z) (hci X)
  apply cellFieldInverse_graded_metric_difference_mixed_bound p q sZ δ r j hq hr hj G hG v W hv hvb
    par htrans F c ci a b hab hc' hci' hm hs M Md eps lam κ hM hMd heps hlam hκ hκ1 hb hdb hgl
    (fun l X => clamped_linear_profile_joint_measurable p q a b hab par.rev f hf hfm l X)
    (fun l t X => clamped_linear_profile_fast_reserve p q a b hab par.rev f hf l t X)
    (fun t X => cell_periodic_linear_profile par.rev _
      (hper _ (Set.projIcc a b hab t).2 X))
    (fun l i hi t z => clamped_linear_profile_slow_reserve p q i hi a b hab par.rev
      f hf l t z) S hS
    (fun l s hs i hi t z X => clamped_linear_profile_mixed_bound p q s i δ hs hi
      a b hab par.rev f hf (S s i) lam (hfb s hs i hi) l t z X)
    ?_ t ht X z
  intro l t X
  exact transverse_profile_fourier_centered par (Icc a b) f hft _
    (Set.projIcc a b hab t).2 X ((hf _ (Set.projIcc a b hab t).2).1 X).continuous
    (hcenter _ (Set.projIcc a b hab t).2 X) l
end

/-! Actual weak cell inverses inherit grading from source reserves only on the original window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_window_source_uniform_metric_difference_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → Vec 2 → E) (c ci : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) v sZ a b 0
      (fun t z => f t X z) (fun t z => ci t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M Md eps lam κ : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hdb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev - 1) X‖ ≤ Md * eps * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (C : ℝ) (hC : 0 ≤ C)
    (hfb : ∀ r, r ≤ p → ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤
        C * lam ^ (δ + r))
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (fun y => c t Y y - ci t Y y) z) X‖ ≤
      (metricInverseUniformConstant p M Md κ * C) * eps * lam ^ (δ + r) := by
  have hh := cellFieldInverse_window_source_metric_difference_mixed_bound p q sZ δ r j hq hr hj
    G hG v W hv hvb par htrans f c ci a b hab hc hci hm hs M Md eps lam κ
    hM hMd heps hlam hκ hκ1 hb hdb hgl hf hft hfm hper hcenter
    (fun _ _ => C) (fun _ _ _ _ => hC) hfb t ht X z
  rw [metricDifferenceModeJetConstant_source_mul] at hh
  apply hh.trans
  have hb' := mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right
        (metricInverseUniformConstant_entry_le p r hr M Md κ hM hMd hκ) hC) heps)
    (pow_nonneg hlam (δ + r))
  convert hb' using 1
  ring
end

/-! Clamped measurable source data recover the original window time primitive. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem CellInverseParameterData.window_clamped_time_integral
    {p : ℕ} {par : Fin 2} {lam M κ W : ℝ}
    {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {drift : ℝ → Vec 2 → Vec 2}
    (data : CellInverseParameterData p par lam M κ W G drift)
    (sZ q : ℕ) (hsZ : 2 ≤ sZ) (hq : 2 ≤ q) (a b : ℝ) (hab : a ≤ b)
    (f c : ℝ → Vec 2 → Vec 2 → E)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) drift sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b hab t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    IntervalIntegrable (fun s => -cellOperator (G s X) (drift s) (c s X) z + f s X z) volume a t ∧
      c t X z = ∫ s in a..t, -cellOperator (G s X) (drift s) (c s X) z + f s X z := by
  let F := fun s X z => f (Set.projIcc a b hab s) X z
  have hi (Y : Vec 2) : IsCellFieldInverse (fun s => G s Y) drift sZ a b 0
      (fun s z => F s Y z) (fun s z => c s Y z) := by
    apply cellFieldInverse_source_congr_on (E := E) (fun s => G s Y) drift sZ a b 0
      (fun s z => f s Y z) (fun s z => F s Y z) (fun s z => c s Y z) _ (hc Y)
    intro s hs
    dsimp only [F]
    rw [Set.projIcc_of_mem hab hs]
  obtain ⟨hInt, heq⟩ := cellFieldInverse_window_time_integral 0 q sZ hq hsZ G data.metric
    drift W data.drift_measurable data.drift_bound par data.transverse F c a b hab hi
    (fun s _ => hf _ (Set.projIcc a b hab s).2)
    (fun s _ Y w r => hft _ (Set.projIcc a b hab s).2 Y w r)
    hfm (fun s _ Y n w => hper _ (Set.projIcc a b hab s).2 Y n w) S hS
    (fun j hj s _ Y w => hb j hj _ (Set.projIcc a b hab s).2 Y w) t ht X z
  have he (s : ℝ) (hs : s ∈ uIcc a t) : F s X z = f s X z := by
    rw [uIcc_of_le ht.1] at hs
    dsimp only [F]
    rw [Set.projIcc_of_mem hab ⟨hs.1, hs.2.trans ht.2⟩]
  refine ⟨hInt.congr (fun s hs => by rw [he s (uIoc_subset_uIcc hs)]), ?_⟩
  rw [heq]
  exact intervalIntegral.integral_congr (fun s hs => by rw [he s hs])
end

/-! Original window data preserve the transverse geometry of genuine inverse fields. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace]

include P in
theorem setting_window_inverse_clamped_transverse (q sZ : ℕ) (hq : 2 ≤ q)
    (f c : ℝ → Vec 2 → Vec 2 → Wspace)
    (hc : ∀ X, IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v sZ a b 0
      (fun t z => f t X z) (fun t z => c t X z))
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z,
      Measurable (fun t => l (f (Set.projIcc a b P.window t) X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    : IsTransverseOn par (Icc a b) c := by
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have data := setting_inverse_parameter_data P 0 (Nat.zero_le qs) W hW
  have hlocal (Y : Vec 2) : IsCellFieldInverse
      (fun t => Matrix.of (Q.G (Set.projIcc a b P.window t) Y))
      (localCellDrift a b P.window Q.v) sZ a b (0 : Vec 2 → Wspace)
      (fun t z => f t Y z) (fun t z => c t Y z) :=
    cellFieldInverse_local_coefficients (E := Wspace)
      (fun t => Matrix.of (Q.G t Y)) Q.v sZ a b P.window (0 : Vec 2 → Wspace)
      (fun t z => f t Y z) (fun t z => c t Y z) (hc Y)
  exact data.window_clamped_transverse sZ q hq a b P.window f c hlocal
    hf hft hfm hper S hS hb
end

end AVRegularity.CycleComparison.Lift
end
