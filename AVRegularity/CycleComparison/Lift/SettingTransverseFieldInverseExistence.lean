-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Lift.CellFieldAmbientBoxReserve
import AVRegularity.CycleComparison.Lift.LiftMeanCompositionLowDegree
public import AVRegularity.CycleComparison.Lift.TailTestScalarBudget
import AVRegularity.CycleComparison.Lift.NormalizedSourceArrayZeroMatrixBound
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
import AVRegularity.CycleComparison.Lift.SecondCrossMean
import AVRegularity.CycleComparison.Lift.LiftMeanRecursionCongruence

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! Affine tests identify the actual first coefficient entries, including their component support. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

local instance firstCoefficientScalarFormulaDecidableEq : DecidableEq ι := Classical.decEq ι

include P in
theorem liftCoefficient_first_scalar_apply (sX sZ : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (α : DerivativeWord2 1) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2)
    (v u : ι) (ξ : h u) :
    Cc 0 1 1 α t X z v u ξ =
      ((profileCellResponse
        (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
        (clampedFirstSourceProfile Q.η V a b P.window 1) a t (z par.rev)).re *
          basisVec par (α 0)) • Pi.single u ξ v := by
  classical
  let T : Vec 2 →L[ℝ] (∀ i, h i) := (ContinuousLinearMap.proj (α 0)).smulRight (Pi.single u ξ)
  have he := liftApply_one_linear_single_of_zero_order (Cc 0 1) α t X z v u ξ
    (fun β j => liftSequence_zero_order_coefficient_zero P sX sZ Cc hseq
      0 (Nat.zero_le H) 1 le_rfl β t ht X z v j)
  rw [← he]
  have hh := congrFun (liftApply_first_linear_scalar P sX sZ Cc hseq T t ht X z) v
  simpa only [T, ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply,
    Pi.smul_apply, smul_smul] using! hh

include P in
theorem liftCoefficient_first_diagonal_scalar (sX sZ : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (α : DerivativeWord2 1) (t : ℝ) (ht : t ∈ Set.Icc a b) (X z : Vec 2) (v : ι) :
    Cc 0 1 1 α t X z v v =
      ((profileCellResponse
        (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
        (clampedFirstSourceProfile Q.η V a b P.window 1) a t (z par.rev)).re *
          basisVec par (α 0)) • ContinuousLinearMap.id ℝ (h v) := by
  classical
  apply ContinuousLinearMap.ext
  intro ξ
  rw [liftCoefficient_first_scalar_apply P sX sZ Cc hseq α t ht X z v v ξ]
  simp only [Pi.single_eq_same, smul_apply, ContinuousLinearMap.id_apply]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! A finite scalar majorant for all of the metric comparison energy readouts. -/

def pairedEnergyScalarBudget (N K k : ℕ) (B : ℕ → ℝ) : ℝ :=
  (2 ^ N * (k + 1) * 2 ^ (K + 1)) * ∑ n ∈ Finset.range (N + 1), B n

theorem pairedEnergyScalarBudget_nonneg (N K k : ℕ) (B : ℕ → ℝ) (hB : ∀ n, 0 ≤ B n) :
    0 ≤ pairedEnergyScalarBudget N K k B := by
  unfold pairedEnergyScalarBudget
  exact mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ => hB n)

theorem pairedEnergyScalarBudget_dominates (N K k n m r : ℕ) (B : ℕ → ℝ)
    (hB : ∀ n, 0 ≤ B n) (hn : n ≤ N) (hm : m ≤ n) (hr : r ≤ K) :
    (2 ^ m * (k + 1) * 2 ^ (r + 1)) * B n ≤ pairedEnergyScalarBudget N K k B := by
  have hb : B n ≤ ∑ i ∈ Finset.range (N + 1), B i :=
    Finset.single_le_sum (fun i _ => hB i) (Finset.mem_range.mpr (by omega))
  have hp : (2 : ℝ) ^ m ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) (hm.trans hn)
  have hq : (2 : ℝ) ^ (r + 1) ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  exact mul_le_mul (mul_le_mul (mul_le_mul_of_nonneg_right hp (by positivity)) hq
    (by positivity) (by positivity)) hb (hB n) (by positivity)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual weak cell inverses inherit graded mixed scalar-dual bounds from their source. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_graded_dual_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → ℝ → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => c t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M lam κ : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X,
      Measurable (fun x : ℝ × ℝ => ((l (f x.1 X x.2) : ℝ) : ℂ)))
    (hff : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      ContDiff ℝ (q : ℕ∞) (fun z => ((l (f t X z) : ℝ) : ℂ)))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t z,
      ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (fun y => ((l (f t X y) : ℝ) : ℂ)) z))
    (S : (E →L[ℝ] ℝ) → ℕ → ℕ → ℝ)
    (hS : ∀ l r, r ≤ p → ∀ j ≤ q, 0 ≤ S l r j)
    (hfb : ∀ l r, r ≤ p → ∀ j ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ r
        (fun Y => iteratedDeriv j (fun y => ((l (f t Y y) : ℝ) : ℂ)) z) X‖ ≤ S l r j * lam ^ (δ + r))
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      unitProfileFourierCoeff (fun z => ((l (f t X z) : ℝ) : ℂ)) 0 = 0)
    (t : ℝ) (ht : t ∈ Icc a b) (l : E →L[ℝ] ℝ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (fun y => ((l (c t Y y) : ℝ) : ℂ)) z) X‖ ≤
      (parameterizedModeJetConstant p r M 1 κ (fun s => (2 : ℝ) ^ s * S l s j) *
        centeredProfileJetConstant) * lam ^ (δ + r) := by
  let F := fun r X z => ((l (f r X z) : ℝ) : ℂ)
  have he : (fun X z => ((l (c t X z) : ℝ) : ℂ)) =
      fun X z => profileCellResponse (fun r => G r X par.rev par.rev) (fun r => F r X) a t (z par.rev) := by
    funext X z
    have hj : ∀ j ≤ q, ∀ r ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv j (F r X) y‖ ≤ S l 0 j * lam ^ δ := by
      intro j hj r _ y _
      simpa only [norm_iteratedFDeriv_zero, Nat.add_zero] using! hfb l 0 (Nat.zero_le p) j hj r y X
    exact congrFun (cellFieldInverse_dual_eq_profileResponse (fun r => G r X) (hG X) v W hv hvb
      par htrans (fun r => f r X) (fun r => c r X) sZ a b hab (hc X) l (hfm l X)
      q hq (fun j => S l 0 j * lam ^ δ)
      (fun j hj => mul_nonneg (hS l 0 (Nat.zero_le p) j hj) (pow_nonneg hlam δ)) (fun r _ => hff l r X)
      (fun r _ z => congrArg (fun y => ((l y : ℝ) : ℂ)) (hper r X z)) hj t ht) z
  simp_rw [show ∀ Y y, ((l (c t Y y) : ℝ) : ℂ) =
      profileCellResponse (fun s => G s Y par.rev par.rev) (fun s => F s Y) a t (y par.rev)
      from fun Y y => congrFun (congrFun he Y) y]
  have hh := profileCellResponse_graded_mixed_bound p q δ r j hr hj
    (fun s Y => G s Y par.rev par.rev) hm hs M lam κ a t hM hlam hκ ht.1 hb hgl
    F (hfm l) (hff l) (fun s Y y => congrArg (fun x => ((l x : ℝ) : ℂ)) (hper s Y y))
    (hfs l) (S l) (hS l) (hfb l) (hcenter l)
    (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ) X z
  simpa only [cell_coordinate_projection_norm, one_pow, one_mul, ContinuousLinearMap.proj_apply] using! hh

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Finite real coordinates and the compiled scalar Fourier response construct an actual vector field inverse. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finite_profile_response_field_inverse
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)) (V : ℝ)
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → E) (a b : ℝ) (hab : a ≤ b) (q : ℕ) (hq : 2 ≤ q)
    (C : (E →L[ℝ] ℝ) → ℕ → ℝ) (hC : ∀ l j, j ≤ q → 0 ≤ C l j)
    (hfm : ∀ l : E →L[ℝ] ℝ, Measurable (fun p : ℝ × ℝ => ((l (f p.1 p.2) : ℝ) : ℂ)))
    (hf : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b, ContDiff ℝ q (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ l : E →L[ℝ] ℝ, ∀ t, Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C l j)
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      unitProfileFourierCoeff (fun x => ((l (f t x) : ℝ) : ℂ)) 0 = 0) :
    IsCellFieldInverse G v q a b 0 (fun t z => f t (z par.rev))
      (fun t z => finiteProfileResponse (fun r => G r par.rev par.rev) f a t (z par.rev)) := by
  classical
  let e := (Module.finBasis ℝ E).equivFunL
  let l := fun j => (ContinuousLinearMap.proj j).comp e.toContinuousLinearMap
  let cs := fun j (t : ℝ) (z : Vec 2) =>
    (profileCellResponse (fun r => G r par.rev par.rev)
      (fun s x => ((l j (f s x) : ℝ) : ℂ)) a t (z par.rev)).re
  have hc j : IsCellFieldInverse G v q a b 0
      (fun t z => l j (f t (z par.rev))) (cs j) := by
    simpa only [Complex.ofReal_re] using profileResponse_real_field_inverse G hG v V hv hb par ht
      (fun s x => ((l j (f s x) : ℝ) : ℂ)) a b hab (hfm (l j)) q hq (C (l j))
      (hC (l j)) (hf (l j)) (hp (l j)) (hj (l j)) (by intro t x; simp) (hcenter (l j))
  have hi := cellFieldInverse_pi_synthesis e.symm.toContinuousLinearMap G v q (by omega)
    a b hab (fun j t z => l j (f t (z par.rev))) cs hc
  have hsrc : (fun (t : ℝ) (z : Vec 2) => e.symm (fun j => l j (f t (z par.rev)))) =
      fun (t : ℝ) (z : Vec 2) => f t (z par.rev) := by
    funext t z
    exact e.symm_apply_apply (f t (z par.rev))
  change IsCellFieldInverse G v q a b 0 (fun t z => f t (z par.rev))
    (fun t z => e.symm (fun j => cs j t z))
  change IsCellFieldInverse G v q a b 0
    (fun t z => e.symm (fun j => l j (f t (z par.rev))))
    (fun t z => e.symm (fun j => cs j t z)) at hi
  rw [hsrc] at hi
  exact hi
end

/-! Existence facade for the explicit finite-coordinate profile inverse. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finite_profile_field_inverse_exists
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)) (V : ℝ)
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → E) (a b : ℝ) (hab : a ≤ b) (q : ℕ) (hq : 2 ≤ q)
    (C : (E →L[ℝ] ℝ) → ℕ → ℝ) (hC : ∀ l j, j ≤ q → 0 ≤ C l j)
    (hfm : ∀ l : E →L[ℝ] ℝ, Measurable (fun p : ℝ × ℝ => ((l (f p.1 p.2) : ℝ) : ℂ)))
    (hf : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b, ContDiff ℝ q (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ l : E →L[ℝ] ℝ, ∀ t, Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C l j)
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      unitProfileFourierCoeff (fun x => ((l (f t x) : ℝ) : ℂ)) 0 = 0) :
    ∃ c : ℝ → Vec 2 → E, IsCellFieldInverse G v q a b 0 (fun t z => f t (z par.rev)) c := by
  refine ⟨fun t z => finiteProfileResponse (fun r => G r par.rev par.rev) f a t (z par.rev), ?_⟩
  exact finite_profile_response_field_inverse G hG v hv V hb par ht f a b hab q hq C hC hfm hf hp hj hcenter
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual weak cell inverses inherit vector grading without a dimension-dependent constant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_graded_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → ℝ → E) (c : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => c t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M lam κ : ℝ) (hM : 0 ≤ M) (hlam : 0 ≤ lam) (hκ : 0 < κ)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X,
      Measurable (fun x : ℝ × ℝ => ((l (f x.1 X x.2) : ℝ) : ℂ)))
    (hff : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      ContDiff ℝ (q : ℕ∞) (fun z => ((l (f t X z) : ℝ) : ℂ)))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t z,
      ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (fun y => ((l (f t X y) : ℝ) : ℂ)) z))
    (S : ℕ → ℕ → ℝ)
    (hS : ∀ r, r ≤ p → ∀ j ≤ q, 0 ≤ S r j)
    (hfb : ∀ l : E →L[ℝ] ℝ, ∀ r, r ≤ p → ∀ j ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ r
        (fun Y => iteratedDeriv j (fun y => ((l (f t Y y) : ℝ) : ℂ)) z) X‖ ≤ (S r j * ‖l‖) * lam ^ (δ + r))
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      unitProfileFourierCoeff (fun z => ((l (f t X z) : ℝ) : ℂ)) 0 = 0)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (c t Y) z) X‖ ≤
      (parameterizedModeJetConstant p r M 1 κ (fun s => (2 : ℝ) ^ s * S s j) *
        centeredProfileJetConstant) * lam ^ (δ + r) := by
  let Sl := fun (l : E →L[ℝ] ℝ) s i => S s i * ‖l‖
  let S' := fun (l : E →L[ℝ] ℝ) s i => Sl l s i * lam ^ δ
  have hSl : ∀ l s, s ≤ p → ∀ i ≤ q, 0 ≤ Sl l s i :=
    fun l s hs i hi => mul_nonneg (hS s hs i hi) (norm_nonneg l)
  have hS' : ∀ l s, s ≤ p → ∀ i ≤ q, 0 ≤ S' l s i :=
    fun l s hs i hi => mul_nonneg (hSl l s hs i hi) (pow_nonneg hlam δ)
  have hfb' : ∀ l s, s ≤ p → ∀ i ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ s
        (fun Y => iteratedDeriv i (fun y => ((l (f t Y y) : ℝ) : ℂ)) z) X‖ ≤
        S' l s i * lam ^ s := by
    intro l s hs i hi t z X
    simpa only [S', Sl, pow_add, mul_assoc] using hfb l s hs i hi t z X
  have hbox := cellFieldInverse_ambient_box_reserve p q sZ hq G hG v W hv hvb par htrans
    f c a b hab hc hm hs M lam κ hM hlam hκ hb hgl hfm hff hper hfs S' hS' hfb'
    hcenter t ht
  let C := parameterizedModeJetConstant p r M 1 κ (fun s => (2 : ℝ) ^ s * S s j) *
    centeredProfileJetConstant
  have hC : 0 ≤ C := mul_nonneg
    (parameterizedModeJetConstant_nonneg p r M 1 κ _ hM zero_le_one hκ
      (fun s hs => mul_nonneg (by positivity) (hS s (hs.trans hr) j hj)))
    centeredProfileJetConstant_nonneg
  apply mixed_jet_norm_le_from_complexified_real_duals r j (c t)
    (hbox.mono hr hj) X z (C * lam ^ (δ + r)) (mul_nonneg hC (pow_nonneg hlam _))
  intro l
  have hh := cellFieldInverse_graded_dual_mixed_bound p q sZ δ r j hq hr hj G hG v W hv hvb
    par htrans f c a b hab hc hm hs M lam κ hM hlam hκ hb hgl hfm hff hper hfs
    Sl hSl hfb hcenter t ht l X z
  apply hh.trans_eq
  have he : (fun s => (2 : ℝ) ^ s * Sl l s j) =
      fun s => ((2 : ℝ) ^ s * S s j) * ‖l‖ := by
    funext s
    exact (mul_assoc _ _ _).symm
  rw [he, parameterizedModeJetConstant_source_mul]
  dsimp only [C]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original data reserve supports every actual uncentered rank step, including truncated predecessors. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_uncentered_data_of_predecessor_family
    (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hper : ∀ hh n m (α : DerivativeWord2 m) v u, ∀ t ∈ Set.Icc a b, ∀ X,
      AVenhance.IsZ2Periodic (fun z => Cc hh n m α t X z v u))
    (hcut : ∀ hh ≤ H, ∀ n, N < n → Cc hh n = 0)
    (P₀ hh n : ℕ) (hreserve : P₀ + (N + D) ≤ qs) (hhh : hh ≤ H)
    (hn : 1 ≤ n) (hnR : n ≤ N + D)
    (prior : ∀ h' ≤ H, ∀ m ≤ N + D,
      ambientRecurrenceRank (N + D) h' m < ambientRecurrenceRank (N + D) hh n →
      AmbientLiftCoefficientData par a b P.window lam m (ambientDegreeSlowReserve P₀ (N + D) m)
        (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) h' m) (Cc h' m)
        (fun v u => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h' m
          CG Cw Cj * finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) h' v u)) :
    AmbientLiftUncenteredData par a b P.window lam hh n (ambientDegreeSlowReserve P₀ (N + D) n)
      (ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n) Q Cc
      (ambientUncenteredBudget P₀ (max k (L + 2)) D H (N + D) hh n CG Cw Cj
        (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj))
      (finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh) := by
  let p := ambientDegreeSlowReserve P₀ (N + D) n
  let q := ambientDegreeFastReserve (max k (L + 2)) D H (N + D) hh n
  have hp : p + 1 ≤ qs :=
    (ambientDegreeSlowReserve_coefficient P₀ (N + D) n hn hnR).trans hreserve
  have hq : q + 1 ≤ qf := by
    have hc := ambientDegreeFastReserve_data (max k (L + 2)) D H (N + D) hh n hn hnR
    rw [P.qf_eq]
    dsimp only [q] at ⊢
    omega
  apply setting_liftA_power_data_of_coefficients P Cc hper hh n p q hn hp hq
    (fun h m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D H (N + D) N h m CG Cw Cj)
    (fun h m => ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ h m _ _ _)
  · have hd := prior hh hhh (n - 1) (by omega)
      (ambientRecurrenceRank_degree (N + D) hh n 1 (by omega) hn)
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n 1 hnR hn
      change p + 1 ≤ _
      rw [← he]
    · have he := ambientDegreeFastReserve_cross (max k (L + 2)) D H (N + D) hh n 1 hnR hn
      change q + 1 ≤ _
      rw [← he]
      dsimp only [q]
      omega
  · intro hn₂
    have hd := prior hh hhh (n - 2) (by omega)
      (ambientRecurrenceRank_degree (N + D) hh n 2 (by omega) hn₂)
    apply hd.mono
    · have he := ambientDegreeSlowReserve_source P₀ (N + D) n 2 hnR hn₂
      change p + 2 ≤ _
      rw [← he]
    · have he := ambientDegreeFastReserve_cross (max k (L + 2)) D H (N + D) hh n 2 hnR hn₂
      change q ≤ _
      rw [← he]
      dsimp only [q]
      omega
  · intro hh0 j hj
    have hjD : j ≤ D := hj.trans (Nat.min_le_left _ _)
    have hjn : j ≤ n := hj.trans (Nat.min_le_right _ _)
    by_cases hpred : n - j ≤ N
    · have hd := prior (hh - 1) (by omega) (n - j) (by omega)
        (ambientRecurrenceRank_source (N + D) hh n j (by omega) hnR)
      exact hd.mono (ambient_source_slow_box_supported P₀ N D n j hnR hjn hpred)
        (ambient_source_fast_box_supported (max k (L + 2)) N D H hh n j
          (by omega) hhh hnR hjn hjD)
    · rw [ambientCoefficientScalarBudget_cutoff P₀ (max k (L + 2)) D H (N + D) N
        (hh - 1) (n - j) (by omega) (by omega)]
      simp only [zero_mul, hcut (hh - 1) (by omega) (n - j) (by omega)]
      exact ambient_zero_coefficient_data par a b P.window lam (n - j)
        (max D (p + j)) (max D (q + D - j))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual weak cell inverses with identical forcing have graded scalar-dual metric difference bounds. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_graded_dual_metric_difference_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → ℝ → E) (c ci : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => c t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => ci t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M Md eps lam κ : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hdb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev - 1) X‖ ≤ Md * eps * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X,
      Measurable (fun x : ℝ × ℝ => ((l (f x.1 X x.2) : ℝ) : ℂ)))
    (hff : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      ContDiff ℝ (q : ℕ∞) (fun z => ((l (f t X z) : ℝ) : ℂ)))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t z,
      ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (fun y => ((l (f t X y) : ℝ) : ℂ)) z))
    (S : (E →L[ℝ] ℝ) → ℕ → ℕ → ℝ)
    (hS : ∀ l r, r ≤ p → ∀ j ≤ q, 0 ≤ S l r j)
    (hfb : ∀ l r, r ≤ p → ∀ j ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ r
        (fun Y => iteratedDeriv j (fun y => ((l (f t Y y) : ℝ) : ℂ)) z) X‖ ≤ S l r j * lam ^ (δ + r))
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      unitProfileFourierCoeff (fun z => ((l (f t X z) : ℝ) : ℂ)) 0 = 0)
    (t : ℝ) (ht : t ∈ Icc a b) (l : E →L[ℝ] ℝ) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (fun y => ((l (c t Y y - ci t Y y) : ℝ) : ℂ)) z) X‖ ≤
      (metricDifferenceModeJetConstant p r M Md κ (fun s => (2 : ℝ) ^ s * S l s j) *
        centeredProfileJetConstant) * eps * lam ^ (δ + r) := by
  let F := fun s X z => ((l (f s X z) : ℝ) : ℂ)
  have he : (fun X z => ((l (c t X z - ci t X z) : ℝ) : ℂ)) =
      fun X z => profileCellResponse (fun s => G s X par.rev par.rev) (fun s => F s X) a t (z par.rev) -
        profileCellResponse (fun _ => 1) (fun s => F s X) a t (z par.rev) := by
    funext X z
    have hj : ∀ j ≤ q, ∀ s ∈ Icc a b, ∀ y ∈ Icc (0 : ℝ) 1,
        ‖iteratedDeriv j (F s X) y‖ ≤ S l 0 j * lam ^ δ := by
      intro j hj s _ y _
      simpa only [norm_iteratedFDeriv_zero, Nat.add_zero] using!
        hfb l 0 (Nat.zero_le p) j hj s y X
    have hC (j : ℕ) (hj : j ≤ q) : 0 ≤ S l 0 j * lam ^ δ :=
      mul_nonneg (hS l 0 (Nat.zero_le p) j hj) (pow_nonneg hlam _)
    have hGrep := congrFun (cellFieldInverse_dual_eq_profileResponse (fun s => G s X) (hG X) v W hv hvb
      par htrans (fun s => f s X) (fun s => c s X) sZ a b hab (hc X) l (hfm l X)
      q hq (fun j => S l 0 j * lam ^ δ) hC (fun s _ => hff l s X)
      (fun s _ y => congrArg (fun x => ((l x : ℝ) : ℂ)) (hper s X y)) hj t ht) z
    have hIrep := congrFun (cellFieldInverse_dual_eq_profileResponse (fun _ => 1) cellIdentityMetric v W hv hvb
      par htrans (fun s => f s X) (fun s => ci s X) sZ a b hab (hci X) l (hfm l X)
      q hq (fun j => S l 0 j * lam ^ δ) hC (fun s _ => hff l s X)
      (fun s _ y => congrArg (fun x => ((l x : ℝ) : ℂ)) (hper s X y)) hj t ht) z
    rw [map_sub, Complex.ofReal_sub, hGrep, hIrep]
    simp only [Matrix.one_apply_eq]
    rfl
  let Df := fun Y y => ((l (c t Y y - ci t Y y) : ℝ) : ℂ)
  change ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (Df Y) z) X‖ ≤ _
  have hDf : Df = fun Y y =>
      profileCellResponse (fun s => G s Y par.rev par.rev) (fun s => F s Y) a t (y par.rev) -
        profileCellResponse (fun _ => 1) (fun s => F s Y) a t (y par.rev) := he
  rw [hDf]
  have hh := profileCellResponse_graded_metric_difference_mixed_bound p q δ r j hr hj
    (fun s Y => G s Y par.rev par.rev) hm hs M Md eps lam κ a t hM hMd heps hlam hκ hκ1 ht.1 hb hdb hgl
    F (hfm l) (hff l) (fun s Y y => congrArg (fun x => ((l x : ℝ) : ℂ)) (hper s Y y))
    (hfs l) (S l) (hS l) (hfb l) (hcenter l)
    (ContinuousLinearMap.proj par.rev : Vec 2 →L[ℝ] ℝ) X z
  simpa only [cell_coordinate_projection_norm, one_pow, one_mul, ContinuousLinearMap.proj_apply] using! hh
end

/-! Actual weak cell inverses inherit transverse geometry from source reserves only on the original window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_window_source_transverse (p q sZ : ℕ) (hq : 2 ≤ q)
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
    (lam : ℝ)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth p q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (S : ℕ → ℕ → ℝ)
    (hS : ∀ r, r ≤ p → ∀ j ≤ q, 0 ≤ S r j)
    (hfb : ∀ r, r ≤ p → ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j (f t Y) z) X‖ ≤
        S r j * lam ^ r)
    : IsTransverseOn par (Icc a b) c := by
  let F : ℝ → Vec 2 → ℝ → E := fun t X x =>
    f (Set.projIcc a b hab t) X (x • basisVec par.rev)
  have hc' : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => F t X (z par.rev)) (fun t z => c t X z) := by
    intro X
    exact cellFieldInverse_clamped_transverse_source (fun t => G t X) v sZ a b hab
      par f hft X 0 (fun t z => c t X z) (hc X)
  apply cellFieldInverse_profile_transverse G hG v W hv hvb par htrans F c sZ q hq
    a b hab hc'
    (fun l X => clamped_linear_profile_joint_measurable p q a b hab par.rev f hf hfm l X)
    (fun l t _ X => clamped_linear_profile_fast_reserve p q a b hab par.rev f hf l t X)
    (fun t _ X => cell_periodic_linear_profile par.rev _
      (hper _ (Set.projIcc a b hab t).2 X))
    (fun l _ j => S 0 j * ‖l‖)
    (fun l _ j hj => mul_nonneg (hS 0 (Nat.zero_le p) j hj) (norm_nonneg l))
    ?_
  intro l j hj t _ X x _
  have h := clamped_linear_profile_mixed_bound p q 0 j 0 (Nat.zero_le p) hj
    a b hab par.rev f hf (S 0 j) lam
    (by simpa only [Nat.zero_add] using hfb 0 (Nat.zero_le p) j hj) l t x X
  simpa only [norm_iteratedFDeriv_zero, Nat.zero_add, pow_zero, mul_one] using h
end

/-! Actual weak cell inverses inherit vector grading without a dimension-dependent constant. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem cellFieldInverse_graded_metric_difference_mixed_bound (p q sZ δ r j : ℕ) (hq : 2 ≤ q)
    (hr : r ≤ p) (hj : j ≤ q)
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X, IsCellMetric (fun t _ => G t X))
    (v : ℝ → Vec 2 → Vec 2) (W : ℝ)
    (hv : Measurable (fun x : ℝ × Vec 2 => v x.1 x.2))
    (hvb : ∀ t z, ∑ i, v t z i ^ 2 ≤ W ^ 2)
    (par : Fin 2) (htrans : ∀ t z, v t z par.rev = 0)
    (f : ℝ → Vec 2 → ℝ → E) (c ci : ℝ → Vec 2 → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b)
    (hc : ∀ X, IsCellFieldInverse (fun t => G t X) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => c t X z))
    (hci : ∀ X, IsCellFieldInverse (fun _ i j => if i = j then 1 else 0) v sZ a b 0
      (fun t z => f t X (z par.rev)) (fun t z => ci t X z))
    (hm : ∀ X, Measurable (fun t => G t X par.rev par.rev))
    (hs : ∀ t, ContDiff ℝ (p : ℕ∞) (fun X => G t X par.rev par.rev))
    (M Md eps lam κ : ℝ) (hM : 0 ≤ M) (hMd : 0 ≤ Md) (heps : 0 ≤ eps)
    (hlam : 0 ≤ lam) (hκ : 0 < κ) (hκ1 : κ ≤ 1)
    (hb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev) X‖ ≤ M * lam ^ r)
    (hdb : ∀ r ≤ p, ∀ t X,
      ‖iteratedFDeriv ℝ r (fun Y => G t Y par.rev par.rev - 1) X‖ ≤ Md * eps * lam ^ r)
    (hgl : ∀ t X, κ ≤ G t X par.rev par.rev)
    (hfm : ∀ l : E →L[ℝ] ℝ, ∀ X,
      Measurable (fun x : ℝ × ℝ => ((l (f x.1 X x.2) : ℝ) : ℂ)))
    (hff : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      ContDiff ℝ (q : ℕ∞) (fun z => ((l (f t X z) : ℝ) : ℂ)))
    (hper : ∀ t X, Function.Periodic (f t X) 1)
    (hfs : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t z,
      ContDiff ℝ (p : ℕ∞) (fun X => iteratedDeriv j (fun y => ((l (f t X y) : ℝ) : ℂ)) z))
    (S : ℕ → ℕ → ℝ)
    (hS : ∀ r, r ≤ p → ∀ j ≤ q, 0 ≤ S r j)
    (hfb : ∀ l : E →L[ℝ] ℝ, ∀ r, r ≤ p → ∀ j ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ r
        (fun Y => iteratedDeriv j (fun y => ((l (f t Y y) : ℝ) : ℂ)) z) X‖ ≤ (S r j * ‖l‖) * lam ^ (δ + r))
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t X,
      unitProfileFourierCoeff (fun z => ((l (f t X z) : ℝ) : ℂ)) 0 = 0)
    (t : ℝ) (ht : t ∈ Icc a b) (X z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ j
      (fun y => c t Y y - ci t Y y) z) X‖ ≤
      (metricDifferenceModeJetConstant p r M Md κ (fun s => (2 : ℝ) ^ s * S s j) *
        centeredProfileJetConstant) * eps * lam ^ (δ + r) := by
  let Sl := fun (l : E →L[ℝ] ℝ) s i => S s i * ‖l‖
  let S' := fun (l : E →L[ℝ] ℝ) s i => Sl l s i * lam ^ δ
  have hSl : ∀ l s, s ≤ p → ∀ i ≤ q, 0 ≤ Sl l s i :=
    fun l s hs i hi => mul_nonneg (hS s hs i hi) (norm_nonneg l)
  have hS' : ∀ l s, s ≤ p → ∀ i ≤ q, 0 ≤ S' l s i :=
    fun l s hs i hi => mul_nonneg (hSl l s hs i hi) (pow_nonneg hlam δ)
  have hfb' : ∀ l s, s ≤ p → ∀ i ≤ q, ∀ t z X,
      ‖iteratedFDeriv ℝ s
        (fun Y => iteratedDeriv i (fun y => ((l (f t Y y) : ℝ) : ℂ)) z) X‖ ≤
        S' l s i * lam ^ s := by
    intro l s hs i hi t z X
    simpa only [S', Sl, pow_add, mul_assoc] using hfb l s hs i hi t z X
  have hbox := cellFieldInverse_ambient_box_reserve p q sZ hq G hG v W hv hvb par htrans
    f c a b hab hc hm hs M lam κ hM hlam hκ hb hgl hfm hff hper hfs S' hS' hfb'
    hcenter t ht
  have hboxi := cellFieldInverse_ambient_box_reserve p q sZ hq (fun _ _ => 1)
    (fun _ => cellIdentityMetric) v W hv hvb par htrans f ci a b hab hci
    (fun _ => measurable_const) (fun _ => contDiff_const) 1 lam κ zero_le_one hlam hκ
    (fun r _ _ X => by
      simp only [Matrix.one_apply_eq]
      simpa only [abs_one] using scalarConstant_scaled_jet_le 1 lam hlam r X)
    (fun _ _ => by simpa only [Matrix.one_apply_eq] using hκ1) hfm hff hper hfs S' hS' hfb' hcenter t ht
  let C := metricDifferenceModeJetConstant p r M Md κ (fun s => (2 : ℝ) ^ s * S s j) *
    centeredProfileJetConstant
  have hC : 0 ≤ C := by
    dsimp only [C]
    apply mul_nonneg _ centeredProfileJetConstant_nonneg
    unfold metricDifferenceModeJetConstant
    exact mul_nonneg (mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (metricDifferenceKernelSourceConstant_nonneg p r M Md κ _ hM hMd hκ
        (fun s hs => mul_nonneg (by positivity) (hS s (hs.trans hr) j hj)))))
      (div_nonneg (by positivity) hκ.le)
  apply mixed_jet_norm_le_from_complexified_real_duals r j (fun Y y => c t Y y - ci t Y y)
    ((hbox.sub hboxi).mono hr hj) X z (C * eps * lam ^ (δ + r))
    (mul_nonneg (mul_nonneg hC heps) (pow_nonneg hlam _))
  intro l
  have hh := cellFieldInverse_graded_dual_metric_difference_mixed_bound p q sZ δ r j hq hr hj G hG v W hv hvb
    par htrans f c ci a b hab hc hci hm hs M Md eps lam κ hM hMd heps hlam hκ hκ1 hb hdb hgl hfm hff hper hfs
    Sl hSl hfb hcenter t ht l X z
  apply hh.trans_eq
  have he : (fun s => (2 : ℝ) ^ s * Sl l s j) =
      fun s => ((2 : ℝ) ^ s * S s j) * ‖l‖ := by
    funext s
    exact (mul_assoc _ _ _).symm
  rw [he, metricDifferenceModeJetConstant_source_mul]
  dsimp only [C]
  ring
end

end AVRegularity.CycleComparison.Lift
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Clamp source history, then transfer the constructed finite-coordinate inverse to the original window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finite_profile_window_response_inverse
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)) (V : ℝ)
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → E) (a b : ℝ) (hab : a ≤ b) (q : ℕ) (hq : 2 ≤ q)
    (C : (E →L[ℝ] ℝ) → ℕ → ℝ) (hC : ∀ l j, j ≤ q → 0 ≤ C l j)
    (hfm : ∀ l : E →L[ℝ] ℝ, Measurable (fun p : ℝ × ℝ => ((l (f (Set.projIcc a b hab p.1) p.2) : ℝ) : ℂ)))
    (hf : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b, ContDiff ℝ q (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b, Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C l j)
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      unitProfileFourierCoeff (fun x => ((l (f t x) : ℝ) : ℂ)) 0 = 0) :
    IsCellFieldInverse G v q a b 0 (fun t z => f t (z par.rev))
      (fun t z => finiteProfileResponse (fun r => G r par.rev par.rev)
        (fun s x => f (Set.projIcc a b hab s) x) a t (z par.rev)) := by
  let fc := fun t x => f (Set.projIcc a b hab t) x
  have hc := finite_profile_response_field_inverse G hG v hv V hb par ht fc a b hab q hq C hC
    hfm
    (fun l t hti => by
      simpa only [fc, Set.projIcc_of_mem hab hti] using hf l t hti)
    (fun l t => hp l (Set.projIcc a b hab t) (Set.projIcc a b hab t).2)
    (fun l j hj' t hti x hx => by
      simpa only [fc, Set.projIcc_of_mem hab hti] using hj l j hj' t hti x hx)
    (fun l t hti => by
      simpa only [fc, Set.projIcc_of_mem hab hti] using hcenter l t hti)
  exact cellFieldInverse_source_congr_on G v q a b 0
    (fun t z => fc t (z par.rev)) (fun t z => f t (z par.rev))
    (fun t z => finiteProfileResponse (fun r => G r par.rev par.rev) fc a t (z par.rev))
    (fun t hti => by funext z; simp only [fc, Set.projIcc_of_mem hab hti]) hc
end

/-! Clamp source history, then transfer the constructed finite-coordinate inverse to the original window. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

theorem finite_profile_window_inverse_exists
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : Measurable (fun p : ℝ × Vec 2 => v p.1 p.2)) (V : ℝ)
    (hb : ∀ t z, ∑ i, v t z i ^ 2 ≤ V ^ 2)
    (par : Fin 2) (ht : ∀ t z, v t z par.rev = 0)
    (f : ℝ → ℝ → E) (a b : ℝ) (hab : a ≤ b) (q : ℕ) (hq : 2 ≤ q)
    (C : (E →L[ℝ] ℝ) → ℕ → ℝ) (hC : ∀ l j, j ≤ q → 0 ≤ C l j)
    (hfm : ∀ l : E →L[ℝ] ℝ, Measurable (fun p : ℝ × ℝ => ((l (f (Set.projIcc a b hab p.1) p.2) : ℝ) : ℂ)))
    (hf : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b, ContDiff ℝ q (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b, Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ l : E →L[ℝ] ℝ, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C l j)
    (hcenter : ∀ l : E →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      unitProfileFourierCoeff (fun x => ((l (f t x) : ℝ) : ℂ)) 0 = 0) :
    ∃ c : ℝ → Vec 2 → E, IsCellFieldInverse G v q a b 0 (fun t z => f t (z par.rev)) c := by
  let fc := fun t x => f (Set.projIcc a b hab t) x
  obtain ⟨c, hc⟩ := finite_profile_field_inverse_exists G hG v hv V hb par ht fc a b hab q hq C hC
    hfm
    (fun l t hti => by
      simpa only [fc, Set.projIcc_of_mem hab hti] using hf l t hti)
    (fun l t => hp l (Set.projIcc a b hab t) (Set.projIcc a b hab t).2)
    (fun l j hj' t hti x hx => by
      simpa only [fc, Set.projIcc_of_mem hab hti] using hj l j hj' t hti x hx)
    (fun l t hti => by
      simpa only [fc, Set.projIcc_of_mem hab hti] using hcenter l t hti)
  refine ⟨c, ?_⟩
  exact cellFieldInverse_source_congr_on G v q a b 0
    (fun t z => fc t (z par.rev)) (fun t z => f t (z par.rev)) c
    (fun t hti => by funext z; simp only [fc, Set.projIcc_of_mem hab hti]) hc
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! The explicit finite-coordinate response solves the original lift setting cell equation. -/

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
theorem setting_profile_response_inverse
    (q : ℕ) (hq : 2 ≤ q) (X : Vec 2) (f : ℝ → ℝ → Wspace)
    (C : (Wspace →L[ℝ] ℝ) → ℕ → ℝ) (hC : ∀ l j, j ≤ q → 0 ≤ C l j)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ,
      Measurable (fun p : ℝ × ℝ => ((l (f (Set.projIcc a b P.window p.1) p.2) : ℝ) : ℂ)))
    (hf : ∀ l : Wspace →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      ContDiff ℝ q (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ l : Wspace →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ l : Wspace →L[ℝ] ℝ, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C l j)
    (hcenter : ∀ l : Wspace →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      unitProfileFourierCoeff (fun x => ((l (f t x) : ℝ) : ℂ)) 0 = 0) :
    IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
      (fun t z => f t (z par.rev))
      (fun t z => finiteProfileResponse
        (fun r => Q.G (Set.projIcc a b P.window r) X par.rev par.rev)
        (fun s x => f (Set.projIcc a b P.window s) x) a t (z par.rev)) := by
  let G := fun t => Matrix.of (Q.G t X)
  let G' := fun t => G (Set.projIcc a b P.window t)
  let v' := localCellDrift a b P.window Q.v
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have hm := localCellDrift_measurable a b P.window Q.v (setting_drift_continuous P) P.v_meas
  have hb t z : (∑ i, v' t z i ^ 2) ≤ W ^ 2 := hW _ (Set.projIcc a b P.window t).2 z
  have ht t z : v' t z par.rev = 0 := setting_transverse_drift_zero P _ z
  have hc := finite_profile_window_response_inverse G' (setting_cell_metric P X) v' hm W hb
    par ht f a b P.window q hq C hC hfm hf hp hj hcenter
  apply cellFieldInverse_coefficients_congr_on G' G v' Q.v q a b 0
    (fun t z => f t (z par.rev)) _ _ _ hc
  · intro t hti
    simp only [G', Set.projIcc_of_mem P.window hti]
  · intro t hti
    exact localCellDrift_eq a b P.window Q.v t hti
end

/-! The original lift setting constructs a genuine finite-past inverse for every admissible finite-coordinate profile source. -/

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
theorem setting_profile_field_inverse_exists
    (q : ℕ) (hq : 2 ≤ q) (X : Vec 2) (f : ℝ → ℝ → Wspace)
    (C : (Wspace →L[ℝ] ℝ) → ℕ → ℝ) (hC : ∀ l j, j ≤ q → 0 ≤ C l j)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ,
      Measurable (fun p : ℝ × ℝ => ((l (f (Set.projIcc a b P.window p.1) p.2) : ℝ) : ℂ)))
    (hf : ∀ l : Wspace →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      ContDiff ℝ q (fun x => ((l (f t x) : ℝ) : ℂ)))
    (hp : ∀ l : Wspace →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      Function.Periodic (fun x => ((l (f t x) : ℝ) : ℂ)) 1)
    (hj : ∀ l : Wspace →L[ℝ] ℝ, ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ x ∈ Icc (0 : ℝ) 1,
      ‖iteratedDeriv j (fun y => ((l (f t y) : ℝ) : ℂ)) x‖ ≤ C l j)
    (hcenter : ∀ l : Wspace →L[ℝ] ℝ, ∀ t ∈ Icc a b,
      unitProfileFourierCoeff (fun x => ((l (f t x) : ℝ) : ℂ)) 0 = 0) :
    ∃ c : ℝ → Vec 2 → Wspace,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
        (fun t z => f t (z par.rev)) c := by
  let G := fun t => Matrix.of (Q.G t X)
  let G' := fun t => G (Set.projIcc a b P.window t)
  let v' := localCellDrift a b P.window Q.v
  obtain ⟨W, hW⟩ := setting_drift_bound P
  have hm := localCellDrift_measurable a b P.window Q.v (setting_drift_continuous P) P.v_meas
  have hb t z : (∑ i, v' t z i ^ 2) ≤ W ^ 2 := hW _ (Set.projIcc a b P.window t).2 z
  have ht t z : v' t z par.rev = 0 := setting_transverse_drift_zero P _ z
  obtain ⟨c, hc⟩ := finite_profile_window_inverse_exists G' (setting_cell_metric P X) v' hm W hb
    par ht f a b P.window q hq C hC hfm hf hp hj hcenter
  refine ⟨c, ?_⟩
  apply cellFieldInverse_coefficients_congr_on G' G v' Q.v q a b 0
    (fun t z => f t (z par.rev)) c _ _ hc
  · intro t hti
    simp only [G', Set.projIcc_of_mem P.window hti]
  · intro t hti
    exact localCellDrift_eq a b P.window Q.v t hti
end

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleComparison.Lift

/-! The original reserve closes the actual centered paired source using earlier difference states. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V 0 N K k L qs qf CG Cw Cj edge Θ)

include P in
theorem setting_ambient_centered_paired_grading_of_earlier_states
    (Cc Ci : ℕ → ℕ → LiftCoeff ι h) (P₀ n : ℕ)
    (hreserve : P₀ + (N + D) ≤ qs) (hn : 1 ≤ n) (hnR : n ≤ N + D)
    (g : ℝ) (hg : 0 ≤ g) (CGI : ℕ → ℝ)
    (hGI : ∀ r, r ≤ qs →
      (⨆ t ∈ Set.Icc a b, ⨆ X : Vec 2,
        ‖iteratedFDeriv ℝ r (fun Y => fun i j : Fin 2 =>
          Q.G t Y i j - (if i = j then 1 else 0)) X‖ₑ) ≤
        ENNReal.ofReal (CGI r * g * lam ^ r))
    (Bd : ℕ → ℝ) (hBd : ∀ m, 0 ≤ Bd m)
    (native : ∀ m ≤ N + D, AmbientScalarPowerRecurrenceData par a b P.window lam
      P₀ (max k (L + 2)) (N + D) N 0 0 m CG Cw Cj Q Cc (physicalEdgeEnvelopeMatrix π edge))
    (nativei : ∀ m ≤ N + D, AmbientScalarPowerRecurrenceData par a b P.window lam
      P₀ (max k (L + 2)) (N + D) N 0 0 m (identityMetricJetBudget CG) Cw Cj
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      Ci (physicalEdgeEnvelopeMatrix π edge))
    (prior : ∀ m < n, AmbientLiftCoefficientData par a b P.window lam m
      (ambientDegreeSlowReserve P₀ (N + D) m)
      (ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m)
      (fun d α t X z v u => Cc 0 m d α t X z v u - Ci 0 m d α t X z v u)
      (fun v u => (Bd m * (if v = u then 1 else 0)) * g))
    (priorU : ∀ m, 1 ≤ m → m < n → ∀ A u v ξ,
      ∀ r ≤ ambientDegreeSlowReserve P₀ (N + D) m,
      ∀ s ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 m,
      ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftUncenteredField Q Cc 0 m (lam • A) u v ξ t Y y -
        normalizedLiftUncenteredField
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci 0 m (lam • A) u v ξ t Y y) z) X‖ ≤
        (pairedAmbientUncenteredBudget P₀ (max k (L + 2)) D (N + D) m CG Cw CGI
          (fun j => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D 0 (N + D) N 0 j
            (identityMetricJetBudget CG) Cw Cj) Bd A * (if v = u then 1 else 0) * ‖ξ‖) *
          g * lam ^ (m + r)) :
    let Bi := fun m => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D 0 (N + D) N 0 m
      (identityMetricJetBudget CG) Cw Cj
    let KM := fun m => ambientUncenteredBudget P₀ (max k (L + 2)) D 0 (N + D) 0 m CG Cw Cj
      (fun h j => ambientCoefficientScalarBudget P₀ (max k (L + 2)) D 0 (N + D) N h j CG Cw Cj)
    ∀ A u v ξ, ∀ r ≤ ambientDegreeSlowReserve P₀ (N + D) n,
      ∀ s ≤ ambientDegreeFastReserve (max k (L + 2)) D 0 (N + D) 0 n,
      ∀ t ∈ Set.Icc a b, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (fun y =>
        normalizedLiftSourceField Q Cc 0 n (lam • A) u v ξ t Y y -
        normalizedLiftSourceField
          (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
          Ci 0 n (lam • A) u v ξ t Y y) z) X‖ ≤
        (pairedAmbientCenteredBudget P₀ (max k (L + 2)) D (N + D) n CG Cw CGI Bi Bd KM A *
          (if v = u then 1 else 0) * ‖ξ‖) * g * lam ^ (n + r) := by
  let R := N + D
  let Q₀ := max k (L + 2)
  let p := ambientDegreeSlowReserve P₀ R n
  let q := ambientDegreeFastReserve Q₀ D 0 R 0 n
  let B₀ := fun m => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N 0 m CG Cw Cj
  let Bi := fun m => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N 0 m (identityMetricJetBudget CG) Cw Cj
  let KM := fun m => ambientUncenteredBudget P₀ Q₀ D 0 R 0 m CG Cw Cj
    (fun h j => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N h j CG Cw Cj)
  let KMi := fun m => ambientUncenteredBudget P₀ Q₀ D 0 R 0 m (identityMetricJetBudget CG) Cw Cj
    (fun h j => ambientCoefficientScalarBudget P₀ Q₀ D 0 R N h j (identityMetricJetBudget CG) Cw Cj)
  let Kd := fun m => pairedAmbientUncenteredBudget P₀ Q₀ D R m CG Cw CGI Bi Bd
  have hBi m : 0 ≤ Bi m := ambientCoefficientScalarBudget_nonneg _ _ _ _ _ _ _ _ _ _ _
  have hKd m A : 0 ≤ Kd m A := pairedAmbientUncenteredBudget_nonneg _ _ _ _ _ _ _ _ _ _ hBi hBd A
  have coeff m (hm : m ≤ R) : AmbientLiftCoefficientData par a b P.window lam m
      (ambientDegreeSlowReserve P₀ R m) (ambientDegreeFastReserve Q₀ D 0 R 0 m)
      (Cc 0 m) (fun v u => B₀ m * (if v = u then 1 else 0)) := by
    simpa only [B₀, finiteMatrixPower_zero] using (native m hm).coefficient
  have coeffi m (hm : m ≤ R) : AmbientLiftCoefficientData par a b P.window lam m
      (ambientDegreeSlowReserve P₀ R m) (ambientDegreeFastReserve Q₀ D 0 R 0 m)
      (Ci 0 m) (fun v u => Bi m * (if v = u then 1 else 0)) := by
    simpa only [Bi, finiteMatrixPower_zero] using (nativei m hm).coefficient
  have unc m (hm : 1 ≤ m) (hmR : m ≤ R) : AmbientLiftUncenteredData par a b P.window lam 0 m
      (ambientDegreeSlowReserve P₀ R m) (ambientDegreeFastReserve Q₀ D 0 R 0 m)
      Q Cc (KM m) (fun v u => if v = u then 1 else 0) := by
    simpa only [KM, finiteMatrixPower_zero] using (native m hmR).uncentered hm
  have unci m (hm : 1 ≤ m) (hmR : m ≤ R) : AmbientLiftUncenteredData par a b P.window lam 0 m
      (ambientDegreeSlowReserve P₀ R m) (ambientDegreeFastReserve Q₀ D 0 R 0 m)
      (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
      Ci (KMi m) (fun v u => if v = u then 1 else 0) := by
    simpa only [KMi, finiteMatrixPower_zero] using (nativei m hmR).uncentered hm
  have current := setting_ambient_uncentered_paired_grading_of_predecessors P Cc Ci P₀ n
    hreserve hn hnR g hg CGI hGI B₀ Bi Bd hBd
    (fun m hm => coeff m (by omega)) (fun m hm => coeffi m (by omega)) prior
  have slow j (hj : j ≤ n) : p + j = ambientDegreeSlowReserve P₀ R (n - j) :=
    ambientDegreeSlowReserve_source P₀ R n j hnR hj
  have fast m (hm : m ≤ n) : q ≤ ambientDegreeFastReserve Q₀ D 0 R 0 m :=
    ambientDegreeFastReserve_mono Q₀ D 0 R 0 0 n m le_rfl hm
  dsimp only
  intro A u v ξ r hr s hs t ht X z
  have result := ambient_ordered_centered_paired_grading par a b P.window lam g
    (by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le) hg n p q Q
    (⟨Q.η, fun _ _ i j => if i = j then 1 else 0, Q.v, Q.edge⟩ : LiftOperatorData ι h D)
    Cc Ci B₀ Bi Bd hBi hBd (KM n) (KMi n) (Kd n) (hKd n) KM KMi Kd hKd
    (unc n hn hnR) (unci n hn hnR)
    (fun A u v ξ r hr s hs t ht X z => (current A t ht v u ξ).2 r hr s hs X z)
    (fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      exact (coeff j (by omega)).mono
        (ambientDegreeSlowReserve_mono P₀ R n j (by omega)) (fast j (by omega)))
    (fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      exact (coeffi j (by omega)).mono
        (ambientDegreeSlowReserve_mono P₀ R n j (by omega)) (fast j (by omega)))
    (fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      exact (prior j (by omega)).mono
        (ambientDegreeSlowReserve_mono P₀ R n j (by omega)) (fast j (by omega)))
    (fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      exact (unc (n - j) (by omega) (by omega)).mono
        (le_of_eq (slow j (by omega))) (fast (n - j) (Nat.sub_le _ _)))
    (fun j hj => by
      have hj' := Finset.mem_Icc.mp hj
      exact (unci (n - j) (by omega) (by omega)).mono
        (le_of_eq (slow j (by omega))) (fast (n - j) (Nat.sub_le _ _)))
    (fun j hj A u v ξ r hr s hs t ht X z => by
      have hj' := Finset.mem_Icc.mp hj
      have hslow := hr.trans (le_of_eq (slow j (by omega)))
      exact priorU (n - j) (by omega) (by omega) A u v ξ r hslow s
        (hs.trans (fast (n - j) (Nat.sub_le _ _))) t ht X z)
    A u v ξ t ht
  exact (result.2 r hr s hs X z).trans_eq (by rfl)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The genuine recurrence source meets every inverse premise using only the actual earlier states. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D : ℕ}

theorem ambient_ordered_centered_source_data (par : Fin 2) (a b : ℝ) (hab : a ≤ b)
    (lam : ℝ) (hlam : 0 ≤ lam) (hh n p q sX sZ N H : ℕ)
    (Q : LiftOperatorData ι h D) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hhh : hh ≤ H) (hnN : n ≤ N)
    (F : ι → ι → ℝ) (hF : ∀ v u, 0 ≤ F v u) (B : ℕ → ℕ → ℝ)
    (hB : ∀ h m, 0 ≤ B h m) (K : (Vec 2 →L[ℝ] ℝ) → ℝ)
    (KM : ℕ → ℕ → (Vec 2 →L[ℝ] ℝ) → ℝ)
    (uncentered : AmbientLiftUncenteredData par a b hab lam hh n p q Q Cc K (finiteMatrixPower F hh))
    (coef : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      AmbientLiftCoefficientData par a b hab lam j p q (Cc ab.1 j)
        (fun v u => B ab.1 j * finiteMatrixPower F ab.1 v u))
    (mean : ∀ j ∈ Finset.Icc 1 (n - 2), ∀ ab ∈ Finset.HasAntidiagonal.antidiagonal hh,
      AmbientLiftUncenteredData par a b hab lam ab.2 (n - j) (p + j) q Q Cc
        (KM ab.2 (n - j)) (finiteMatrixPower F ab.2)) :
    AmbientLiftSourceData par a b hab lam hh n p q Q Cc
      (orderedCenteredScalarConstant hh n p q B K KM) (finiteMatrixPower F hh) := by
  have hg := ambient_ordered_centered_power_grading par a b hab lam hlam hh n p q Q Cc F hF
    B hB K KM uncentered coef mean
  refine ⟨?_, finiteMatrixPower_nonneg F hF hh, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro A
    exact orderedCenteredScalarConstant_nonneg hh n p q B K KM A hB
      (uncentered.constant_nonneg A) (fun j hj ab hab' => (mean j hj ab hab').constant_nonneg A)
  · intro A u v ξ t ht
    exact (hg A u v ξ t ht).1
  · intro A u v ξ r hr s hs t ht X z
    exact (hg A u v ξ t ht).2 r hr s hs X z
  · intro A u v ξ
    apply liftCellSource_normalized_transverse_of_terms par (Set.Icc a b) Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n v A lam
      (uncentered.transverse A u v ξ)
    intro j hj ab hab'
    have ht := liftApply_transverse par (Set.Icc a b) j (Cc ab.1 j)
      (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) ab.2 (n - j))
      (coef j hj ab hab').transverse
    intro t ht' X z s
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (ht t ht' X z s)
  · intro A u v ξ l X z
    apply liftCellSource_normalized_clamped_dual_measurable_of_terms Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n a b hab v l A lam X z
      (uncentered.measurable A u v ξ l X z)
      (l.continuous.measurable.comp (uncentered.mean_component_measurable A u v ξ X))
    intro j hj ab hab'
    exact ambient_ordered_mean_clamped_dual_measurable par a b hab lam hlam j (n - j)
      p q (p + j) q ab.2 (by omega) Q Cc (Cc ab.1 j) _ _ (KM ab.2 (n - j))
      (coef j hj ab hab') (mean j hj ab hab') A u v ξ l X z
  · intro A u v ξ t ht
    apply liftCellSource_normalized_periodic_of_terms Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n t v A lam
      (uncentered.periodic A u v ξ t ht)
    intro j hj ab hab' X k z
    have he := Finset.HasAntidiagonal.mem_antidiagonal.mp hab'
    have hp := liftApply_periodic Q sX sZ a b N H Cc hseq ab.1 (by omega) j
      (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) ab.2 (n - j)) t ht X
    exact congrArg (fun x : ∀ i, h i => (Real.exp ((lam • A) X))⁻¹ • x v) (hp k z)
  · intro A u v ξ t ht X
    unfold normalizedLiftSourceField
    rw [AVRegularity.fieldCellMean_smul]
    rw [liftCellSource_component_mean_zero Q sX sZ a b N H Cc hseq hh n hhh hnN
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t ht X v
      (liftA_fast_continuous_of_normalized_box Q Cc _ hh n p q t A lam
        (fun w => uncentered.box A u w ξ t ht) X)]
    exact smul_zero _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution
namespace AVRegularity.CycleComparison.Lift

/-! Actual bounded transverse cell sources possess a finite-past inverse in the original setting. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
  {Wspace : Type*} [NormedAddCommGroup Wspace] [NormedSpace ℝ Wspace]
  [FiniteDimensional ℝ Wspace] [CompleteSpace Wspace]

include P in
theorem setting_transverse_field_inverse_exists
    (q : ℕ) (hq : 2 ≤ q) (f : ℝ → Vec 2 → Vec 2 → Wspace)
    (hf : ∀ t ∈ Icc a b, IsBoxSmooth 0 q (f t))
    (hft : IsTransverseOn par (Icc a b) f)
    (hfm : ∀ l : Wspace →L[ℝ] ℝ, ∀ X z, Measurable (fun t => l (f t X z)))
    (hper : ∀ t ∈ Icc a b, ∀ X, ∀ n : Fin 2 → ℤ, ∀ z,
      f t X (z + AVenhance.Infra.Torus.intVector n) = f t X z)
    (hcenter : ∀ t ∈ Icc a b, ∀ X, fieldCellMean (f t X) = 0)
    (S : ℕ → ℝ) (hS : ∀ j ≤ q, 0 ≤ S j)
    (hb : ∀ j ≤ q, ∀ t ∈ Icc a b, ∀ X z, ‖iteratedFDeriv ℝ j (f t X) z‖ ≤ S j)
    (X : Vec 2) :
    ∃ c : ℝ → Vec 2 → Wspace,
      IsCellFieldInverse (fun t => Matrix.of (Q.G t X)) Q.v q a b 0
        (fun t z => f t X z) c := by
  let F : ℝ → ℝ → Wspace := fun t x => f t X (x • basisVec par.rev)
  obtain ⟨c, hc⟩ := setting_profile_field_inverse_exists P q hq X F
    (fun l j => S j * ‖l‖) (fun l j hj => mul_nonneg (hS j hj) (norm_nonneg l))
    (fun l => clamped_linear_profile_joint_measurable 0 q a b P.window par.rev f hf hfm l X)
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
  refine ⟨c, cellFieldInverse_source_congr_on _ Q.v q a b 0
    (fun t z => F t (z par.rev)) (fun t z => f t X z) c ?_ hc⟩
  intro t ht
  funext z
  exact (transverse_profile_representation par (Icc a b) f hft t ht X z).symm

end AVRegularity.CycleComparison.Lift
end
