-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovTruncGluedSlow
public import AVRegularity.Construction.KernelDefect.UniformDefect
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
import AVRegularity.CycleComparison.Reconstruction.PartitionBound

/-! **The defect of the derivative array, with a constant uniform in the kernel order.**

The term bound of the defect flux of the fine tail and of the coarse filter tails has the moment
constant `kdMomentConst φ₀ n L Γ` of the order `n` of its kernel. Here the bound is proved with
the constant of any order `n₀ ≤ S.order` that has `L + 1 ≤ 2n₀`
(`fd_derivFactorialNormSq_le_of_order_le`), hence, for kernels of arbitrary admissible orders,
with the one constant `kdUniformMomentConst φ₀ L Γ` (`fd_derivFactorialNormSq_le_uniform`). The
proof uses `kdRealization_jet_le_of_order_le` in place of `kdRealization_jet_le`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.Construction.KernelDefect

namespace AVRegularity.EntryTerminal.Ingredients.ResidualFlux

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- **The jet bound of the defect of the derivative array, with the constant of a lower order.**
For a kernel of any order `S.order ≥ n₀`, `L + 1 ≤ 2n₀`. -/
theorem fd_derivFactorialNormSq_le_of_order_le {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (L : ℕ) (n₀ : ℕ+) (Γ : ℝ)
    (S : KernelSpec) (t ρ : ℝ) (hn : n₀ ≤ S.order) (hL : L + 1 ≤ 2 * (n₀ : ℕ))
    (hr : 0 < S.width) (hρ : 0 < ρ) (h1 : ‖S.H₁ t‖ ≤ Γ) (h2 : ‖S.H₂ t‖ ≤ Γ)
    (k m K : ℕ) (hK : k + m + L ≤ K) (V : TorusHk (K + 1) E) (a : Vec 2 → E)
    (hV : IsClassicalRep V a (K + 1)) :
    derivFactorialNormSq (m + 1) ρ
        (kdRealization φ₀ hφ S t
          (truncateTorusHk (by omega : (k + (m + 1)) + L ≤ K + 1) V)).val ≤
      (kdMomentConst φ₀ n₀ L Γ * (((k + (L + m)).factorial : ℝ) / k.factorial) *
          (S.width / ρ) ^ L * (ρ⁻¹) ^ m) ^ 2 * gradFactorialNormSq ρ V.val := by
  have hKL : (k + (m + 1)) + L ≤ K + 1 := by omega
  set u := truncateTorusHk hKL V with hu
  have hrep : IsClassicalRep u a ((k + (m + 1)) + L) :=
    Construction.Preservation.FullLift.classicalRep_truncate hKL le_rfl V a
      (CycleComparison.Reconstruction.isClassicalRep_of_le hV hKL)
  set c0 := kdMomentConst φ₀ n₀ L Γ with hc0
  set Q : ℝ := (((k + (L + m)).factorial : ℝ) / k.factorial) with hQ
  set r := S.width with hrdef
  unfold derivFactorialNormSq
  calc ∑ i : Fin (k + 1), factorialWeight ρ i.val *
        ∑ w : DerivativeWord2 (i.val + (m + 1)),
          ‖(kdRealization φ₀ hφ S t u).val ⟨⟨i.val + (m + 1), by omega⟩, w⟩‖ ^ 2
      ≤ ∑ i : Fin (k + 1), factorialWeight ρ i.val *
          ((c0 * r ^ L) ^ 2 * derivativeNormSq u.val
            ⟨i.val + (m + 1) + L, by omega⟩) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (factorialWeight_nonneg _ _)
        have := kdRealization_jet_le_of_order_le hφ hd hnonneg hmass hsupp L n₀ Γ S t hn hL hr
          h1 h2 u a hrep
          (j := i.val + (m + 1)) (by omega)
        exact this
    _ ≤ ∑ i : Fin (k + 1), (c0 * Q * (r / ρ) ^ L * (ρ⁻¹) ^ m) ^ 2 *
          (factorialWeight ρ (i.val + (L + m)) *
            derivativeNormSq V.val ⟨i.val + (L + m) + 1, by omega⟩) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have hw := fd_weight_shift hρ hr m L (Nat.lt_succ_iff.mp i.isLt)
        have hD := derivativeNormSq_nonneg V.val ⟨i.val + (L + m) + 1, by omega⟩
        have hidx : derivativeNormSq u.val ⟨i.val + (m + 1) + L, by omega⟩ =
            derivativeNormSq V.val ⟨i.val + (L + m) + 1, by omega⟩ := by
          have : (⟨i.val + (m + 1) + L, by omega⟩ : Fin (K + 1 + 1)) =
              ⟨i.val + (L + m) + 1, by omega⟩ :=
            Fin.ext (by show i.val + (m + 1) + L = i.val + (L + m) + 1; omega)
          have hE : derivativeNormSq u.val ⟨i.val + (m + 1) + L, by omega⟩ =
              derivativeNormSq V.val ⟨i.val + (m + 1) + L, by omega⟩ := rfl
          rw [hE]
          exact congrArg (derivativeNormSq V.val) this
        rw [hidx]
        have e : (c0 * r ^ L) ^ 2 = c0 ^ 2 * r ^ (2 * L) := by
          rw [mul_pow, ← pow_mul, mul_comm L 2]
        have e2 : (c0 * Q * (r / ρ) ^ L * (ρ⁻¹) ^ m) ^ 2 =
            c0 ^ 2 * (Q ^ 2 * (r / ρ) ^ (2 * L) * (ρ⁻¹) ^ (2 * m)) := by
          rw [mul_pow, mul_pow, mul_pow, ← pow_mul, ← pow_mul, mul_comm L 2, mul_comm m 2]
          ring
        calc _ = c0 ^ 2 * ((factorialWeight ρ i.val * r ^ (2 * L)) *
              derivativeNormSq V.val ⟨i.val + (L + m) + 1, by omega⟩) := by rw [e]; ring
          _ ≤ c0 ^ 2 * ((Q ^ 2 * (r / ρ) ^ (2 * L) * (ρ⁻¹) ^ (2 * m) *
                factorialWeight ρ (i.val + (L + m))) *
              derivativeNormSq V.val ⟨i.val + (L + m) + 1, by omega⟩) := by
              refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hw hD) (sq_nonneg _)
          _ = _ := by rw [e2]; ring
    _ = (c0 * Q * (r / ρ) ^ L * (ρ⁻¹) ^ m) ^ 2 * ∑ i : Fin (k + 1),
          factorialWeight ρ (i.val + (L + m)) *
            derivativeNormSq V.val ⟨i.val + (L + m) + 1, by omega⟩ := by rw [Finset.mul_sum]
    _ ≤ _ := by
        refine mul_le_mul_of_nonneg_left ?_ (sq_nonneg _)
        unfold gradFactorialNormSq
        let g : Fin (k + 1) → Fin (K + 1) := fun i => ⟨i.val + (L + m), by omega⟩
        have hg : Function.Injective g := fun x y h => by
          apply Fin.ext
          have := congrArg Fin.val h
          simp only [g] at this
          omega
        have := Finset.sum_image (s := (Finset.univ : Finset (Fin (k + 1))))
          (f := fun j : Fin (K + 1) => factorialWeight ρ j.val *
            ∑ w : DerivativeWord2 (j.val + 1), ‖V.val ⟨⟨j.val + 1, Nat.succ_lt_succ j.isLt⟩, w⟩‖ ^ 2)
          (g := g) (fun x _ y _ h => hg h)
        refine le_trans (le_of_eq ?_) (le_trans (le_of_eq this.symm.symm.symm) ?_)
        · exact rfl
        · exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
            (fun m _ _ => mul_nonneg (factorialWeight_nonneg _ _)
              (Finset.sum_nonneg fun _ _ => sq_nonneg _))

/-- **The jet bound of the defect of the derivative array, uniform in the order.** The constant
`kdUniformMomentConst φ₀ L Γ` depends on the profile, `L` and `Γ` only. -/
theorem fd_derivFactorialNormSq_le_uniform {φ₀ : Vec 2 → ℝ} (hφ : Integrable φ₀)
    (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀) (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : Function.support φ₀ ⊆ closedEuclideanUnitBall) (L : ℕ) (Γ : ℝ)
    (S : KernelSpec) (t ρ : ℝ) (hL : L + 1 ≤ 2 * (S.order : ℕ))
    (hr : 0 < S.width) (hρ : 0 < ρ) (h1 : ‖S.H₁ t‖ ≤ Γ) (h2 : ‖S.H₂ t‖ ≤ Γ)
    (k m K : ℕ) (hK : k + m + L ≤ K) (V : TorusHk (K + 1) E) (a : Vec 2 → E)
    (hV : IsClassicalRep V a (K + 1)) :
    derivFactorialNormSq (m + 1) ρ
        (kdRealization φ₀ hφ S t
          (truncateTorusHk (by omega : (k + (m + 1)) + L ≤ K + 1) V)).val ≤
      (kdUniformMomentConst φ₀ L Γ * (((k + (L + m)).factorial : ℝ) / k.factorial) *
          (S.width / ρ) ^ L * (ρ⁻¹) ^ m) ^ 2 * gradFactorialNormSq ρ V.val :=
  fd_derivFactorialNormSq_le_of_order_le hφ hd hnonneg hmass hsupp L (kdUniformOrder L) Γ S t ρ
    (kdUniformOrder_le hL) (kdUniformOrder_spec L) hr hρ h1 h2 k m K hK V a hV

end AVRegularity.EntryTerminal.Ingredients.ResidualFlux
