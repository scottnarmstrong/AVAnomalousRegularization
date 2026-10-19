-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Lift.NormalizedCellB1ScaledDriftMixedGrading
import AVRegularity.Construction.InitialLayer.Comparison
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Finite suborder sums give common normalized cross-operator constants. -/

def normalizedCellB1UniformConstant (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M W : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    normalizedCellB1MixedConstant r s A M W 1

def normalizedCellB2UniformConstant (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M : ℝ) : ℝ :=
  ∑ r ∈ Finset.range (p + 1), ∑ s ∈ Finset.range (q + 1),
    normalizedCellB2MixedConstant r s A M 1

theorem normalizedCellB1MixedConstant_factor (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M W C : ℝ) :
    normalizedCellB1MixedConstant p q A M W C =
      normalizedCellB1MixedConstant p q A M W 1 * C := by
  unfold normalizedCellB1MixedConstant
  ring

theorem normalizedCellB2MixedConstant_factor (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M C : ℝ) :
    normalizedCellB2MixedConstant p q A M C =
      normalizedCellB2MixedConstant p q A M 1 * C := by
  unfold normalizedCellB2MixedConstant
  ring

theorem normalizedCellB1MixedConstant_nonneg (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M W : ℝ)
    (hM : 0 ≤ M) (hW : 0 ≤ W) : 0 ≤ normalizedCellB1MixedConstant p q A M W 1 := by
  unfold normalizedCellB1MixedConstant
  positivity

theorem normalizedCellB2MixedConstant_nonneg (p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) (M : ℝ)
    (hM : 0 ≤ M) : 0 ≤ normalizedCellB2MixedConstant p q A M 1 := by
  unfold normalizedCellB2MixedConstant
  positivity

theorem normalizedCellB1MixedConstant_le_uniform (p q r s : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (A : Vec 2 →L[ℝ] ℝ) (M W : ℝ) (hM : 0 ≤ M) (hW : 0 ≤ W) :
    normalizedCellB1MixedConstant r s A M W 1 ≤ normalizedCellB1UniformConstant p q A M W := by
  apply (Finset.single_le_sum (fun s _ => normalizedCellB1MixedConstant_nonneg r s A M W hM hW)
    (show s ∈ Finset.range (q + 1) by simp only [Finset.mem_range]; omega)).trans
  exact Finset.single_le_sum (fun r _ => Finset.sum_nonneg fun s _ =>
    normalizedCellB1MixedConstant_nonneg r s A M W hM hW)
    (show r ∈ Finset.range (p + 1) by simp only [Finset.mem_range]; omega)

theorem normalizedCellB2MixedConstant_le_uniform (p q r s : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (A : Vec 2 →L[ℝ] ℝ) (M : ℝ) (hM : 0 ≤ M) :
    normalizedCellB2MixedConstant r s A M 1 ≤ normalizedCellB2UniformConstant p q A M := by
  apply (Finset.single_le_sum (fun s _ => normalizedCellB2MixedConstant_nonneg r s A M hM)
    (show s ∈ Finset.range (q + 1) by simp only [Finset.mem_range]; omega)).trans
  exact Finset.single_le_sum (fun r _ => Finset.sum_nonneg fun s _ =>
    normalizedCellB2MixedConstant_nonneg r s A M hM)
    (show r ∈ Finset.range (p + 1) by simp only [Finset.mem_range]; omega)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Normalized exponential tests retain exactly the common left-coefficient box reserve. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem normalized_lift_test_box_reserve (n p q : ℕ) (c : LiftCoeff ι h)
    (lam : ℝ) (A : Vec 2 →L[ℝ] ℝ) (t : ℝ) (v u : ι) (ξ : h u)
    (hf : ∀ m ≤ n, ∀ α : DerivativeWord2 m,
      IsBoxSmooth p q (fun X z => c m α t X z v u)) :
    IsBoxSmooth p q (fun X z => (Real.exp ((lam • A) X))⁻¹ •
      liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t X z v) := by
  have he (X z : Vec 2) := normalized_exponential_lift_polynomial n c A t X z v u ξ lam
  simp_rw [he]
  apply IsBoxSmooth.sum
  intro m hm
  apply IsBoxSmooth.const_smul
  apply IsBoxSmooth.sum
  intro α _
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  exact ((hf m hmn α).clm_comp (ContinuousLinearMap.apply ℝ (h v) ξ)).const_smul _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Fixed component maps transport the actual weak inverse through its scalar-dual equations. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem cellJetOfField_postcomposition_at (L : E →L[ℝ] F) (l : F →L[ℝ] ℝ)
    (c : ℝ → Vec 2 → E) (t : ℝ) (hd : Differentiable ℝ (c t)) :
    cellJetOfField l (fun s z => L (c s z)) t = cellJetOfField (l.comp L) c t := by
  funext α x
  have hder : fderiv ℝ (fun y => L (c t y)) x = L.comp (fderiv ℝ (c t) x) :=
    (L.hasFDerivAt.comp x (hd x).hasFDerivAt).fderiv
  unfold cellJetOfField
  split_ifs <;> simp only [hder, ContinuousLinearMap.comp_apply]

variable [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]

theorem cellFieldInverse_postcomposition (L : E →L[ℝ] F)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (hsZ : 1 ≤ sZ) (a b : ℝ)
    (c0 : Vec 2 → E) (g c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse G v sZ a b c0 g c) :
    IsCellFieldInverse G v sZ a b (fun z => L (c0 z))
      (fun t z => L (g t z)) (fun t z => L (c t z)) := by
  have hsZ0 : ((sZ : ℕ∞) : WithTop ℕ∞) ≠ 0 := by
    exact_mod_cast (Nat.one_le_iff_ne_zero.mp hsZ)
  refine ⟨fun t ht => L.contDiff.comp (hc.1 t ht), ?_⟩
  intro l
  have he (t : ℝ) (ht : t ∈ Set.Icc a b) : cellJetOfField (l.comp L) c t =
      cellJetOfField l (fun s z => L (c s z)) t :=
    (cellJetOfField_postcomposition_at L l c t ((hc.1 t ht).differentiable hsZ0)).symm
  obtain ⟨S, M, J, B⟩ := hc.2 (l.comp L)
  refine ⟨AVRegularity.InitialLayer.cellSolution_congr_jet measurableSet_Icc he S, ?_, ?_, ?_⟩
  · intro t ht
    change cellMean (fun x => ((l (L (c t x)) : ℝ) : ℂ)) = 0
    exact M t ht
  · change (fun x => ((l (L (c a x)) : ℝ) : ℂ)) =ᵐ[volume.restrict AVenhance.unitCube]
      (fun x => ((l (L (c0 x)) : ℝ) : ℂ))
    exact J
  · rw [← AVRegularity.InitialLayer.cellEnergyNorm_congr_jet measurableSet_Icc he]
    exact B

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Tested lift composition adds cell grades and preserves the exact ordered slow derivative budget. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_slow_input_mixed_grading (n p q δ : ℕ) (c : LiftCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι)
    (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth p q (fun Y y => c m α t Y y v u))
    (lam : ℝ) (hlam : 0 ≤ lam) (B C : ι → ℝ)
    (hB : ∀ u, 0 ≤ B u) (hC : ∀ u, 0 ≤ C u)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun w => c m α t Y w v u) y) X‖ ≤ B u * lam ^ (n - m + a))
    (hbg : ∀ u, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y u) X‖ ≤ C u * lam ^ (δ + a)) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => liftApply n c (fun _ => g) t Y y v) z) X‖ ≤
      ∑ m ∈ Finset.range (n + 1), ∑ _α : DerivativeWord2 m, ∑ u,
        (2 ^ (p + 2 * q) * B u * C u) * lam ^ (n + δ + p) := by
  let T := fun m (α : DerivativeWord2 m) u Y y =>
    c m α t Y y v u (orderedDerivative α g Y u)
  have hT m (hm : m ≤ n) α u : IsBoxSmooth p q (T m α u) := by
    exact isBoxSmooth_bilinear (hc m hm α u)
      (isBoxSmooth_slow_field p q _ (AVRegularity.contDiff_orderedDerivative_comp hm α hg u))
      (ContinuousLinearMap.id ℝ (h u →L[ℝ] h v))
  have hbound m (hm : m ≤ n) α u :
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (T m α u Y) z) X‖ ≤
        (2 ^ (p + 2 * q) * B u * C u) * lam ^ (n + δ + p) := by
    have hgm : ContDiff ℝ ((p + m : ℕ) : ℕ∞) g :=
      hg.of_le (by exact_mod_cast Nat.add_le_add_left hm p)
    have he := AVRegularity.orderedDerivative_clm_comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) u) α
      (hgm.of_le (by exact_mod_cast Nat.le_add_left m p))
    have hh := norm_mixed_operator_ordered_input_graded_le p q n m δ hm α
      (fun Y y => c m α t Y y v u) (fun Y => g Y u) (hc m hm α u)
      ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp hgm) X z lam (B u) (C u)
      hlam (hB u) (hC u) (hbc m hm α u) (fun a ha => hbg u a (by omega))
    have he' (Y : Vec 2) : orderedDerivative α (fun Y => g Y u) Y = orderedDerivative α g Y u :=
      congrFun he Y
    simpa only [he', T] using hh
  have hsum m (hm : m ≤ n) α : IsBoxSmooth p q (fun Y y => ∑ u, T m α u Y y) :=
    IsBoxSmooth.sum Finset.univ (fun u _ => hT m hm α u)
  have hsum' m (hm : m ≤ n) : IsBoxSmooth p q
      (fun Y y => ∑ α : DerivativeWord2 m, ∑ u, T m α u Y y) :=
    IsBoxSmooth.sum Finset.univ (fun α _ => hsum m hm α)
  simp only [liftApply]
  apply (norm_mixed_jet_finset_sum_le (Finset.range (n + 1)) p q
    (fun m Y y => ∑ α : DerivativeWord2 m, ∑ u, T m α u Y y)
    (fun m hm => hsum' m (by have he := Finset.mem_range.mp hm; omega)) X z).trans
  apply Finset.sum_le_sum
  intro m hm
  have hmn : m ≤ n := by have he := Finset.mem_range.mp hm; omega
  apply (norm_mixed_jet_finset_sum_le Finset.univ p q
    (fun α Y y => ∑ u, T m α u Y y) (fun α _ => hsum m hmn α) X z).trans
  apply Finset.sum_le_sum
  intro α _
  apply (norm_mixed_jet_finset_sum_le Finset.univ p q (T m α) (fun u _ => hT m hmn α u) X z).trans
  exact Finset.sum_le_sum fun u _ => hbound m hmn α u

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Every reserved suborder of the actual normalized cross operator has a common constant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedCellB2_uniform_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M C : ℝ)
    (hη0 : 0 ≤ η) (hη1 : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 2) q f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbf : ∀ a ≤ p + 2, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB2 η G t
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y) z) X‖ ≤
      (normalizedCellB2UniformConstant p q A M * C) * lam ^ ((δ + 2) + r) := by
  have hh := normalizedCellB2_mixed_grading_at_slow_point r s δ η lam M C
    hη0 hη1 hlam hM hC A G t f
    (hf.mono (by omega) (by omega))
    (fun i j => (hG i j).mono (by omega) hs)
     X
    (fun i j a ha b hb y => hbG i j a (by omega) b (hb.trans hs) y)
    
    (fun a ha b hb y => hbf a (by omega) b (by omega) y) z
  rw [normalizedCellB2MixedConstant_factor] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (normalizedCellB2MixedConstant_le_uniform p q r s hr hs A M hM) hC)
    (pow_nonneg hlam _))

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Cross diffusion constants keep one linear metric perturbation factor. -/

theorem normalizedCellB1MixedConstant_metric_mul (p q : ℕ) (A : Homogenization.Vec 2 →L[ℝ] ℝ)
    (M g C : ℝ) :
    normalizedCellB1MixedConstant p q A (M * g) 0 C =
      normalizedCellB1MixedConstant p q A M 0 C * g := by
  unfold normalizedCellB1MixedConstant
  ring

theorem normalizedCellB2MixedConstant_metric_mul (p q : ℕ) (A : Homogenization.Vec 2 →L[ℝ] ℝ)
    (M g C : ℝ) :
    normalizedCellB2MixedConstant p q A (M * g) C =
      normalizedCellB2MixedConstant p q A M C * g := by
  unfold normalizedCellB2MixedConstant
  ring

theorem normalizedCellB1UniformConstant_metric_mul (p q : ℕ) (A : Homogenization.Vec 2 →L[ℝ] ℝ)
    (M g : ℝ) :
    normalizedCellB1UniformConstant p q A (M * g) 0 =
      normalizedCellB1UniformConstant p q A M 0 * g := by
  unfold normalizedCellB1UniformConstant
  simp_rw [normalizedCellB1MixedConstant_metric_mul]
  simp only [Finset.sum_mul]

theorem normalizedCellB2UniformConstant_metric_mul (p q : ℕ) (A : Homogenization.Vec 2 →L[ℝ] ℝ)
    (M g : ℝ) :
    normalizedCellB2UniformConstant p q A (M * g) =
      normalizedCellB2UniformConstant p q A M * g := by
  unfold normalizedCellB2UniformConstant
  simp_rw [normalizedCellB2MixedConstant_metric_mul]
  simp only [Finset.sum_mul]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Left-coefficient grades combine into degree n on every normalized exponential coarse test. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def finiteLiftSymbolBudget (n : ℕ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
    |((List.ofFn α).map (fun k => A (basisVec k))).prod|

theorem finiteLiftSymbolBudget_nonneg (n : ℕ) (A : Vec 2 →L[ℝ] ℝ) :
    0 ≤ finiteLiftSymbolBudget n A :=
  Finset.sum_nonneg fun _m _ => Finset.sum_nonneg fun _α _ => abs_nonneg _

theorem normalized_lift_test_mixed_grading (n p q : ℕ) (c : LiftCoeff ι h)
    (lam B : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ)
    (t : ℝ) (v u : ι) (ξ : h u)
    (hf : ∀ m ≤ n, ∀ α : DerivativeWord2 m,
      IsBoxSmooth p q (fun X z => c m α t X z v u)) (X z : Vec 2)
    (hb : ∀ m ≤ n, ∀ α : DerivativeWord2 m,
      ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q (fun y => c m α t Y y v u) z) X‖ ≤
        B * lam ^ (n - m + p)) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ •
        liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • Pi.single u ξ) t Y y v) z) X‖ ≤
      (finiteLiftSymbolBudget n A * B) * lam ^ (n + p) * ‖ξ‖ := by
  simp_rw [normalized_exponential_lift_polynomial]
  have hinner (m : ℕ) (hm : m ∈ Finset.range (n + 1)) :
      IsBoxSmooth p q (fun Y y => ∑ α : DerivativeWord2 m,
        ((List.ofFn α).map (fun k => A (basisVec k))).prod • c m α t Y y v u ξ) := by
    apply IsBoxSmooth.sum
    intro α _
    exact ((hf m (by have hh := Finset.mem_range.mp hm; omega) α).clm_comp
      (ContinuousLinearMap.apply ℝ (h v) ξ)).const_smul _
  apply (norm_mixed_jet_finset_sum_le (Finset.range (n + 1)) p q _
    (fun m hm => (hinner m hm).const_smul _) X z).trans
  have he : (finiteLiftSymbolBudget n A * B) * lam ^ (n + p) * ‖ξ‖ =
      ∑ m ∈ Finset.range (n + 1), ∑ α : DerivativeWord2 m,
        |((List.ofFn α).map (fun k => A (basisVec k))).prod| *
          (B * lam ^ (n + p) * ‖ξ‖) := by
    unfold finiteLiftSymbolBudget
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro m _
    apply Finset.sum_congr rfl
    intro α _
    ring
  rw [he]
  apply Finset.sum_le_sum
  intro m hm
  have hmn : m ≤ n := by have hh := Finset.mem_range.mp hm; omega
  rw [norm_mixed_jet_const_smul (hinner m hm), abs_of_nonneg (pow_nonneg hlam m)]
  apply (mul_le_mul_of_nonneg_left
    (norm_mixed_jet_finset_sum_le Finset.univ p q _
      (fun α _ => ((hf m hmn α).clm_comp (ContinuousLinearMap.apply ℝ (h v) ξ)).const_smul _) X z)
    (pow_nonneg hlam m)).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro α _
  rw [norm_mixed_jet_const_smul ((hf m hmn α).clm_comp (ContinuousLinearMap.apply ℝ (h v) ξ))]
  have ha := (norm_mixed_operator_apply_le p q _ (hf m hmn α) ξ X z).trans
    (mul_le_mul_of_nonneg_right (hb m hmn α) (norm_nonneg ξ))
  apply (mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left ha (abs_nonneg _)) (pow_nonneg hlam m)).trans_eq
  have hp : m + (n - m + p) = n + p := by omega
  calc
    _ = |((List.ofFn α).map (fun k => A (basisVec k))).prod| *
        (B * (lam ^ m * lam ^ (n - m + p)) * ‖ξ‖) := by ring
    _ = _ := by rw [← pow_add, hp]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! The common coefficient state supplies its normalized exponential tests at every reserved suborder. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
  {c : LiftCoeff ι h} {M : ι → ι → ℝ}

theorem AmbientLiftCoefficientData.normalized_test_box
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (normalizedLiftTestField c n (lam • A) u v ξ t) :=
  normalized_lift_test_box_reserve n p q c lam A t v u ξ
    (fun m hm α => data.box m hm α v u t ht)

theorem AmbientLiftCoefficientData.normalized_test_measurable
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (A : Vec 2 →L[ℝ] ℝ) (v u : ι)
    [FiniteDimensional ℝ (h v)] [MeasurableSpace (h v)] [BorelSpace (h v)]
    (ξ : h u) (X z : Vec 2) :
    Measurable (fun t => normalizedLiftTestField c n (lam • A) u v ξ
      (Set.projIcc a b hab t) X z) := by
  unfold normalizedLiftTestField
  simp_rw [normalized_exponential_lift_polynomial]
  apply Finset.measurable_sum
  intro m hm
  apply Measurable.const_smul
  apply Finset.measurable_sum
  intro α _
  exact (data.applied_measurable m (by have hh := Finset.mem_range.mp hm; omega)
    α v u ξ X z).const_smul _

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Ordered tested lift composition has a dimension-independent finite-word matrix majorant. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_slow_input_matrix_grading (n p q δ : ℕ) (c : LiftCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι)
    (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth p q (fun Y y => c m α t Y y v u))
    (lam : ℝ) (hlam : 0 ≤ lam) (B C : ι → ℝ)
    (hB : ∀ u, 0 ≤ B u) (hC : ∀ u, 0 ≤ C u)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun w => c m α t Y w v u) y) X‖ ≤ B u * lam ^ (n - m + a))
    (hbg : ∀ u, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y u) X‖ ≤ C u * lam ^ (δ + a)) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => liftApply n c (fun _ => g) t Y y v) z) X‖ ≤
      (finiteLiftWordCount n * 2 ^ (p + 2 * q) * (∑ u, B u * C u)) * lam ^ (n + δ + p) := by
  have hh := liftApply_slow_input_mixed_grading n p q δ c g t X z v hg hc lam hlam B C
    hB hC hbc hbg
  apply hh.trans_eq
  have hi : (∑ u, (2 ^ (p + 2 * q) * B u * C u) * lam ^ (n + δ + p)) =
      (2 ^ (p + 2 * q) * (∑ u, B u * C u)) * lam ^ (n + δ + p) := by
    rw [← Finset.sum_mul]
    congr 1
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => mul_assoc _ _ _)
  simp_rw [hi]
  rw [finite_lift_word_sum]
  ring

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Recover actual exponential lift fields from their normalized component tests. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {par : Fin 2} {a b lam : ℝ} {hab : a ≤ b} {n p q : ℕ}
  {c : LiftCoeff ι h} {M : ι → ι → ℝ}

theorem exponential_lift_test_component_recover (A : Vec 2 →L[ℝ] ℝ)
    (n : ℕ) (c : LiftCoeff ι h) (u v : ι) (ξ : h u) (t : ℝ) (X z : Vec 2) :
    liftApply n c (fun _ Y => Real.exp (A Y) • Pi.single u ξ) t X z v =
      Real.exp (A X) • normalizedLiftTestField c n A u v ξ t X z := by
  unfold normalizedLiftTestField
  rw [smul_smul, mul_inv_cancel₀ (Real.exp_ne_zero _), one_smul]

theorem AmbientLiftCoefficientData.raw_test_box
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u) (t : ℝ) (ht : t ∈ Set.Icc a b) :
    IsBoxSmooth p q (liftApply n c (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) t) := by
  apply isBoxSmooth_pi
  intro v
  simp_rw [exponential_lift_test_component_recover]
  exact isBoxSmooth_bilinear
    (isBoxSmooth_slow_field p q _ (Real.contDiff_exp.comp (lam • A).contDiff))
    (data.normalized_test_box A v u ξ t ht)
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] h v →L[ℝ] h v)

theorem AmbientLiftCoefficientData.raw_test_measurable
    (data : AmbientLiftCoefficientData par a b hab lam n p q c M)
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    (A : Vec 2 →L[ℝ] ℝ) (u : ι) (ξ : h u) (X z : Vec 2) :
    Measurable (fun t => liftApply n c
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) (Set.projIcc a b hab t) X z) := by
  apply Measurable.of_eval
  intro v
  simp_rw [exponential_lift_test_component_recover]
  exact (data.normalized_test_measurable A v u ξ X z).const_smul (Real.exp ((lam • A) X))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Every reserved suborder of the actual normalized cross operator has a common constant. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem normalizedCellB1_scaled_drift_uniform_mixed_grading_at_slow_point (p q δ : ℕ) (η lam M W C : ℝ)
    (hη : η ≤ 1) (hlam : 0 ≤ lam) (hM : 0 ≤ M) (hW : 0 ≤ W) (hC : 0 ≤ C)
    (A : Vec 2 →L[ℝ] ℝ) (G : ℝ → Vec 2 → Fin 2 → Fin 2 → ℝ) (v : ℝ → Vec 2 → Vec 2) (t : ℝ)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth (p + 1) (q + 1) f)
    (hG : ∀ i j, IsBoxSmooth (p + 1) q (fun Y (_ : Vec 2) => G t Y i j))
    (hv : ∀ k, IsBoxSmooth p q (fun (_ : Vec 2) z => v t z k)) (X : Vec 2)
    (hbG : ∀ i j, ∀ a ≤ p + 1, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun (_ : Vec 2) => G t Y i j) z) X‖ ≤ M * lam ^ a)
    (hbv : ∀ k, ∀ a ≤ p, ∀ b ≤ q, ∀ z,
      ‖iteratedFDeriv ℝ a (fun (_ : Vec 2) => iteratedFDeriv ℝ b
        (fun y => Real.sqrt η * v t y k) z) X‖ ≤ W * lam ^ a)
    (hbf : ∀ a ≤ p + 1, ∀ b ≤ q + 1, ∀ z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ C * lam ^ (δ + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => (Real.exp ((lam • A) Y))⁻¹ • cellB1 η G v t
        (fun Z w => Real.exp ((lam • A) Z) • f Z w) Y y) z) X‖ ≤
      (normalizedCellB1UniformConstant p q A M W * C) * lam ^ ((δ + 1) + r) := by
  have hh := normalizedCellB1_scaled_drift_mixed_grading_at_slow_point r s δ η lam M W C
    hη hlam hM hW hC A G v t f
    (hf.mono (by omega) (by omega))
    (fun i j => (hG i j).mono (by omega) hs)
    (fun k => (hv k).mono hr hs) X
    (fun i j a ha b hb y => hbG i j a (by omega) b (hb.trans hs) y)
    (fun k a ha b hb y => hbv k a (ha.trans hr) b (hb.trans hs) y)
    (fun a ha b hb y => hbf a (by omega) b (by omega) y) z
  rw [normalizedCellB1MixedConstant_factor] at hh
  exact hh.trans (mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_right
      (normalizedCellB1MixedConstant_le_uniform p q r s hr hs A M W hM hW) hC)
    (pow_nonneg hlam _))

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Raw exponential composition retains a single local exponential factor for cancellation. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def exponentialLiftCompositionRawConstant (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  finiteLiftWordCount n * 2 ^ (p + 2 * q) * (2 ^ (p + n) * (max 1 ‖A‖) ^ (p + n))

theorem liftApply_exponential_input_raw_uniform_mixed_bound (n p q δ : ℕ) (c : LiftCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2) (v : ι)
    (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth p q (fun Y y => c m α t Y y v u))
    (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (B C : ι → ℝ)
    (hB : ∀ u, 0 ≤ B u) (hC : ∀ u, 0 ≤ C u)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun w => c m α t Y w v u) y) X‖ ≤ B u * lam ^ (n - m + a))
    (hbg : ∀ u, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y u) X‖ ≤ C u * lam ^ (δ + a))
    (r s : ℕ) (hr : r ≤ p) (hs : s ≤ q) (z : Vec 2) :
    ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s
      (fun y => liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v) z) X‖ ≤
      (Real.exp ((lam • A) X) *
        (exponentialLiftCompositionRawConstant n p q A * (∑ u, B u * C u))) * lam ^ (n + δ + r) := by
  let K := 2 ^ (p + n) * (max 1 ‖A‖) ^ (p + n)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  let F := fun Z => Real.exp ((lam • A) Z) • g Z
  have hF : ContDiff ℝ ((p + n : ℕ) : ℕ∞) F :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul hg
  have hFb u a (ha : a ≤ r + n) :
      ‖iteratedFDeriv ℝ a (fun Y => F Y u) X‖ ≤
        (Real.exp ((lam • A) X) * K * C u) * lam ^ (δ + a) := by
    have hh := norm_slow_exponential_smul_graded_le (p + n) δ A lam (C u) hlam (hC u)
      (fun Y => g Y u) ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp hg)
      X (hbg u) a (by omega)
    simpa only [F, Pi.smul_apply, K, mul_assoc] using! hh
  have hh := liftApply_slow_input_matrix_grading n r s δ c F t X z v
    (hF.of_le (by exact_mod_cast Nat.add_le_add_right hr n))
    (fun m hm α u => (hc m hm α u).mono hr hs) lam hlam B
    (fun u => Real.exp ((lam • A) X) * K * C u) hB
    (fun u => mul_nonneg (mul_nonneg (Real.exp_pos _).le hK) (hC u))
    (fun m hm α u a ha b hb y => hbc m hm α u a (ha.trans hr) b (hb.trans hs) y) hFb
  have hsum : (∑ u, B u * (Real.exp ((lam • A) X) * K * C u)) =
      (Real.exp ((lam • A) X) * K) * (∑ u, B u * C u) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun u _ => by ring)
  rw [hsum] at hh
  have hpw : (2 : ℝ) ^ (r + 2 * s) ≤ 2 ^ (p + 2 * q) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  have hU : 0 ≤ Real.exp ((lam • A) X) * finiteLiftWordCount n * K * (∑ u, B u * C u) :=
    mul_nonneg (mul_nonneg (mul_nonneg (Real.exp_pos _).le (finiteLiftWordCount_nonneg n)) hK)
      (Finset.sum_nonneg fun u _ => mul_nonneg (hB u) (hC u))
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw hU)
    (pow_nonneg hlam (n + δ + r))
  convert hb using 1 <;> dsimp only [exponentialLiftCompositionRawConstant, K] <;> ring
end

/-! Normalized ordered lift compositions retain the sum of the two degrees. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def exponentialLiftCompositionNormalizedConstant (n p q : ℕ) (A : Vec 2 →L[ℝ] ℝ) : ℝ :=
  2 ^ (p + 2 * q) * (max 1 ‖A‖) ^ p * exponentialLiftCompositionRawConstant n p q A

theorem liftApply_exponential_input_normalized_mixed_bound (n p q δ : ℕ) (c : LiftCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2) (v : ι)
    (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth p q (fun Y y => c m α t Y y v u))
    (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (B C : ι → ℝ)
    (hB : ∀ u, 0 ≤ B u) (hC : ∀ u, 0 ≤ C u)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun w => c m α t Y w v u) y) X‖ ≤ B u * lam ^ (n - m + a))
    (hbg : ∀ u, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y u) X‖ ≤ C u * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ •
        liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v) z) X‖ ≤
      (exponentialLiftCompositionNormalizedConstant n p q A * (∑ u, B u * C u)) *
        lam ^ (n + δ + p) := by
  have hF : ContDiff ℝ ((p + n : ℕ) : ℕ∞)
      (fun Z => Real.exp ((lam • A) Z) • g Z) :=
    (Real.contDiff_exp.comp (lam • A).contDiff).smul hg
  have hf := liftApply_component_box_reserve n p q c
    (fun _ Z => Real.exp ((lam • A) Z) • g Z) t v hF hc
  have hK : 0 ≤ exponentialLiftCompositionRawConstant n p q A := by
    unfold exponentialLiftCompositionRawConstant
    exact mul_nonneg (mul_nonneg (finiteLiftWordCount_nonneg n) (by positivity)) (by positivity)
  have hsum : 0 ≤ ∑ u, B u * C u :=
    Finset.sum_nonneg fun u _ => mul_nonneg (hB u) (hC u)
  have hh := norm_mixed_exponential_normalized_le p q (n + δ) A lam
    (exponentialLiftCompositionRawConstant n p q A * (∑ u, B u * C u))
    hlam (mul_nonneg hK hsum)
    (fun Y y => liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v)
    hf X (fun r hr s hs y =>
      liftApply_exponential_input_raw_uniform_mixed_bound n p q δ c g t X v hg hc
        lam hlam A B C hB hC hbc hbg r s hr hs y) z
  simpa only [exponentialLiftCompositionNormalizedConstant, mul_assoc] using hh
end

/-! Ordered normalized compositions use matrix products, preserving mass-weighted Schur budgets. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_exponential_input_matrix_product_bound (n p q δ : ℕ) (c : LiftCoeff ι h)
    (g : Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2) (v : ι)
    (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      IsBoxSmooth p q (fun Y y => c m α t Y y v u))
    (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ) (B C : ι → ι → ℝ) (w : ι)
    (hB : ∀ i j, 0 ≤ B i j) (hC : ∀ i j, 0 ≤ C i j)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun w => c m α t Y w v u) y) X‖ ≤ B v u * lam ^ (n - m + a))
    (hbg : ∀ u, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y u) X‖ ≤ C u w * lam ^ (δ + a))
    (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ •
        liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v) z) X‖ ≤
      (exponentialLiftCompositionNormalizedConstant n p q A * finiteMatrixProduct B C v w) *
        lam ^ (n + δ + p) :=
  liftApply_exponential_input_normalized_mixed_bound n p q δ c g t X v hg hc lam hlam A
    (B v) (fun u => C u w) (hB v) (fun u => hC u w) hbc hbg z
end

/-! Ordered corrections combine their two source heights by matrix-power multiplication. -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_exponential_input_power_bound (n p q δ h₁ h₂ : ℕ)
    (c : LiftCoeff ι h) (g : Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2) (v u : ι)
    (hg : ContDiff ℝ ((p + n : ℕ) : ℕ∞) g)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ w,
      IsBoxSmooth p q (fun Y y => c m α t Y y v w))
    (lam : ℝ) (hlam : 0 ≤ lam) (A : Vec 2 →L[ℝ] ℝ)
    (F : ι → ι → ℝ) (hF : ∀ w w', 0 ≤ F w w') (B C : ℝ)
    (hB : 0 ≤ B) (hC : 0 ≤ C) (ξ : h u)
    (hbc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ w, ∀ a ≤ p, ∀ b ≤ q, ∀ y,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
        (fun z => c m α t Y z v w) y) X‖ ≤
          (B * finiteMatrixPower F h₁ v w) * lam ^ (n - m + a))
    (hbg : ∀ w, ∀ a ≤ p + n,
      ‖iteratedFDeriv ℝ a (fun Y => g Y w) X‖ ≤
        (C * finiteMatrixPower F h₂ w u * ‖ξ‖) * lam ^ (δ + a)) (z : Vec 2) :
    ‖iteratedFDeriv ℝ p (fun Y => iteratedFDeriv ℝ q
      (fun y => (Real.exp ((lam • A) Y))⁻¹ •
        liftApply n c (fun _ Z => Real.exp ((lam • A) Z) • g Z) t Y y v) z) X‖ ≤
      (exponentialLiftCompositionNormalizedConstant n p q A * B * C *
        finiteMatrixPower F (h₁ + h₂) v u * ‖ξ‖) * lam ^ (n + δ + p) := by
  have hb := liftApply_exponential_input_matrix_product_bound n p q δ c g t X v hg hc
    lam hlam A (fun v w => B * finiteMatrixPower F h₁ v w)
    (fun w u => (C * ‖ξ‖) * finiteMatrixPower F h₂ w u) u
    (fun v w => mul_nonneg hB (finiteMatrixPower_nonneg F hF h₁ v w))
    (fun w u => mul_nonneg (mul_nonneg hC (norm_nonneg ξ))
      (finiteMatrixPower_nonneg F hF h₂ w u)) hbc
    (fun w a ha => by convert hbg w a ha using 1; ring) z
  rw [finiteMatrixProduct_scalar_powers] at hb
  convert hb using 1
  ring
end

end AVRegularity.CycleComparison.Lift
end
