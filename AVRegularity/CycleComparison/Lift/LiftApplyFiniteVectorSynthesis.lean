-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.CycleComparison.Lift.WordPolynomialFiniteExtraction
import AVRegularity.CycleComparison.Residual.Jets.Lift
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola

@[expose] public noncomputable section

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Reserved source word jets inherit joint slow-position and fast-position continuity. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem boxSmooth_fast_word_slow_jet_continuous
    (p q r s : ℕ) (hr : r ≤ p) (hs : s ≤ q)
    (f : Vec 2 → Vec 2 → E) (hf : IsBoxSmooth p q f) (β : DerivativeWord2 s) :
    Continuous (fun x : Vec 2 × Vec 2 => iteratedFDeriv ℝ r
      (fun X => orderedDerivative β (f X) x.2) x.1) := by
  let J := ContinuousMultilinearMap ℝ (fun _ : Fin s => Vec 2) E
  let L : J →L[ℝ] E := ContinuousMultilinearMap.apply ℝ (fun _ : Fin s => Vec 2) E
    (fun i => basisVec (β (Fin.rev i)))
  let post := ContinuousLinearMap.compContinuousMultilinearMapL ℝ
    (fun _ : Fin r => Vec 2) J E L
  have hc := post.continuous.comp (hf.2.2 r s hr hs)
  apply hc.congr
  intro x
  have he : (fun X => orderedDerivative β (f X) x.2) =
      L ∘ (fun X => iteratedFDeriv ℝ s (f X) x.2) := by
    funext X
    exact congrFun (orderedDerivative_eq_iteratedFDeriv β
      ((hf.1 X).of_le (by exact_mod_cast hs))) x.2
  rw [he, L.iteratedFDeriv_comp_left (hf.2.1 s hs x.2).contDiffAt
    (by exact_mod_cast hr)]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Coordinate derivatives distribute over sums under their exact rectangular reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem fastPartial_add_box (k : Fin 2) (f g : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth 0 1 f) (hg : IsBoxSmooth 0 1 g) :
    fastPartial k (fun X z => f X z + g X z) = fun X z =>
      fastPartial k f X z + fastPartial k g X z := by
  funext X z
  unfold fastPartial
  rw [fderiv_fun_add ((hf.1 X).differentiable one_ne_zero z)
    ((hg.1 X).differentiable one_ne_zero z)]
  rfl

theorem slowPartial_add_box (k : Fin 2) (f g : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth 1 0 f) (hg : IsBoxSmooth 1 0 g) :
    slowPartial k (fun X z => f X z + g X z) = fun X z =>
      slowPartial k f X z + slowPartial k g X z := by
  funext X z
  unfold slowPartial
  rw [fderiv_fun_add ((boxSmooth_slow_contDiff hf z).differentiable one_ne_zero X)
    ((boxSmooth_slow_contDiff hg z).differentiable one_ne_zero X)]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory
namespace AVRegularity.CycleComparison.Lift

/-! First slow and fast coordinate derivatives preserve time measurability at their separate reserves. -/

variable {T E : Type*} [MeasurableSpace T]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem fastPartial_parameter_measurable (f : T → Vec 2 → Vec 2 → E)
    (hm : ∀ X z, Measurable (fun t => f t X z))
    (hf : ∀ t X, Differentiable ℝ (f t X)) (k : Fin 2) (X z : Vec 2) :
    Measurable (fun t => fastPartial k (f t) X z) := by
  exact fderiv_apply_parameter_measurable (fun t y => f t X y) (hm X)
    (fun t => hf t X) z (basisVec k)

theorem slowPartial_parameter_measurable (f : T → Vec 2 → Vec 2 → E)
    (hm : ∀ X z, Measurable (fun t => f t X z))
    (hf : ∀ t z, Differentiable ℝ (fun X => f t X z)) (k : Fin 2) (X z : Vec 2) :
    Measurable (fun t => slowPartial k (f t) X z) := by
  exact fderiv_apply_parameter_measurable (fun t Y => f t Y z)
    (fun Y => hm Y z) (fun t => hf t z) X (basisVec k)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! Fixed output maps commute with either partial derivative using only its own reserve. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fastPartial_postcomposition (L : E →L[ℝ] F) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth 0 1 f) (k : Fin 2) (X z : Vec 2) :
    fastPartial k (fun Y y => L (f Y y)) X z = L (fastPartial k f X z) := by
  have hd := (hf.1 X).differentiable (by norm_num)
  have hh := L.hasFDerivAt.comp z (hd z).hasFDerivAt
  change fderiv ℝ (L ∘ f X) z (basisVec k) = _
  rw [hh.fderiv]
  rfl

theorem slowPartial_postcomposition (L : E →L[ℝ] F) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth 1 0 f) (k : Fin 2) (X z : Vec 2) :
    slowPartial k (fun Y y => L (f Y y)) X z = L (slowPartial k f X z) := by
  have hh := boxSmooth_slow_contDiff hf z
  have hd := hh.differentiable (by norm_num)
  have hder := L.hasFDerivAt.comp X (hd X).hasFDerivAt
  change fderiv ℝ (L ∘ (fun Y => f Y z)) X (basisVec k) = _
  rw [hder.fderiv]
  rfl

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleComparison.Lift

/-! A globally defined time integrand for the actual finite-past response. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def clampedDuhamelField (rate : ℝ) (g : ℝ → Vec 2 → ℝ) (f : ℝ → Vec 2 → E)
    (a b : ℝ) (hab : a ≤ b) : ℝ → Vec 2 → E := fun s Y =>
  transverseModeKernel rate (fun t => g t Y) (projIcc a b hab s) b • f (projIcc a b hab s) Y

def duhamelSlowJetMajorant (n : ℕ) (M κ : ℝ) (S : ℕ → ℝ) (q : ℕ) : ℝ :=
  (∑ j ∈ Finset.range (q + 1), (q.choose j : ℝ) * j.factorial * S (q - j)) *
    (1 + q.factorial * (2 * ((2 : ℝ) ^ n * M) / κ) ^ q)

theorem duhamelSlowJetMajorant_nonneg (n q : ℕ) (M κ : ℝ) (S : ℕ → ℝ)
    (hM : 0 ≤ M) (hκ : 0 < κ) (hS : ∀ j ≤ q, 0 ≤ S j) :
    0 ≤ duhamelSlowJetMajorant n M κ S q := by
  apply mul_nonneg
  · apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _))
      (hS (q - j) (Nat.sub_le q j))
  · positivity

theorem transverseModeResponse_eq_clamped_integral (rate : ℝ)
    (g : ℝ → Vec 2 → ℝ) (f : ℝ → Vec 2 → E) (a b : ℝ) (hab : a ≤ b) :
    (fun X => transverseModeResponse rate (fun t => g t X) (fun t => f t X) a b) =
      fun X => ∫ s, clampedDuhamelField rate g f a b hab s X ∂volume.restrict (Ioc a b) := by
  funext X
  rw [transverseModeResponse, intervalIntegral.integral_of_le hab]
  apply integral_congr_ae
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
  simp only [clampedDuhamelField, projIcc_of_mem hab (show s ∈ Icc a b from ⟨hs.1.le, hs.2⟩)]

end AVRegularity.CycleComparison.Lift
end

section
namespace AVRegularity.CycleComparison.Lift

/-! Complex Fourier weights commute with the literal real-kernel time response. -/

theorem transverseModeResponse_complex_mul (rate : ℝ) (g : ℝ → ℝ)
    (f : ℝ → ℂ) (c : ℂ) (a b : ℝ) :
    transverseModeResponse rate g (fun t => c * f t) a b =
      c * transverseModeResponse rate g f a b := by
  unfold transverseModeResponse
  have he : (fun t => transverseModeKernel rate g t b • (c * f t)) =
      fun t => c * (transverseModeKernel rate g t b • f t) := by
    funext t
    simp only [Complex.real_smul]
    ring
  rw [he, intervalIntegral.integral_const_mul]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization
namespace AVRegularity.CycleComparison.Lift

/-! The cell coordinate maps have dimension-independent norm one bounds. -/

theorem cell_coordinate_projection_norm_le (q : Fin 2) :
    ‖(ContinuousLinearMap.proj q : Vec 2 →L[ℝ] ℝ)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro x
  simpa only [ContinuousLinearMap.proj_apply, one_mul] using norm_le_pi_norm x q

theorem cell_coordinate_line_norm (q : Fin 2) :
    ‖(ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec q : Vec 2)‖ = 1 := by
  simp only [ContinuousLinearMap.norm_smulRight_apply, ContinuousLinearMap.norm_id,
    norm_basisVec, mul_one]

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev Filter
open scoped Topology
namespace AVRegularity.CycleComparison.Lift

/-! Fixed finite derivative coordinates recover continuity of full multilinear jets. -/

variable {T E : Type*} [TopologicalSpace T] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem continuous_multilinear_of_basis_coordinates (q : ℕ)
    (f : T → ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E)
    (hf : ∀ w : DerivativeWord2 q, Continuous (fun t => f t (fun i => basisVec (w i)))) :
    Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  change Tendsto f (𝓝 t₀) (𝓝 (f t₀))
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have hc : Continuous (fun t => ∑ w : DerivativeWord2 q,
      ‖f t (fun i => basisVec (w i)) - f t₀ (fun i => basisVec (w i))‖) :=
    continuous_finsetSum Finset.univ (fun w _ => ((hf w).sub continuous_const).norm)
  have hlim : Tendsto (fun t => ∑ w : DerivativeWord2 q,
      ‖f t (fun i => basisVec (w i)) - f t₀ (fun i => basisVec (w i))‖) (𝓝 t₀) (𝓝 0) := by
    simpa only [sub_self, norm_zero, Finset.sum_const_zero] using
      (hc.continuousAt (x := t₀)).tendsto
  apply squeeze_zero (fun t => norm_nonneg (f t - f t₀)) ?_ hlim
  intro t
  simpa only [sub_apply] using AVRegularity.ChartTransport.norm_le_sum_basisVec (f t - f t₀)

end AVRegularity.CycleComparison.Lift
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Lift

/-! Finite coordinate synthesis recovers smoothness of full multilinear jets. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def derivativeCoordinateTensor (q : ℕ) (w : DerivativeWord2 q) :
    ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) ℝ :=
  (ContinuousMultilinearMap.mkPiAlgebra ℝ (Fin q) ℝ).compContinuousLinearMap
    (fun i => ContinuousLinearMap.proj (w i))

theorem multilinear_eq_sum_basis_coordinates (q : ℕ)
    (T : ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E) :
    T = ∑ w : DerivativeWord2 q,
      (derivativeCoordinateTensor q w).smulRight (T (fun i => basisVec (w i))) := by
  classical
  ext x
  have hx : x = fun i => ∑ j : Fin 2, x i j • basisVec j :=
    funext fun i => AVRegularity.ChartTransport.vec2_eq_sum_basisVec _
  have he : T x = ∑ w : DerivativeWord2 q, T (fun i => x i (w i) • basisVec (w i)) := by
    conv_lhs => rw [hx]
    exact T.toMultilinearMap.map_sum (fun i j => x i j • basisVec j)
  rw [he]
  simp only [sum_apply]
  apply Finset.sum_congr rfl
  intro w _
  simp only [ContinuousMultilinearMap.map_smul_univ,
    ContinuousMultilinearMap.smulRight_apply, derivativeCoordinateTensor,
    ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousMultilinearMap.mkPiAlgebra_apply, ContinuousLinearMap.proj_apply]

theorem contDiff_multilinear_of_basis_coordinates (q p : ℕ)
    (f : Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin q => Vec 2) E)
    (hf : ∀ w : DerivativeWord2 q,
      ContDiff ℝ (p : ℕ∞) (fun X => f X (fun i => basisVec (w i)))) :
    ContDiff ℝ (p : ℕ∞) f := by
  classical
  have he : f = fun X => ∑ w : DerivativeWord2 q,
      (derivativeCoordinateTensor q w).smulRight (f X (fun i => basisVec (w i))) :=
    funext fun X => multilinear_eq_sum_basis_coordinates q (f X)
  rw [he]
  exact ContDiff.sum (fun w _ =>
    (ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin q => Vec 2) E
      (derivativeCoordinateTensor q w)).contDiff.comp (hf w))
end

/-! Equality of left coefficients at a time identifies the entire differential operator at that time. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_congr_at_time (n : ℕ) (c d : LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (he : ∀ m (α : DerivativeWord2 m) X z v u, c m α t X z v u = d m α t X z v u) :
    liftApply n c a t = liftApply n d a t := by
  funext X z v
  simp only [liftApply, he]
end

/-! The literal lift action is linear in its operator coefficient array. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_coefficient_add (n : ℕ) (c d : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) :
    liftApply n (fun m α t X z v u => c m α t X z v u + d m α t X z v u) f =
      fun t X z => liftApply n c f t X z + liftApply n d f t X z := by
  funext t X z
  ext v
  simp only [liftApply, add_apply, Finset.sum_add_distrib, Pi.add_apply]

theorem liftApply_coefficient_sub (n : ℕ) (c d : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) :
    liftApply n (fun m α t X z v u => c m α t X z v u - d m α t X z v u) f =
      fun t X z => liftApply n c f t X z - liftApply n d f t X z := by
  funext t X z
  ext v
  simp only [liftApply, sub_apply, Finset.sum_sub_distrib, Pi.sub_apply]

theorem liftApply_coefficient_smul (n : ℕ) (c : LiftCoeff ι h) (a : ℝ)
    (f : ℝ → Vec 2 → ∀ i, h i) :
    liftApply n (fun m α t X z v u => a • c m α t X z v u) f =
      fun t X z => a • liftApply n c f t X z := by
  funext t X z
  ext v
  simp only [liftApply, smul_apply, Finset.smul_sum, Pi.smul_apply]
end

/-! Continuous fast coefficient arrays give continuous lift actions on any fixed coarse field. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

theorem liftApply_component_fast_continuous (n : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2) (v : ι)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ u,
      Continuous (fun z => c m α t X z v u)) :
    Continuous (fun z => liftApply n c f t X z v) := by
  simp only [liftApply]
  apply continuous_finsetSum
  intro m hm
  apply continuous_finsetSum
  intro α _
  apply continuous_finsetSum
  intro u _
  exact (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (f t) X u)).continuous.comp
    (hc m (by have := Finset.mem_range.mp hm; omega) α u)

theorem liftApply_fast_continuous (n : ℕ) (c : LiftCoeff ι h)
    (f : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X : Vec 2)
    (hc : ∀ m ≤ n, ∀ α : DerivativeWord2 m, ∀ v u,
      Continuous (fun z => c m α t X z v u)) :
    Continuous (fun z => liftApply n c f t X z) := by
  apply continuous_pi
  intro v
  simp only [liftApply]
  apply continuous_finsetSum
  intro m hm
  apply continuous_finsetSum
  intro α _
  apply continuous_finsetSum
  intro u _
  exact (ContinuousLinearMap.apply ℝ (h v) (orderedDerivative α (f t) X u)).continuous.comp
    (hc m (by have := Finset.mem_range.mp hm; omega) α v u)
end

/-! The lift action is one finite sum over its coefficient, word and input-component indices. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def LiftActionIndex (ι : Type*) (n : ℕ) :=
  (m : Fin (n + 1)) × (DerivativeWord2 m.val × ι)

instance (n : ℕ) : Fintype (LiftActionIndex ι n) :=
  inferInstanceAs (Fintype ((m : Fin (n + 1)) × (DerivativeWord2 m.val × ι)))

theorem liftApply_finite_vector_synthesis (n : ℕ) (c : LiftCoeff ι h)
    (f : Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) (v : ι) :
    (∑ p : LiftActionIndex ι n,
      c p.1.val p.2.1 t X z v p.2.2 (orderedDerivative p.2.1 f X p.2.2)) =
      liftApply n c (fun _ => f) t X z v := by
  classical
  change (∑ p : (m : Fin (n + 1)) × (DerivativeWord2 m.val × ι), _) = _
  rw [Fintype.sum_sigma]
  simp only [Fintype.sum_prod_type]
  exact Fin.sum_univ_eq_sum_range
    (fun m => ∑ α : DerivativeWord2 m, ∑ u, c m α t X z v u (orderedDerivative α f X u)) (n + 1)
end

end AVRegularity.CycleComparison.Lift
end
