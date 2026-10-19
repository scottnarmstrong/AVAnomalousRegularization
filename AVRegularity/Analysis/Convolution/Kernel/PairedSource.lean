-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Analysis.Convolution.Kernel.ApproximationBounds
import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Algebra.Order.Star.Real
import Mathlib.CategoryTheory.Category.Basic
import Mathlib.Tactic.Monotonicity.Lemmas

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
namespace AVRegularity.Analysis.Convolution

/-! Sharp classical derivative tensor bounds of actual positive averages of weak Sobolev data. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem coordinate_kernel_average_eq_weak_component_torus {K m : ℕ} (hmK : m ≤ K)
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (f : TorusHk K E) (w : DerivativeWord 2 m) :
    averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous)
      (orderedKernelDerivative κ m (fun k => R.symm (basisVec (w k))))
      (integrable_orderedKernelDerivative hc hd m (fun k => R.symm (basisVec (w k))))
      (cellToTorus (f.val (valueIndex2 K))) =
    averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous)
      κ (hd.continuous.integrable_of_hasCompactSupport hc)
      (cellToTorus (f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩)) := by
  have h := congrArg (fun g : TorusHk K E =>
    cellToTorus (g.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩)) (periodicSmoothing_eq_weakAverage R hc hd f)
  let A := averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous)
    (orderedKernelDerivative κ m (fun k => R.symm (basisVec (w k))))
    (integrable_orderedKernelDerivative hc hd m (fun k => R.symm (basisVec (w k))))
    (cellToTorus (f.val (valueIndex2 K)))
  let B := averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous) κ
    (hd.continuous.integrable_of_hasCompactSupport hc)
    (cellToTorus (f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩))
  change cellToTorus (torusToCell A) = cellToTorus (torusToCell B) at h
  rw [cellToTorus_torusToCell, cellToTorus_torusToCell] at h
  exact h

theorem sum_reverse_words {B : Type*} [AddCommMonoid B] (m : ℕ) (A : DerivativeWord 2 m → B) :
    (∑ w : DerivativeWord 2 m, A (fun k => w k.rev)) = ∑ w : DerivativeWord 2 m, A w := by
  let e : Equiv.Perm (DerivativeWord 2 m) :=
    { toFun := fun w k => w k.rev
      invFun := fun w k => w k.rev
      left_inv := fun w => by funext k; simp only [Fin.rev_rev]
      right_inv := fun w => by funext k; simp only [Fin.rev_rev] }
  exact Equiv.sum_comp e A

theorem iteratedFDeriv_positive_average_norm_le_torus {K m : ℕ} (hmK : m ≤ K)
    (R : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ)
    (hpos : ∀ᵐ z, 0 ≤ κ z) (hmass : ∫ z, κ z = 1)
    (f : TorusHk K E) (x v : Vec 2) :
    ‖iteratedFDeriv ℝ m (fun x : Vec 2 => translation (-torusQuotient x)
      (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
        (cellToTorus (f.val (valueIndex2 K))))) x (fun _ => v)‖ ≤
      ‖euclideanCoordinateEquiv.symm v‖^m * Real.sqrt (derivativeNormSq f.val ⟨m, Nat.lt_succ_of_le hmK⟩) := by
  let F := fun x : Vec 2 => translation (-torusQuotient x)
      (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
        (cellToTorus (f.val (valueIndex2 K))))
  have hw (w : DerivativeWord 2 m) :
      ‖iteratedFDeriv ℝ m F x (fun k => basisVec (w k))‖^2 ≤
        ‖f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, (fun k => w k.rev)⟩‖^2 := by
    have h := iteratedFDeriv_translation_average_apply torusQuotient continuous_torusQuotient R hc hd
      (cellToTorus (f.val (valueIndex2 K))) m x (fun k => basisVec (w k))
    change iteratedFDeriv ℝ m F x (fun k => basisVec (w k)) =
      translation (-torusQuotient x) (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous)
        (orderedKernelDerivative κ m (fun k => R.symm (basisVec (w k.rev))))
        (integrable_orderedKernelDerivative hc hd m (fun k => R.symm (basisVec (w k.rev))))
        (cellToTorus (f.val (valueIndex2 K)))) at h
    rw [h, coordinate_kernel_average_eq_weak_component_torus hmK R hc hd f, translation_norm]
    apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr
    calc
      _ ≤ 1 * ‖cellToTorus (f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, (fun k => w k.rev)⟩)‖ :=
        ContinuousLinearMap.le_of_opNorm_le _ (averagingOperator_contraction (E := E) (μ := torusMeasure)
          (torusQuotient.comp R.toLinearEquiv.toAddHom) (continuous_torusQuotient.comp R.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc) hpos hmass) _
      _ = _ := by rw [one_mul, cellToTorus.norm_map]
  have hs : (∑ w : DerivativeWord 2 m, ‖iteratedFDeriv ℝ m F x (fun k => basisVec (w k))‖^2) ≤
      derivativeNormSq f.val ⟨m, Nat.lt_succ_of_le hmK⟩ := by
    calc
      _ ≤ ∑ w : DerivativeWord 2 m, ‖f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, (fun k => w k.rev)⟩‖^2 :=
        Finset.sum_le_sum (fun w _ => hw w)
      _ = _ := by
        change (∑ w : DerivativeWord 2 m, ‖f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, (fun k => w k.rev)⟩‖^2) =
          ∑ w : DerivativeWord 2 m, ‖f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩‖^2
        exact sum_reverse_words m (fun w => ‖f.val ⟨⟨m, Nat.lt_succ_of_le hmK⟩, w⟩‖^2)
  change ‖iteratedFDeriv ℝ m F x (fun _ => v)‖ ≤ _
  rw [iteratedFDeriv_same_direction_eq_tensor]
  exact (directionalTensorValue_norm_le m _ v).trans
    (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hs) (pow_nonneg (norm_nonneg _) _))

end AVRegularity.Analysis.Convolution
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVenhance.Infra.Torus AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.Analysis.Convolution

/-! Finite coordinate expansion of paired-axis differentiated kernels. -/

/-- Literal finite expansion: each appended coordinate differentiates one of the two factors. -/
def transverseCoordinateFamily {B : Type*} [AddCommGroup B] [Module ℝ B]
    (F : ℕ → ℕ → B) (cH cV : Fin 2 → ℝ) :
    (m : ℕ) → DerivativeWord2 m → ℕ → ℕ → B
  | 0, _, p, q => F p q
  | m+1, w, p, q =>
      cH (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1) q +
      cV (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) p (q+1)

theorem transverseCoordinateFamily_snoc {B : Type*} [AddCommGroup B] [Module ℝ B]
    (F : ℕ → ℕ → B) (cH cV : Fin 2 → ℝ) {m : ℕ} (w : DerivativeWord2 m)
    (i : Fin 2) (p q : ℕ) :
    transverseCoordinateFamily F cH cV (m+1) (Fin.snoc w i) p q =
      cH i • transverseCoordinateFamily F cH cV m w (p+1) q +
      cV i • transverseCoordinateFamily F cH cV m w p (q+1) := by
  simp only [transverseCoordinateFamily, Fin.init_snoc, Fin.snoc_last]

/-- Finite expansion costs only the two coordinate coefficients at each derivative. -/
theorem norm_transverseCoordinateFamily_le {B : Type*} [NormedAddCommGroup B] [NormedSpace ℝ B]
    (F : ℕ → ℕ → B) (cH cV : Fin 2 → ℝ) {C M : ℝ} (hC : 0 ≤ C)
    (hH : ∀ i, |cH i| ≤ C) (hV : ∀ i, |cV i| ≤ C) {N : ℕ}
    (hF : ∀ p q, p+q ≤ N → ‖F p q‖ ≤ M)
    (m : ℕ) (w : DerivativeWord2 m) (p q : ℕ) (ht : p+q+m ≤ N) :
    ‖transverseCoordinateFamily F cH cV m w p q‖ ≤ (2*C)^m * M := by
  induction m generalizing p q with
  | zero => simpa only [transverseCoordinateFamily, pow_zero, one_mul, add_zero] using hF p q ht
  | succ m ih =>
      have hp := ih (Fin.init w) (p+1) q (by omega)
      have hq := ih (Fin.init w) p (q+1) (by omega)
      calc
        ‖transverseCoordinateFamily F cH cV (m+1) w p q‖ ≤
            ‖cH (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1) q‖ +
            ‖cV (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) p (q+1)‖ := norm_add_le _ _
        _ = |cH (w (Fin.last m))| * ‖transverseCoordinateFamily F cH cV m (Fin.init w) (p+1) q‖ +
            |cV (w (Fin.last m))| * ‖transverseCoordinateFamily F cH cV m (Fin.init w) p (q+1)‖ := by
          rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
        _ ≤ C * ((2*C)^m*M) + C * ((2*C)^m*M) :=
          add_le_add (mul_le_mul (hH _) hp (norm_nonneg _) hC)
            (mul_le_mul (hV _) hq (norm_nonneg _) hC)
        _ = (2*C)^(m+1)*M := by rw [pow_succ]; ring

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

theorem transverseCoordinateFamily_derivative_torus
    (F : ℕ → ℕ → L2 E torusMeasure) (vH vV : Vec 2)
    (hH : ∀ p q e, HasWeakDirectionalDeriv vH (fun x => inner ℝ e (F p q (torusQuotient x)))
      (fun x => inner ℝ e (F (p+1) q (torusQuotient x))))
    (hV : ∀ p q e, HasWeakDirectionalDeriv vV (fun x => inner ℝ e (F p q (torusQuotient x)))
      (fun x => inner ℝ e (F p (q+1) (torusQuotient x))))
    (cH cV : Fin 2 → ℝ) (hc : ∀ i, cH i • vH + cV i • vV = basisVec i)
    (m : ℕ) (w : DerivativeWord2 m) (p q : ℕ) (i : Fin 2) (e : E) :
    HasWeakDirectionalDeriv (basisVec i)
      (fun x => inner ℝ e (transverseCoordinateFamily F cH cV m w p q (torusQuotient x)))
      (fun x => inner ℝ e (transverseCoordinateFamily F cH cV (m+1) (Fin.snoc w i) p q (torusQuotient x))) := by
  rw [transverseCoordinateFamily_snoc]
  suffices hw : ∀ (m : ℕ) (w : DerivativeWord2 m) (p q : ℕ) (e : E),
      HasWeakDirectionalDeriv (basisVec i)
        (fun x => inner ℝ e (transverseCoordinateFamily F cH cV m w p q (torusQuotient x)))
        (fun x => inner ℝ e ((cH i • transverseCoordinateFamily F cH cV m w (p+1) q +
          cV i • transverseCoordinateFamily F cH cV m w p (q+1)) (torusQuotient x))) from hw m w p q e
  intro m
  induction m with
  | zero =>
      intro w p q e
      simpa only [transverseCoordinateFamily, hc i] using
        hasWeakDirectionalDeriv_l2_linear_direction_torus (hH p q) (hV p q) (cH i) (cV i) e
  | succ m ih =>
      intro w p q e
      have hw := hasWeakDirectionalDeriv_l2_linear_input_torus
        (ih (Fin.init w) (p+1) q) (ih (Fin.init w) p (q+1))
        (cH (w (Fin.last m))) (cV (w (Fin.last m))) e
      change HasWeakDirectionalDeriv (basisVec i)
        (fun x => inner ℝ e (transverseCoordinateFamily F cH cV (m+1) w p q (torusQuotient x))) _ at hw
      have heq : cH i • transverseCoordinateFamily F cH cV (m+1) w (p+1) q +
          cV i • transverseCoordinateFamily F cH cV (m+1) w p (q+1) =
          cH (w (Fin.last m)) •
            (cH i • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1+1) q +
              cV i • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1) (q+1)) +
          cV (w (Fin.last m)) •
            (cH i • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1) (q+1) +
              cV i • transverseCoordinateFamily F cH cV m (Fin.init w) p (q+1+1)) := by
        change cH i •
            (cH (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1+1) q +
              cV (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1) (q+1)) +
          cV i •
            (cH (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) (p+1) (q+1) +
              cV (w (Fin.last m)) • transverseCoordinateFamily F cH cV m (Fin.init w) p (q+1+1)) = _
        module
      rw [heq]
      exact hw

variable [MeasurableSpace E] [BorelSpace E]

/-- The actual paired plane coordinate jet from its two differentiated kernel factors. -/
def pairedCoordinateJetPlane {K : ℕ} (R S : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (f : L2 E (volume : Measure (Vec 2))) : JetL2 (volume.restrict (Set.univ : Set (Vec 2))) K E :=
  WithLp.toLp 2 (fun a : JetIndex2 K => planeToUniv
    (transverseCoordinateFamily
      (fun p q => pairedAxisAveragePlane R S κ hc hd (basisVec 0) (basisVec 1) p q f)
      cH cV a.1.val a.2 0 0))

/-- The same actual paired coordinate jet using normalized torus averages and the cell isometry. -/
def pairedCoordinateJetTorus {K : ℕ} (R S : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (f : L2 E torusMeasure) : JetL2 (volume.restrict AVenhance.unitCube) K E :=
  WithLp.toLp 2 (fun a : JetIndex2 K => torusToCell
    (transverseCoordinateFamily
      (fun p q => pairedAxisAverageTorus R S κ hc hd (basisVec 0) (basisVec 1) p q f)
      cH cV a.1.val a.2 0 0))

omit [BorelSpace E] in
 theorem pairedCoordinateJetTorus_global_ae {K : ℕ} (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (f : L2 E torusMeasure) (a : JetIndex2 K) :
    periodicJetRepresentative (pairedCoordinateJetTorus R S κ hc hd cH cV f) a =ᵐ[volume]
      fun x => transverseCoordinateFamily
        (fun p q => pairedAxisAverageTorus R S κ hc hd (basisVec 0) (basisVec 1) p q f)
        cH cV a.1.val a.2 0 0 (torusQuotient x) := by
  have h := cellToTorus_global_ae (pairedCoordinateJetTorus R S κ hc hd cH cV f) a
  change (fun x => cellToTorus (torusToCell (transverseCoordinateFamily
    (fun p q => pairedAxisAverageTorus R S κ hc hd (basisVec 0) (basisVec 1) p q f)
    cH cV a.1.val a.2 0 0)) (torusQuotient x)) =ᵐ[volume] _ at h
  rw [cellToTorus_torusToCell] at h
  exact h.symm

omit [BorelSpace E] in
 theorem pairedCoordinateJetTorus_mem_graph {K : ℕ} (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
    (f : L2 E torusMeasure) :
    pairedCoordinateJetTorus (K := K) R S κ hc hd cH cV f ∈ torusHkGraph (E := E) K := by
  rw [mem_torusHkGraph_iff]
  refine ⟨periodicJetRepresentative_periodic _, periodicJetRepresentative_memL2 _, ?_⟩
  intro j w i e
  let F := fun p q => pairedAxisAverageTorus R S κ hc hd (basisVec 0) (basisVec 1) p q f
  have hw := (hasWeakDirectionalDeriv_basis_iff i _ _).mp
    (transverseCoordinateFamily_derivative_torus F (R (basisVec 0)) (S (basisVec 1))
      (fun p q e => pairedAxisAverageTorus_first R S hc hd _ _ p q f e)
      (fun p q e => pairedAxisAverageTorus_second R S hc hd _ _ p q f e)
      cH cV hcoeff j.val w 0 0 i e)
  apply hasWeakPartialDerivOn_congr_ae _ _ hw
  · simpa [Measure.restrict_univ, Function.comp_def, F, lowerIndex2, lowerIndex] using
      (pairedCoordinateJetTorus_global_ae R S hc hd cH cV f (lowerIndex2 j w)).symm.fun_comp (inner ℝ e)
  · simpa [Measure.restrict_univ, Function.comp_def, F, nextIndex2, nextIndex] using
      (pairedCoordinateJetTorus_global_ae R S hc hd cH cV f (nextIndex2 j w i)).symm.fun_comp (inner ℝ e)

/-- The same proved ordered weak promotion for actual paired torus convolution. -/
def pairedWeakSmoothingTorus {K : ℕ} (R S : Vec 2 ≃L[ℝ] Vec 2) (κ : Vec 2 → ℝ)
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
    (f : L2 E torusMeasure) : TorusHk K E :=
  ⟨pairedCoordinateJetTorus R S κ hc hd cH cV f,
    pairedCoordinateJetTorus_mem_graph R S hc hd cH cV hcoeff f⟩

theorem pairedWeakSmoothingTorus_value {K : ℕ} (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
    (f : L2 E torusMeasure) :
    (pairedWeakSmoothingTorus (K := K) R S κ hc hd cH cV hcoeff f).val (valueIndex2 K) =
      torusToCell (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp R.continuous) κ
        (hd.continuous.integrable_of_hasCompactSupport hc)
        (averagingOperator (torusQuotient.comp S.toLinearEquiv.toAddHom)
          (continuous_torusQuotient.comp S.continuous) κ
          (hd.continuous.integrable_of_hasCompactSupport hc) f)) := rfl

end AVRegularity.Analysis.Convolution
end
end
end

section
@[expose] public section
noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Analysis.Convolution

/-! Kernel-only constants for finite paired coordinate expansions. -/

theorem exists_uniform_pair_kernel_bound (κ : Vec 2 → ℝ) (a b : Vec 2) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ p q : ℕ, p+q ≤ N →
      (∫ z, ‖orderedKernelDerivative κ p (fun _ => a) z‖) *
      (∫ z, ‖orderedKernelDerivative κ q (fun _ => b) z‖) ≤ M := by
  let L := fun p q : ℕ =>
    (∫ z, ‖orderedKernelDerivative κ p (fun _ => a) z‖) *
      (∫ z, ‖orderedKernelDerivative κ q (fun _ => b) z‖)
  have hL : ∀ p q, 0 ≤ L p q := fun _ _ => mul_nonneg
    (integral_nonneg fun _ => norm_nonneg _) (integral_nonneg fun _ => norm_nonneg _)
  refine ⟨∑ p ∈ Finset.range (N+1), ∑ q ∈ Finset.range (N+1), L p q,
    Finset.sum_nonneg (fun p _ => Finset.sum_nonneg (fun q _ => hL p q)), ?_⟩
  intro p q hpq
  exact (Finset.single_le_sum (a := q) (s := Finset.range (N+1)) (fun j _ => hL p j) (Finset.mem_range.mpr (by omega))).trans
    (Finset.single_le_sum (a := p) (s := Finset.range (N+1)) (fun j _ => Finset.sum_nonneg (fun k _ => hL j k))
      (Finset.mem_range.mpr (by omega)))

theorem exists_uniform_paired_word_bound_torus {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (N : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E],
      ∀ (R S : Vec 2 ≃L[ℝ] Vec 2) (cH cV : Fin 2 → ℝ) (C : ℝ),
      0 ≤ C → (∀ i, |cH i| ≤ C) → (∀ i, |cV i| ≤ C) →
      ∀ (m : ℕ) (w : DerivativeWord2 m), m ≤ N →
      ∀ f : L2 E torusMeasure,
      ‖transverseCoordinateFamily
        (fun p q => pairedAxisAverageTorus R S κ hc hd (basisVec 0) (basisVec 1) p q f)
        cH cV m w 0 0‖ ≤ (2*C)^m * M * ‖f‖ := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_pair_kernel_bound κ (basisVec 0) (basisVec 1) N
  refine ⟨M, hM, ?_⟩
  intro E _ _ _ R S cH cV C hC hH hV m w hm f
  have hF : ∀ p q, p+q ≤ N →
      ‖pairedAxisAverageTorus R S κ hc hd (basisVec 0) (basisVec 1) p q f‖ ≤ M * ‖f‖ := by
    intro p q hpq
    exact (pairedAxisAverageTorus_norm_le R S hc hd _ _ p q f).trans
      (mul_le_mul_of_nonneg_right (hbound p q hpq) (norm_nonneg f))
  simpa only [mul_assoc] using norm_transverseCoordinateFamily_le _ cH cV hC hH hV hF m w 0 0 (by simpa only [zero_add] using hm)

/-! Truncation and derivative identities for paired smoothing on the carriers. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem truncate_pairedWeakSmoothingTorus {K N : ℕ} (hKN : K ≤ N)
    (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
    (f : TorusHk K E) :
    truncateTorusHk hKN (pairedWeakSmoothingTorus (K := N) R S κ hc hd cH cV hcoeff
      (cellToTorus (f.val (valueIndex2 K)))) =
      periodicWeakAverage R.toLinearEquiv.toAddHom R.continuous κ (hd.continuous.integrable_of_hasCompactSupport hc)
        (periodicWeakAverage S.toLinearEquiv.toAddHom S.continuous κ (hd.continuous.integrable_of_hasCompactSupport hc) f) := by
  apply TorusHk.ext_value
  change torusToCell (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
      (continuous_torusQuotient.comp R.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
      (averagingOperator (torusQuotient.comp S.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp S.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
        (cellToTorus (f.val (valueIndex2 K))))) =
    torusToCell (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
      (continuous_torusQuotient.comp R.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
      (cellToTorus (torusToCell (averagingOperator (torusQuotient.comp S.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp S.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
        (cellToTorus (f.val (valueIndex2 K)))))))
  rw [cellToTorus_torusToCell]

omit [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
 theorem prefix_valueIndex_eq_top {K L : ℕ} (w : DerivativeWord2 K) :
    prefixJetIndex (K := L) w (valueIndex2 L) =
      truncateJetIndex (Nat.le_add_left K L) (⟨⟨K, Nat.lt_succ_self K⟩, w⟩ : JetIndex 2 K) := by
  change (⟨⟨K, _⟩, Fin.append w Fin.elim0⟩ : JetIndex 2 (L+K)) = ⟨⟨K, _⟩, w⟩
  have hw : Fin.append w Fin.elim0 = w := by
    rw [Fin.append_elim0]
    rfl
  rw [hw]

theorem derivative_pairedWeakSmoothing_torus {K L : ℕ}
    (R S : Vec 2 ≃L[ℝ] Vec 2) {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (cH cV : Fin 2 → ℝ)
    (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
    (f : TorusHk K E) (w : DerivativeWord2 K) :
    derivativeTorusHk w (pairedWeakSmoothingTorus (K := L+K) R S κ hc hd cH cV hcoeff
      (cellToTorus (f.val (valueIndex2 K)))) =
      pairedWeakSmoothingTorus (K := L) R S κ hc hd cH cV hcoeff
        (cellToTorus (f.val ⟨⟨K, Nat.lt_succ_self K⟩, w⟩)) := by
  apply TorusHk.ext_value
  rw [derivativeTorusHk_apply, prefix_valueIndex_eq_top]
  have hv := congrArg (fun g : TorusHk K E => g.val ⟨⟨K, Nat.lt_succ_self K⟩, w⟩)
    (truncate_pairedWeakSmoothingTorus (Nat.le_add_left K L) R S hc hd cH cV hcoeff f)
  rw [truncateTorusHk_apply] at hv
  rw [hv]
  change torusToCell (averagingOperator (torusQuotient.comp R.toLinearEquiv.toAddHom)
      (continuous_torusQuotient.comp R.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
      (cellToTorus (torusToCell (averagingOperator (torusQuotient.comp S.toLinearEquiv.toAddHom)
        (continuous_torusQuotient.comp S.continuous) κ (hd.continuous.integrable_of_hasCompactSupport hc)
        (cellToTorus (f.val ⟨⟨K, Nat.lt_succ_self K⟩, w⟩)))))) = _
  rw [cellToTorus_torusToCell]
  rfl
end

/-! Finite tensor and factorial recombination of the paired coordinate derivatives. -/

section
variable {μ : Measure (Vec 2)}
variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E]
/-- Uniform weighted component domination bounds the exact source factorial norm. -/
theorem factorialNormSq_le_uniform_weighted_components {N : ℕ}
    (D : JetL2 μ N E) {ρ A : ℝ} (hρ : 0 ≤ ρ)
    (hD : ∀ a : JetIndex 2 N, ρ^a.1.val * ‖D a‖ ≤ A) :
    factorialNormSq ρ D ≤
      (∑ j : Fin (N+1), (Fintype.card (DerivativeWord2 j.val) : ℝ)) * A^2 := by
  unfold factorialNormSq derivativeNormSq
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro j _
  rw [Finset.mul_sum]
  calc
    (∑ w : DerivativeWord2 j.val, ρ^(2*j.val)/(j.val.factorial : ℝ)^2 * ‖D ⟨j,w⟩‖^2) ≤
        ∑ _w : DerivativeWord2 j.val, A^2 := by
      apply Finset.sum_le_sum
      intro w _
      have hsq : (ρ^j.val * ‖D ⟨j,w⟩‖)^2 ≤ A^2 := by
        simpa only [pow_two] using mul_self_le_mul_self
          (mul_nonneg (pow_nonneg hρ _) (norm_nonneg _)) (hD ⟨j,w⟩)
      have hfac : 1 ≤ (j.val.factorial : ℝ)^2 := by
        have hf : (1 : ℝ) ≤ (j.val.factorial : ℝ) := by exact_mod_cast Nat.succ_le_iff.mpr (Nat.factorial_pos j.val)
        exact one_le_pow₀ hf
      calc
        ρ^(2*j.val)/(j.val.factorial : ℝ)^2 * ‖D ⟨j,w⟩‖^2 =
            (ρ^j.val * ‖D ⟨j,w⟩‖)^2 / (j.val.factorial : ℝ)^2 := by
          rw [mul_pow, ← pow_mul, Nat.mul_comm j.val 2]
          ring
        _ ≤ A^2 / (j.val.factorial : ℝ)^2 := div_le_div_of_nonneg_right hsq (sq_nonneg _)
        _ ≤ A^2 := div_le_self (sq_nonneg _) hfac
    _ = (Fintype.card (DerivativeWord2 j.val) : ℝ) * A^2 := by
      simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- The finite-order reweighting uses only a two-column coefficient bound 2/r. -/
theorem paired_weighted_component_bound {m N : ℕ} (hm : m ≤ N)
    {r ρ M t d : ℝ} (hr : 0 < r) (hrρ : r ≤ ρ) (hM : 0 ≤ M) (ht : 0 ≤ t)
    (hd : d ≤ (2*(2/r))^m*M*t) :
    ρ^m*d ≤ 4^N*(ρ/r)^N*M*t := by
  have hρ : 0 ≤ ρ := hr.le.trans hrρ
  have hratio : 1 ≤ ρ/r := (one_le_div hr).mpr hrρ
  have hscale : 1 ≤ 4*(ρ/r) := (by norm_num : (1 : ℝ) ≤ 4).trans
    (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio (by norm_num : (0 : ℝ) ≤ 4))
  calc
    ρ^m*d ≤ ρ^m*((2*(2/r))^m*M*t) := mul_le_mul_of_nonneg_left hd (pow_nonneg hρ _)
    _ = (4*(ρ/r))^m*M*t := by
      have heq : ρ*(2*(2/r)) = 4*(ρ/r) := by ring
      rw [← mul_assoc, ← mul_assoc, ← mul_pow, heq]
    _ ≤ (4*(ρ/r))^N*M*t :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hscale hm) hM) ht
    _ = 4^N*(ρ/r)^N*M*t := by rw [mul_pow]

/-- Actual paired factorial gain from L²; its constants precede matrices and value spaces. -/
theorem exists_paired_L2_factorial_gain_torus {κ : Vec 2 → ℝ}
    (hc : HasCompactSupport κ) (hd : ContDiff ℝ (⊤ : ℕ∞) κ) (N : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E],
      ∀ (R S : Vec 2 ≃L[ℝ] Vec 2) (cH cV : Fin 2 → ℝ)
        (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
        (r ρ : ℝ), 0 < r → r ≤ ρ → (∀ i, |cH i| ≤ 2/r) → (∀ i, |cV i| ≤ 2/r) →
      ∀ f : L2 E torusMeasure,
      Real.sqrt (factorialNormSq ρ (pairedWeakSmoothingTorus (K := N) R S κ hc hd cH cV hcoeff f).val) ≤
        D * (ρ/r)^N * ‖f‖ := by
  obtain ⟨M, hM, hbound⟩ := exists_uniform_paired_word_bound_torus hc hd N
  let Q : ℝ := ∑ j : Fin (N+1), (Fintype.card (DerivativeWord2 j.val) : ℝ)
  have hQ : 0 ≤ Q := Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
  refine ⟨Real.sqrt Q * 4^N * M, by positivity, ?_⟩
  intro E _ _ _ _ _ R S cH cV hcoeff r ρ hr hrρ hH hV f
  have hρ : 0 ≤ ρ := hr.le.trans hrρ
  let A : ℝ := 4^N*(ρ/r)^N*M*‖f‖
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hcomponent : ∀ a : JetIndex 2 N,
      ρ^a.1.val * ‖(pairedWeakSmoothingTorus (K := N) R S κ hc hd cH cV hcoeff f).val a‖ ≤ A := by
    intro a
    change ρ^a.1.val * ‖torusToCell (transverseCoordinateFamily
      (fun p q => pairedAxisAverageTorus R S κ hc hd (basisVec 0) (basisVec 1) p q f)
      cH cV a.1.val a.2 0 0)‖ ≤ A
    rw [torusToCell.norm_map]
    exact paired_weighted_component_bound (Nat.le_of_lt_succ a.1.isLt) hr hrρ hM (norm_nonneg f)
      (hbound E R S cH cV (2/r) (by positivity) hH hV a.1.val a.2 (Nat.le_of_lt_succ a.1.isLt) f)
  have hs := factorialNormSq_le_uniform_weighted_components
    (pairedWeakSmoothingTorus (K := N) R S κ hc hd cH cV hcoeff f).val hρ hcomponent
  calc
    Real.sqrt (factorialNormSq ρ (pairedWeakSmoothingTorus (K := N) R S κ hc hd cH cV hcoeff f).val) ≤
        Real.sqrt (Q*A^2) := Real.sqrt_le_sqrt hs
    _ = Real.sqrt Q * A := by rw [Real.sqrt_mul hQ, Real.sqrt_sq hA]
    _ = (Real.sqrt Q * 4^N * M)*(ρ/r)^N*‖f‖ := by dsimp only [A]; ring
end

/-! Uniform arbitrary finite-order factorial gain for the literal paired kernel. -/

/-- Constants precede both ellipse transports and the finite Hilbert value carrier. -/
theorem exists_paired_factorial_gain_torus {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) (K L : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E],
      ∀ (R S : Vec 2 ≃L[ℝ] Vec 2) (cH cV : Fin 2 → ℝ)
        (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
        (r ρ : ℝ), 0 < r → r ≤ ρ → (∀ i, |cH i| ≤ 2/r) → (∀ i, |cV i| ≤ 2/r) →
      ∀ f : TorusHk K E,
      Real.sqrt (factorialNormSq ρ (pairedWeakSmoothingTorus (K := L+K) R S (momentKernel φ₀ n)
        (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n) cH cV hcoeff
        (cellToTorus (f.val (valueIndex2 K)))).val) ≤
        D * (ρ/r)^L * Real.sqrt (factorialNormSq ρ f.val) := by
  have hκc := hasCompactSupport_momentKernel hc n
  have hκd := contDiff_momentKernel hc hd n
  have hφ : Integrable φ₀ := hd.continuous.integrable_of_hasCompactSupport hc
  obtain ⟨C, hC, hgain⟩ := exists_paired_L2_factorial_gain_torus hκc hκd L
  refine ⟨Real.sqrt (((L+K+1 : ℕ) : ℝ)*(1+C^2)), Real.sqrt_nonneg _, ?_⟩
  intro E _ _ _ _ _ _ R S cH cV hcoeff r ρ hr hrρ hH hV f
  have hρ : 0 ≤ ρ := hr.le.trans hrρ
  have hratio : 1 ≤ ρ/r := (one_le_div hr).mpr hrρ
  have hp : 1 ≤ (ρ/r)^L := one_le_pow₀ hratio
  let G := pairedWeakSmoothingTorus (K := L+K) R S (momentKernel φ₀ n) hκc hκd cH cV hcoeff
    (cellToTorus (f.val (valueIndex2 K)))
  have hf : 0 ≤ factorialNormSq ρ f.val := factorialNormSq_nonneg ρ _
  have hlo : factorialNormSq ρ (truncateTorusHk (Nat.le_add_left K L) G).val ≤ factorialNormSq ρ f.val := by
    rw [truncate_pairedWeakSmoothingTorus]
    exact (periodicWeakAverage_momentKernel_factorialNormSq R.toLinearEquiv.toAddHom R.continuous hφ hnonneg hmass n ρ _).trans
      (periodicWeakAverage_momentKernel_factorialNormSq S.toLinearEquiv.toAddHom S.continuous hφ hnonneg hmass n ρ f)
  have hfamily : (∑ w : DerivativeWord2 K, factorialNormSq ρ (derivativeJet w G.val)) ≤
      (C*(ρ/r)^L)^2 * derivativeNormSq f.val ⟨K, Nat.lt_succ_self K⟩ := by
    unfold derivativeNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro w _
    have hv := hgain E R S cH cV hcoeff r ρ hr hrρ hH hV
      (cellToTorus (f.val ⟨⟨K, Nat.lt_succ_self K⟩, w⟩))
    rw [cellToTorus.norm_map] at hv
    have hs : (Real.sqrt (factorialNormSq ρ (derivativeTorusHk w G).val))^2 ≤
        (C*(ρ/r)^L*‖f.val ⟨⟨K, Nat.lt_succ_self K⟩, w⟩‖)^2 := by
      apply (sq_le_sq₀ (Real.sqrt_nonneg _) (by positivity)).mpr
      change Real.sqrt (factorialNormSq ρ (derivativeTorusHk w
        (pairedWeakSmoothingTorus (K := L+K) R S (momentKernel φ₀ n) hκc hκd cH cV hcoeff
          (cellToTorus (f.val (valueIndex2 K))))).val) ≤ _
      rw [derivative_pairedWeakSmoothing_torus]
      exact hv
    rw [Real.sq_sqrt (factorialNormSq_nonneg ρ _), mul_pow] at hs
    exact hs
  have htop := factorialNormSq_order_le f.val ρ hρ ⟨K, Nat.lt_succ_self K⟩
  have hhi : (ρ^(2*K)/(K.factorial : ℝ)^2) *
      (∑ w : DerivativeWord2 K, factorialNormSq ρ (derivativeJet w G.val)) ≤
      (C*(ρ/r)^L)^2 * factorialNormSq ρ f.val := by
    calc
      _ ≤ (ρ^(2*K)/(K.factorial : ℝ)^2) *
          ((C*(ρ/r)^L)^2 * derivativeNormSq f.val ⟨K, Nat.lt_succ_self K⟩) :=
        mul_le_mul_of_nonneg_left hfamily (by positivity)
      _ = (C*(ρ/r)^L)^2 *
          (ρ^(2*K)/(K.factorial : ℝ)^2 * derivativeNormSq f.val ⟨K, Nat.lt_succ_self K⟩) := by ring
      _ ≤ (C*(ρ/r)^L)^2 * factorialNormSq ρ f.val :=
        mul_le_mul_of_nonneg_left htop (sq_nonneg _)
  have hsq : factorialNormSq ρ G.val ≤
      (((L+K+1 : ℕ) : ℝ)*(1+C^2))*((ρ/r)^L * Real.sqrt (factorialNormSq ρ f.val))^2 := by
    have hs := (factorialNormSq_split_le G.val ρ hρ).trans
      (mul_le_mul_of_nonneg_left (add_le_add hlo hhi) (Nat.cast_nonneg _))
    have hb : factorialNormSq ρ f.val ≤ ((ρ/r)^L)^2 * factorialNormSq ρ f.val :=
      le_mul_of_one_le_left hf (one_le_pow₀ hp)
    have hh := add_le_add hb (le_refl ((C*(ρ/r)^L)^2 * factorialNormSq ρ f.val))
    have hx := hs.trans (mul_le_mul_of_nonneg_left hh (Nat.cast_nonneg _))
    rw [mul_pow, Real.sq_sqrt hf]
    convert hx using 1
    ring
  calc
    Real.sqrt (factorialNormSq ρ G.val) ≤
        Real.sqrt ((((L+K+1 : ℕ) : ℝ)*(1+C^2))*((ρ/r)^L * Real.sqrt (factorialNormSq ρ f.val))^2) :=
      Real.sqrt_le_sqrt hsq
    _ = Real.sqrt (((L+K+1 : ℕ) : ℝ)*(1+C^2))*(ρ/r)^L*Real.sqrt (factorialNormSq ρ f.val) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), mul_assoc]

/-- Constants precede both ellipse transports and the finite Hilbert value carrier. -/
theorem exists_paired_factorial_gain_orders_torus {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1) (n : ℕ+) (K N : ℕ) (hKN : K ≤ N) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E],
      ∀ (R S : Vec 2 ≃L[ℝ] Vec 2) (cH cV : Fin 2 → ℝ)
        (hcoeff : ∀ i, cH i • R (basisVec 0) + cV i • S (basisVec 1) = basisVec i)
        (r ρ : ℝ), 0 < r → r ≤ ρ → (∀ i, |cH i| ≤ 2/r) → (∀ i, |cV i| ≤ 2/r) →
      ∀ f : TorusHk K E,
      Real.sqrt (factorialNormSq ρ (pairedWeakSmoothingTorus (K := N) R S (momentKernel φ₀ n)
        (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n) cH cV hcoeff
        (cellToTorus (f.val (valueIndex2 K)))).val) ≤
        D * (ρ/r)^(N-K) * Real.sqrt (factorialNormSq ρ f.val) := by
  generalize hL : N-K = L at *
  have hN : L+K = N := by rw [← hL]; exact Nat.sub_add_cancel hKN
  subst N
  exact exists_paired_factorial_gain_torus hc hd hnonneg hmass n K L

end AVRegularity.Analysis.Convolution
end
end
end

section
@[expose] public section
noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
namespace AVRegularity.Analysis.Convolution

/-! Moment integration of the sharp Taylor remainder with the genuine Euclidean matrix norm. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

theorem norm_integral_momentKernel_smooth_error_le {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, ‖coordinateHilbertEquiv.symm z‖ ≤ 1)
    (n : ℕ+) {K : ℕ} (hK : 0 < K) (hKn : K ≤ 2*(n:ℕ))
    {F : Vec 2 → E} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (C : ℝ) (hCpos : 0 ≤ C)
    (hC : ∀ x v, ‖iteratedFDeriv ℝ K F x (fun _ => v)‖ ≤ ‖coordinateHilbertEquiv.symm v‖^K * C)
    (T : HilbertTwo →L[ℝ] HilbertTwo) :
    ‖(∫ z : Vec 2, momentKernel φ₀ n z • F (-spatialHilbertOperator T z)) - F 0‖ ≤
      (∫ z : Vec 2, ‖momentKernel φ₀ n z‖) * (‖T‖^K * C / (K.factorial : ℝ)) := by
  let q := momentKernel φ₀ n
  let H := -spatialHilbertOperator T
  let P := fun z : Vec 2 => ∑ k ∈ Finset.range K, (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => H z)
  have hqc := hasCompactSupport_momentKernel hc n
  have hq := (contDiff_momentKernel hc hd n).continuous
  have hiF : Integrable (fun z : Vec 2 => q z • F (H z)) :=
    (hq.smul (hF.continuous.comp H.continuous)).integrable_of_hasCompactSupport hqc.smul_right
  have hiP : Integrable (fun z : Vec 2 => q z • P z) := by
    change Integrable (fun z : Vec 2 => q z • ∑ k ∈ Finset.range K, (k.factorial : ℝ)⁻¹ • iteratedFDeriv ℝ k F 0 (fun _ => H z))
    simp_rw [Finset.smul_sum]
    exact integrable_finsetSum (Finset.range K) (fun k _ => integrable_momentKernel_taylor_term hc hd n F H k)
  have hp : (∫ z : Vec 2, q z • P z) = F 0 :=
    integral_momentKernel_taylor_polynomial hc hd hmass n hK hKn F H
  have he : (∫ z : Vec 2, q z • F (H z)) - F 0 = ∫ z : Vec 2, q z • (F (H z) - P z) := by
    simp_rw [smul_sub]
    rw [integral_sub hiF hiP, hp]
  change ‖(∫ z : Vec 2, q z • F (H z)) - F 0‖ ≤ _
  rw [he]
  calc
    ‖∫ z : Vec 2, q z • (F (H z) - P z)‖ ≤ ∫ z : Vec 2, ‖q z‖ * (‖T‖^K * C / (K.factorial : ℝ)) := by
      apply norm_integral_le_of_norm_le
        ((integrable_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n).norm.mul_const _)
      exact Filter.Eventually.of_forall fun z => by
        change ‖q z • (F (H z) - P z)‖ ≤ ‖q z‖ * (‖T‖^K * C / (K.factorial : ℝ))
        by_cases hz : q z = 0
        · simp only [hz, zero_smul, norm_zero, zero_mul, le_refl]
        · have hnorm : ‖coordinateHilbertEquiv.symm (H z)‖ ≤ ‖T‖ := by
            calc
              _ = ‖T (coordinateHilbertEquiv.symm z)‖ := by
                change ‖coordinateHilbertEquiv.symm (-spatialHilbertOperator T z)‖ = _
                rw [map_neg, norm_neg, spatialHilbertOperator_apply, coordinateHilbertEquiv.symm_apply_apply]
              _ ≤ ‖T‖ * ‖coordinateHilbertEquiv.symm z‖ := T.le_opNorm _
              _ ≤ ‖T‖ * 1 := mul_le_mul_of_nonneg_left (support_momentKernel_norm_le hsupp n z hz) (norm_nonneg _)
              _ = ‖T‖ := mul_one _
          rw [norm_smul]
          apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
          exact (norm_taylor_remainder_euclidean_le hF hK C hC (H z)).trans
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) hnorm _) hCpos) (Nat.cast_nonneg _))
    _ = _ := integral_mul_const _ _

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution Filter
open scoped Topology
namespace AVRegularity.Analysis.Convolution

/-! The source sharp moment-kernel approximation rate on actual weak Sobolev inputs. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem momentKernel_approximation_torus {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, ‖coordinateHilbertEquiv.symm z‖ ≤ 1)
    (n : ℕ+) {K : ℕ} (hK : 0 < K) (hKn : K < 2*(n:ℕ))
    (T : HilbertTwo →L[ℝ] HilbertTwo) (f : TorusHk K E) :
    ‖averagingOperator (torusQuotient.comp (spatialHilbertOperator T).toAddHom) (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous) (momentKernel φ₀ n)
        (integrable_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n)
        (cellToTorus (f.val (valueIndex2 K))) - cellToTorus (f.val (valueIndex2 K))‖ ≤
      (∫ z : Vec 2, ‖momentKernel φ₀ n z‖) *
        (‖T‖^K * Real.sqrt (derivativeNormSq f.val ⟨K, Nat.lt_succ_self K⟩) / (K.factorial : ℝ)) := by
  have hφ : Integrable φ₀ := hd.continuous.integrable_of_hasCompactSupport hc
  obtain ⟨R, hz⟩ := AVRegularity.Analysis.Convolution.exists_shrinking_linearEquiv
  let fm := fun m : ℕ => averagingOperator (torusQuotient.comp (R m).toLinearEquiv.toAddHom) (continuous_torusQuotient.comp (R m).continuous) φ₀ hφ
    (cellToTorus (f.val (valueIndex2 K)))
  let A := averagingOperator (E := E) (μ := torusMeasure) (torusQuotient.comp (spatialHilbertOperator T).toAddHom) (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous) (momentKernel φ₀ n) (integrable_momentKernel hφ n)
  have hlim : Tendsto fm atTop (𝓝 (cellToTorus (f.val (valueIndex2 K)))) := by
    apply tendsto_averagingOperator_of_tendsto_zero
      (fun m => torusQuotient.comp (R m).toLinearEquiv.toAddHom)
      (fun m => continuous_torusQuotient.comp (R m).continuous) _ hφ hmass
    intro z
    change Tendsto (fun m => torusQuotient ((R m).toLinearEquiv.toAddHom z)) atTop (𝓝 0)
    simpa only [Function.comp_def, map_zero] using (continuous_torusQuotient.tendsto 0).comp (hz z)
  have herr := (((A.continuous.tendsto _).comp hlim).sub hlim).norm
  apply le_of_tendsto herr
  exact Eventually.of_forall fun m => by
    let F := fun x : Vec 2 => translation (-torusQuotient x) (fm m)
    have hF : ContDiff ℝ (⊤ : ℕ∞) F := by
      exact contDiff_translation_average torusQuotient continuous_torusQuotient (R m) hc hd _
    have hb := norm_integral_momentKernel_smooth_error_le hc hd hmass hsupp n hK hKn.le hF
      (Real.sqrt (derivativeNormSq f.val ⟨K, Nat.lt_succ_self K⟩)) (Real.sqrt_nonneg _)
      (fun x v => iteratedFDeriv_positive_average_norm_le_torus (le_refl K) (R m) hc hd
        (Eventually.of_forall hnonneg) hmass f x v) T
    have he : (∫ z : Vec 2, momentKernel φ₀ n z • F (-spatialHilbertOperator T z)) = A (fm m) := by
      rw [averagingOperator_apply]
      apply integral_congr_ae
      exact Eventually.of_forall fun z => by
        change momentKernel φ₀ n z • translation (-torusQuotient (-spatialHilbertOperator T z)) (fm m) = _
        simp only [map_neg, neg_neg]
        rfl
    have h0 : F 0 = fm m := by simp only [F, map_zero, neg_zero, translation_zero]
    simpa only [he, h0, Function.comp_def] using hb

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
namespace AVRegularity.Analysis.Convolution

/-! Approximation of the literal composition of the two moment-kernel averages. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem norm_comp_sub_le (A B : F →L[ℝ] F) (hA : ‖A‖ ≤ 1) (f : F) :
    ‖A (B f) - f‖ ≤ ‖B f - f‖ + ‖A f - f‖ := by
  calc
    _ = ‖A (B f - f) + (A f - f)‖ := by rw [map_sub]; congr 1; abel
    _ ≤ ‖A (B f - f)‖ + ‖A f - f‖ := norm_add_le _ _
    _ ≤ ‖B f - f‖ + ‖A f - f‖ := by
      exact add_le_add (by simpa only [one_mul] using
        ContinuousLinearMap.le_of_opNorm_le A hA (B f-f)) le_rfl

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]

theorem momentKernel_paired_approximation_torus {φ₀ : Vec 2 → ℝ}
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, ‖coordinateHilbertEquiv.symm z‖ ≤ 1)
    (n : ℕ+) {K : ℕ} (hK : 0 < K) (hKn : K < 2*(n:ℕ))
    (T S : HilbertTwo →L[ℝ] HilbertTwo) (f : TorusHk K E) :
    ‖averagingOperator (E := E) (μ := torusMeasure) (torusQuotient.comp (spatialHilbertOperator T).toAddHom) (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous) (momentKernel φ₀ n)
        (integrable_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n) (averagingOperator (E := E) (μ := torusMeasure) (torusQuotient.comp (spatialHilbertOperator S).toAddHom) (continuous_torusQuotient.comp (spatialHilbertOperator S).continuous) (momentKernel φ₀ n)
        (integrable_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n) (cellToTorus (f.val (valueIndex2 K)))) - cellToTorus (f.val (valueIndex2 K))‖ ≤
      (∫ z : Vec 2, ‖momentKernel φ₀ n z‖) *
        ((‖S‖^K + ‖T‖^K) * Real.sqrt (derivativeNormSq f.val ⟨K, Nat.lt_succ_self K⟩) / (K.factorial : ℝ)) := by
  have hφ : Integrable φ₀ := hd.continuous.integrable_of_hasCompactSupport hc
  let A := averagingOperator (E := E) (μ := torusMeasure) (torusQuotient.comp (spatialHilbertOperator T).toAddHom) (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous) (momentKernel φ₀ n) (integrable_momentKernel hφ n)
  let B := averagingOperator (E := E) (μ := torusMeasure) (torusQuotient.comp (spatialHilbertOperator S).toAddHom) (continuous_torusQuotient.comp (spatialHilbertOperator S).continuous) (momentKernel φ₀ n) (integrable_momentKernel hφ n)
  have hA : ‖A‖ ≤ 1 := averagingOperator_momentKernel_contraction (E := E) (μ := torusMeasure) (torusQuotient.comp (spatialHilbertOperator T).toAddHom) (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous) hφ hnonneg hmass n
  have hT := momentKernel_approximation_torus hc hd hnonneg hmass hsupp n hK hKn T f
  have hS := momentKernel_approximation_torus hc hd hnonneg hmass hsupp n hK hKn S f
  change ‖A (B (cellToTorus (f.val (valueIndex2 K)))) - cellToTorus (f.val (valueIndex2 K))‖ ≤ _
  calc
    _ ≤ ‖B (cellToTorus (f.val (valueIndex2 K))) - cellToTorus (f.val (valueIndex2 K))‖ + ‖A (cellToTorus (f.val (valueIndex2 K))) - cellToTorus (f.val (valueIndex2 K))‖ := norm_comp_sub_le A B hA _
    _ ≤ _ := (add_le_add hS hT).trans (le_of_eq (by ring))

end AVRegularity.Analysis.Convolution
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Analysis.Convolution

/-! The paired Taylor estimate in the source factorial Sobolev norm. -/

section
variable {E : Type*} [NormedAddCommGroup E] [mE : MeasurableSpace E]

 theorem top_derivative_factorial_norm_le {K : ℕ} {U : Set (Vec 2)}
    (D : JetL2 (volume.restrict U) K E) (ρ : ℝ) (hρ : 0 ≤ ρ) :
    ρ^K / (K.factorial : ℝ) *
      Real.sqrt (derivativeNormSq D ⟨K, Nat.lt_succ_self K⟩) ≤
      Real.sqrt (factorialNormSq ρ D) := by
  have h := Real.sqrt_le_sqrt
    (factorialNormSq_order_le D ρ hρ ⟨K, Nat.lt_succ_self K⟩)
  have hw : ρ^(2*K)/(K.factorial : ℝ)^2 =
      (ρ^K/(K.factorial : ℝ))^2 := by
    simp only [div_pow, ← pow_mul, Nat.mul_comm]
  rw [hw, Real.sqrt_mul (sq_nonneg _),
    Real.sqrt_sq (div_nonneg (pow_nonneg hρ _) (Nat.cast_nonneg _))] at h
  exact h

theorem top_derivative_scaled_le {K : ℕ} {U : Set (Vec 2)}
    {D : JetL2 (volume.restrict U) K E} (r ρ C : ℝ)
    (hr : 0 ≤ r) (hρ : 0 < ρ) (hC : 0 ≤ C) :
    (r*C)^K * Real.sqrt (derivativeNormSq D ⟨K, Nat.lt_succ_self K⟩) /
        (K.factorial : ℝ) ≤
      C^K * (r/ρ)^K * Real.sqrt (factorialNormSq ρ D) := by
  have h := mul_le_mul_of_nonneg_left
    (top_derivative_factorial_norm_le D ρ hρ.le)
    (mul_nonneg (pow_nonneg hC K) (pow_nonneg (div_nonneg hr hρ.le) K))
  have he : (r*C)^K * Real.sqrt (derivativeNormSq D ⟨K, Nat.lt_succ_self K⟩) /
      (K.factorial : ℝ) =
      C^K * (r/ρ)^K *
        (ρ^K / (K.factorial : ℝ) *
          Real.sqrt (derivativeNormSq D ⟨K, Nat.lt_succ_self K⟩)) := by
    rw [mul_pow, div_pow]
    field_simp
  exact he ▸ h

theorem paired_price_factorial_le {K : ℕ} {U : Set (Vec 2)}
    (D : JetL2 (volume.restrict U) K E) (r ρ C M t s : ℝ)
    (hr : 0 ≤ r) (hρ : 0 < ρ) (hC : 0 ≤ C) (hM : 0 ≤ M)
    (ht : 0 ≤ t) (hs : 0 ≤ s) (htC : t ≤ r*C) (hsC : s ≤ r*C) :
    M * ((s^K+t^K) *
      Real.sqrt (derivativeNormSq D ⟨K, Nat.lt_succ_self K⟩) /
      (K.factorial : ℝ)) ≤
      2 * M * C^K * (r/ρ)^K * Real.sqrt (factorialNormSq ρ D) := by
  have hp := add_le_add (pow_le_pow_left₀ hs hsC K) (pow_le_pow_left₀ ht htC K)
  have hfac : 0 ≤ (K.factorial : ℝ) := Nat.cast_nonneg _
  calc
    _ ≤ M * (((r*C)^K+(r*C)^K) *
        Real.sqrt (derivativeNormSq D ⟨K, Nat.lt_succ_self K⟩) /
        (K.factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_right hp (Real.sqrt_nonneg _)) hfac) hM
    _ = 2*M * ((r*C)^K *
        Real.sqrt (derivativeNormSq D ⟨K, Nat.lt_succ_self K⟩) /
        (K.factorial : ℝ)) := by ring
    _ ≤ 2*M * (C^K*(r/ρ)^K*Real.sqrt (factorialNormSq ρ D)) :=
      mul_le_mul_of_nonneg_left (top_derivative_scaled_le r ρ C hr hρ hC)
        (mul_nonneg (by norm_num) hM)
    _ = _ := by ring

variable {φ₀ : Vec 2 → ℝ}

theorem scaledSpatialEquiv_toAddHom_eq_spatialHilbertOperator
    (H : HilbertTwo ≃L[ℝ] HilbertTwo) {r : ℝ} (hr : r ≠ 0) :
    (scaledSpatialEquiv H r hr).toLinearEquiv.toAddHom =
      (spatialHilbertOperator (r • H.toContinuousLinearMap)).toAddHom := by
  ext x i
  change (scaledSpatialEquiv H r hr x) i =
    (spatialHilbertOperator (r • H.toContinuousLinearMap) x) i
  rw [scaledSpatialEquiv_apply]
  simp [spatialHilbertOperator]

omit mE in
theorem averagingOperator_torus_congr_map
    {ρ σ : Vec 2 →+ UnitAddTorus (Fin 2)}
    (hρ : ρ = σ) (hρc : Continuous ρ) (hσc : Continuous σ)
    {κ : Vec 2 → ℝ} (hκ : Integrable κ) [NormedSpace ℝ E] [CompleteSpace E] :
    averagingOperator (E := E) (μ := torusMeasure) ρ hρc κ hκ =
      averagingOperator (E := E) (μ := torusMeasure) σ hσc κ hκ := by
  subst σ
  have hp : hρc = hσc := Subsingleton.elim _ _
  subst hσc
  rfl

variable [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [FiniteDimensional ℝ E]

theorem momentKernel_paired_spatial_approximation_torus
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, ‖coordinateHilbertEquiv.symm z‖ ≤ 1)
    (n : ℕ+) {K : ℕ} (hK : 0 < K) (hKn : K < 2*(n:ℕ))
    (H₁ H₂ : HilbertTwo ≃L[ℝ] HilbertTwo) (V : HilbertTwo ≃L[ℝ] HilbertTwo)
    (h₁ : V (coordinateVector 0) = H₁ (coordinateVector 0))
    (h₂ : V (coordinateVector 1) = H₂ (coordinateVector 1))
    (r ρ C_H : ℝ) (hr : 0 < r) (hρ : 0 < ρ) (_hrρ : r ≤ ρ)
    (hC : 0 ≤ C_H) (hH₁ : ‖H₁.toContinuousLinearMap‖ ≤ C_H)
    (hH₂ : ‖H₂.toContinuousLinearMap‖ ≤ C_H)
    (f : TorusHk K E) :
    ‖(pairedWeakSmoothingTorus (K := K) (scaledSpatialEquiv H₁ r hr.ne')
      (scaledSpatialEquiv H₂ r hr.ne') (momentKernel φ₀ n)
      (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
      (fun i => inverseColumnCoeff V r i) (fun i => inverseRowCoeff V r i)
      (inverse_column_scaled_spatial_coefficients H₁ H₂ V h₁ h₂ hr)
      (cellToTorus (f.val (valueIndex2 K)))).val (valueIndex2 K) -
        f.val (valueIndex2 K)‖ ≤
      2 * (∫ z : Vec 2, ‖momentKernel φ₀ n z‖) * C_H^K *
        (r/ρ)^K * Real.sqrt (factorialNormSq ρ f.val) := by
  let R := scaledSpatialEquiv H₁ r hr.ne'
  let S := scaledSpatialEquiv H₂ r hr.ne'
  let T := r • H₁.toContinuousLinearMap
  let Q := r • H₂.toContinuousLinearMap
  let κ := momentKernel φ₀ n
  let hκ := integrable_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n
  let f₀ := cellToTorus (f.val (valueIndex2 K))
  let A := averagingOperator (E := E) (μ := torusMeasure)
    (torusQuotient.comp (spatialHilbertOperator T).toAddHom)
    (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous) κ hκ
  let B := averagingOperator (E := E) (μ := torusMeasure)
    (torusQuotient.comp (spatialHilbertOperator Q).toAddHom)
    (continuous_torusQuotient.comp (spatialHilbertOperator Q).continuous) κ hκ
  have hT : ‖T‖ ≤ r*C_H := by
    dsimp [T]
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_left hH₁ hr.le
  have hQ : ‖Q‖ ≤ r*C_H := by
    dsimp [Q]
    rw [norm_smul, Real.norm_of_nonneg hr.le]
    exact mul_le_mul_of_nonneg_left hH₂ hr.le
  have hval :
      (pairedWeakSmoothingTorus (K := K) R S κ (hasCompactSupport_momentKernel hc n)
        (contDiff_momentKernel hc hd n) (fun i => inverseColumnCoeff V r i)
        (fun i => inverseRowCoeff V r i)
        (inverse_column_scaled_spatial_coefficients H₁ H₂ V h₁ h₂ hr) f₀).val
      (valueIndex2 K) = torusToCell (A (B f₀)) := by
    rw [pairedWeakSmoothingTorus_value]
    have hR := scaledSpatialEquiv_toAddHom_eq_spatialHilbertOperator H₁ hr.ne'
    have hS := scaledSpatialEquiv_toAddHom_eq_spatialHilbertOperator H₂ hr.ne'
    have hR' : (R.toLinearEquiv.toAddHom : Vec 2 →+ Vec 2) =
        ((spatialHilbertOperator T).toAddHom : Vec 2 →+ Vec 2) :=
      congrArg (fun g : Vec 2 →ₙ+ Vec 2 => (g : Vec 2 →+ Vec 2)) hR
    have hS' : (S.toLinearEquiv.toAddHom : Vec 2 →+ Vec 2) =
        ((spatialHilbertOperator Q).toAddHom : Vec 2 →+ Vec 2) :=
      congrArg (fun g : Vec 2 →ₙ+ Vec 2 => (g : Vec 2 →+ Vec 2)) hS
    have hRt := congrArg (fun g : Vec 2 →+ Vec 2 => torusQuotient.comp g) hR'
    have hSt := congrArg (fun g : Vec 2 →+ Vec 2 => torusQuotient.comp g) hS'
    have hA := averagingOperator_torus_congr_map
      (ρ := torusQuotient.comp (R.toLinearEquiv.toAddHom : Vec 2 →+ Vec 2))
      (σ := torusQuotient.comp ((spatialHilbertOperator T).toAddHom : Vec 2 →+ Vec 2))
      (E := E) hRt
      (continuous_torusQuotient.comp R.continuous)
      (continuous_torusQuotient.comp (spatialHilbertOperator T).continuous) hκ
    have hB := averagingOperator_torus_congr_map
      (ρ := torusQuotient.comp (S.toLinearEquiv.toAddHom : Vec 2 →+ Vec 2))
      (σ := torusQuotient.comp ((spatialHilbertOperator Q).toAddHom : Vec 2 →+ Vec 2))
      (E := E) hSt
      (continuous_torusQuotient.comp S.continuous)
      (continuous_torusQuotient.comp (spatialHilbertOperator Q).continuous) hκ
    rw [hA, hB]
  have happrox := momentKernel_paired_approximation_torus hc hd hnonneg hmass hsupp n
    hK hKn T Q f
  change ‖A (B f₀) - f₀‖ ≤ _ at happrox
  have hM : 0 ≤ ∫ z : Vec 2, ‖κ z‖ := integral_nonneg (fun _ => norm_nonneg _)
  have hprice := paired_price_factorial_le (D := f.val) r ρ C_H
    (∫ z : Vec 2, ‖κ z‖) ‖Q‖ ‖T‖ hr.le hρ hC hM
    (norm_nonneg _) (norm_nonneg _) hQ hT
  have hzero : torusToCell f₀ = f.val (valueIndex2 K) := torusToCell_cellToTorus _
  calc
    _ = ‖torusToCell (A (B f₀)) - torusToCell f₀‖ := by rw [hval, hzero]
    _ = ‖A (B f₀) - f₀‖ := by
      rw [← map_sub]
      exact torusToCell.norm_map _
    _ ≤ (∫ z : Vec 2, ‖κ z‖) *
        ((‖Q‖^K + ‖T‖^K) *
          Real.sqrt (derivativeNormSq f.val ⟨K, Nat.lt_succ_self K⟩) /
          (K.factorial : ℝ)) := happrox
    _ ≤ 2 * (∫ z : Vec 2, ‖κ z‖) * C_H^K *
        (r/ρ)^K * Real.sqrt (factorialNormSq ρ f.val) := by
      simpa only [add_comm] using hprice
end

/-! The source paired smoother with its gain, contraction, and approximation
  estimates packaged on one ordered weak-jet output. -/

section
variable {φ₀ : Vec 2 → ℝ}

theorem exists_paired_source_smoothing_torus
    (hc : HasCompactSupport φ₀) (hd : ContDiff ℝ (⊤ : ℕ∞) φ₀)
    (hnonneg : ∀ z, 0 ≤ φ₀ z) (hmass : ∫ z, φ₀ z = 1)
    (hsupp : ∀ z ∈ Function.support φ₀, euclideanNorm z ≤ 1)
    (n : ℕ+) (K N : ℕ) (hKN : K ≤ N) (hK : 0 < K) (hKn : K < 2*(n:ℕ)) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
      [CompleteSpace E] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E],
      ∀ (H₁ H₂ V : HilbertTwo ≃L[ℝ] HilbertTwo)
        (h₁ : V (coordinateVector 0) = H₁ (coordinateVector 0))
        (h₂ : V (coordinateVector 1) = H₂ (coordinateVector 1))
        (_hV : ‖V.symm.toContinuousLinearMap‖ ≤ 2)
        (r ρ C_H : ℝ) (hr : 0 < r) (_hrρ : r ≤ ρ) (_hC : 0 ≤ C_H)
        (_hH₁ : ‖H₁.toContinuousLinearMap‖ ≤ C_H)
        (_hH₂ : ‖H₂.toContinuousLinearMap‖ ≤ C_H)
        (f : TorusHk K E),
      let R := scaledSpatialEquiv H₁ r hr.ne'
      let S := scaledSpatialEquiv H₂ r hr.ne'
      let cH := fun i => inverseColumnCoeff V r i
      let cV := fun i => inverseRowCoeff V r i
      let hcfs := inverse_column_scaled_spatial_coefficients H₁ H₂ V h₁ h₂ hr
      let G := pairedWeakSmoothingTorus (K := N) R S (momentKernel φ₀ n)
        (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
        cH cV hcfs (cellToTorus (f.val (valueIndex2 K)))
      Real.sqrt (factorialNormSq ρ G.val) ≤
          D * (ρ/r)^(N-K) * Real.sqrt (factorialNormSq ρ f.val) ∧
        Real.sqrt (factorialNormSq ρ (truncateTorusHk hKN G).val) ≤
          Real.sqrt (factorialNormSq ρ f.val) ∧
        ‖f.val (valueIndex2 K) - (truncateTorusHk hKN G).val (valueIndex2 K)‖ ≤
          2 * (∫ z : Vec 2, ‖momentKernel φ₀ n z‖) *
            C_H^K * (r/ρ)^K *
              Real.sqrt (factorialNormSq ρ f.val) := by
  obtain ⟨D, hD, hgain⟩ :=
    exists_paired_factorial_gain_orders_torus hc hd hnonneg hmass n K N hKN
  refine ⟨D, hD, ?_⟩
  intro E _ _ _ _ _ _ H₁ H₂ V h₁ h₂ _hV r ρ C_H hr _hrρ _hC _hH₁ _hH₂ f
  let R := scaledSpatialEquiv H₁ r hr.ne'
  let S := scaledSpatialEquiv H₂ r hr.ne'
  let cH := fun i => inverseColumnCoeff V r i
  let cV := fun i => inverseRowCoeff V r i
  let hcfs := inverse_column_scaled_spatial_coefficients H₁ H₂ V h₁ h₂ hr
  let G := pairedWeakSmoothingTorus (K := N) R S (momentKernel φ₀ n)
    (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
    cH cV hcfs (cellToTorus (f.val (valueIndex2 K)))
  have hcoeff := inverse_column_scaled_spatial_coefficients H₁ H₂ V h₁ h₂ hr
  have hcfs_bound : ∀ i, |cH i| ≤ 2/r ∧ |cV i| ≤ 2/r :=
    fun i => inverse_column_scaled_coefficients_bound V _hV hr i
  have hgain' := hgain E R S cH cV hcoeff r ρ hr _hrρ
    (fun i => (hcfs_bound i).1) (fun i => (hcfs_bound i).2) f
  have hcontract_sq :
      factorialNormSq ρ (truncateTorusHk hKN G).val ≤ factorialNormSq ρ f.val := by
    rw [truncate_pairedWeakSmoothingTorus]
    exact (periodicWeakAverage_momentKernel_factorialNormSq
      R.toLinearEquiv.toAddHom R.continuous
      (hd.continuous.integrable_of_hasCompactSupport hc)
      hnonneg hmass n ρ _).trans
      (periodicWeakAverage_momentKernel_factorialNormSq
        S.toLinearEquiv.toAddHom S.continuous
        (hd.continuous.integrable_of_hasCompactSupport hc)
        hnonneg hmass n ρ f)
  have happrox := momentKernel_paired_spatial_approximation_torus hc hd hnonneg hmass
    hsupp n hK hKn H₁ H₂ V h₁ h₂ r ρ C_H hr
    (lt_of_lt_of_le hr _hrρ) _hrρ _hC _hH₁ _hH₂ f
  have htruncate_value :
      (truncateTorusHk hKN G).val (valueIndex2 K) =
        (pairedWeakSmoothingTorus (K := K) R S (momentKernel φ₀ n)
          (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
          cH cV hcfs (cellToTorus (f.val (valueIndex2 K)))).val (valueIndex2 K) := by
    have hN := truncate_pairedWeakSmoothingTorus hKN R S
      (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
      cH cV hcfs f
    have hK := truncate_pairedWeakSmoothingTorus (Nat.le_refl K) R S
      (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
      cH cV hcfs f
    have hN0 := congrArg (fun q : TorusHk K E => q.val (valueIndex2 K)) hN
    have hK0 := congrArg (fun q : TorusHk K E => q.val (valueIndex2 K)) hK
    have hK0' :
        (pairedWeakSmoothingTorus (K := K) R S (momentKernel φ₀ n)
          (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
          cH cV hcfs (cellToTorus (f.val (valueIndex2 K)))).val (valueIndex2 K) =
          (periodicWeakAverage R.toLinearEquiv.toAddHom R.continuous (momentKernel φ₀ n)
            (integrable_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n)
            (periodicWeakAverage S.toLinearEquiv.toAddHom S.continuous (momentKernel φ₀ n)
              (integrable_momentKernel (hd.continuous.integrable_of_hasCompactSupport hc) n) f)).val
            (valueIndex2 K) := by
      simpa [truncateTorusHk_apply, truncateJetIndex, valueIndex2, valueIndex] using hK0
    simpa [G] using hN0.trans hK0'.symm
  have happrox' :
      ‖(pairedWeakSmoothingTorus (K := K) R S (momentKernel φ₀ n)
          (hasCompactSupport_momentKernel hc n) (contDiff_momentKernel hc hd n)
          cH cV hcfs (cellToTorus (f.val (valueIndex2 K)))).val (valueIndex2 K) -
          f.val (valueIndex2 K)‖ ≤
        2 * (∫ z : Vec 2, ‖momentKernel φ₀ n z‖) * C_H^K * (r/ρ)^K *
          Real.sqrt (factorialNormSq ρ f.val) := happrox
  refine ⟨hgain', Real.sqrt_le_sqrt hcontract_sq, ?_⟩
  rw [htruncate_value, norm_sub_rev]
  exact happrox'
end

end AVRegularity.Analysis.Convolution
end
end
end
end
