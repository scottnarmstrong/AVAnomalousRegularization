-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.EntryWeak.NativeLiftMetric
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
public import AVRegularity.Statements.Intermediate.CycleComparison.LiftApply
import AVRegularity.CycleReference.ChartDerivativeBounded
import AVRegularity.CycleComparison.Residual.QuietMean.FastIndep
public import AVRegularity.Statements.Intermediate.CycleComparison.SourceCoeff
public import AVRegularity.Definitions.Construction.Gen.ParShift
import AVRegularity.CycleComparison.Lift.PositiveFluxLiftCoefficientAction
public import AVRegularity.CycleComparison.Lift.FourierParameterJetContinuity
import Mathlib.Analysis.Calculus.ContDiff.Bounds

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Real parameter word jets use only their finite derivative reserve. -/

variable {U : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def realWordJet (f : U → E) (n : ℕ) (w : Fin n → U) (Y : U) : E :=
  iteratedFDeriv ℝ n f Y w

theorem realWordJet_derivative_cons (f : U → E) (n : ℕ)
    (w : Fin n → U) (v Y : U) :
    (fderiv ℝ (iteratedFDeriv ℝ n f) Y).flipMultilinear w v =
      realWordJet f (n + 1) (Fin.cons v w) Y := by
  change fderiv ℝ (iteratedFDeriv ℝ n f) Y v w =
    iteratedFDeriv ℝ (n + 1) f Y (Fin.cons v w)
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]

theorem finite_realWordJet_contDiff (f : U → E) (n r : ℕ)
    (hf : ContDiff ℝ ((n + r : ℕ) : ℕ∞) f) (w : Fin n → U) :
    ContDiff ℝ (r : ℕ∞) (realWordJet f n w) := by
  have hd : ContDiff ℝ (r : ℕ∞) (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show r + n ≤ n + r by omega))
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => U) E w).contDiff.comp hd

theorem finite_realWordJet_hasFDerivAt (f : U → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (w : Fin n → U) (Y : U) :
    HasFDerivAt (realWordJet f n w)
      ((fderiv ℝ (iteratedFDeriv ℝ n f) Y).flipMultilinear w) Y := by
  have hd : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + n ≤ n + 1 by omega))
  exact (hd.differentiable (by norm_num) Y).hasFDerivAt.continuousMultilinear_apply_const w

theorem finite_realWordJet_cons_eq_fderiv (f : U → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (w : Fin n → U) (v Y : U) :
    realWordJet f (n + 1) (Fin.cons v w) Y =
      fderiv ℝ (realWordJet f n w) Y v := by
  rw [(finite_realWordJet_hasFDerivAt f n hf w Y).fderiv]
  exact (realWordJet_derivative_cons f n w v Y).symm

theorem finite_realWordJet_derivative_bound (f : U → E) (n r : ℕ)
    (hf : ContDiff ℝ ((n + r : ℕ) : ℕ∞) f)
    (w : Fin n → U) (hw : ∀ i, ‖w i‖ ≤ 1) (Y : U) :
    ‖iteratedFDeriv ℝ r (realWordJet f n w) Y‖ ≤
      ‖iteratedFDeriv ℝ (n + r) f Y‖ := by
  induction n generalizing r Y with
  | zero =>
      have he : realWordJet f 0 w = f := by
        funext Z
        exact iteratedFDeriv_zero_apply _
      rw [he, zero_add]
  | succ n ih =>
      by_cases hr : r = 0
      · subst r
        simp only [norm_iteratedFDeriv_zero, Nat.add_zero]
        apply (ContinuousMultilinearMap.le_opNorm _ w).trans
        have hp : (∏ i, ‖w i‖) ≤ 1 := by
          exact (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun i _ => hw i)).trans_eq
            (by simp)
        exact (mul_le_mul_of_nonneg_left hp (norm_nonneg _)).trans_eq (mul_one _)
      · obtain ⟨u, w, rfl⟩ := Fin.exists_cons w
        have hlow : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f :=
          hf.of_le (by exact_mod_cast (show n + 1 ≤ n + 1 + r by omega))
        have he : realWordJet f (n + 1) (Fin.cons u w) =
            fun Z => fderiv ℝ (realWordJet f n w) Z u := by
          funext Z
          exact finite_realWordJet_cons_eq_fderiv f n hlow w u Z
        rw [he]
        have hbase : ContDiff ℝ ((n + (r + 1) : ℕ) : ℕ∞) f := by
          have heq : n + (r + 1) = n + 1 + r := by omega
          rw [heq]
          exact hf
        have hs := finite_realWordJet_contDiff f n (r + 1) hbase w
        have hd : ContDiff ℝ (r : ℕ∞) (fderiv ℝ (realWordJet f n w)) :=
          hs.fderiv_right (by exact_mod_cast (show r + 1 ≤ r + 1 by rfl))
        have hb := norm_iteratedFDeriv_clm_apply_const (c := u)
          (hd.contDiffAt (x := Y)) (n := r) (le_refl _)
        have hu : ‖u‖ ≤ 1 := by simpa using hw 0
        have hw' : ∀ i, ‖w i‖ ≤ 1 := fun i => by simpa using hw i.succ
        have hm := hb.trans (mul_le_mul_of_nonneg_right hu (norm_nonneg _))
        rw [one_mul, norm_iteratedFDeriv_fderiv] at hm
        have hi := ih (r + 1) hbase w hw' Y
        have hn : n + (r + 1) = n + 1 + r := by omega
        rw [hn] at hi
        exact hm.trans hi

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Actual coordinate words quantitatively control the full finite-dimensional derivative. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_coordinate_word_family_derivative_bound (d N : ℕ)
    (J : List (Fin d) → Vec d → E)
    (hc : ∀ w, w.length ≤ N → Continuous (J w))
    (hd : ∀ w, w.length < N → ∀ i Y,
      HasDerivAt (fun h : ℝ => J w (Y + h • basisVec i)) (J (i :: w) Y) 0)
    (B : ℝ) (hB : 0 ≤ B) (hb : ∀ w, w.length ≤ N → ∀ Y, ‖J w Y‖ ≤ B)
    (w : List (Fin d)) (r : ℕ) (hr : w.length + r ≤ N) (Y : Vec d) :
    ‖iteratedFDeriv ℝ r (J w) Y‖ ≤ (d : ℝ) ^ r * B := by
  induction r generalizing w Y with
  | zero => simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul] using hb w (by omega) Y
  | succ r ih =>
    have hreg := finite_coordinate_word_family_contDiff d N J hc hd w (r + 1) hr
    have hfd : ContDiff ℝ (r : ℕ∞) (fderiv ℝ (J w)) :=
      hreg.fderiv_right (by exact_mod_cast (show r + 1 ≤ r + 1 by rfl))
    have hnext (i : Fin d) : ContDiff ℝ (r : ℕ∞) (J (i :: w)) :=
      finite_coordinate_word_family_contDiff d N J hc hd (i :: w) r (by simp only [List.length_cons]; omega)
    have hdir (v : Vec d) : ‖iteratedFDeriv ℝ r (fun X => fderiv ℝ (J w) X v) Y‖ ≤
        ((d : ℝ) ^ (r + 1) * B) * ‖v‖ := by
      have he : (fun X => fderiv ℝ (J w) X v) = fun X => ∑ i, v i • J (i :: w) X := by
        funext X
        rw [(finiteContinuousPartials_hasFDerivAt d (J w) (fun i => J (i :: w))
          (hd w (by omega)) (fun i => hc (i :: w) (by simp only [List.length_cons]; omega)) X).fderiv]
        exact finiteCoordinateDerivative_apply d _ v
      rw [he, iteratedFDeriv_fun_sum_apply (fun i _ => ((hnext i).const_smul (v i)).contDiffAt)]
      calc
        ‖∑ i, iteratedFDeriv ℝ r (fun X => v i • J (i :: w) X) Y‖ ≤
            ∑ i, ‖iteratedFDeriv ℝ r (fun X => v i • J (i :: w) X) Y‖ := norm_sum_le _ _
        _ ≤ ∑ _i : Fin d, ‖v‖ * ((d : ℝ) ^ r * B) := by
          apply Finset.sum_le_sum
          intro i _
          rw [iteratedFDeriv_const_smul_apply' (hnext i).contDiffAt, norm_smul]
          exact mul_le_mul (norm_le_pi_norm v i)
            (ih (i :: w) (by simp only [List.length_cons]; omega) Y)
            (norm_nonneg _) (norm_nonneg _)
        _ = ((d : ℝ) ^ (r + 1) * B) * ‖v‖ := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, pow_succ]
          ring
    rw [← norm_iteratedFDeriv_fderiv]
    apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
    intro V
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by positivity) hB) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    intro v
    have he : (iteratedFDeriv ℝ r (fderiv ℝ (J w)) Y V) v =
        iteratedFDeriv ℝ r (fun X => fderiv ℝ (J w) X v) Y V := by
      change _ = iteratedFDeriv ℝ r ((ContinuousLinearMap.apply ℝ E v) ∘ fderiv ℝ (J w)) Y V
      rw [(ContinuousLinearMap.apply ℝ E v).iteratedFDeriv_comp_left hfd.contDiffAt le_rfl]
      rfl
    rw [he]
    exact ((ContinuousMultilinearMap.le_opNorm _ V).trans
      (mul_le_mul_of_nonneg_right (hdir v) (Finset.prod_nonneg fun _ _ => norm_nonneg _))).trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! Finite joint word jets restrict to genuine smooth affine coordinate slices. -/

variable {U V E : Type*}
  [NormedAddCommGroup U] [NormedSpace ℝ U]
  [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem finite_realWordJet_affine_derivative_bound (f : U → E) (n r : ℕ)
    (hf : ContDiff ℝ ((n + r : ℕ) : ℕ∞) f)
    (w : Fin n → U) (hw : ∀ i, ‖w i‖ ≤ 1)
    (L : V →L[ℝ] U) (hL : ‖L‖ ≤ 1) (a : U) (x : V) :
    ‖iteratedFDeriv ℝ r (fun y => realWordJet f n w (L y + a)) x‖ ≤
      ‖iteratedFDeriv ℝ (n + r) f (L x + a)‖ := by
  let g : U → E := fun y => realWordJet f n w (y + a)
  have hg : ContDiff ℝ (r : ℕ∞) g :=
    (finite_realWordJet_contDiff f n r hf w).comp (contDiff_id.add contDiff_const)
  have he : (fun y => realWordJet f n w (L y + a)) = g ∘ L := rfl
  rw [he, L.iteratedFDeriv_comp_right hg x (le_refl _)]
  have hb := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ r g (L x)) (fun _ : Fin r => L)
  have hp : (∏ _ : Fin r, ‖L‖) ≤ 1 :=
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L) (fun _ _ => hL)).trans_eq (by simp)
  have hm := hb.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  rw [mul_one] at hm
  have ht : iteratedFDeriv ℝ r g (L x) =
      iteratedFDeriv ℝ r (realWordJet f n w) (L x + a) :=
    iteratedFDeriv_comp_add_right r a (L x)
  rw [ht] at hm ⊢
  exact hm.trans (finite_realWordJet_derivative_bound f n r hf w hw (L x + a))

theorem finite_realWordJet_affine_eq (f : U → E) (n : ℕ)
    (hf : ContDiff ℝ (n : ℕ∞) f) (L : V →L[ℝ] U) (a : U)
    (w : Fin n → V) (x : V) :
    realWordJet (fun y => f (L y + a)) n w x =
      realWordJet f n (fun i => L (w i)) (L x + a) := by
  let g : U → E := fun y => f (y + a)
  have hg : ContDiff ℝ (n : ℕ∞) g := hf.comp (contDiff_id.add contDiff_const)
  change iteratedFDeriv ℝ n (g ∘ L) x w = _
  rw [L.iteratedFDeriv_comp_right hg x (le_refl _),
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  change iteratedFDeriv ℝ n g (L x) (fun i => L (w i)) = _
  rw [show iteratedFDeriv ℝ n g (L x) = iteratedFDeriv ℝ n f (L x + a) from
    iteratedFDeriv_comp_add_right n a (L x)]
  rfl

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Genuine finite real parameter derivatives preserve measurability. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem finite_independentParameterWordJet_measurable {S : Type*} [MeasurableSpace S]
    (f : S → P → E) (n : ℕ) :
    (∀ s, ContDiff ℝ (n : ℕ∞) (f s)) → (∀ Y, Measurable (fun s => f s Y)) →
    ∀ (w : Fin n → P) (Y : P),
      Measurable (fun s => realWordJet (f s) n w Y) := by
  induction n with
  | zero =>
      intro _ hm w Y
      simpa only [realWordJet, iteratedFDeriv_zero_apply] using hm Y
  | succ n ih =>
      intro hf hm w Y
      obtain ⟨u, w, rfl⟩ := Fin.exists_cons w
      have hsmall (s : S) : ContDiff ℝ (n : ℕ∞) (f s) :=
        (hf s).of_le (by exact_mod_cast (show n ≤ n + 1 by omega))
      let h : ℕ → ℝ := fun k => 1 / ((k : ℝ) + 1)
      have hseq : Tendsto h atTop (𝓝[≠] 0) := by
        apply tendsto_nhdsWithin_iff.mpr
        refine ⟨tendsto_one_div_add_atTop_nhds_zero_nat, ?_⟩
        exact Filter.Eventually.of_forall fun k => by
          change h k ≠ 0
          dsimp only [h]
          positivity
      apply measurable_of_tendsto_metrizable
        (f := fun k s => (h k)⁻¹ • (realWordJet (f s) n w (Y + h k • u) -
          realWordJet (f s) n w Y))
      · intro k
        exact (ih hsmall hm w (Y + h k • u)).sub (ih hsmall hm w Y) |>.const_smul _
      · apply tendsto_pi_nhds.mpr
        intro s
        have hL := finite_realWordJet_hasFDerivAt (f s) n (hf s) w Y
        have hline : HasDerivAt (fun a : ℝ => Y + a • u) u 0 := by
          simpa using ((hasDerivAt_id (0 : ℝ)).smul_const u).const_add Y
        have hd := hL.comp_hasDerivAt_of_eq 0 hline (by simp)
        have ht := hd.tendsto_slope_zero.comp hseq
        simpa only [Function.comp_def, zero_add, zero_smul, add_zero,
          realWordJet_derivative_cons] using ht

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Constant coarse-field amplitudes pass through the literal lift differential operator. -/

variable {ι : Type*} [Fintype ι]

theorem scalarLiftApply_coarse_smul (n : ℕ) (c : LiftCoeff ι (fun _ => ℝ))
    (f : Vec 2 → ι → ℝ) (hf : ContDiff ℝ (⊤ : ℕ∞) f) (a t : ℝ) (Y z : Vec 2) (v : ι) :
    liftApply n c (fun _ X => a • f X) t Y z v = a * liftApply n c (fun _ => f) t Y z v := by
  simp only [liftApply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α _
  have hd : orderedDerivative α (fun X => a • f X) =
      fun X => a • orderedDerivative α f X := by
    simpa only [smul_apply, ContinuousLinearMap.id_apply] using
      orderedDerivative_clm_comp (a • ContinuousLinearMap.id ℝ (ι → ℝ)) α
        (hf.of_le (by exact_mod_cast le_top))
  rw [hd, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro u _
  simp only [Pi.smul_apply]
  exact (c m α t Y z v u).map_smul a (orderedDerivative α f Y u)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Zeroth fast-jet fields retain exactly the joint smoothness and derivative norm of their readout. -/

variable {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem zero_fast_jet_field_contDiff (f : P → Vec 2 → E) (r : ℕ)
    (h : ContDiff ℝ (r : ℕ∞) (fun X : P × Vec 2 => iteratedFDeriv ℝ 0 (f X.1) X.2)) :
    ContDiff ℝ (r : ℕ∞) (Function.uncurry f) := by
  have hh := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Vec 2) E Fin.elim0).contDiff.comp h
  exact hh

theorem norm_joint_zero_fast_jet (f : P → Vec 2 → E) (r : ℕ) (X : P × Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X : P × Vec 2 => iteratedFDeriv ℝ 0 (f X.1) X.2) X‖ =
      ‖iteratedFDeriv ℝ r (Function.uncurry f) X‖ := by
  have he : (fun X : P × Vec 2 => iteratedFDeriv ℝ 0 (f X.1) X.2) =
      (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm ∘ Function.uncurry f := rfl
  rw [he]
  exact (continuousMultilinearCurryFin0 ℝ (Vec 2) E).symm.norm_iteratedFDeriv_comp_left _ X r

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Actual parameter words and fast jets uniformly control full joint derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coordinate_word_joint_derivative_bound (d N K : ℕ)
    (J : List (Fin d) → Vec d → Vec 2 → E)
    (hc : ∀ w, w.length ≤ N → ∀ n, n ≤ K →
      Continuous (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n (J w X.1) X.2))
    (hf : ∀ w, w.length ≤ N → ∀ Y, ContDiff ℝ (K : ℕ∞) (J w Y))
    (hd : ∀ w, w.length < N → ∀ n, n ≤ K → ∀ i Y z,
      HasDerivAt (fun h : ℝ => iteratedFDeriv ℝ n (J w (Y + h • basisVec i)) z)
        (iteratedFDeriv ℝ n (J (i :: w) Y) z) 0)
    (B : ℝ) (hB : 0 ≤ B)
    (hb : ∀ w, w.length ≤ N → ∀ n, n ≤ K → ∀ Y z, ‖iteratedFDeriv ℝ n (J w Y) z‖ ≤ B)
    (w : List (Fin d)) (r n : ℕ) (hN : w.length + r ≤ N) (hK : n + r ≤ K)
    (X : Vec d × Vec 2) :
    ‖iteratedFDeriv ℝ r (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n (J w X.1) X.2) X‖ ≤
      ((d : ℝ) + 1) ^ r * B := by
  induction r generalizing w n X with
  | zero => simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul] using hb w (by omega) n (by omega) X.1 X.2
  | succ r ih =>
    let F := fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n (J w X.1) X.2
    have hreg : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) F :=
      coordinate_word_joint_contDiff d N K J hc hf hd w (r + 1) n hN hK
    have hfd : ContDiff ℝ (r : ℕ∞) (fderiv ℝ F) :=
      hreg.fderiv_right (by exact_mod_cast (show r + 1 ≤ r + 1 by rfl))
    let C := fun q : Vec 2 [×n + 1]→L[ℝ] E => q.curryLeft
    have hC : @IsBoundedLinearMap ℝ (Vec 2 [×n + 1]→L[ℝ] E)
        (Vec 2 →L[ℝ] Vec 2 [×n]→L[ℝ] E)
        (inferInstance : NontriviallyNormedField ℝ).toNormedField.toField.toSemifield.toSemiring
        (inferInstance : NormedAddCommGroup (Vec 2 [×n + 1]→L[ℝ] E)).toSeminormedAddCommGroup
        (inferInstance : NormedSpace ℝ (Vec 2 [×n + 1]→L[ℝ] E)).toModule
        (inferInstance : NormedAddCommGroup (Vec 2 →L[ℝ] Vec 2 [×n]→L[ℝ] E)).toSeminormedAddCommGroup
        (inferInstance : NormedSpace ℝ (Vec 2 →L[ℝ] Vec 2 [×n]→L[ℝ] E)).toModule C := by
      refine { map_add := ?_, map_smul := ?_, bound := ⟨1, zero_lt_one, ?_⟩ }
      · intro x y; rfl
      · intro c x; rfl
      · intro q
        change ‖q.curryLeft‖ ≤ 1 * ‖q‖
        rw [ContinuousMultilinearMap.curryLeft_norm, one_mul]
    let Cmap := hC.toContinuousLinearMap
    have hnext (i : Fin d) : ContDiff ℝ (r : ℕ∞)
        (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ n (J (i :: w) X.1) X.2) :=
      coordinate_word_joint_contDiff d N K J hc hf hd (i :: w) r n
        (by simp only [List.length_cons]; omega) (by omega)
    have hfast : ContDiff ℝ (r : ℕ∞)
        (fun X : Vec d × Vec 2 => iteratedFDeriv ℝ (n + 1) (J w X.1) X.2) :=
      coordinate_word_joint_contDiff d N K J hc hf hd w r (n + 1) (by omega) (by omega)
    have hdir (V : Vec d × Vec 2) : ‖iteratedFDeriv ℝ r (fun Y => fderiv ℝ F Y V) X‖ ≤
        (((d : ℝ) + 1) ^ (r + 1) * B) * ‖V‖ := by
      let T := (ContinuousLinearMap.apply ℝ (Vec 2 [×n]→L[ℝ] E) V.2).comp Cmap
      have hT : ‖T‖ ≤ ‖V.2‖ := by
        apply ContinuousLinearMap.opNorm_le_bound T (norm_nonneg _)
        intro q
        change ‖q.curryLeft V.2‖ ≤ ‖V.2‖ * ‖q‖
        exact (q.curryLeft.le_opNorm V.2).trans_eq (by rw [ContinuousMultilinearMap.curryLeft_norm, mul_comm])
      have he : (fun Y => fderiv ℝ F Y V) = fun Y : Vec d × Vec 2 =>
          (∑ i, V.1 i • iteratedFDeriv ℝ n (J (i :: w) Y.1) Y.2) +
          T (iteratedFDeriv ℝ (n + 1) (J w Y.1) Y.2) := by
        funext Y
        have ha := finiteContinuousPartials_hasFDerivAt d
          (fun Z => iteratedFDeriv ℝ n (J w Z) Y.2)
          (fun i Z => iteratedFDeriv ℝ n (J (i :: w) Z) Y.2)
          (fun i Z => hd w (by omega) n (by omega) i Z Y.2)
          (fun i => (hc (i :: w) (by simp only [List.length_cons]; omega) n (by omega)).comp
            (continuous_id.prodMk continuous_const)) Y.1
        have hs : ContDiff ℝ 1 (iteratedFDeriv ℝ n (J w Y.1)) :=
          (hf w (by omega) Y.1).iteratedFDeriv_right (by exact_mod_cast (show 1 + n ≤ K by omega))
        have hh := joint_fderiv_apply_of_slice_derivatives d
          (fun Z z => iteratedFDeriv ℝ n (J w Z) z) Y _ _
          (hreg.differentiable (by norm_cast) Y) ha (hs.differentiable (by norm_num) Y.2).hasFDerivAt V
        change fderiv ℝ F Y V = _ at hh
        rw [hh, finiteCoordinateDerivative_apply, fderiv_iteratedFDeriv]
        rfl
      have hsum : ContDiff ℝ (r : ℕ∞) (fun Y : Vec d × Vec 2 =>
          ∑ i, V.1 i • iteratedFDeriv ℝ n (J (i :: w) Y.1) Y.2) :=
        ContDiff.sum fun i _ => (hnext i).const_smul (V.1 i)
      rw [he]
      change ‖iteratedFDeriv ℝ r ((fun Y : Vec d × Vec 2 =>
        ∑ i, V.1 i • iteratedFDeriv ℝ n (J (i :: w) Y.1) Y.2) +
        T ∘ (fun Y : Vec d × Vec 2 => iteratedFDeriv ℝ (n + 1) (J w Y.1) Y.2)) X‖ ≤ _
      rw [iteratedFDeriv_add_apply hsum.contDiffAt (T.contDiff.comp hfast).contDiffAt,
        iteratedFDeriv_fun_sum_apply (fun i _ => ((hnext i).const_smul (V.1 i)).contDiffAt),
        T.iteratedFDeriv_comp_left hfast.contDiffAt le_rfl]
      have hp : 0 ≤ ((d : ℝ) + 1) ^ r * B := mul_nonneg (by positivity) hB
      have hsumB : ‖∑ i, iteratedFDeriv ℝ r
          (fun Y : Vec d × Vec 2 => V.1 i • iteratedFDeriv ℝ n (J (i :: w) Y.1) Y.2) X‖ ≤
          (d : ℝ) * (‖V.1‖ * (((d : ℝ) + 1) ^ r * B)) := by
        apply (norm_sum_le _ _).trans
        calc
          _ ≤ ∑ _i : Fin d, ‖V.1‖ * (((d : ℝ) + 1) ^ r * B) := by
            apply Finset.sum_le_sum
            intro i _
            rw [iteratedFDeriv_const_smul_apply' (hnext i).contDiffAt, norm_smul]
            exact mul_le_mul (norm_le_pi_norm V.1 i)
              (ih (i :: w) n (by simp only [List.length_cons]; omega) (by omega) X)
              (norm_nonneg _) (norm_nonneg _)
          _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      have hfastB := (T.norm_compContinuousMultilinearMap_le _).trans
        (mul_le_mul hT (ih w (n + 1) (by omega) (by omega) X) (norm_nonneg _) (norm_nonneg _))
      calc
        _ ≤ _ := norm_add_le _ _
        _ ≤ (d : ℝ) * (‖V.1‖ * (((d : ℝ) + 1) ^ r * B)) +
            ‖V.2‖ * (((d : ℝ) + 1) ^ r * B) := add_le_add hsumB hfastB
        _ ≤ (d : ℝ) * (‖V‖ * (((d : ℝ) + 1) ^ r * B)) +
            ‖V‖ * (((d : ℝ) + 1) ^ r * B) := add_le_add
          (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right (norm_fst_le V) hp) (by positivity))
          (mul_le_mul_of_nonneg_right (norm_snd_le V) hp)
        _ = _ := by rw [pow_succ]; ring
    rw [← norm_iteratedFDeriv_fderiv]
    apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hB)
    intro U
    apply ContinuousLinearMap.opNorm_le_bound _
      (mul_nonneg (mul_nonneg (by positivity) hB) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
    intro V
    have he : (iteratedFDeriv ℝ r (fderiv ℝ F) X U) V =
        iteratedFDeriv ℝ r (fun Y => fderiv ℝ F Y V) X U := by
      change _ = iteratedFDeriv ℝ r ((ContinuousLinearMap.apply ℝ _ V) ∘ fderiv ℝ F) X U
      rw [(ContinuousLinearMap.apply ℝ _ V).iteratedFDeriv_comp_left hfd.contDiffAt le_rfl]
      rfl
    rw [he]
    exact ((ContinuousMultilinearMap.le_opNorm _ U).trans
      (mul_le_mul_of_nonneg_right (hdir V) (Finset.prod_nonneg fun _ _ => norm_nonneg _))).trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! The genuine fast derivative is the joint derivative restricted to fast directions. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jointFastDerivative (n : ℕ) (f : Vec 2 × Vec 2 → E)
    (X : Vec 2 × Vec 2) : ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) E :=
  (iteratedFDeriv ℝ n f X).compContinuousLinearMap
    (fun _ => ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))

theorem jointFastDerivative_eq (n : ℕ) (f : Vec 2 × Vec 2 → E)
    (hf : ContDiff ℝ (n : ℕ∞) f) (z Y : Vec 2) :
    iteratedFDeriv ℝ n (fun x => f (x, Y)) z = jointFastDerivative n f (z, Y) := by
  ext w
  have he := finite_realWordJet_affine_eq f n hf
    (ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)) (0, Y) w z
  simpa only [realWordJet, jointFastDerivative, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    ContinuousLinearMap.inl_apply, Prod.mk_add_mk, zero_add, add_zero] using he

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.EntryWeakProofs

/-! A scalar path matrix records its full product without a component-count factor. -/

open AVRegularity.CycleComparison.Lift

def weightedPathMatrix (h : ℕ) (θ : ℕ → ℝ) (v u : Fin (h + 1)) : ℝ :=
  if v.val = u.val + 1 then θ u.val else 0

theorem weightedPathMatrix_zero_row (h : ℕ) (θ : ℕ → ℝ) (u : Fin (h + 1)) :
    weightedPathMatrix h θ 0 u = 0 := by
  simp only [weightedPathMatrix, ite_eq_right
    (show ¬ (0 : Fin (h + 1)).val = u.val + 1 by simp only [Fin.val_zero]; omega)]

theorem weightedPathMatrix_positive_row (h : ℕ) (θ : ℕ → ℝ)
    (v : Fin (h + 1)) (hv : 0 < v.val) :
    weightedPathMatrix h θ v = fun u =>
      if u = (⟨v.val - 1, by omega⟩ : Fin (h + 1)) then θ (v.val - 1) else 0 := by
  funext u
  unfold weightedPathMatrix
  by_cases hu : u = (⟨v.val - 1, by omega⟩ : Fin (h + 1))
  · subst u
    have hn : v.val = (⟨v.val - 1, by omega⟩ : Fin (h + 1)).val + 1 := by
      dsimp only [Fin.val_mk]
      omega
    simp only [ite_eq_left hn, ite_true]
  · have hn : ¬ v.val = u.val + 1 := by
      intro he
      apply hu
      apply Fin.ext
      dsimp only [Fin.val_mk]
      omega
    simp only [ite_eq_right hn, ite_eq_right hu]

theorem weightedPathMatrix_power_column_zero (h : ℕ) (θ : ℕ → ℝ)
    (n : ℕ) (v : Fin (h + 1)) :
    finiteMatrixPower (weightedPathMatrix h θ) n v 0 =
      if v.val = n then ∏ j ∈ Finset.range n, θ j else 0 := by
  induction n generalizing v with
  | zero =>
      rw [finiteMatrixPower_zero]
      simp only [Finset.range_zero, Finset.prod_empty]
      have he : v = 0 ↔ v.val = 0 := Fin.ext_iff
      simp only [he]
  | succ n ih =>
      rw [finiteMatrixPower_succ]
      unfold finiteMatrixProduct
      by_cases hv : v.val = 0
      · have hv0 : v = 0 := Fin.ext hv
        subst v
        simp only [weightedPathMatrix_zero_row, zero_mul, Finset.sum_const_zero,
          ite_eq_right (show ¬ (0 : Fin (h + 1)).val = n + 1 by
            simp only [Fin.val_zero]; omega)]
      · have hvp : 0 < v.val := by omega
        rw [weightedPathMatrix_positive_row h θ v hvp]
        simp only [ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, ite_true]
        rw [ih]
        dsimp only [Fin.val_mk]
        by_cases hn : v.val = n + 1
        · have hp : v.val - 1 = n := by omega
          simp only [ite_eq_left hn, ite_eq_left hp]
          rw [hp, Finset.prod_range_succ]
          exact mul_comm _ _
        · have hp : ¬ v.val - 1 = n := by omega
          simp only [ite_eq_right hn, ite_eq_right hp, mul_zero]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! A finite joint reserve gives uniform slow control of genuine fast derivatives. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def jointFastRestrictionCLM (n : ℕ) :
    ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2 × Vec 2) E →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin n => Vec 2) E :=
  ContinuousMultilinearMap.compContinuousLinearMapL
    (fun _ => ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))

theorem jointFastRestrictionCLM_norm_le_one (n : ℕ) :
    ‖jointFastRestrictionCLM (E := E) n‖ ≤ 1 := by
  have hL : ‖ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2)‖ ≤ 1 := by
    apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    intro x
    simp only [ContinuousLinearMap.inl_apply, Prod.norm_def, norm_zero,
      max_eq_left (norm_nonneg x), one_mul]
    exact le_rfl
  exact (ContinuousMultilinearMap.norm_compContinuousLinearMapL_le E
    (fun _ : Fin n => ContinuousLinearMap.inl ℝ (Vec 2) (Vec 2))).trans
    ((Finset.prod_le_prod₀ (fun _ _ => norm_nonneg _) (fun _ _ => hL)).trans_eq (by simp))

theorem jointFastDerivative_contDiff (n r : ℕ) (f : Vec 2 × Vec 2 → E)
    (hf : ContDiff ℝ ((n + r : ℕ) : ℕ∞) f) :
    ContDiff ℝ (r : ℕ∞) (jointFastDerivative n f) := by
  have hd : ContDiff ℝ (r : ℕ∞) (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show r + n ≤ n + r by omega))
  exact (jointFastRestrictionCLM (E := E) n).contDiff.comp hd

theorem jointFastDerivative_fderiv_bound (n : ℕ) (f : Vec 2 × Vec 2 → E)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (X : Vec 2 × Vec 2) :
    ‖fderiv ℝ (jointFastDerivative n f) X‖ ≤ ‖iteratedFDeriv ℝ (n + 1) f X‖ := by
  have hd : ContDiff ℝ 1 (iteratedFDeriv ℝ n f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast (show 1 + n ≤ n + 1 by omega))
  have hb := (jointFastRestrictionCLM (E := E) n).norm_iteratedFDeriv_comp_left
    (hd.contDiffAt (x := X)) (n := 1) (by norm_num)
  rw [norm_iteratedFDeriv_one, norm_iteratedFDeriv_one, norm_fderiv_iteratedFDeriv] at hb
  exact hb.trans ((mul_le_mul_of_nonneg_right (jointFastRestrictionCLM_norm_le_one n)
    (norm_nonneg _)).trans_eq (one_mul _))

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public section
open Filter Topology
namespace AVRegularity.EntryWeakProofs

/-! Positive powers of the actual weak wavelengths vanish with the terminal level. -/

theorem weak_epsilon_tendsto_zero {q : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) :
    Tendsto (ocEpsilon q Λ) atTop (𝓝 0) := by
  have h := (CycleReference.epsilon_parent_tendsto_zero hq hΛ).comp
    (tendsto_add_atTop_nat 1)
  simpa only [Function.comp_def, Nat.add_sub_cancel] using h

theorem weak_epsilon_rpow_tendsto_zero {q p : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p) :
    Tendsto (fun m => ocEpsilon q Λ m ^ p) atTop (𝓝 0) := by
  have h := (Real.continuousAt_rpow_const 0 p (Or.inr hp.le)).tendsto.comp
    (weak_epsilon_tendsto_zero hq hΛ)
  simpa only [Real.zero_rpow hp.ne', Function.comp_def] using h

theorem weak_epsilon_rpow_eventually_small {q p : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p) {c : ℝ} (hc : 0 < c) :
    ∃ M : ℕ, ∀ m ≥ M, ocEpsilon q Λ m ^ p ≤ c := by
  have h := (weak_epsilon_rpow_tendsto_zero hq hΛ hp).eventually
    (gt_mem_nhds hc)
  obtain ⟨M, hM⟩ := eventually_atTop.1 h
  exact ⟨M, fun m hm => (hM m hm).le⟩

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization Set
namespace AVRegularity.EntryWeakProofs

/-! Genuine fast derivatives of slow difference quotients have a uniform joint-reserve budget. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem jointFastDerivative_slow_difference_bound (n : ℕ)
    (f : Vec 2 × Vec 2 → E) (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f)
    (C : ℝ) (hb : ∀ X, ‖iteratedFDeriv ℝ (n + 1) f X‖ ≤ C)
    (z X Y : Vec 2) :
    ‖jointFastDerivative n f (z, Y) - jointFastDerivative n f (z, X)‖ ≤ C * ‖Y - X‖ := by
  have hg : ContDiff ℝ 1 (jointFastDerivative n f) := jointFastDerivative_contDiff n 1 f hf
  have hbd (Z : Vec 2 × Vec 2) : ‖fderiv ℝ (jointFastDerivative n f) Z‖ ≤ C :=
    (jointFastDerivative_fderiv_bound n f hf Z).trans (hb Z)
  have hm := convex_univ.norm_image_sub_le_of_norm_fderiv_le
    (fun Z _ => (hg.differentiable (by norm_num)) Z) (fun Z _ => hbd Z)
    (mem_univ (z, X)) (mem_univ (z, Y))
  simpa only [Prod.mk_sub_mk, sub_self, Prod.norm_def, norm_zero,
    max_eq_right (norm_nonneg _)] using hm

theorem joint_fast_quotient_derivative_bound (n : ℕ) (f : Vec 2 × Vec 2 → E)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (C : ℝ)
    (hb : ∀ X, ‖iteratedFDeriv ℝ (n + 1) f X‖ ≤ C)
    (Y v z : Vec 2) (h : ℝ) (hh : h ≠ 0) :
    ‖iteratedFDeriv ℝ n (fun x => h⁻¹ • (f (x, Y + h • v) - f (x, Y))) z‖ ≤ C * ‖v‖ := by
  have hn : ContDiff ℝ (n : ℕ∞) f := hf.of_le (by exact_mod_cast (Nat.le_succ n))
  have hs (X : Vec 2) : ContDiff ℝ (n : ℕ∞) (fun x => f (x, X)) :=
    hn.comp₂ contDiff_id contDiff_const
  change ‖iteratedFDeriv ℝ n (h⁻¹ • ((fun x => f (x, Y + h • v)) -
    (fun x => f (x, Y)))) z‖ ≤ C * ‖v‖
  rw [iteratedFDeriv_const_smul_apply (𝕜 := ℝ) (a := h⁻¹) (x := z)
      (f := (fun x => f (x, Y + h • v)) - (fun x => f (x, Y))) ((hs (Y + h • v) |>.sub (hs Y)).contDiffAt),
    iteratedFDeriv_sub (hs (Y + h • v)) (hs Y), Pi.sub_apply,
    jointFastDerivative_eq n f hn, jointFastDerivative_eq n f hn, norm_smul,
    Real.norm_eq_abs, abs_inv]
  have hm := jointFastDerivative_slow_difference_bound n f hf C hb z Y (Y + h • v)
  have he : ‖Y + h • v - Y‖ = |h| * ‖v‖ := by
    simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]
  rw [he] at hm
  calc
    |h|⁻¹ * ‖jointFastDerivative n f (z, Y + h • v) - jointFastDerivative n f (z, Y)‖ ≤
        |h|⁻¹ * (C * (|h| * ‖v‖)) :=
      mul_le_mul_of_nonneg_left hm (inv_nonneg.mpr (abs_nonneg h))
    _ = C * ‖v‖ := by
      have ha : |h| ≠ 0 := abs_ne_zero.mpr hh
      field_simp

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.CycleComparison.Lift
namespace AVRegularity.EntryWeakProofs

/-! A finite coordinate synthesis recovers strong measurability of the full slow derivative. -/

variable {d : ℕ} {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

theorem finite_vec_eq_sum_basis (v : Vec d) : v = ∑ i, v i • basisVec i := by
  funext j
  simp [basisVec, Pi.single_apply]

theorem independent_fderiv_parameter_stronglyMeasurable (f : T → Vec d → E)
    (hm : ∀ x, Measurable (fun t => f t x)) (hd : ∀ t, Differentiable ℝ (f t))
    (x : Vec d) : StronglyMeasurable (fun t => fderiv ℝ (f t) x) := by
  let S := fun v : Fin d → E => ∑ q : Fin d,
    (ContinuousLinearMap.proj q : Vec d →L[ℝ] ℝ).smulRight (v q)
  have hS : Continuous S := by
    apply continuous_finsetSum
    intro q _
    exact (ContinuousLinearMap.smulRightL ℝ (Vec d) E
      (ContinuousLinearMap.proj q)).continuous.comp (continuous_apply q)
  have hv : StronglyMeasurable (fun t (q : Fin d) => fderiv ℝ (f t) x (basisVec q)) :=
    (measurable_pi_iff.mpr (fun q => fderiv_apply_parameter_measurable f hm hd x (basisVec q))).stronglyMeasurable
  have he : (fun t => fderiv ℝ (f t) x) =
      fun t => S (fun q => fderiv ℝ (f t) x (basisVec q)) := by
    funext t
    apply ContinuousLinearMap.ext
    intro ξ
    conv_lhs => rw [finite_vec_eq_sum_basis ξ]
    simp [S, map_smul, ContinuousLinearMap.smulRight_apply]
  rw [he]
  simpa only [Function.comp_def] using! hS.comp_stronglyMeasurable hv

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Empty high-order edge lists let the source use its effective order, independently of the ambient Dm. -/

variable {E : Type*} [AddCommMonoid E]

theorem sum_Icc_subtype_of_zero_above (K D : ℕ) (hKD : K ≤ D)
    (F : Finset.Icc 2 D → E) (hz : ∀ d, K < d.val → F d = 0) :
    (∑ d : Finset.Icc 2 D, F d) =
      ∑ d : Finset.Icc 2 K, F ⟨d.val, Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩ := by
  classical
  let f : ℕ → E := fun d => if hd : d ∈ Finset.Icc 2 D then F ⟨d, hd⟩ else 0
  have hsub : Finset.Icc 2 K ⊆ Finset.Icc 2 D := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hd).1, (Finset.mem_Icc.mp hd).2.trans hKD⟩
  calc
    _ = ∑ d : Finset.Icc 2 D, f d.val := by
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [f]
      rw [dite_eq_left d.property]
    _ = ∑ d ∈ Finset.Icc 2 D, f d := Finset.sum_attach _ f
    _ = ∑ d ∈ Finset.Icc 2 K, f d := by
      symm
      apply Finset.sum_subset hsub
      intro d hd hnot
      have hhigh : K < d := by
        have hlo := (Finset.mem_Icc.mp hd).1
        by_contra hn
        exact hnot (Finset.mem_Icc.mpr ⟨hlo, by omega⟩)
      dsimp only [f]
      rw [dite_eq_left hd]
      exact hz ⟨d, hd⟩ hhigh
    _ = ∑ d : Finset.Icc 2 K, f d.val := (Finset.sum_attach _ f).symm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro d _
      dsimp only [f]
      rw [dite_eq_left (hsub d.property)]

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.CycleComparison.Lift Filter Set
namespace AVRegularity.EntryWeakProofs

/-! Dominated slow-parameter integration with merely measurable time slices.
The differentiation argument is that of compact parameter integrals. -/

variable {d : ℕ} {T : Type*} [MeasurableSpace T]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [CompleteSpace E] in
theorem independent_parameter_integral_continuous (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec d → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hc : ∀ t, Continuous (f t)) (C : ℝ) (hb : ∀ t x, ‖f t x‖ ≤ C) :
    Continuous (fun x => ∫ t, f t x ∂μ) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply continuousAt_of_dominated
  · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · exact Eventually.of_forall (fun y => ae_of_all μ (fun t => hb t y))
  · exact integrable_const C
  · exact ae_of_all μ (fun t => (hc t).continuousAt)

omit [CompleteSpace E] in
theorem independent_parameter_integral_hasFDerivAt (μ : Measure T) [IsFiniteMeasure μ]
    (f : T → Vec d → E) (hm : ∀ x, Measurable (fun t => f t x))
    (hd : ∀ t, Differentiable ℝ (f t)) (C₀ C₁ : ℝ)
    (hb₀ : ∀ t x, ‖f t x‖ ≤ C₀)
    (hb₁ : ∀ t x, ‖fderiv ℝ (f t) x‖ ≤ C₁) (x : Vec d) :
    HasFDerivAt (fun y => ∫ t, f t y ∂μ)
      (∫ t, fderiv ℝ (f t) x ∂μ) x := by
  apply hasFDerivAt_integral_of_dominated_of_fderiv_le (s := univ)
    (μ := μ) (F := fun y t => f t y)
    (F' := fun y t => fderiv ℝ (f t) y)
    (bound := fun _ => C₁) (Filter.univ_mem)
  · exact Eventually.of_forall (fun y => (hm y).aestronglyMeasurable)
  · exact (integrable_const C₀).mono' (hm x).aestronglyMeasurable
      (ae_of_all μ (fun t => hb₀ t x))
  · exact (independent_fderiv_parameter_stronglyMeasurable f hm hd x).aestronglyMeasurable
  · exact ae_of_all μ (fun t y _ => hb₁ t y)
  · exact integrable_const C₁
  · exact ae_of_all μ (fun t y _ => (hd t y).hasFDerivAt)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Empty higher-degree edge lists allow the literal source operator to use a fixed effective cap. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]

def degreeRangeInclusion (K D : ℕ) (hKD : K ≤ D) :
    (Finset.Icc 2 K) ↪ (Finset.Icc 2 D) where
  toFun d := ⟨d.val, Finset.mem_Icc.mpr
    ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩
  inj' _ _ he := Subtype.ext (congrArg (fun d : Finset.Icc 2 D => d.val) he)

theorem sum_degreeRange_restrict {E : Type*} [AddCommMonoid E] {K D : ℕ}
    (hKD : K ≤ D) (f : Finset.Icc 2 D → E)
    (hz : ∀ d, K < d.val → f d = 0) :
    (∑ d : Finset.Icc 2 D, f d) =
      ∑ d : Finset.Icc 2 K, f (degreeRangeInclusion K D hKD d) := by
  classical
  let e := degreeRangeInclusion K D hKD
  have hs : (Finset.univ.map e).sum f = ∑ d : Finset.Icc 2 K, f (e d) :=
    Finset.sum_map _ _ _
  rw [← hs]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro d _ hd
  apply hz d
  by_contra! hle
  have he : e ⟨d.val, Finset.mem_Icc.mpr
      ⟨(Finset.mem_Icc.mp d.property).1, hle⟩⟩ = d := Subtype.ext rfl
  exact hd (Finset.mem_map.mpr ⟨_, Finset.mem_univ _, he⟩)
end

/-! The literal source ignores empty orders above the effective finite menu. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}

def restrictConstituentEdges (K : ℕ) (hKD : K ≤ D) (edge : ConstituentEdges D h) :
    ConstituentEdges K h := fun v u d => edge v u
      ⟨d.val, Finset.mem_Icc.mpr
        ⟨(Finset.mem_Icc.mp d.property).1, (Finset.mem_Icc.mp d.property).2.trans hKD⟩⟩

theorem sourceFlux_restrict_effective_order (K : ℕ) (hKD : K ≤ D)
    (edge : ConstituentEdges D h) (hz : ∀ v u d, K < d.val → edge v u d = [])
    (η ε t : ℝ) (f : Vec 2 → Vec 2 → ∀ i, h i) (k : Fin 2) :
    sourceFlux edge η ε t f k = sourceFlux (restrictConstituentEdges K hKD edge) η ε t f k := by
  funext X z v
  unfold sourceFlux
  apply Finset.sum_congr rfl
  intro u _
  apply sum_Icc_subtype_of_zero_above K D hKD
  intro d hd
  rw [hz v u d hd]
  rfl

theorem sourceCoeff_restrict_effective_order (K : ℕ) (hKD : K ≤ D)
    (edge : ConstituentEdges D h) (hz : ∀ v u d, K < d.val → edge v u d = [])
    (η t : ℝ) (j : ℕ) (f : Vec 2 → Vec 2 → ∀ i, h i) :
    sourceCoeff edge η j t f = sourceCoeff (restrictConstituentEdges K hKD edge) η j t f := by
  have he : (fun ε => sourceOp edge η ε t f) =
      fun ε => sourceOp (restrictConstituentEdges K hKD edge) η ε t f := by
    funext ε
    unfold sourceOp
    simp_rw [sourceFlux_restrict_effective_order K hKD edge hz]
  funext X z
  unfold sourceCoeff
  have hp : (fun ε => sourceOp edge η ε t f X z) =
      fun ε => sourceOp (restrictConstituentEdges K hKD edge) η ε t f X z := by
    exact congrArg (fun F => fun ε => F ε X z) he
  rw [hp]
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Coupled slow recentering and fast-phase translation preserve the appended child's flow. -/

theorem weak_child_phase_contrast (e : ℝ) (he : e ≠ 0) (Y h z δ : Vec 2) :
    (z + e⁻¹ • h + δ) - e⁻¹ • (Y + h + e • δ) = z - e⁻¹ • Y := by
  rw [smul_add, smul_add, inv_smul_smul₀ he]
  abel

theorem weak_childGeom_phase_shift_flow (D : OCData) (m : ℕ) (pc : ℤ) (a t : ℝ)
    (g : ChainGeom) (z h : Vec 2) (he : D.eps m ≠ 0) :
    (D.childGeom m pc a
      ⟨D.eps m • D.relDisp m pc a t (z + (D.eps m)⁻¹ • h),
        z + (D.eps m)⁻¹ • h + D.relDisp m pc a t (z + (D.eps m)⁻¹ • h)⟩
      (g.1, g.2.1 + h, g.2.2)).1 =
    (D.childGeom m pc a
      ⟨D.eps m • D.relDisp m pc a t z, z + D.relDisp m pc a t z⟩ g).1 := by
  funext u x r
  dsimp only [OCData.childGeom]
  rw [weak_child_phase_contrast (D.eps m) he]
  have hzero : z + D.relDisp m pc a t z -
      (D.eps m)⁻¹ • (g.2.1 + D.eps m • D.relDisp m pc a t z) =
      z - (D.eps m)⁻¹ • g.2.1 := by
    rw [smul_add, inv_smul_smul₀ he]
    abel
  rw [hzero]

/-! Reuse the proved mixed directional bounds for full joint source reserve production. -/

section
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem mixed_slow_direction_norm_le (a b : ℕ) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth (a + 1) b f) (v X z : Vec 2) :
    ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (fun w => fderiv ℝ (fun Y' => f Y' w) Y v) z) X‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ (a + 1) (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ :=
  CycleComparison.Lift.norm_mixed_slow_direction_le hf v X z

theorem mixed_fast_direction_norm_le (a b : ℕ) (f : Vec 2 → Vec 2 → E)
    (hf : IsBoxSmooth a (b + 1) f) (v X z : Vec 2) :
    ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b
      (fun w => fderiv ℝ (f Y) w v) z) X‖ ≤
      ‖v‖ * ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ (b + 1) (f Y) z) X‖ :=
  CycleComparison.Lift.norm_mixed_fast_direction_le hf v X z
end

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity
namespace AVRegularity.EntryWeakProofs

/-! Uniform mixed derivative bounds control the full joint derivative without additional premises. -/

universe u

theorem box_joint_derivative_bound (n : ℕ) : ∀ (E : Type u)
    [NormedAddCommGroup E] [NormedSpace ℝ E] (f : Vec 2 → Vec 2 → E)
    (_hf : IsBoxSmooth n n f) (M : ℝ) (_hM : 0 ≤ M)
    (_hb : ∀ a b, a + b ≤ n → ∀ X z,
      ‖iteratedFDeriv ℝ a (fun Y => iteratedFDeriv ℝ b (f Y) z) X‖ ≤ M)
    (X : Vec 2 × Vec 2),
    ‖iteratedFDeriv ℝ n (Function.uncurry f) X‖ ≤ 2 ^ n * M := by
  induction n with
  | zero =>
      intro E _ _ f hf M hM hb X
      simpa only [norm_iteratedFDeriv_zero, pow_zero, one_mul, Function.uncurry] using
        hb 0 0 (by omega) X.1 X.2
  | succ n ih =>
      intro E _ _ f hf M hM hb X
      have hj := hf.contDiff_uncurry le_rfl le_rfl
      have hfd : ContDiff ℝ (n : ℕ∞) (fderiv ℝ (Function.uncurry f)) :=
        hj.fderiv_right (by exact_mod_cast (show n + 1 ≤ n + 1 by rfl))
      have hdir (w : Vec 2 × Vec 2) :
          ‖iteratedFDeriv ℝ n (fun U => fderiv ℝ (Function.uncurry f) U w) X‖ ≤
            (2 ^ (n + 1) * M) * ‖w‖ := by
        let g₁ := fun Y z => fderiv ℝ (fun Y' => f Y' z) Y w.1
        let g₂ := fun Y z => fderiv ℝ (f Y) z w.2
        have he : (fun U => fderiv ℝ (Function.uncurry f) U w) =
            Function.uncurry g₁ + Function.uncurry g₂ := by
          funext U
          rw [(hf.hasFDerivAt_uncurry (by omega) (by omega) U).fderiv]
          rfl
        have h₁ : IsBoxSmooth n n g₁ := (hf.slowDir w.1).mono le_rfl (by omega)
        have h₂ : IsBoxSmooth n n g₂ := (hf.fastDir w.2).mono (by omega) le_rfl
        have hb₁ : ∀ a b, a + b ≤ n → ∀ Y z,
            ‖iteratedFDeriv ℝ a (fun Y' => iteratedFDeriv ℝ b (g₁ Y') z) Y‖ ≤ ‖w.1‖ * M := by
          intro a b hab Y z
          exact (mixed_slow_direction_norm_le a b f (hf.mono (by omega) (by omega)) w.1 Y z).trans
            (mul_le_mul_of_nonneg_left (hb (a + 1) b (by omega) Y z) (norm_nonneg _))
        have hb₂ : ∀ a b, a + b ≤ n → ∀ Y z,
            ‖iteratedFDeriv ℝ a (fun Y' => iteratedFDeriv ℝ b (g₂ Y') z) Y‖ ≤ ‖w.2‖ * M := by
          intro a b hab Y z
          exact (mixed_fast_direction_norm_le a b f (hf.mono (by omega) (by omega)) w.2 Y z).trans
            (mul_le_mul_of_nonneg_left (hb a (b + 1) (by omega) Y z) (norm_nonneg _))
        rw [he, iteratedFDeriv_add_apply (h₁.contDiff_uncurry le_rfl le_rfl).contDiffAt
          (h₂.contDiff_uncurry le_rfl le_rfl).contDiffAt]
        have hp : 0 ≤ (2 : ℝ) ^ n * M := mul_nonneg (by positivity) hM
        calc
          ‖_ + _‖ ≤ ‖iteratedFDeriv ℝ n (Function.uncurry g₁) X‖ +
              ‖iteratedFDeriv ℝ n (Function.uncurry g₂) X‖ := norm_add_le _ _
          _ ≤ 2 ^ n * (‖w.1‖ * M) + 2 ^ n * (‖w.2‖ * M) :=
            add_le_add (ih E g₁ h₁ _ (mul_nonneg (norm_nonneg _) hM) hb₁ X)
              (ih E g₂ h₂ _ (mul_nonneg (norm_nonneg _) hM) hb₂ X)
          _ = (2 ^ n * M) * ‖w.1‖ + (2 ^ n * M) * ‖w.2‖ := by ring
          _ ≤ (2 ^ n * M) * ‖w‖ + (2 ^ n * M) * ‖w‖ :=
            add_le_add (mul_le_mul_of_nonneg_left (norm_fst_le w) hp)
              (mul_le_mul_of_nonneg_left (norm_snd_le w) hp)
          _ = (2 ^ (n + 1) * M) * ‖w‖ := by rw [pow_succ]; ring
      rw [← norm_iteratedFDeriv_fderiv]
      apply ContinuousMultilinearMap.opNorm_le_bound (mul_nonneg (by positivity) hM)
      intro v
      apply ContinuousLinearMap.opNorm_le_bound _
        (mul_nonneg (mul_nonneg (by positivity) hM) (Finset.prod_nonneg fun _ _ => norm_nonneg _))
      intro w
      have he : (iteratedFDeriv ℝ n (fderiv ℝ (Function.uncurry f)) X v) w =
          iteratedFDeriv ℝ n (fun U => fderiv ℝ (Function.uncurry f) U w) X v := by
        change _ = iteratedFDeriv ℝ n
          ((ContinuousLinearMap.apply ℝ E w) ∘ fderiv ℝ (Function.uncurry f)) X v
        rw [(ContinuousLinearMap.apply ℝ E w).iteratedFDeriv_comp_left hfd.contDiffAt le_rfl]
        rfl
      rw [he]
      exact ((ContinuousMultilinearMap.le_opNorm _ v).trans
        (mul_le_mul_of_nonneg_right (hdir w) (Finset.prod_nonneg fun _ _ => norm_nonneg _))).trans_eq
          (by ring)

end AVRegularity.EntryWeakProofs
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Fixed scheduling metadata leave only the literal strict child-center conditions variable. -/

theorem weak_admissible_iff_child_centers_of_metadata (D : OCData) (bw : ℝ)
    (j₀ level : ℕ) (slot : ℤ) (A B : RealChain)
    (hA : IsAdmissibleChain D bw j₀ level slot A)
    (hb : B.baseLevel = A.baseLevel) (hs : B.slots = A.slots)
    (hl : B.children.length = A.children.length) :
    IsAdmissibleChain D bw j₀ level slot B ↔
      ∀ j : Fin B.children.length, ∑ i : Fin 2, |B.children[j].center i| <
        (1 + 2) * bw / 4 * D.eps (B.baseLevel + 1 + j) := by
  have hctx : B.ctxLevel = A.ctxLevel := by
    simp only [RealChain.ctxLevel, RealChain.lastLevel, hb, hl]
  have hslot : B.slot = A.slot := by simp only [RealChain.slot, hs]
  constructor
  · intro h j
    exact h.2.2.2.2.2.2 j.val j.is_lt
  · intro h
    refine ⟨hctx.trans hA.1, ?_, ?_, hslot.trans hA.2.2.2.1, ?_, ?_, ?_⟩
    · rw [hb]
      exact hA.2.1
    · rw [hs, hl]
      exact hA.2.2.1
    · rw [hs]
      exact hA.2.2.2.2.1
    · intro k hk
      simpa only [hb, hs] using hA.2.2.2.2.2.1 k (by simpa only [hs] using hk)
    · intro j hj
      exact h ⟨j, hj⟩

/-! Appending a scheduled child preserves the reserved carrier when its genuine center fits. -/

theorem weak_carrier_append_child (D : OCData) (bw mres : ℝ) (j₀ i : ℕ) (p slot : ℤ)
    (A : RealChain) (hA : IsCarrierChain D bw j₀ i p mres A) (hslot : Odd slot)
    (hs : IsScheduledIn D i slot p) (c : ChainChild)
    (hc : (∑ a : Fin 2, |c.center a|) < (1 + mres) * bw / 4 * D.eps i) :
    IsCarrierChain D bw j₀ (i + 1) slot mres
      {A with slots := A.slots ++ [slot], children := A.children ++ [c]} := by
  rcases hA with ⟨hlevel, hbase, hlen, hp, hodd, hsch, hcenters⟩
  have hsl : A.baseLevel + 1 + A.children.length = i := by
    simpa only [RealChain.ctxLevel, RealChain.lastLevel, Nat.add_assoc,
      Nat.add_comm, Nat.add_left_comm] using hlevel
  have hlast : A.slots[A.children.length] = p := by
    obtain ⟨sl, q, hq⟩ : ∃ sl q, A.slots = sl ++ [q] := by
      rcases List.eq_nil_or_concat A.slots with hn | ⟨sl, q, hq⟩
      · rw [hn] at hlen
        simp only [List.length_nil] at hlen
        omega
      · exact ⟨sl, q, by simpa only [List.concat_eq_append] using hq⟩
    have hcount : A.children.length = sl.length := by
      rw [hq] at hlen
      simp only [List.length_append, List.length_singleton] at hlen
      omega
    have hp' : q = p := by simpa only [RealChain.slot, hq, List.getLastD_concat] using hp
    simpa [hq, hcount] using hp'
  refine ⟨?_, hbase, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [RealChain.ctxLevel, RealChain.lastLevel, List.length_append, List.length_singleton]
    simp only [RealChain.ctxLevel, RealChain.lastLevel] at hlevel
    omega
  · simp only [List.length_append, List.length_singleton]
    omega
  · simp only [RealChain.slot, List.getLastD_concat]
  · intro q hq
    rcases List.mem_append.mp hq with hq | hq
    · exact hodd q hq
    · have hq' : q = slot := List.mem_singleton.mp hq
      subst q
      exact hslot
  · intro k hk
    have hk' : k + 1 < A.slots.length + 1 := by simpa only [List.length_append, List.length_singleton] using hk
    by_cases hlt : k + 1 < A.slots.length
    · simpa only [List.getElem_append_left hlt, List.getElem_append_left (by omega : k < A.slots.length)]
        using hsch k hlt
    · have hklen : k = A.children.length := by omega
      subst k
      simpa [hlen, hlast, hsl] using hs
  · intro k hk
    have hk' : k < A.children.length + 1 := by simpa only [List.length_append, List.length_singleton] using hk
    by_cases hlt : k < A.children.length
    · simpa only [List.getElem_append_left hlt] using hcenters k hlt
    · have hklen : k = A.children.length := by omega
      subst k
      simpa [hsl] using hc

end AVRegularity.EntryWeakProofs
end
end
