-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.PulseTailPeriodic
import AVRegularity.CycleComparison.Reconstruction.TailForceSlice
public import AVRegularity.CycleComparison.TailPresentation.ArraysProof
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleComparison.Reconstruction.LiftSource
public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableTail
import AVRegularity.CycleComparison.Reconstruction.Orders
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The parts of a pulse rest are continuous in the label**. At a window time, the label lift of a
coarse field of class `C^N` is continuous (`setting_labelLift_continuous`: it is a finite sum of
continuous coefficients applied to jets of order at most `N`), hence so is the mean part together
with the material part of a rest (`setting_restMean_lift_continuous`); the source part is `c` times
the label divergence of a `C¹` label edge flux (`setting_labelSourcePart_continuous`) and the tail
is `c` times the label divergence of the `C¹` tail flux plus the continuous cleanup remainders
(`setting_restTail_label_continuous`). These give the integrability needed to split the tested
rest into its parts. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- **The label lift of a `C^N` coarse field is continuous in the label** at a window time. -/
theorem setting_labelLift_continuous (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ) (g : ℝ → Vec 2 → ∀ i, h i)
    (ρs es : ℝ) {c t : ℝ} (hg : ContDiff ℝ (N : ℕ∞) (g (c⁻¹ * t)))
    (hs : c⁻¹ * t ∈ Icc a b) (v : ι) :
    Continuous (fun y => labelLift Cc N H ε g ρs es c t y v) := by
  simp only [labelLift_coeff_sum]
  refine continuous_finsetSum _ fun hh hhm => continuous_finsetSum _ fun n hn =>
    (continuous_finsetSum _ fun q _ => ?_).const_smul _
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
  have hnN : n ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hn)
  have hqn : q.1.val ≤ N := (Nat.lt_succ_iff.1 q.1.isLt).trans hnN
  have hbox := (hseq.2.2.2.2.2.1 hh hhh n q.1.val q.2.1 v q.2.2 (c⁻¹ * t) hs).1
  have hc : Continuous (fun y : Vec 2 =>
      Cc hh n q.1.val q.2.1 (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) v q.2.2) :=
    (CoarseFluxDiff.contDiff_sample hbox (Nat.zero_le _) (Nat.zero_le _) ρs es).continuous
  have hj0 : ContDiff ℝ ((0 : ℕ) : ℕ∞) (orderedDerivative q.2.1 (g (c⁻¹ * t))) :=
    ChartTransport.contDiff_orderedDerivative (p := 0) q.2.1
      (hg.of_le (by exact_mod_cast (show 0 + q.1.val ≤ N by omega)))
  have hj : Continuous (fun y : Vec 2 =>
      orderedDerivative q.2.1 (g (c⁻¹ * t)) (ρs⁻¹ • y) q.2.2) :=
    (continuous_apply q.2.2).comp (hj0.continuous.comp (continuous_const_smul ρs⁻¹))
  exact hc.clm_apply hj

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The mean part and the material part of a rest are continuous in the label.** -/
theorem setting_restMean_lift_continuous (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc) (ε : ℝ)
    (f df : ℝ → Vec 2 → ∀ i, h i) (ρs es : ℝ) {c t : ℝ} (hs : c⁻¹ * t ∈ Icc a b)
    (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t))) (hdf : ContDiff ℝ (N : ℕ∞) (df (c⁻¹ * t)))
    (v : ι) :
    Continuous (fun y => (restMean Q Cc N H ε f ρs es c t y +
      labelLift Cc N H ε df ρs es c t y) v) := by
  have hM : ContDiff ℝ (N : ℕ∞) (fun X => ∑ r ∈ Finset.range (H + 1),
      liftMeanPoly Q Cc N ε (fun _ => f (c⁻¹ * t)) r (c⁻¹ * t) X) :=
    ContDiff.sum fun r hr => setting_liftMeanPoly_contDiff P hsX hsZ hseq ε
      (Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)) _ hf hs
  have hfun : (fun y => (restMean Q Cc N H ε f ρs es c t y +
      labelLift Cc N H ε df ρs es c t y) v) =
      fun y => labelLift Cc N H ε (fun s X => df s X +
        ∑ r ∈ Finset.range (H + 1), liftMeanPoly Q Cc N ε (fun _ => f (c⁻¹ * t)) r s X)
        ρs es c t y v :=
    funext fun y => congrFun
      (setting_restMean_add_lift P sX sZ hsX hsZ Cc hseq ε f df ρs es c t hs hf hdf y) v
  refine (congrArg Continuous hfun).mpr ?_
  exact setting_labelLift_continuous sX sZ Cc hseq ε _ ρs es (hdf.add hM) hs v

section Source

variable {Pc : Type*} {Ctx : Pc → Type*}

include P in
/-- **The source part of a rest is continuous in the label.** -/
theorem setting_labelSourcePart_continuous (F : ChartedFamily ι h D Pc Ctx) (ν' e' E' : ℝ)
    (p₀ : Pc) (c₀ : Ctx p₀) {c lam' : ℝ} (hQe : Q.edge = liftEdges c lam' (F.fiber p₀ c₀))
    (hc : c ≠ 0) (he : e' ≠ 0) (hν : ν' ≠ 0) {ε ρs : ℝ}
    (hscale : Real.sqrt Q.η * ε = e' * ρs⁻¹) (hlam : lam' * ρs⁻¹ = E'⁻¹)
    (hsc : c⁻¹ * (e' * (e' / ν')) = 1) {sX sZ : ℕ} (hsZ : 1 ≤ sZ)
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (f : ℝ → Vec 2 → ∀ i, h i) {t : ℝ} (hf : ContDiff ℝ (⊤ : ℕ∞) (f (c⁻¹ * t)))
    (ht : c⁻¹ * t ∈ Set.Icc a b) (v : ι) :
    Continuous (fun y => labelSourcePart Q Cc N H ε f ρs e' c t y v) := by
  have h1 : ∀ y, labelSourcePart Q Cc N H ε f ρs e' c t y v =
      c • ∑ i₀ : Fin 2, fderiv ℝ (fun y' => labelEdgeFlux F ν' e' E' p₀ c₀ t
        (labelLift Cc N H ε f ρs e' c t) v y' i₀) y (basisVec i₀) := fun y => by
    rw [← source_part_label_div P F ν' e' E' p₀ c₀ hQe hc he hν hscale hlam hsc hsZ hseq f hf
      ht y v, smul_smul, mul_inv_cancel₀ hc, one_smul]
  simp only [h1]
  exact (continuous_finsetSum _ fun i₀ _ =>
    ((setting_labelEdgeFlux_labelLift_contDiff P F ν' e' E' p₀ c₀ hQe hc he hν hscale hlam hsZ
      hseq f hf ht v i₀).continuous_fderiv one_ne_zero).clm_apply continuous_const).const_smul c

end Source

include P in
/-- **The tail of a rest is continuous in the label.** -/
theorem setting_restTail_label_continuous (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc ≤ K + D + 2) (hZ : sZc ≤ max (k + 1) (L + 2)) (ε : ℝ) {c ρs es : ℝ}
    (hc : c ≠ 0) (hρ : ρs ≠ 0) (he : es ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vc : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ)
      (fun j => Vc hh j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) (hA : ContDiff ℝ (⊤ : ℕ∞) (A (c⁻¹ * t))) :
    Continuous (fun y => restTail Q Cc N H ε A ρs es c t y) := by
  have hbox := setting_tail_cleanupChain_box P sX sZ hsX hsZ Cc hseq hX hZ ε A Vc hV ht hA
  have h1 : ∀ y, restTail Q Cc N H ε A ρs es c t y =
      c • (∑ i₀ : Fin 2, fderiv ℝ (fun y' => tailFluxLabel H N Acl ε c ρs es Vc t y' i₀) y
          (basisVec i₀)
        + ∑ hh ∈ Finset.range (H + 1),
          c⁻¹ • ε ^ (N + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vc hh) t y) := fun y => by
    rw [← setting_restTail_label P sX sZ hsX hsZ Cc hseq sXc sZc Acl hAcl hXc hZc hX hZ ε hρ he
      A Vc hV ht hA y, smul_smul, mul_inv_cancel₀ hc, one_smul]
  simp only [h1]
  refine ((continuous_finsetSum _ fun i₀ _ =>
    ((contDiff_tailFluxLabel hXc hZc H N Acl ε c ρs es Vc t hbox i₀).continuous_fderiv
      one_ne_zero).clm_apply continuous_const).add
    (continuous_finsetSum _ fun hh hhm => ?_)).const_smul c
  exact ((continuous_cleanupRemainder_sample hAcl hXc c⁻¹ ρs es t
    (hbox hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)))).const_smul (ε ^ (N + 1))).const_smul
      c⁻¹

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Mixed slow/fast cell jets of the tail flux coefficient arrays**. An entry of the tail flux
array `tailFluxCoefficient` of order `1 ≤ m ≤ 2N+D` in the direction `par.rev` is the transverse
primitive `z ↦ P_Y(z par.rev)`, `P_Y = centeredIntervalPrimitive f_Y`, of the tail left entry along
the line `f_Y(r) = tailLeftCoefficient … Y (r • e)` (`e = basisVec par.rev`); all other entries
vanish.

* The empty fast word: the slow jets of `P_Y(z par.rev)` on the unit cell are bounded by
  `2 ^ (i + 1)` times the slow jets of the source
  (`parameter_centeredIntervalPrimitive_slow_norm_le`).
* A positive fast word `δ`: it vanishes unless every letter is `par.rev`, and then it is the
  constant `par.rev`-word of length `|δ| - 1` of the source at `(z par.rev) • e`
  (`orderedDerivative_transversePrimitiveField_succ`, `iteratedDeriv_line_eq`), whose slow jets are
  bounded by the mixed jets of the source (`norm_mixed_linear_profile_le`).

With the uniform mixed bounds of the tail left entries (`setting_tailEntry`) and the Schur budget of
the powers of the physical edge envelope, the mixed Schur jets of the tail flux arrays at one time
of the window are bounded by `tailMixedConst m' * Θ ^ hh`
(`setting_tailFluxCoefficient_mixed_schur`), uniformly by `tailMixedBound * Θ ^ hh`
(`setting_tailFluxCoefficient_mixed_jets`, the hypothesis `hjet` of `setting_tailTime`). -/

section Generic

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- An iterated derivative along the line `r ↦ r • e_p` is the constant `p`-word of the field at
the point of the line. -/
theorem iteratedDeriv_line_eq (p : Fin 2) (G : Vec 2 → E) {b : ℕ}
    (hG : ContDiff ℝ (b : ℕ∞) G) (x : ℝ) :
    iteratedDeriv b (fun r : ℝ => G (r • basisVec p)) x =
      orderedDerivative (fun _ : Fin b => p) G (x • basisVec p) := by
  let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec p)
  have hl : (fun r : ℝ => G (r • basisVec p)) = G ∘ line := rfl
  have h1 : iteratedFDeriv ℝ b (G ∘ line) x =
      (iteratedFDeriv ℝ b G (line x)).compContinuousLinearMap (fun _ => line) :=
    line.iteratedFDeriv_comp_right hG x (i := b) (by exact_mod_cast le_rfl)
  have h2 := congrFun (orderedDerivative_eq_iteratedFDeriv (fun _ : Fin b => p) hG)
    (x • basisVec p)
  rw [iteratedDeriv_eq_iteratedFDeriv, hl, h1, h2,
    ContinuousMultilinearMap.compContinuousLinearMap_apply]
  simp [line]

/-- The positive fast words of a transverse primitive: only the words in the transverse letter
survive, and they are the iterated derivatives of the source along the transverse line. -/
theorem orderedDerivative_transversePrimitiveField_succ [CompleteSpace E] (p : Fin 2)
    (g : Vec 2 → Vec 2 → E) (Y : Vec 2) {b : ℕ} (hgY : ContDiff ℝ (b : ℕ∞) (g Y))
    (δ : DerivativeWord2 (b + 1)) (z : Vec 2) :
    orderedDerivative δ (transversePrimitiveField p g Y) z =
      if ∀ k, δ k = p then iteratedDeriv b (fun r : ℝ => g Y (r • basisVec p)) (z p)
      else 0 := by
  have hf : ContDiff ℝ (b : ℕ∞) (fun r : ℝ => g Y (r • basisVec p)) :=
    hgY.comp ((ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec p)).contDiff
  exact congrFun (orderedDerivative_centeredIntervalPrimitive_profile_succ b δ _ hf p) z

/-- The slow jets of a transverse primitive (the empty fast word): continuous in the fast
variable, and bounded on the unit cell by `2 ^ (i + 1)` times the mixed jets of the source. -/
theorem transversePrimitiveField_word_zero [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (p : Fin 2) {sX sZ : ℕ}
    (g : Vec 2 → Vec 2 → E) (hg : IsBoxSmooth sX sZ g) {C : ℝ}
    (hC : ∀ r ≤ sX, ∀ s ≤ sZ, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (g Y) z) X‖ ≤ C)
    {i : ℕ} (hi : i ≤ sX) (δ : DerivativeWord2 0) (X : Vec 2) :
    Continuous (fun z => iteratedFDeriv ℝ i
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X) ∧
      ∀ z, z p ∈ Set.Icc (0 : ℝ) 1 → ‖iteratedFDeriv ℝ i
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X‖ ≤
          2 ^ (i + 1) * C := by
  have hb : ∀ j ≤ sX, ∀ (r : ℝ) (Y : Vec 2),
      ‖iteratedFDeriv ℝ j (fun Y' => g Y' (r • basisVec p)) Y‖ ≤ C := fun j hj r Y =>
    (norm_mixed_jet_fast_zero j g Y (r • basisVec p)).symm.trans_le
      (hC j hj 0 (Nat.zero_le _) Y (r • basisVec p))
  have he : ∀ z : Vec 2, (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) =
      fun Y => transversePrimitiveField p g Y z := by
    intro z
    funext Y
    rw [orderedDerivative_zero]
  refine ⟨?_, fun z hz => ?_⟩
  · have hJ : (fun z => iteratedFDeriv ℝ i
          (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X) =
        fun z => iteratedFDeriv ℝ i (fun Y => transversePrimitiveField p g Y z) X := by
      funext z
      rw [he z]
    rw [hJ]
    exact ((transversePrimitiveField_slow_regularities p sX sZ g hg (fun _ => C) hb).2 i
      hi).comp (Continuous.prodMk_right X)
  · rw [he z]
    have h := parameter_centeredIntervalPrimitive_slow_norm_le sX
      (fun r Y => g Y (r • basisVec p))
      (fun Y => (hg.1 Y).continuous.comp (continuous_id.smul continuous_const))
      (fun r => boxSmooth_slow_contDiff hg (r • basisVec p)) (fun _ => C) hb i hi X (z p) hz
    calc ‖iteratedFDeriv ℝ i (fun Y => transversePrimitiveField p g Y z) X‖
        ≤ 2 ^ i * (2 * C) := h
      _ = 2 ^ (i + 1) * C := by ring

/-- The slow jets of a positive fast word of a transverse primitive: continuous in the fast
variable, and bounded everywhere by the mixed jets of the source. -/
theorem transversePrimitiveField_word_succ [CompleteSpace E] (p : Fin 2) {sX sZ : ℕ}
    (g : Vec 2 → Vec 2 → E) (hg : IsBoxSmooth sX sZ g) {C : ℝ}
    (hC : ∀ r ≤ sX, ∀ s ≤ sZ, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (g Y) z) X‖ ≤ C)
    {i b : ℕ} (hi : i ≤ sX) (hb : b ≤ sZ) (δ : DerivativeWord2 (b + 1)) (X : Vec 2) :
    Continuous (fun z => iteratedFDeriv ℝ i
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X) ∧
      ∀ z, ‖iteratedFDeriv ℝ i
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X‖ ≤ C := by
  have hgb : ∀ Y, ContDiff ℝ (b : ℕ∞) (g Y) := fun Y =>
    (hg.1 Y).of_le (by exact_mod_cast hb)
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0 (Nat.zero_le _) X X)
  by_cases hall : ∀ k, δ k = p
  · have he1 : ∀ z : Vec 2,
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) =
          fun Y => iteratedDeriv b (fun r : ℝ => g Y (r • basisVec p)) (z p) := by
      intro z
      funext Y
      rw [orderedDerivative_transversePrimitiveField_succ p g Y (hgb Y) δ z, ite_eq_left hall]
    have he2 : ∀ z : Vec 2,
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) =
          fun Y => orderedDerivative (fun _ : Fin b => p) (g Y) ((z p) • basisVec p) := by
      intro z
      rw [he1 z]
      funext Y
      exact iteratedDeriv_line_eq p (g Y) (hgb Y) (z p)
    let line : ℝ →L[ℝ] Vec 2 := (ContinuousLinearMap.id ℝ ℝ).smulRight (basisVec p)
    have hn : ‖(basisVec p : Vec 2)‖ = 1 := by simp [basisVec, Pi.norm_single]
    have hline : ‖line‖ ≤ 1 := by
      refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun r => le_of_eq ?_
      calc ‖line r‖ = ‖r • (basisVec p : Vec 2)‖ := rfl
        _ = ‖r‖ * ‖(basisVec p : Vec 2)‖ := norm_smul r _
        _ = 1 * ‖r‖ := by rw [hn, mul_one, one_mul]
    refine ⟨?_, fun z => ?_⟩
    · have hJ : (fun z => iteratedFDeriv ℝ i
            (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X) =
          fun z => iteratedFDeriv ℝ i
            (fun Y => orderedDerivative (fun _ : Fin b => p) (g Y) ((z p) • basisVec p)) X := by
        funext z
        rw [he2 z]
      have hw : Continuous (fun z : Vec 2 => ((X, (z p) • basisVec p) : Vec 2 × Vec 2)) :=
        continuous_const.prodMk ((continuous_apply p).smul continuous_const)
      rw [hJ]
      exact (boxSmooth_fast_word_slow_jet_continuous sX sZ i b hi hb g hg
        (fun _ : Fin b => p)).comp hw
    · rw [he1 z]
      have hB := norm_mixed_linear_profile_le sX sZ i b hi hb g hg line X (z p)
      calc ‖iteratedFDeriv ℝ i
            (fun Y => iteratedDeriv b (fun r : ℝ => g Y (r • basisVec p)) (z p)) X‖
          ≤ ‖line‖ ^ b *
            ‖iteratedFDeriv ℝ i (fun Y => iteratedFDeriv ℝ b (g Y) (line (z p))) X‖ := hB
        _ ≤ 1 * C := mul_le_mul (pow_le_one₀ (norm_nonneg _) hline) (hC i hi b hb X _)
            (norm_nonneg _) zero_le_one
        _ = C := one_mul C
  · have he : ∀ z : Vec 2,
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) =
          fun _ => (0 : E) := by
      intro z
      funext Y
      rw [orderedDerivative_transversePrimitiveField_succ p g Y (hgb Y) δ z, ite_eq_right hall]
    have hJ : (fun z => iteratedFDeriv ℝ i
          (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X) =
        fun _ => 0 := by
      funext z
      rw [he z]
      exact congrFun (iteratedFDeriv_fun_zero (𝕜 := ℝ) (E := Vec 2)) X
    refine ⟨?_, fun z => ?_⟩
    · rw [hJ]
      exact continuous_const
    · rw [he z]
      simpa only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero] using hC0

/-- The slow jets of any fast word of a transverse primitive, through fast order one above the
source: continuous in the fast variable, and bounded on the unit cell by `2 ^ (i + 1)` times the
mixed jets of the source. -/
theorem transversePrimitiveField_word [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (p : Fin 2) {sX sZ : ℕ}
    (g : Vec 2 → Vec 2 → E) (hg : IsBoxSmooth sX sZ g) {C : ℝ}
    (hC : ∀ r ≤ sX, ∀ s ≤ sZ, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (g Y) z) X‖ ≤ C)
    {i b : ℕ} (hi : i ≤ sX) (hb : b ≤ sZ + 1) (δ : DerivativeWord2 b) (X : Vec 2) :
    Continuous (fun z => iteratedFDeriv ℝ i
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X) ∧
      ∀ z, z p ∈ Set.Icc (0 : ℝ) 1 → ‖iteratedFDeriv ℝ i
        (fun Y => orderedDerivative δ (transversePrimitiveField p g Y) z) X‖ ≤
          2 ^ (i + 1) * C := by
  cases b with
  | zero => exact transversePrimitiveField_word_zero p g hg hC hi δ X
  | succ b =>
    have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC 0 (Nat.zero_le _) 0 (Nat.zero_le _) X X)
    obtain ⟨hc, hbd⟩ := transversePrimitiveField_word_succ p g hg hC hi (by omega) δ X
    exact ⟨hc, fun z _ =>
      (hbd z).trans (le_mul_of_one_le_left hC0 (one_le_pow₀ (by norm_num)))⟩

/-- **Mixed cell jets of a transverse primitive.** A box-smooth source of orders `(sX, sZ)` with
mixed jets at most `C` has transverse primitive whose mixed cell jets of slow order `i ≤ sX` and
fast words of length at most `sZ + 1` are at most `2 ^ (i + 1) * C`. -/
theorem mixedCellJet_transversePrimitiveField_le [CompleteSpace E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E] (p : Fin 2) (I : Set ℝ) {sX sZ : ℕ}
    (g : ℝ → Vec 2 → Vec 2 → E) (hg : ∀ t ∈ I, IsBoxSmooth sX sZ (g t)) {C : ℝ}
    (hC : ∀ t ∈ I, ∀ r ≤ sX, ∀ s ≤ sZ, ∀ X z,
      ‖iteratedFDeriv ℝ r (fun Y => iteratedFDeriv ℝ s (g t Y) z) X‖ ≤ C)
    {i b : ℕ} (hi : i ≤ sX) (hb : b ≤ sZ + 1) (δ : DerivativeWord2 b) :
    MixedTail.mixedCellJet I i δ (fun t => transversePrimitiveField p (g t)) ≤
      ENNReal.ofReal (2 ^ (i + 1) * C) := by
  rw [MixedTail.mixedCellJet_eq_cellL2Jet]
  refine cellL2Jet_le_unit_bound I i _ _ (fun t ht X => ?_) (fun t ht X z hz => ?_)
  · exact (transversePrimitiveField_word p (g t) (hg t ht) (hC t ht) hi hb δ X).1
  · have hc : z p ∈ Set.Ioo (0 : ℝ) 1 := hz p (Set.mem_univ _)
    exact (transversePrimitiveField_word p (g t) (hg t ht) (hC t ht) hi hb δ X).2 z
      ⟨hc.1.le, hc.2.le⟩

end Generic

/-! ### The constants -/

/-- The constant of the mixed Schur jets of the tail flux coefficient arrays of order `m'`:
`2 ^ m' * 2` entries, each with mixed cell jets at most `2 ^ (K + 1)` times the uniform
entry constant of the tail left arrays. -/
def tailMixedConst (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (m' : ℕ) : ℝ :=
  2 ^ m' * 2 * (2 ^ (K + 1) * TailPresentation.tailEntryTotal K k L D H N CG Cw Cj)

/-- The constant of the mixed Schur jets of the tail flux coefficient arrays of all orders. -/
def tailMixedBound (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) : ℝ :=
  tailMixedConst K k L D H N CG Cw Cj (2 * N + D)

theorem tailMixedConst_nonneg (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) (m' : ℕ) :
    0 ≤ tailMixedConst K k L D H N CG Cw Cj m' := by
  have := TailPresentation.tailEntryTotal_nonneg K k L D H N CG Cw Cj
  unfold tailMixedConst
  positivity

theorem tailMixedBound_nonneg (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) :
    0 ≤ tailMixedBound K k L D H N CG Cw Cj :=
  tailMixedConst_nonneg K k L D H N CG Cw Cj (2 * N + D)

theorem tailMixedConst_le_bound (K k L D H N : ℕ) (CG Cw : ℕ → ℝ) (Cj : ℕ → ℕ → ℝ) {m' : ℕ}
    (hm : m' ≤ 2 * N + D) :
    tailMixedConst K k L D H N CG Cw Cj m' ≤ tailMixedBound K k L D H N CG Cw Cj := by
  have hT := TailPresentation.tailEntryTotal_nonneg K k L D H N CG Cw Cj
  have h1 : (2 : ℝ) ^ m' ≤ 2 ^ (2 * N + D) := pow_le_pow_right₀ (by norm_num) hm
  have hc : 0 ≤ 2 ^ (K + 1) * TailPresentation.tailEntryTotal K k L D H N CG Cw Cj := by
    positivity
  unfold tailMixedBound tailMixedConst
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right h1 (by norm_num)) hc

/-! ### The tail flux arrays under the lift setting -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **Mixed cell jets of one tail flux entry.** At a time `τ` of the window, the mixed cell jets
of slow order `i ≤ K` and fast words of length at most `max k (L + 2) + D` of an entry of the tail
flux array are at most `2 ^ (K + 1)` times the uniform tail entry constant times the `hh`-th power
of the physical edge envelope. -/
theorem setting_tailFlux_entry_mixed_le (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    {τ : ℝ} (hτ : τ ∈ Set.Icc a b) {bb : ℕ}
    (hbb : bb ≤ TailPresentation.arrayFastOrder k L D + 1)
    (δ : DerivativeWord2 bb) {i : ℕ} (hi : i ≤ K) (m' : ℕ) (α : DerivativeWord2 m')
    (dir : Fin 2) (v u : ι) :
    MixedTail.mixedCellJet {τ} i δ
        (fun t X z => tailFluxCoefficient par Q Cc N hh n dir m' α t X z v u) ≤
      ENNReal.ofReal (2 ^ (K + 1) * TailPresentation.tailEntryTotal K k L D H N CG Cw Cj *
        finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
  have hw := finiteMatrixPower_nonneg _
    (physicalEdgeEnvelopeMatrix_nonneg π edge P.envelope.nonneg) hh v u
  have hT := TailPresentation.tailEntryTotal_nonneg K k L D H N CG Cw Cj
  by_cases hm : 1 ≤ m' ∧ m' ≤ 2 * N + D
  · by_cases hd : dir = par.rev
    · have he : (fun t X z => tailFluxCoefficient par Q Cc N hh n dir m' α t X z v u) =
          fun t => transversePrimitiveField par.rev
            (fun X z => tailLeftCoefficient Q Cc N hh n m' α t X z v u) := by
        funext t X z
        simp only [tailFluxCoefficient, positiveFluxLiftCoefficient,
          centeredFluxLiftCoefficient, positiveLiftCoefficient, ite_eq_left hm,
          transverseCenteredFlux, ite_eq_left hd, transversePrimitiveField]
      have htI : ∀ t ∈ ({τ} : Set ℝ), t ∈ Set.Icc a b := by
        intro t ht
        rw [Set.mem_singleton_iff.1 ht]
        exact hτ
      have hent := fun (t : ℝ) (ht : t ∈ ({τ} : Set ℝ)) =>
        TailPresentation.setting_tailEntry P Cc hseq hh hhh n (by omega) hnR t (htI t ht)
          m' α v u
      rw [he]
      refine (mixedCellJet_transversePrimitiveField_le par.rev {τ}
        (fun t X z => tailLeftCoefficient Q Cc N hh n m' α t X z v u)
        (fun t ht => (hent t ht).1) (fun t ht => (hent t ht).2.2) hi hbb δ).trans ?_
      apply ENNReal.ofReal_le_ofReal
      have h2 : (2 : ℝ) ^ (i + 1) ≤ 2 ^ (K + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
      exact (mul_le_mul_of_nonneg_right h2 (mul_nonneg hT hw)).trans_eq (by ring)
    · have he : (fun t X z => tailFluxCoefficient par Q Cc N hh n dir m' α t X z v u) =
          fun _ _ _ => (0 : h u →L[ℝ] h v) := by
        funext t X z
        simp only [tailFluxCoefficient, positiveFluxLiftCoefficient,
          centeredFluxLiftCoefficient, transverseCenteredFlux, ite_eq_right hd]
      rw [he]
      exact (mixedCellJet_zero (E := h u →L[ℝ] h v) {τ} i δ).le.trans bot_le
  · have he : (fun t X z => tailFluxCoefficient par Q Cc N hh n dir m' α t X z v u) =
        fun _ _ _ => (0 : h u →L[ℝ] h v) := by
      funext t X z
      exact positiveFluxLiftCoefficient_outside par dir (2 * N + D) _ m' hm α t X z v u
    rw [he]
    exact (mixedCellJet_zero (E := h u →L[ℝ] h v) {τ} i δ).le.trans bot_le

include P in
/-- **Mixed Schur jets of the tail flux coefficient arrays.** At a time `τ` of the window, for a
fast word of length at most `max k (L + 2) + D` and a slow order at most `K`, the weighted block
norm of the mixed cell jets of the tail flux coefficients of order `m'` is at most
`tailMixedConst m' * Θ ^ hh`. -/
theorem setting_tailFluxCoefficient_mixed_schur (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : N < n) (hnR : n ≤ 2 * N + D)
    {τ : ℝ} (hτ : τ ∈ Set.Icc a b) {bb : ℕ}
    (hbb : bb ≤ TailPresentation.arrayFastOrder k L D + 1)
    (δ : DerivativeWord2 bb) {i : ℕ} (hi : i ≤ K) (m' : ℕ) :
    MixedTail.schurMixedJet π {τ} i δ (fun q : DerivativeWord2 m' × Fin 2 =>
        tailFluxCoefficient par Q Cc N hh n q.2 m' q.1) ≤
      ENNReal.ofReal (tailMixedConst K k L D H N CG Cw Cj m' * Θ ^ hh) := by
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := hι
    simp [MixedTail.schurMixedJet, schurSums]
  · have hΘ : 0 ≤ Θ :=
      (Finset.sum_nonneg (fun u _ => P.envelope.nonneg (Classical.choice hι) u)).trans
        (P.envelope.row_sum (Classical.choice hι))
    have hcard : Fintype.card (DerivativeWord2 m' × Fin 2) = 2 ^ m' * 2 := by simp
    have hcardR : ((Fintype.card (DerivativeWord2 m' × Fin 2) : ℕ) : ℝ) = 2 ^ m' * 2 := by
      exact_mod_cast hcard
    have hN : ∀ v u, (∑ q : DerivativeWord2 m' × Fin 2, MixedTail.mixedCellJet {τ} i δ
        (fun t X z => tailFluxCoefficient par Q Cc N hh n q.2 m' q.1 t X z v u)) ≤
        ENNReal.ofReal (tailMixedConst K k L D H N CG Cw Cj m' *
          finiteMatrixPower (physicalEdgeEnvelopeMatrix π edge) hh v u) := by
      intro v u
      refine (Finset.sum_le_sum fun q _ => setting_tailFlux_entry_mixed_le P Cc hseq hh hhh n
        hn hnR hτ hbb δ hi m' q.1 q.2 v u).trans (le_of_eq ?_)
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← ENNReal.ofReal_natCast,
        ← ENNReal.ofReal_mul (Nat.cast_nonneg _), hcardR]
      congr 1
      unfold tailMixedConst
      ring
    exact TailPresentation.schurSums_le_of_power π P.mass_pos edge hΘ
      ⟨P.envelope.nonneg, P.envelope.row_sum, P.envelope.col_sum⟩ hh
      (tailMixedConst_nonneg K k L D H N CG Cw Cj m') _ hN

include P in
/-- **The mixed jet hypothesis of `setting_tailTime`.** At a time `τ` of the window, for every
tail degree, every fast word of length at most `r ≤ max k (L + 2) + D` and every slow order at most
`Acl + 2 + r ≤ K`, the mixed Schur jets of the tail flux coefficient arrays of every order are at
most `tailMixedBound * Θ ^ hh`. -/
theorem setting_tailFluxCoefficient_mixed_jets (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (Acl r : ℕ) (hK : Acl + 2 + r ≤ K)
    (hr : r ≤ TailPresentation.arrayFastOrder k L D + 1) {τ : ℝ} (hτ : τ ∈ Set.Icc a b) :
    ∀ n ∈ Finset.Icc (N + 1) (2 * N + D), ∀ bb, bb ≤ r → ∀ δ : DerivativeWord2 bb,
      ∀ i, i ≤ Acl + 2 + r → ∀ m',
        MixedTail.schurMixedJet π {τ} i δ (fun q : DerivativeWord2 m' × Fin 2 =>
          tailFluxCoefficient par Q Cc N hh n q.2 m' q.1) ≤
            ENNReal.ofReal (tailMixedBound K k L D H N CG Cw Cj * Θ ^ hh) := by
  intro n hn bb hbb δ i hi m'
  obtain ⟨hn1, hn2⟩ := Finset.mem_Icc.1 hn
  rcases isEmpty_or_nonempty ι with hι | hι
  · have := hι
    simp [MixedTail.schurMixedJet, schurSums]
  · have hΘ : 0 ≤ Θ :=
      (Finset.sum_nonneg (fun u _ => P.envelope.nonneg (Classical.choice hι) u)).trans
        (P.envelope.row_sum (Classical.choice hι))
    by_cases hm : m' ≤ 2 * N + D
    · refine (setting_tailFluxCoefficient_mixed_schur P Cc hseq hh hhh n (by omega) hn2 hτ
        (by omega) δ (i := i) (by omega) m').trans ?_
      exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
        (tailMixedConst_le_bound K k L D H N CG Cw Cj hm) (pow_nonneg hΘ _))
    · have he : (fun q : DerivativeWord2 m' × Fin 2 =>
          tailFluxCoefficient par Q Cc N hh n q.2 m' q.1) = fun _ _ _ _ _ _ => 0 := by
        funext q t X z v u
        exact tailFluxCoefficient_outside par q.2 Q Cc N hh n m' q.1 t X z v u
          (Or.inr (by omega))
      rw [he]
      exact (schurMixedJet_zero (h := h) (κ := DerivativeWord2 m' × Fin 2) π {τ} i
        δ).le.trans bot_le

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lifted coarse flux of one charted pulse at one time**. For a
physical flux `F` and cleanup chains of the positive degrees of the lift of the chart-frame field of
`div F`:

* `setting_liftDiffTime`: `ρ` times the chains are chains of the straight lifted coarse flux of the
  inverse-Piola pull-back `F'`, and the data `CoarseFluxDiff.DiffTime` of the differentiated
  coarse-flux estimate hold at one cell time (mixed jets of the lift coefficients from the lift
  grading, `CoarseFluxDiff.mjet_bounds`). -/

/-- Reindexing a sum over `[1, N]`. -/
theorem sum_Icc_one_eq_sum_range {M : Type*} [AddCommMonoid M] (f : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, f n = ∑ n ∈ Finset.range N, f (n + 1) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel]
  exact Finset.sum_congr rfl fun n _ => by rw [add_comm]

/-- The sampled cleanup flux of a multiple of a chain. -/
theorem cleanupFlux_smul_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c ρ e : ℝ) (A : ℕ) (W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (κ : ℝ) (t : ℝ) (x : Vec 2)
    (k : Fin 2) :
    cleanupFlux c ρ e A (fun j τ X z k' => κ • W j τ X z k') t x k =
      κ • cleanupFlux c ρ e A W t x k := by
  show e • ∑ j ∈ Finset.range A, (e / ρ) ^ j • (κ • W j (c * t) (ρ⁻¹ • x) (e⁻¹ • x) k) =
    κ • (e • ∑ j ∈ Finset.range A, (e / ρ) ^ j • W j (c * t) (ρ⁻¹ • x) (e⁻¹ • x) k)
  simp only [Finset.smul_sum, smul_smul]
  exact Finset.sum_congr rfl fun j _ => by rw [show e * ((e / ρ) ^ j * κ) = κ * (e * (e / ρ) ^ j) by
    ring]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The data of one cell time of the lifted coarse flux of a charted pulse.** -/
theorem setting_liftDiffTime (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (Acl r kres : ℕ) (hAcl : 1 ≤ Acl) (hX : Acl + 2 + r ≤ K + D + 2) (hr : r ≤ k)
    (hZ : r + 1 ≤ max (k + 1) (L + 2)) (hk : Acl + 2 + r + N + 1 ≤ kres)
    (Cg : ℝ) (hCg : 0 ≤ Cg) (hΘ : 0 ≤ Θ) (hh : ℕ) (hhh : hh ≤ H)
    (hgr : ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ Acl + 2 + r →
      schurEnergyJet π (Set.Icc a b) k j (Cc hh n m) ≤
        ENNReal.ofReal (Cg * Θ ^ hh * lam ^ (n - m + j)))
    (hst : ∀ c0 : ∀ i, h i, ∀ t ∈ Set.Icc a b, ∀ X z, ∀ n, 1 ≤ n → n ≤ N →
      liftApply n (Cc hh n) (fun _ _ => c0) t X z = 0)
    (θ : ℝ) (hθ : 2 ^ (Acl + 2 + r) * Cg * Θ ^ hh ≤ θ) (F : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (χ ψ : ℝ → Vec 2 → Vec 2) (hχ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (χ s))
    (hψ : ∀ s, Differentiable ℝ (ψ s)) (hψχ : ∀ s y, ψ s (χ s y) = y)
    (hχψ : ∀ s x, χ s (ψ s x) = x) (hd : ∀ s y, (jacMatrix (χ s) y).det = 1)
    (hF : ∀ s k', ContDiff ℝ ((kres + 2 : ℕ) : ℕ∞) (fun x => F s x k'))
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) {τ : ℝ}
    (hτ : τ ∈ Set.Icc a b)
    (hV : ∀ n', n' < N → IsCleanupChain (Acl + 2 + r) (max (k + 1) (L + 2)) Acl
      (liftApply (n' + 1) (Cc hh (n' + 1)) (fun s X => ∑ k' : Fin 2,
        fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k') (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k')) τ)
      (fun _ _ _ => 0) (fun j => Vn hh n' j τ))
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (heρ : e ≤ ρ) (hM : ∃ M : ℕ, e⁻¹ = (M : ℝ)) :
    CoarseFluxDiff.DiffTime π (Set.Icc a b) Acl r N kres (max (k + 1) (L + 2))
      (fun n => Cc hh n) (fun s y k' => invPiola (χ s) (F s) y k') ℓ ρ e rs εc τ
      (ENNReal.ofReal θ) (fun n j X z k' => ρ • Vn hh (n - 1) j τ X z k') := by
  have hℓ : 0 < ℓ := by rw [P.ℓ_eq]; exact div_pos P.e_pos (Real.sqrt_pos.2 P.ν_pos)
  have hεc : 0 ≤ εc := by
    rw [P.εc_eq, P.dstar_eq]
    exact div_nonneg (mul_nonneg hℓ.le (Real.sqrt_nonneg _)) P.ρ_pos.le
  have hlam0 : 0 ≤ lam := by rw [P.lam_eq]; exact div_nonneg P.ρ_pos.le P.E_pos.le
  -- the pulled-back flux is smooth
  have hF' : ∀ s k', ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun y => invPiola (χ s) (F s) y k') :=
    fun s k' => contDiff_invPiola ((hχ s).of_le (by exact_mod_cast le_top)) (hd s)
      (fun l => (hF s l).of_le (by exact_mod_cast Nat.le_succ _)) k'
  refine ⟨fun n hn => ?_, hεc, P.εc_le, hF' (ℓ ^ 2 * τ), by omega⟩
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.1 hn
  obtain ⟨hj0, hj⟩ := CoarseFluxDiff.mjet_bounds π (Set.Icc a b) (A := Acl) (r := r) (k := k) hr
    (Cc hh n) Cg Θ lam hCg hΘ hlam0 P.lam_le hh n
    (fun m α v u t ht => (hseq.2.2.2.2.2.1 hh hhh n m α v u t ht).1.mono hX (by omega))
    (fun α t ht X z v u => CoarseFluxDiff.coeff_zero_of_const (Cc hh n) n t X z
      (fun c0 => hst c0 t ht X z n hn1 hnN) α v u)
    (fun m hm α t ht X z v u => hseq.2.2.2.1 hh hhh n m hm α t X z v u)
    (fun m hm1 hmn j hj => hgr n hn1 hnN m hm1 hmn j hj)
  -- the chain of the straight lifted coarse flux
  obtain ⟨n', rfl⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by omega⟩
  have hn' : n' < N := by omega
  have hc := (hV n' hn').clm_comp (by omega) (by omega) IsSlowSmooth.zero
    (ρ • ContinuousLinearMap.id ℝ (∀ i, h i))
  have hA : ContDiff ℝ ((n' + 1 : ℕ) : ℕ∞) (fun X => ∑ k' : Fin 2,
      fderiv ℝ (fun x => F (ℓ ^ 2 * τ) x k') (χ (ℓ ^ 2 * τ) (ρ • X)) (basisVec k')) := by
    have hdiv : ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (fun x => ∑ k' : Fin 2,
        fderiv ℝ (fun x' => F (ℓ ^ 2 * τ) x' k') x (basisVec k')) :=
      ContDiff.sum fun k' _ => ((hF _ k').fderiv_right (by exact_mod_cast le_rfl)).clm_apply
        contDiff_const
    exact (hdiv.comp (((hχ _).of_le (by exact_mod_cast le_top)).comp
      (contDiff_const_smul ρ))).of_le (by exact_mod_cast (by omega : n' + 1 ≤ kres + 1))
  have hcf : CoarseFluxDiff.coarseField (fun s y k' => invPiola (χ s) (F s) y k') ℓ ρ τ =
      (fun s X => ρ • ∑ k' : Fin 2, fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k')
        (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k')) τ := by
    funext X'
    exact coarseField_invPiola (hχ _) (hψ _) (hψχ _) (hχψ _) (hd _) F
      (fun l => ((hF' _ l).differentiable (by simp))) X'
  have e1 : liftApply (n' + 1) (Cc hh (n' + 1))
        (CoarseFluxDiff.coarseField (fun s y k' => invPiola (χ s) (F s) y k') ℓ ρ) τ =
      fun X z => ρ • liftApply (n' + 1) (Cc hh (n' + 1)) (fun s X => ∑ k' : Fin 2,
        fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k') (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k')) τ X z := by
    rw [Lift.liftApply_congr_time (n' + 1) (Cc hh (n' + 1)) _ (fun s X => ρ • ∑ k' : Fin 2,
      fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k') (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k')) τ hcf]
    funext X z
    exact liftApply_smul_field (n' + 1) (Cc hh (n' + 1)) (fun s X => ∑ k' : Fin 2,
      fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k') (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k')) ρ τ hA X z
  have e2 : (fun X z => (ρ • ContinuousLinearMap.id ℝ (∀ i, h i))
      (liftApply (n' + 1) (Cc hh (n' + 1)) (fun s X => ∑ k' : Fin 2,
        fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k') (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k')) τ X z)) =
      liftApply (n' + 1) (Cc hh (n' + 1))
        (CoarseFluxDiff.coarseField (fun s y k' => invPiola (χ s) (F s) y k') ℓ ρ) τ := by
    rw [e1]
    rfl
  have e3 : (fun (_ _ : Vec 2) (k' : Fin 2) =>
      (ρ • ContinuousLinearMap.id ℝ (∀ i, h i)) ((0 : Fin 2 → ∀ i, h i) k')) =
      fun _ _ _ => 0 := by
    funext X z k'
    simp
  have e4 : (fun j X z k' => (ρ • ContinuousLinearMap.id ℝ (∀ i, h i)) (Vn hh n' j τ X z k')) =
      fun j X z k' => ρ • Vn hh (n' + 1 - 1) j τ X z k' := by
    funext j X z k'
    simp
  rw [e2, e3, e4] at hc
  exact {
    mass_pos := P.mass_pos
    τ_mem := hτ
    ρ_pos := P.ρ_pos
    rs_pos := hrs
    rs_le := hrse
    e_le := heρ
    e_inv := hM
    hA := hAcl
    hZ := hZ
    order := by omega
    box := fun m α v u => (hseq.2.2.2.2.2.1 hh hhh (n' + 1) m α v u τ hτ).1.mono hX (by omega)
    mjet0 := hj0
    mjet := fun bb hb δ i hi m => (hj bb hb δ i hi m).trans (ENNReal.ofReal_le_ofReal hθ)
    smooth := fun k' => hF' (ℓ ^ 2 * τ) k'
    chain := hc }

/-- The constant of the physical lifted coarse-flux slice bound. -/
def liftPhysConst (H N Acl r kres Nχ : ℕ) (Dχ : ℝ) : ℝ :=
  2 * ChartTransport.fluxConst Dχ r *
    (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i * (((H + 1 : ℕ) : ℝ) ^ 2 *
      (2 * N * ∑ n ∈ Finset.Icc 1 N, CoarseFluxDiff.fluxWordConst n Acl r i))) *
    (2 * ChartTransport.densConst kres 0 2 (2 ^ Nχ * Dχ * compConst Dχ Nχ))

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
theorem liftPhysConst_nonneg (H N Acl r kres Nχ : ℕ) (Dχ : ℝ) :
    0 ≤ liftPhysConst H N Acl r kres Nχ Dχ := by
  unfold liftPhysConst
  refine mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (fluxConst_nonneg r))
    (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ =>
        CoarseFluxDiff.fluxWordConst_nonneg n Acl r i))))) ?_
  exact mul_nonneg (by norm_num) (ChartTransport.densConst_nonneg kres 0 2 _)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The weighted word derivatives of the physical lifted coarse flux of one pulse at one
time.** -/
theorem setting_liftFluxPhys_word_slice (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (Acl r kres : ℕ) (hAcl : 1 ≤ Acl) (hX : Acl + 2 + r ≤ K + D + 2) (hr : r ≤ k)
    (hZ : r + 1 ≤ max (k + 1) (L + 2)) (hk : Acl + 2 + r + N + 1 ≤ kres)
    (Cg : ℝ) (hCg : 0 ≤ Cg) (hΘ : 0 ≤ Θ)
    (hgr : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ Acl + 2 + r →
      schurEnergyJet π (Set.Icc a b) k j (Cc hh n m) ≤
        ENNReal.ofReal (Cg * Θ ^ hh * lam ^ (n - m + j)))
    (hst : ∀ hh, hh ≤ H → ∀ c0 : ∀ i, h i, ∀ t ∈ Set.Icc a b, ∀ X z, ∀ n, 1 ≤ n → n ≤ N →
      liftApply n (Cc hh n) (fun _ _ => c0) t X z = 0)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : ∀ hh, hh ≤ H → 2 ^ (Acl + 2 + r) * Cg * Θ ^ hh ≤ θ)
    (F : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (χ ψ : ℝ → Vec 2 → Vec 2)
    (hχ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (χ s)) (hψ : ∀ s, Differentiable ℝ (ψ s))
    (hψχ : ∀ s y, ψ s (χ s y) = y) (hχψ : ∀ s x, χ s (ψ s x) = x)
    (hd : ∀ s y, (jacMatrix (χ s) y).det = 1)
    (hF : ∀ s k', ContDiff ℝ ((kres + 2 : ℕ) : ℕ∞) (fun x => F s x k'))
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) {t : ℝ}
    (ht : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc a b)
    (hFp : ∀ k', IsZ2Periodic (fun x => F t x k'))
    (hV : ∀ hh, hh ≤ H → ∀ n', n' < N → IsCleanupChain (Acl + 2 + r) (max (k + 1) (L + 2)) Acl
      (liftApply (n' + 1) (Cc hh (n' + 1)) (fun s X => ∑ k' : Fin 2,
        fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k') (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k'))
          ((ℓ ^ 2)⁻¹ * t))
      (fun _ _ _ => 0) (fun j => Vn hh n' j ((ℓ ^ 2)⁻¹ * t)))
    (hslow : ∀ hh, hh ≤ H → ∀ n', n' < N → ∀ j, j < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vn hh n' j ((ℓ ^ 2)⁻¹ * t) (X + ρ⁻¹ • latticeShift n) = Vn hh n' j ((ℓ ^ 2)⁻¹ * t) X)
    (hC : IsChart (χ t) (ψ t)) {Dχ Rχ : ℝ} {Nχ : ℕ} (hDχ : 1 ≤ Dχ) (hNχ : kres + 1 ≤ Nχ)
    (hJχr : JetBound (χ t) (r + 1) Dχ Rχ) (hJχN : JetBound (χ t) Nχ Dχ Rχ)
    (hJψ : JetBound (ψ t) r Dχ Rχ) (hψr : ContDiff ℝ (r : ℕ∞) (ψ t)) (hρR : ρ ≤ Rχ)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (hsR : rs ≤ Rχ) (heρ : e ≤ ρ) {M : ℕ}
    (hM : e⁻¹ = (M : ℝ)) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) :
    fluxInt π (fun x a₀ => rs ^ j • orderedDerivative β
        (fun x' => liftFluxPhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vn t x' a₀) x) ≤
      ENNReal.ofReal (liftPhysConst H N Acl r kres Nχ Dχ) *
        ENNReal.ofReal ((e / ρ) ^ 2 * εc ^ 2 * θ ^ 2) *
          CoarseFluxDiff.fluxDensity ρ kres π F t := by
  have hℓ : 0 < ℓ := by rw [P.ℓ_eq]; exact div_pos P.e_pos (Real.sqrt_pos.2 P.ν_pos)
  have hc : ℓ ^ 2 ≠ 0 := by positivity
  set τ : ℝ := (ℓ ^ 2)⁻¹ * t with hτdef
  have hℓτ : ℓ ^ 2 * τ = t := by rw [hτdef, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  -- the label flux, by grade
  set Gh : ℕ → Vec 2 → Fin 2 → ∀ i, h i := fun hh y l => ∑ n ∈ Finset.range N,
    εc ^ (n + 1) • cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n) t y l with hGh
  set G : Vec 2 → Fin 2 → ∀ i, h i := fun y l => ∑ hh ∈ Finset.range (H + 1), Gh hh y l
    with hG
  have hbox : ∀ hh, hh ≤ H → ∀ n', n' < N → ∀ j', j' < Acl →
      IsBoxSmooth (Acl + 2 + r) (max (k + 1) (L + 2)) (Vn hh n' j' τ) :=
    fun hh hhh n' hn' => cleanupChain_zeroFlux_box (hV hh hhh n' hn')
  have hcf : ∀ hh, hh ≤ H → ∀ n', n' < N → ∀ i, i ≤ r → ∀ l, ContDiff ℝ (i : ℕ∞)
      (fun y => cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t y l) :=
    fun hh hhh n' hn' i hi l => contDiff_cleanupFlux_sample_of_le (sX := Acl + 2 + r)
      (sZ := max (k + 1) (L + 2)) (by omega) (by omega) (ℓ ^ 2)⁻¹ ρ e t
      (hbox hh hhh n' hn') l
  have hGhc : ∀ hh ∈ Finset.range (H + 1), ∀ i, i ≤ r → ∀ l,
      ContDiff ℝ (i : ℕ∞) (fun y => Gh hh y l) := fun hh hhm i hi l =>
    ContDiff.sum fun n hn => (hcf hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) n
      (Finset.mem_range.1 hn) i hi l).const_smul _
  have hGc : ∀ l, ContDiff ℝ (r : ℕ∞) (fun y => G y l) := fun l =>
    ContDiff.sum fun hh hhm => hGhc hh hhm r le_rfl l
  have hfast : ∀ hh, hh ≤ H → ∀ n', n' < N → ∀ j', j' < Acl → ∀ X,
      IsZ2Periodic (Vn hh n' j' τ X) := fun hh hhh n' hn' =>
    (hV hh hhh n' hn').periodic (F₀ := fun _ _ _ => 0) (fun _ _ _ => rfl)
  have hGp : ∀ l, IsZ2Periodic (fun y => G y l) := by
    intro l n y
    show ∑ hh ∈ Finset.range (H + 1), ∑ n' ∈ Finset.range N, εc ^ (n' + 1) •
        cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t (y + latticeShift n) l = _
    refine Finset.sum_congr rfl fun hh hhm => Finset.sum_congr rfl fun n' hn' => ?_
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    have hp : cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t (y + latticeShift n) l =
        cleanupFlux (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t y l :=
      cleanupFlux_isZ2Periodic (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t M hM
        (hslow hh hhh n' (Finset.mem_range.1 hn')) (hfast hh hhh n' (Finset.mem_range.1 hn'))
        l n y
    rw [hp]
  -- the physical flux is the Piola transport of the label flux
  have hχd : Differentiable ℝ (χ t) := hC.contΦ.differentiable one_ne_zero
  have hψd : Differentiable ℝ (ψ t) := hC.contΨ.differentiable one_ne_zero
  have hphys : (fun x a₀ => rs ^ j • orderedDerivative β
      (fun x' => liftFluxPhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vn t x' a₀) x) =
      fun x a₀ => rs ^ j • orderedDerivative β
        (fun x' => ∑ l : Fin 2, jacMatrix (χ t) (ψ t x') a₀ l • G (ψ t x') l) x := by
    have he : ∀ a₀, (fun x' => liftFluxPhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vn t x' a₀) =
        fun x' => ∑ l : Fin 2, jacMatrix (χ t) (ψ t x') a₀ l • G (ψ t x') l := fun a₀ => by
      funext x'
      have hK : ∀ l, chartInvJacobian (ψ t) x' a₀ l = jacMatrix (χ t) (ψ t x') a₀ l := fun l => by
        rw [chartInvJacobian_eq_of_inverse hχd hψd (hψχ t) (hχψ t) x',
          chartJacobian_eq_jacMatrix]
      simp only [liftFluxPhys, tailFluxPhys, tailFluxLabel, hK, hG, hGh, Finset.smul_sum,
        smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun l _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun n _ => ?_
      rw [show ℓ ^ 2 * (jacMatrix (χ t) (ψ t x') a₀ l * ((ℓ ^ 2)⁻¹ * εc ^ (n + 1))) =
        jacMatrix (χ t) (ψ t x') a₀ l * εc ^ (n + 1) by field_simp]
    funext x a₀
    rw [he a₀]
  rw [hphys]
  have hχr : ContDiff ℝ ((r + 1 : ℕ) : ℕ∞) (χ t) := (hχ t).of_le (by exact_mod_cast le_top)
  refine (flux_slice hC hj hχr hψr hGc hGp hDχ hrs hsR hJχr hJψ π β).trans ?_
  -- the bound of one grade, by the straight lifted coarse flux of the pull-back
  set X0 : ℝ≥0∞ := CoarseFluxDiff.fluxDensity ρ kres π
    (fun s y k' => invPiola (χ s) (F s) y k') t with hX0
  have hgrade : ∀ hh, hh ≤ H → ∀ i, i ≤ r → ∀ w : DerivativeWord2 i,
      fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => Gh hh x' l) x) ≤
        ENNReal.ofReal (2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 *
          ∑ n ∈ Finset.Icc 1 N, CoarseFluxDiff.fluxWordConst n Acl r i) * X0 := by
    intro hh hhh i hi w
    have hT := setting_liftDiffTime P Cc hseq Acl r kres hAcl hX hr hZ hk Cg hCg hΘ hh hhh
      (hgr hh hhh) (hst hh hhh) θ (hθ hh hhh) F χ ψ hχ hψ hψχ hχψ hd hF Vn ht (hV hh hhh) hrs
      hrse heρ ⟨M, hM⟩
    have hb := CoarseFluxDiff.flux_time_bound
      (Vn := fun n j τ' X z k' => ρ • Vn hh (n - 1) j τ' X z k') hT 1 t rfl hℓτ θ rfl hθ0
      hi w hrs (hrse.trans heρ)
    have hfv : ∀ l, (fun x' => CoarseFluxDiff.fluxVec 1 (fun s y k' => invPiola (χ s) (F s) y k')
        ℓ ρ e εc Acl N (fun n j τ' X z k' => ρ • Vn hh (n - 1) j τ' X z k') t x' l) =
        fun x' => Gh hh x' l := by
      intro l
      funext x'
      simp only [CoarseFluxDiff.fluxVec, one_ne_zero, ite_false, zero_add, cleanupFlux_smul_chain,
        smul_smul, Finset.smul_sum]
      rw [sum_Icc_one_eq_sum_range]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [show ρ⁻¹ * (εc ^ (n + 1) * ρ) = εc ^ (n + 1) by field_simp [P.ρ_pos.ne'],
        Nat.add_sub_cancel]
    unfold fluxInt
    simp only [hfv] at hb
    refine hb.trans (le_of_eq ?_)
    simp only [one_ne_zero, ite_false, zero_add]
    rfl
  -- every word of the label flux
  have hcw : ∀ i, 0 ≤ ((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
      CoarseFluxDiff.fluxWordConst n Acl r i) := fun i =>
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ =>
      CoarseFluxDiff.fluxWordConst_nonneg n Acl r i))
  set Y0 : ℝ≥0∞ := ENNReal.ofReal ((e / ρ) ^ 2 * εc ^ 2 * θ ^ 2) * X0 with hY0
  have hw : ∀ i ∈ Finset.range (j + 1), ∀ w : DerivativeWord2 i,
      fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x) ≤
        ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
          CoarseFluxDiff.fluxWordConst n Acl r i)) * Y0 := by
    intro i hi w
    have hir : i ≤ r := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have e1 : (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x) = fun x l =>
        ∑ hh ∈ Finset.range (H + 1), rs ^ i • orderedDerivative w (fun x' => Gh hh x' l) x := by
      funext x l
      show rs ^ i • orderedDerivative w (fun x' => ∑ hh ∈ Finset.range (H + 1), Gh hh x' l) x = _
      rw [MixedTail.orderedDerivative_sum _ w fun hh hhm => hGhc hh hhm i hir l, Finset.smul_sum]
    have hsum := fluxInt_sum_le (Finset.range (H + 1)) (fun hh x l => rs ^ i •
        orderedDerivative w (fun x' => Gh hh x' l) x)
      (fun hh hhm l => (continuous_orderedDerivative w (hGhc hh hhm i hir l)).fun_const_smul
        (rs ^ i)) π
    refine (le_of_eq (congrArg (fluxInt π) e1)).trans (hsum.trans ?_)
    have hsc : ENNReal.ofReal (2 * N * (e / ρ) ^ 2 * εc ^ 2 * θ ^ 2 *
        ∑ n ∈ Finset.Icc 1 N, CoarseFluxDiff.fluxWordConst n Acl r i) * X0 =
        ENNReal.ofReal (2 * N * ∑ n ∈ Finset.Icc 1 N, CoarseFluxDiff.fluxWordConst n Acl r i) *
          Y0 := by
      rw [hY0, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (by positivity)
        (Finset.sum_nonneg fun n _ => CoarseFluxDiff.fluxWordConst_nonneg n Acl r i))]
      congr 2
      ring
    calc ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ hh ∈ Finset.range (H + 1),
          fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => Gh hh x' l) x)
        ≤ ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ _hh ∈ Finset.range (H + 1),
            ENNReal.ofReal (2 * N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.fluxWordConst n Acl r i) * Y0 := by
          gcongr with hh hhm
          exact (hgrade hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) i hir w).trans_eq hsc
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
          congr 1
          rw [ENNReal.ofReal_mul (p := ((H + 1 : ℕ) : ℝ) ^ 2) (by positivity),
            ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          ring
  have hsum : ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
      fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x) ≤
      ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
        (((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
          CoarseFluxDiff.fluxWordConst n Acl r i))) * Y0 := by
    calc ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x)
        ≤ ∑ i ∈ Finset.range (j + 1), ∑ _w : DerivativeWord2 i,
            ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.fluxWordConst n Acl r i)) * Y0 :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun w _ => hw i hi w
      _ = ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.fluxWordConst n Acl r i))) * Y0 := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (by positivity) (hcw i),
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h2 : ((2 ^ i : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ i) := by
            rw [ENNReal.ofReal_pow (by norm_num)]
            simp
          rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul, h2]
          conv_rhs => rw [ENNReal.ofReal_mul (by positivity)]
          exact (mul_assoc _ _ _).symm
      _ ≤ _ := by
          gcongr ?_ * Y0
          exact ENNReal.ofReal_le_ofReal
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hj))
              fun i _ _ => mul_nonneg (by positivity) (hcw i))
  have hFk : ∀ k', ContDiff ℝ (kres : ℕ∞) (fun x => F t x k') := fun k' =>
    (hF t k').of_le (by exact_mod_cast (by omega : kres ≤ kres + 2))
  have hχk : ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (χ t) := (hχ t).of_le (by exact_mod_cast le_top)
  have hpi := fluxDensity_invPiola_le (χ := χ) (ψ := ψ) hC hNχ hχk hDχ P.ρ_pos hρR hJχN π F hFk
    hFp
  calc ENNReal.ofReal (2 * ChartTransport.fluxConst Dχ r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          fluxInt π (fun x l => rs ^ i • orderedDerivative w (fun x' => G x' l) x)
      ≤ ENNReal.ofReal (2 * ChartTransport.fluxConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.fluxWordConst n Acl r i))) * Y0) := by gcongr
    _ ≤ ENNReal.ofReal (2 * ChartTransport.fluxConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.fluxWordConst n Acl r i))) *
          (ENNReal.ofReal ((e / ρ) ^ 2 * εc ^ 2 * θ ^ 2) *
            (ENNReal.ofReal (2 * ChartTransport.densConst kres 0 2
              (2 ^ Nχ * Dχ * compConst Dχ Nχ)) * CoarseFluxDiff.fluxDensity ρ kres π F t))) := by
        rw [hY0, hX0]
        gcongr
    _ = _ := by
        unfold liftPhysConst
        have h1 : 0 ≤ 2 * ChartTransport.fluxConst Dχ r :=
          mul_nonneg (by norm_num) (fluxConst_nonneg r)
        have h2 : 0 ≤ ∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (2 * N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.fluxWordConst n Acl r i)) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hcw i)
        rw [ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1]
        ring

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The tested edge term of one observed pulse**.
`setting_pulse_edge_tested` for the lift data `pulseLiftData … k (F.fiber p₀ (actual p₀))` of the
pulse whose piece `p₀` has the renewal chart `ocChart … (ocPulseChartIndex k)` as material map:
at a time of the pulse window where the family edge flux is the Piola transport of the label
edge flux of `p₀` (`obs_family_flux`), the source part of the pulse rest, scaled by `ℓ⁻²` and
tested against a `C¹` periodic `φ`, is minus the pairing of the physical edge flux of the pulse
lift with `∇φ`, and that flux is continuous (`pulse_edge_tested_instance`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- **The tested edge term of one observed pulse.** -/
theorem pulse_edge_tested_instance {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {φs : ℝ → Vec 2 → ℝ}
    (hΛ : 1 ≤ Λ) (hφs : IsAdmissibleStream φs) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    {ρ E : ℝ} (hρ : 0 < ρ)
    {kp : ℤ} {D : ℕ} {Pc : Type*} {Ctx : Pc → Type*} (F : ChartedFamily ι h D Pc Ctx)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (htorus : IsTorusCompatible F actual E) (p₀ : Pc)
    (hmat : ∀ t, ⇑((F.piece p₀).material t) =
      ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t)
    {π : ι → ℝ} {a b e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K₀ k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) kp
      (F.fiber p₀ (actual p₀))) π a b e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par V H N K₀ k₀ L qs
      qf CG Cw Cj edgeM Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) kp
      (F.fiber p₀ (actual p₀))) sX sZ a b N H Cc)
    {κ : Type*} [Fintype κ] (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ j, ContDiff ℝ (⊤ : ℕ∞) (φ j)) (hφp : ∀ j, IsZ2Periodic (φ j))
    (hcs : ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) kp
        (F.fiber p₀ (actual p₀))).edge v u d, ∀ w t X z,
        γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z)
    {t : ℝ} (ht : (ocEll q Λ m ν ^ 2)⁻¹ * t ∈ Icc a b) (v : ι)
    (hfam : ∀ {U : Vec 2 → ∀ i, h i}, ContDiff ℝ (D : ℕ∞) U → ∀ (x : Vec 2) (a₀ : Fin 2),
      ∑ i' : ι, ∑ d : admissibleOrders K D v i',
          edgeCoefficient F ν (ocEpsilon q Λ m) E actual K v i' d t x
            (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
              orderedDerivative word (fun y => U y i') x) a₀ =
        ∑ j : Fin 2, chartInvJacobian ⇑((F.piece p₀).material t).symm x a₀ j •
          labelEdgeFlux F ν (ocEpsilon q Λ m) E p₀ (actual p₀) t
            (fun y => U ((F.piece p₀).material t y)) v (((F.piece p₀).material t).symm x) j)
    {φt : Vec 2 → h v} (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    ((ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in unitCube, inner ℝ
        (restSource (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) kp (F.fiber p₀ (actual p₀)))
          Cc N H (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
            (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t x) v) (φt x) =
      -∫ x in unitCube, ∑ a₀ : Fin 2, inner ℝ
        (physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
          (fun y => pulseLift Cc N H (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2)
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp)) t y) v x a₀)
        (fderiv ℝ φt x (basisVec a₀))) ∧
    ∀ a₀ : Fin 2, Continuous (fun x => physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
      (fun y => pulseLift Cc N H (ocDStar q Λ m ν B / ρ)
        (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
          (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2)
        (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp)) t y) v x a₀) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc : ocEll q Λ m ν ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  have hχj := Charts.contDiff_ocChart_joint hφs α q Λ m (ocPulseChartIndex α q Λ m kp)
  have hχs : ContDiff ℝ (⊤ : ℕ∞) (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t) :=
    hχj.comp (contDiff_const.prodMk contDiff_id)
  have hψs : ContDiff ℝ (⊤ : ℕ∞)
      (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t) :=
    (Charts.contDiff_ocChartInv_joint hφs α q Λ m (ocPulseChartIndex α q Λ m kp)).comp
      (contDiff_const.prodMk contDiff_id)
  have hψχ := Charts.ocChartInv_ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t
  have hχψ := Charts.ocChart_ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t
  -- the scales
  have hsq := ocEll_sq_mul (q := q) (Λ := Λ) (m := m) hν
  have hscale : Real.sqrt (pulseLiftData α q Λ m ζ φs hφs ν B ρ (ρ / E) kp
      (F.fiber p₀ (actual p₀))).η * (ocDStar q Λ m ν B / ρ) = ocEpsilon q Λ m * ρ⁻¹ := by
    rw [mul_comm, pulse_scale_h2 α q Λ m ζ hφs hν hB he ρ (ρ / E) kp _, hsq, sq,
      mul_assoc (ocEpsilon q Λ m), mul_inv_cancel₀ he, mul_one]
  have hlam : ρ / E * ρ⁻¹ = E⁻¹ := by
    rw [div_mul_eq_mul_div, mul_inv_cancel₀ hρ.ne', one_div]
  have hee : ocEpsilon q Λ m * (ocEpsilon q Λ m / ν) = ocEll q Λ m ν ^ 2 := by
    rw [← mul_div_assoc, ← sq, ← hsq, mul_div_assoc, div_self hν.ne', mul_one]
  have hsc : (ocEll q Λ m ν ^ 2)⁻¹ * (ocEpsilon q Λ m * (ocEpsilon q Λ m / ν)) = 1 := by
    rw [hee, inv_mul_cancel₀ hc]
  -- the coarse field in the chart frame and the label lift
  have hf : ContDiff ℝ (⊤ : ℕ∞) (chartField cf φ
      (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp)) (ocEll q Λ m ν ^ 2) ρ
      ((ocEll q Λ m ν ^ 2)⁻¹ * t)) := chartField_contDiff cf φ hφ _ hχj _ ρ _
  have hVp : IsZ2Periodic (labelLift Cc N H (ocDStar q Λ m ν B / ρ)
      (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
        (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t) := fun n y =>
    funext fun u => setting_labelLift_periodic P sX sZ Cc hseq _ _
      (fun s => chartField_contDiff cf φ hφ _ hχj _ ρ s) M hM
      (fun s X n' => chartField_periodic cf φ hφp _
        (fun t' y' n'' => Charts.ocChart_latticeShift hφs α q Λ m _ t' n'' y') hρ s X n')
      (pulse_G_slow_invariant α q Λ m ζ hφs ν B hρ.ne' (ρ / E) kp (F.fiber p₀ (actual p₀)))
      hcs t ht u n y
  have hsymm : ⇑((F.piece p₀).material t).symm =
      ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t := funext fun x =>
    ((F.piece p₀).material t).symm_apply_eq.2 (by rw [hmat t]; exact (hχψ x).symm)
  have hUD : ContDiff ℝ (D : ℕ∞) (fun y => labelLift Cc N H (ocDStar q Λ m ν B / ρ)
      (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
        (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
      (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t y)) :=
    (setting_labelLift_contDiff P hsZ hseq _ _ ρ (ocEpsilon q Λ m) hf ht).comp
      (hψs.of_le (by exact_mod_cast le_top))
  have hUχ : (fun y => labelLift Cc N H (ocDStar q Λ m ν B / ρ)
      (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
        (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
      (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t
        ((F.piece p₀).material t y))) =
      labelLift Cc N H (ocDStar q Λ m ν B / ρ)
        (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
          (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t := funext fun y => by
    rw [hmat t, hψχ y]
  have hflux : ∀ x' (a₀ : Fin 2), physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
        (fun y => labelLift Cc N H (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
            (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t y)) v x' a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t) x' a₀ i₀ •
        labelEdgeFlux F ν (ocEpsilon q Λ m) E p₀ (actual p₀) t
          (labelLift Cc N H (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t) v
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t x') i₀ := by
    intro x' a₀
    have h1 := hfam hUD x' a₀
    rw [hsymm, hUχ] at h1
    rw [physEdgeFluxVec_apply]
    exact h1
  have key := setting_pulse_edge_tested P F ν (ocEpsilon q Λ m) E actual K p₀ rfl hc he hν.ne'
    hscale hlam hsc hsZ hseq _ hf ht htorus M hM hVp hχs hψs hψχ hχψ
    (Charts.ocChart_det hφs α q Λ m (ocPulseChartIndex α q Λ m kp) t)
    (fun x n => CycleReference.streamFlow_lattice_equivariant hφs _ t x n) v hflux hφt hφtp
  refine ⟨?_, fun a₀ => ?_⟩
  · rw [← integral_const_mul]
    simp only [← real_inner_smul_left]
    exact key
  · have hfun : (fun x => physEdgeFluxVec F ν (ocEpsilon q Λ m) E actual K t
        (fun y => pulseLift Cc N H (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
            (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2)
          (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp)) t y) v x a₀) =
        fun x => ∑ i₀ : Fin 2, chartInvJacobian
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t) x a₀ i₀ •
          labelEdgeFlux F ν (ocEpsilon q Λ m) E p₀ (actual p₀) t
            (labelLift Cc N H (ocDStar q Λ m ν B / ρ)
              (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
                (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t) v
            (ocChartInv α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp) t x) i₀ :=
      funext fun x => hflux x a₀
    refine (congrArg Continuous hfun).mpr ?_
    exact continuous_piola hχs hψs hψχ hχψ
      (G := fun y i₀ => labelEdgeFlux F ν (ocEpsilon q Λ m) E p₀ (actual p₀) t
        (labelLift Cc N H (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m φs hφs (ocPulseChartIndex α q Λ m kp))
            (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2) t) v y i₀)
      (fun l => (setting_labelEdgeFlux_labelLift_contDiff P F ν (ocEpsilon q Λ m) E p₀
        (actual p₀) rfl hc he hν.ne' hscale hlam hsZ hseq _ hf ht v l).continuous) a₀

end AVRegularity.CycleComparison.Reconstruction
end
