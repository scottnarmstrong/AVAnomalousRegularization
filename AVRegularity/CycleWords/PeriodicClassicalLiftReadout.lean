-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.IntegralMultilinearPolynomialJets
import AVRegularity.CycleWords.SmoothPullbackDifference
import AVRegularity.EntryWeak.JointSourceCongruence
import AVRegularity.CycleComparison.Lift.LeftTermsBlockCoefficientBox
public import AVRegularity.EntryWeak.SourceParameterPeriodicity

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Actual smooth native compositions inherit the weighted difference bound from the input jet arrays. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_composition_difference_jet_bound {K : ℕ}
    (U V W Z : PlaneHk Set.univ K E) (f g : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : planeValue U =ᵐ[volume] f) (hv : planeValue V =ᵐ[volume] g)
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume)
    (hW : planeValue W =ᵐ[volume] f ∘ X) (hZ : planeValue Z =ᵐ[volume] g ∘ X)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout)
    (hout : ∀ z, 0 ≤ qout z) (hin : ∀ z, 0 ≤ qin z)
    (B : ℕ → ℝ) (n : ℕ) (hn : n ≤ K) (w : DerivativeWord2 n) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ n ≤ L * qin (X z))
    (R S T H : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hR : ∀ a, R a =ᵐ[volume] (fun x => qin x • U.toFunction.jet a x))
    (hS : ∀ a, S a =ᵐ[volume] (fun x => qin x • V.toFunction.jet a x))
    (hT : ∀ a, T a =ᵐ[volume] (fun x => qout x • W.toFunction.jet a x))
    (hH : ∀ a, H a =ᵐ[volume] (fun x => qout x • Z.toFunction.jet a x)) :
    ‖(T - H) ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩‖ ≤
      L * smoothPullbackOrderBound B n * ‖R - S‖ := by
  have hUV : planeValue (U - V) =ᵐ[volume] f - g := by
    filter_upwards [planeValue_sub_ae U V, hu, hv] with x hx hu' hv'
    simp only [hx, hu', hv', Pi.sub_apply]
  have hWZ : planeValue (W - Z) =ᵐ[volume] (f - g) ∘ X := by
    filter_upwards [planeValue_sub_ae W Z, hW, hZ] with x hx hw' hz'
    simp only [hx, hw', hz', Pi.sub_apply, Function.comp_apply]
  obtain ⟨hm, hnorm⟩ := weighted_composition_jet_array_bound (U - V) (hf.sub hg) hUV hX hμ
    qout qin P hqout hout hin B n hn w L hL hP hB hb hweight (R - S)
    (weightedJetArray_sub_ae U V qin R S hR hS)
  have hnative := weightedJetArray_sub_ae W Z qout T H hT hH
    ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩
  have hsmooth := weighted_smooth_jet_ae (W - Z) ((hf.sub hg).comp hX) hWZ qout hn w
  have he : hm.toLp (fun z => qout z • orderedDerivative w ((f - g) ∘ X) z) =
      (T - H) ⟨⟨n, Nat.lt_succ_of_le hn⟩, w⟩ := by
    apply Lp.ext
    exact hm.coeFn_toLp.trans (hnative.trans hsmooth).symm
  change ‖hm.toLp (fun z => qout z • orderedDerivative w ((f - g) ∘ X) z)‖ ≤
    L * smoothPullbackOrderBound B n * ‖R - S‖ at hnorm
  rw [he] at hnorm
  exact hnorm
end

/-! The finite native composition difference budget controls the entire weighted jet array. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_composition_difference_array_bound {K : ℕ}
    (U V W Z : PlaneHk Set.univ K E) (f g : Vec 2 → E)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hu : planeValue U =ᵐ[volume] f) (hv : planeValue V =ᵐ[volume] g)
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume)
    (hW : planeValue W =ᵐ[volume] f ∘ X) (hZ : planeValue Z =ᵐ[volume] g ∘ X)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout)
    (hout : ∀ z, 0 ≤ qout z) (hin : ∀ z, 0 ≤ qin z)
    (B : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ K ≤ L * qin (X z))
    (R S T H : PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hR : ∀ a, R a =ᵐ[volume] (fun x => qin x • U.toFunction.jet a x))
    (hS : ∀ a, S a =ᵐ[volume] (fun x => qin x • V.toFunction.jet a x))
    (hT : ∀ a, T a =ᵐ[volume] (fun x => qout x • W.toFunction.jet a x))
    (hH : ∀ a, H a =ᵐ[volume] (fun x => qout x • Z.toFunction.jet a x)) :
    ‖T - H‖ ≤ L * smoothPullbackNormBound B K * ‖R - S‖ := by
  apply (finiteHilbert_norm_le_sum (T - H)).trans
  have hs : (∑ a : JetIndex2 K, ‖(T - H) a‖) ≤
      ∑ a : JetIndex2 K, L * smoothPullbackOrderBound B a.1.val * ‖R - S‖ := by
    apply Finset.sum_le_sum
    intro a _
    have ha := Nat.le_of_lt_succ a.1.isLt
    exact weighted_composition_difference_jet_bound U V W Z f g hf hg hu hv hX hμ hW hZ
      qout qin P hqout hout hin B a.1.val ha a.2 L hL hP
      (fun j hj hn => hB j hj (hn.trans ha))
      (fun j hj hn => hb j hj (hn.trans ha))
      (fun z => (mul_le_mul_of_nonneg_left (pow_le_pow_right₀ (hP z) ha) (hout z)).trans
        (hweight z)) R S T H hR hS hT hH
  apply hs.trans
  unfold smoothPullbackNormBound
  rw [Finset.mul_sum, Finset.sum_mul]
end

/-! Actual smooth composition sends Cauchy weighted input jet arrays to Cauchy output arrays. -/

section
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weighted_composition_array_cauchy {K : ℕ}
    (UN WN : ℕ → PlaneHk Set.univ K E) (fN : ℕ → Vec 2 → E)
    (hs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (fN n))
    (hu : ∀ n, planeValue (UN n) =ᵐ[volume] fN n)
    {X : Vec 2 → Vec 2} (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume)
    (hW : ∀ n, planeValue (WN n) =ᵐ[volume] fN n ∘ X)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout)
    (hout : ∀ z, 0 ≤ qout z) (hin : ∀ z, 0 ≤ qin z)
    (B : ℕ → ℝ) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ K → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ K → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ K ≤ L * qin (X z))
    (RN TN : ℕ → PiLp 2 (fun _ : JetIndex2 K => Lp E 2 (volume : Measure (Vec 2))))
    (hRN : ∀ n a, RN n a =ᵐ[volume] (fun x => qin x • (UN n).toFunction.jet a x))
    (hTN : ∀ n a, TN n a =ᵐ[volume] (fun x => qout x • (WN n).toFunction.jet a x))
    (hc : CauchySeq RN) : CauchySeq TN :=
  cauchySeq_of_norm_sub_le RN TN (L * smoothPullbackNormBound B K) hc (fun n m =>
    weighted_composition_difference_array_bound (UN n) (UN m) (WN n) (WN m)
      (fN n) (fN m) (hs n) (hs m) (hu n) (hu m) hX hμ (hW n) (hW m)
      qout qin P hqout hout hin B L hL hP hB hb hweight (RN n) (RN m) (TN n) (TN m)
      (hRN n) (hRN m) (hTN n) (hTN m))
end

end AVRegularity.CycleWords
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.EntryWeakProofs AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleWords

/-! Native Fourier lifts read the original continuous periodic representative exactly. -/

theorem realClassicalLift_eq_periodic_rep (K : ℕ) (hK : 2 ≤ K)
    (u : TorusHk K ℝ) (f : Vec 2 → ℝ) (hf : Continuous f)
    (hp : AVenhance.IsZ2Periodic f)
    (he : (u.val (valueIndex2 K) : Vec 2 → ℝ) =ᵐ[volume.restrict AVenhance.unitCube] f) :
    realClassicalLift K u = f := by
  apply periodicContinuous_eq_of_cell_ae
    (realClassicalLift K u) f (realClassicalLift_contDiff K 0 (by omega) u).continuous hf
    (realClassicalLift_periodic K u) hp
  exact (realClassicalLift_value_ae K hK u).trans he

end AVRegularity.CycleWords
end
