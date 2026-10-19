-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.Construction.Scales.Times
public import AVRegularity.Statements.Construction.IsAdmissibleQ
public import AVRegularity.Statements.Construction.OcA
public import AVRegularity.CycleWords.PlaneBlochCoefficients

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Genuine plane L2 preimages for single-coordinate fibre fields. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem planeFrequencySingleLift_memLp (a : Vec 2) (P : ℝ)
    (g : Lp E 2 (volume.restrict (planeFrequencyCell a P))) (m : Fin 2 → ℤ) :
    MemLp (fun x => (planeFrequencyCell a P).indicator g
      (x - planeLatticeEmbedding P m)) 2 volume := by
  have hg := (memLp_indicator_iff_restrict (planeFrequencyCell_measurable a P)).mpr
    (Lp.memLp g)
  simpa only [Function.comp_def, sub_eq_add_neg] using
    hg.comp_measurePreserving (measurePreserving_add_right volume (-planeLatticeEmbedding P m))

def planeFrequencySingleLift (a : Vec 2) (P : ℝ)
    (g : Lp E 2 (volume.restrict (planeFrequencyCell a P))) (m : Fin 2 → ℤ) :
    Lp E 2 (volume : Measure (Vec 2)) :=
  (planeFrequencySingleLift_memLp a P g m).toLp
    (fun x => (planeFrequencyCell a P).indicator g (x - planeLatticeEmbedding P m))

theorem planeFrequencySingleLift_fibre_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (g : Lp E 2 (volume.restrict (planeFrequencyCell a P))) (m : Fin 2 → ℤ) :
    planeFrequencyFibreL2 a P hP (planeFrequencySingleLift a P g m)
      =ᵐ[volume.restrict (planeFrequencyCell a P)] fun θ => lp.single 2 m (g θ) := by
  have he : planeFrequencySingleLift a P g m =ᵐ[volume]
      (fun x => (planeFrequencyCell a P).indicator g (x - planeLatticeEmbedding P m)) :=
    (planeFrequencySingleLift_memLp a P g m).coeFn_toLp
  have hc := planeFrequencyFibre_congr_ae a P he
  filter_upwards [planeFrequencyFibreL2_ae a P hP (planeFrequencySingleLift a P g m),
    hc, ae_restrict_mem (planeFrequencyCell_measurable a P)] with θ hθ hcθ hm
  rw [hθ, hcθ]
  exact planeFrequencyCell_translated_indicator_fibre a θ P hP hm g m

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual classical ordered derivatives form a native plane Sobolev carrier whenever their L2 norms are finite. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

def smoothPlaneRawJet (K : ℕ) (f : Vec 2 → E) : RawJet2 K E :=
  fun a => orderedDerivative a.2 f

omit [MeasurableSpace E] [BorelSpace E] in
theorem smoothPlaneRawJet_hasWeakJet (K : ℕ) {f : Vec 2 → E}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    HasOrderedWeakJetOn Set.univ (smoothPlaneRawJet K f) := by
  intro j w i e
  have hs : ContDiff ℝ 1 (orderedDerivative w f) :=
    ChartTransport.contDiff_orderedDerivative w (hf.of_le (by simp))
  have he := smoothVector_weak_coordinate hs i e
  have hn : orderedDerivative (Fin.snoc w i) f =
      fun x => (fderiv ℝ (orderedDerivative w f) x) (basisVec i) := by
    rw [orderedDerivative_succ]
    simp only [Fin.snoc_castSucc, Fin.snoc_last]
  change HasWeakPartialDerivOn Set.univ i (fun x => inner ℝ e (orderedDerivative w f x))
    (fun x => inner ℝ e (orderedDerivative (Fin.snoc w i) f x))
  rw [hn]
  exact he

def smoothPlaneHk (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ a : JetIndex2 K, MemLp (orderedDerivative a.2 f) 2 volume) :
    PlaneHk Set.univ K E :=
  (show PlaneHkFunction Set.univ K E from
    ⟨smoothPlaneRawJet K f,
      fun a => by simpa only [Measure.restrict_univ, smoothPlaneRawJet] using hmem a,
      smoothPlaneRawJet_hasWeakJet K hf⟩).toHk

theorem smoothPlaneHk_jet_ae (K : ℕ) (f : Vec 2 → E) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (hmem : ∀ a : JetIndex2 K, MemLp (orderedDerivative a.2 f) 2 volume)
    (j : ℕ) (hj : j ≤ K) (w : DerivativeWord2 j) :
    planeJetOrder (smoothPlaneHk K f hf hmem) j w =ᵐ[volume] orderedDerivative w f := by
  rw [planeJetOrder_eq_stored hj]
  simpa only [Measure.restrict_univ, smoothPlaneHk, smoothPlaneRawJet] using
    (show PlaneHkFunction Set.univ K E from
      ⟨smoothPlaneRawJet K f,
        fun a => by simpa only [Measure.restrict_univ, smoothPlaneRawJet] using hmem a,
        smoothPlaneRawJet_hasWeakJet K hf⟩).toHk_toFunction_ae ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Uniform smallness of the actual neighbouring-chart transition amplitude. -/

theorem transition_amplitude_le_one {α s q : ℝ} {Λ m : ℕ}
    (hα₀ : 0 < α) (hα₁ : α < 1 / 3) (hs₀ : 0 < s) (hs₁ : s < (1 - α) / 2)
    (hq : IsAdmissibleQ α s q) (hΛ : 128 ≤ Λ) (hm : 1 ≤ m) :
    ocA α q Λ (m - 1) * ocTauPP α q Λ m ≤ 1 := by
  have hE := Scales.epsilon_basic (m := m - 1) hq.1 hΛ
  have hδ := (Scales.admissible_exponent_facts hα₀ hα₁ hs₀ hs₁ hq).2.1
  have hp : ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) ≤ 1 :=
    Real.rpow_le_one hE.1.le hE.2.1 (by positivity)
  have ha := (Scales.admissible_time_scale_facts hα₀ hα₁ hs₀ hs₁ hq hΛ hm).2.2.2.2.1
  calc
    _ ≤ (2 : ℝ) ^ (-25 : ℤ) * ocEpsilon q Λ (m - 1) ^ (2 * ocDelta α q) := ha
    _ ≤ (2 : ℝ) ^ (-25 : ℤ) * 1 := mul_le_mul_of_nonneg_left hp (by positivity)
    _ ≤ 1 := by norm_num

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Bounded coefficient products preserve the actual weighted L2 stored jets. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

theorem weighted_multiplicationRawJet_memLp {K : ℕ} {U : Set (Vec 2)}
    (C : Vec 2 → E →L[ℝ] F) (hC : ContDiff ℝ (K : ℕ) C)
    (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (hw : JetMemL2On U (fun b x => q x • D b x))
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l) (a : JetIndex2 K) :
    MemLp (fun x => q x • multiplicationRawJet C D a x) 2 (volume.restrict U) := by
  simp_rw [multiplicationRawJet_pointwise_weight]
  exact multiplicationRawJet_memL2On hC hw hb a

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A fixed finite weighted L2 majorant controls every actual product jet. -/

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]

def rawProductMaskOrder {K : ℕ} (a : JetIndex2 K) (m : PositionMask a.1.val) : Fin (K + 1) :=
  ⟨maskLeftLength a.1.val m,
    Nat.lt_succ_of_le ((maskLeftLength_le a.1.val m).trans (Nat.le_of_lt_succ a.1.isLt))⟩

def weightedRawProductMajorant {K : ℕ} (A : Fin (K + 1) → ℝ)
    (D : RawJet2 K E) (q : Vec 2 → ℝ) (a : JetIndex2 K) (x : Vec 2) : ℝ :=
  ∑ m : PositionMask a.1.val, A (rawProductMaskOrder a m) *
    ‖q x • D (maskJetIndex (Nat.le_of_lt_succ a.1.isLt) m a.2) x‖

theorem weightedRawProductMajorant_nonneg {K : ℕ} (A : Fin (K + 1) → ℝ)
    (hA : ∀ l, 0 ≤ A l) (D : RawJet2 K E) (q : Vec 2 → ℝ) (a : JetIndex2 K) (x : Vec 2) :
    0 ≤ weightedRawProductMajorant A D q a x :=
  Finset.sum_nonneg (fun _ _ => mul_nonneg (hA _) (norm_nonneg _))

theorem weightedRawProduct_norm_le_majorant {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray C l.val x‖ ≤ A l)
    (D : RawJet2 K E) (q : Vec 2 → ℝ) (a : JetIndex2 K) (x : Vec 2) :
    ‖q x • multiplicationRawJet C D a x‖ ≤ weightedRawProductMajorant A D q a x := by
  rw [multiplicationRawJet_pointwise_weight]
  unfold multiplicationRawJet multiplicationTerm weightedRawProductMajorant
  apply (norm_sum_le _ _).trans
  apply Finset.sum_le_sum
  intro m _
  let l := rawProductMaskOrder a m
  let e := q x • D (maskJetIndex (Nat.le_of_lt_succ a.1.isLt) m a.2) x
  have hcomponent := PiLp.norm_apply_le (coefficientDerivativeArray C l.val x e)
    (maskWordEquiv 2 a.1.val m a.2).1
  have hop := (coefficientDerivativeArray C l.val x).le_opNorm e
  have hbudget := mul_le_mul_of_nonneg_right (hb l x) (norm_nonneg e)
  exact hcomponent.trans (hop.trans hbudget)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual weighted composition jet has a finite L2 budget in the input weighted jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_smooth_composition_word_Lp_norm_le
    {f : Vec 2 → E} {X : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (hμ : MeasurePreserving X volume volume)
    (qout qin P : Vec 2 → ℝ) (hqout : Continuous qout)
    (hout : ∀ z, 0 ≤ qout z) (hin : ∀ z, 0 ≤ qin z)
    (B : ℕ → ℝ) (n : ℕ) (w : DerivativeWord2 n) (L : ℝ) (hL : 0 ≤ L)
    (hP : ∀ z, 1 ≤ P z) (hB : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ∀ z, ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P z)
    (hweight : ∀ z, qout z * P z ^ n ≤ L * qin (X z))
    (hw : ∀ j, j ≤ n → ∀ v : DerivativeWord2 j,
      MemLp (fun x => qin x • orderedDerivative v f x) 2 volume) :
    ‖(weighted_smooth_composition_word_memLp hf hX hμ qout qin P hqout hout hin B n w L hL
      hP hB hb hweight hw).toLp (fun z => qout z • orderedDerivative w (f ∘ X) z)‖ ≤
      L * ∑ c : OrderedFinpartition n, (∏ i : Fin c.length, B (c.partSize i)) *
        ∑ v : DerivativeWord2 c.length,
          ‖(hw c.length c.length_le v).toLp (fun x => qin x • orderedDerivative v f x)‖ := by
  let J := Σ c : OrderedFinpartition n, DerivativeWord2 c.length
  let g (a : J) : Vec 2 → E := fun z => qin (X z) • orderedDerivative a.2 f (X z)
  let c (a : J) := L * ∏ i : Fin a.1.length, B (a.1.partSize i)
  have hg (a : J) : MemLp (g a) 2 volume :=
    (hw a.1.length a.1.length_le a.2).comp_measurePreserving hμ
  have hc (a : J) : 0 ≤ c a := mul_nonneg hL
    (Finset.prod_nonneg (fun i _ => hB _ (a.1.partSize_pos i) (a.1.partSize_le i)))
  have hbound : ∀ᵐ z ∂volume, ‖qout z • orderedDerivative w (f ∘ X) z‖ ≤ ∑ a : J, c a * ‖g a z‖ := by
    apply Filter.Eventually.of_forall
    intro z
    have hh := weighted_smooth_composition_word_norm_bound hf hX B n w z (P z)
      (qout z) (qin (X z)) L (hP z) (hout z) (hin (X z)) hB
      (fun j hj hn => hb j hj hn z) (hweight z)
    simpa only [J, c, g, Fintype.sum_sigma, Finset.mul_sum, Finset.sum_mul,
      mul_assoc, mul_left_comm, mul_comm] using hh
  have hlp := finite_Lp_norm_majorant volume (fun z => qout z • orderedDerivative w (f ∘ X) z)
    g (weighted_smooth_composition_word_memLp hf hX hμ qout qin P hqout hout hin B n w L hL
      hP hB hb hweight hw) hg c hc hbound
  have he (a : J) : ‖(hg a).toLp (g a)‖ =
      ‖(hw a.1.length a.1.length_le a.2).toLp (fun x => qin x • orderedDerivative a.2 f x)‖ := by
    change ‖((hw a.1.length a.1.length_le a.2).comp_measurePreserving hμ).toLp
      ((fun x => qin x • orderedDerivative a.2 f x) ∘ X)‖ = _
    rw [← Lp.toLp_compMeasurePreserving _ hμ, Lp.norm_compMeasurePreserving]
  simp_rw [he] at hlp
  simpa only [J, c, Fintype.sum_sigma, Finset.mul_sum, Finset.sum_mul, mul_assoc] using hlp

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A geometric budget for the transported initial response levels survives
the finite response recurrence. -/

theorem ennResponseMassMajorant_geometric_le (R I ε D : ℝ≥0∞)
    (hR : 1 ≤ R) (hI : 1 ≤ I) (d : ℕ → ℝ≥0∞) (J : ℕ)
    (hd : ∀ j ≤ J, d j ≤ I ^ (j + 1) * ε ^ j * D) :
    ∀ j ≤ J, ennResponseMassMajorant R ε d j ≤ (2 * R * I) ^ (j + 1) * ε ^ j * D := by
  intro j
  induction j with
  | zero =>
    intro hj
    have hh := mul_le_mul_right (hd 0 hj) R
    simp only [ennResponseMassMajorant, Nat.zero_add, pow_one, pow_zero, mul_one] at hh ⊢
    apply hh.trans
    have hc : R * I ≤ 2 * R * I := by
      simpa only [one_mul] using mul_le_mul_left (mul_le_mul_left (by norm_num : (1 : ℝ≥0∞) ≤ 2) R) I
    simpa only [pow_one, pow_zero, mul_one, mul_assoc] using mul_le_mul_left hc D
  | succ j ih =>
    intro hj
    have hh := mul_le_mul_right (add_le_add (hd (j + 1) hj)
      (mul_le_mul_right (ih (by omega)) ε)) R
    have hsmall : I ^ (j + 2) ≤ I * (2 * R * I) ^ (j + 1) := by
      have hc : I ≤ 2 * R * I := by
        calc
          I = 1 * I := by rw [one_mul]
          _ ≤ R * I := mul_le_mul_left hR I
          _ ≤ 2 * R * I := by
            simpa only [one_mul] using mul_le_mul_left (mul_le_mul_left (by norm_num : (1 : ℝ≥0∞) ≤ 2) R) I
      rw [show j + 2 = (j + 1) + 1 by omega, pow_succ]
      simpa only [mul_comm I] using mul_le_mul_left (pow_le_pow_left₀ zero_le hc (j + 1)) I
    have hlast : (2 * R * I) ^ (j + 1) ≤ I * (2 * R * I) ^ (j + 1) := by
      simpa only [one_mul] using mul_le_mul_left hI ((2 * R * I) ^ (j + 1))
    calc
      _ ≤ _ := hh
      _ = R * (I ^ (j + 2) * ε ^ (j + 1) * D +
          (2 * R * I) ^ (j + 1) * ε ^ (j + 1) * D) := by rw [pow_succ ε]; ring
      _ ≤ R * (I * (2 * R * I) ^ (j + 1) * ε ^ (j + 1) * D +
          I * (2 * R * I) ^ (j + 1) * ε ^ (j + 1) * D) :=
        mul_le_mul_right (add_le_add
          (mul_le_mul_left (mul_le_mul_left hsmall _) D)
          (mul_le_mul_left (mul_le_mul_left hlast _) D)) R
      _ = _ := by rw [show j + 1 + 1 = j + 2 by omega, pow_succ (2 * R * I)]; ring

/-! The response mass majorant is finite for finite graded initial masses. -/

theorem ennResponseMassMajorant_ne_top (R ε : ℝ≥0∞) (hR : R ≠ ⊤) (hε : ε ≠ ⊤)
    (d : ℕ → ℝ≥0∞) (J : ℕ) (hd : ∀ j ≤ J, d j ≠ ⊤) :
    ∀ j ≤ J, ennResponseMassMajorant R ε d j ≠ ⊤ := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact ENNReal.mul_ne_top hR (hd 0 hj)
  | succ j ih =>
    intro hj
    exact ENNReal.mul_ne_top hR (ENNReal.add_ne_top.mpr
      ⟨hd (j + 1) hj, ENNReal.mul_ne_top hε (ih (by omega))⟩)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Left operator multiplication preserves literal frequency normal forms and smooth coefficients. -/

section
variable {I V E F G : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

def FrequencyNormalTerm.leftMultiply (t : FrequencyNormalTerm I V E F)
    (A : V → F →L[ℝ] G) : FrequencyNormalTerm I V E G :=
  ⟨t.word, fun x => (A x).comp (t.coefficient x)⟩

def frequencyNormalFormMultiply (ts : List (FrequencyNormalTerm I V E F))
    (A : V → F →L[ℝ] G) : List (FrequencyNormalTerm I V E G) :=
  ts.map (fun t => t.leftMultiply A)
end

/-! Finite normal forms preserve every ordered frequency derivative by the exact product rule. -/

section
variable {I V E F : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

def frequencyNormalFormDerivative (ts : List (FrequencyNormalTerm I V E F))
    (direction : I → V) (i : I) : List (FrequencyNormalTerm I V E F) :=
  ts.flatMap (fun t => [t.coefficientDerivative direction i, t.inputDerivative i])
end

end AVRegularity.CycleWords
end
end
