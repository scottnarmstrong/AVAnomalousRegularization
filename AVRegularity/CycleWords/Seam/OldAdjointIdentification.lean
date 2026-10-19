-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleWords.Seam.LetterTransposeNorm
import AVRegularity.CycleWords.Seam.OldScalar.Bessel
import AVRegularity.CycleWords.CanonicalGraphCommonDriftWindowDifferenceDecay
public import AVRegularity.CycleWords.ConstructedActualWeakNativeGapDecay
public import AVRegularity.CycleWords.Seam.Leibniz

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Analysis.Convolution
open AVRegularity.CoupledEnergyPlane AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **The vector adjoint bound from scalar coordinate bounds.** If each coordinate chain
`ψ_{x,e}` of a family assembled in orthonormal bases obeys a scalar weighted jet bound with constant
`K` against the coordinate `⟨b_e, Φ_x⟩` of the test, the assembled family obeys the inverse-mass
weighted bound with constant `√(m+1)·K` (Parseval in each fibre, `familyNorm_orders_of_components`
across the orders). This is item C of the adjoint chain interface. -/

section Fibre

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_coord_ae (e : E) {K : ℕ} (u : PlaneHk Set.univ K E) (a : ℕ)
    (w : DerivativeWord2 a) :
    planeJetOrder (planeHkCoord e u) a w =ᵐ[volume]
      fun z => inner ℝ e (planeJetOrder u a w z) := by
  by_cases ha : a ≤ K
  · have h := (ae_restrict_iff' MeasurableSet.univ).mp
      ((InnerProductSpace.toDual ℝ E e).coeFn_compLpL (μ := volume.restrict Set.univ)
        (u.val ⟨⟨a, Nat.lt_succ_of_le ha⟩, w⟩))
    filter_upwards [h] with z hz
    simp only [planeJetOrder, ha, dite_true]
    change ((planeHkCoord e u).val ⟨⟨a, Nat.lt_succ_of_le ha⟩, w⟩ : Vec 2 → ℝ) z =
      inner ℝ e ((u.val ⟨⟨a, Nat.lt_succ_of_le ha⟩, w⟩ : Vec 2 → E) z)
    rw [planeHkCoord, mapPlaneHk_component, hz (Set.mem_univ z)]
    rfl
  · refine Filter.Eventually.of_forall fun z => ?_
    simp only [planeJetOrder, ha, dite_false, inner_zero_right]

theorem planeJetOrder_assemble_ae {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E) {K : ℕ}
    (ψ : n → PlaneHk Set.univ K ℝ) (a : ℕ) (w : DerivativeWord2 a) :
    planeJetOrder (planeHkAssemble B ψ) a w =ᵐ[volume]
      fun z => ∑ e, planeJetOrder (ψ e) a w z • B e := by
  by_cases ha : a ≤ K
  · set idx : JetIndex2 K := ⟨⟨a, Nat.lt_succ_of_le ha⟩, w⟩
    have hs := (ae_restrict_iff' MeasurableSet.univ).mp
      (Lp.coeFn_finsetSum (μ := volume.restrict Set.univ) Finset.univ
        (fun e => (mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight (B e)) (ψ e)).val idx))
    have hm : ∀ e, ∀ᵐ z ∂volume,
        ((mapPlaneHk ((ContinuousLinearMap.id ℝ ℝ).smulRight (B e)) (ψ e)).val idx :
          Vec 2 → E) z = ((ψ e).val idx : Vec 2 → ℝ) z • B e := by
      intro e
      have h := (ae_restrict_iff' MeasurableSet.univ).mp
        (((ContinuousLinearMap.id ℝ ℝ).smulRight (B e)).coeFn_compLpL
          (μ := volume.restrict Set.univ) ((ψ e).val idx))
      filter_upwards [h] with z hz
      rw [mapPlaneHk_component, hz (Set.mem_univ z)]
      rfl
    filter_upwards [hs, ae_all_iff.mpr hm] with z hz hzm
    simp only [planeJetOrder, ha, dite_true]
    change ((planeHkAssemble B ψ).val idx : Vec 2 → E) z = _
    rw [planeHkAssemble, planeHk_sum_component, hz (Set.mem_univ z), Finset.sum_apply]
    exact Finset.sum_congr rfl fun e _ => hzm e
  · refine Filter.Eventually.of_forall fun z => ?_
    simp only [planeJetOrder, ha, dite_false, zero_smul, Finset.sum_const_zero]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Parseval for the coordinates of a vector. -/
theorem sum_inner_sq_basis {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E) (y : E) :
    ∑ e, inner ℝ (B e) y ^ 2 = ‖y‖ ^ 2 := by
  rw [← real_inner_self_eq_norm_sq, ← B.sum_inner_mul_inner y y]
  exact Finset.sum_congr rfl fun e _ => by rw [real_inner_comm y (B e), sq]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] in
/-- Parseval for a combination of the basis. -/
theorem norm_sq_sum_smul_basis {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E)
    (c : n → ℝ) : ‖∑ e, c e • B e‖ ^ 2 = ∑ e, c e ^ 2 := by
  rw [← sum_inner_sq_basis B]
  exact Finset.sum_congr rfl fun e _ => by rw [B.orthonormal.inner_right_fintype]

end Fibre

/-- A scalar weighted jet norm is the order sum of the weighted `L²` norms. -/
theorem weightedJetNorm_unit (p : ℝ) (m : ℕ) (s r : ℝ)
    (J : ∀ _ : Unit, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → ℝ) :
    weightedJetNorm (fun _ : Unit => (1 : ℝ)) p m s r J =
      ∑ a ∈ Finset.range (m + 1), ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖J () a w z‖ ^ 2)) 2 volume := by
  unfold weightedJetNorm
  refine Finset.sum_congr rfl fun a _ => ?_
  congr 1
  rw [Fintype.sum_unique, inv_one, ENNReal.ofReal_one, one_mul, ← ENNReal.rpow_natCast,
    ← ENNReal.rpow_mul]
  norm_num

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

omit [∀ i, InnerProductSpace ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] in
/-- The weighted fibre norm of order `a` of a family, squared and summed against the masses, is the
same sum over the orthonormal coordinates. -/
theorem family_order_sq_coords (π : ι → ℝ) {n : ι → Type*}
    [∀ x, Fintype (n x)] (wt : Vec 2 → ℝ)
    (hwt : Continuous wt) (a : ℕ) (U : ∀ x, Vec 2 → DerivativeWord2 a → h x)
    (C : (Σ x, n x) → Vec 2 → DerivativeWord2 a → ℝ)
    (hU : ∀ x w, AEStronglyMeasurable (fun z => U x z w) volume)
    (hC : ∀ xe w, AEStronglyMeasurable (fun z => C xe z w) volume)
    (hpar : ∀ x, ∀ᵐ z ∂volume, ∑ w, ‖U x z w‖ ^ 2 = ∑ e, ∑ w, C ⟨x, e⟩ z w ^ 2) :
    familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹))
        (fun x => eLpNorm (fun z => wt z * Real.sqrt (∑ w, ‖U x z w‖ ^ 2)) 2 volume) =
      familyNorm (fun xe : Σ x, n x => ENNReal.ofReal ((π xe.1)⁻¹))
        (fun xe => eLpNorm (fun z => wt z * Real.sqrt (∑ w, ‖C xe z w‖ ^ 2)) 2 volume) := by
  unfold familyNorm
  congr 1
  rw [Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun x _ => ?_
  dsimp only
  have hmU : AEStronglyMeasurable (fun z => wt z * Real.sqrt (∑ w, ‖U x z w‖ ^ 2)) volume :=
    hwt.aestronglyMeasurable.mul (Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun w _ => (hU x w).norm.pow 2))
  have hmC : ∀ e, AEStronglyMeasurable
      (fun z => wt z * Real.sqrt (∑ w, ‖C ⟨x, e⟩ z w‖ ^ 2)) volume := fun e =>
    hwt.aestronglyMeasurable.mul (Real.continuous_sqrt.comp_aestronglyMeasurable
      (Finset.aestronglyMeasurable_fun_sum _ fun w _ => (hC ⟨x, e⟩ w).norm.pow 2))
  rw [eLpNorm_two_sq_real _ hmU, ← Finset.mul_sum]
  congr 1
  simp only [fun e => eLpNorm_two_sq_real _ (hmC e)]
  rw [← lintegral_finsetSum' _ fun e _ =>
    (((hmC e).aemeasurable.pow_const 2).ennreal_ofReal)]
  refine lintegral_congr_ae ?_
  filter_upwards [hpar x] with z hz
  rw [← ENNReal.ofReal_sum_of_nonneg fun e _ => sq_nonneg _]
  congr 1
  have hsq : ∀ (S : ℝ), 0 ≤ S → (wt z * Real.sqrt S) ^ 2 = wt z ^ 2 * S := fun S hS => by
    rw [mul_pow, Real.sq_sqrt hS]
  rw [hsq _ (Finset.sum_nonneg fun _ _ => sq_nonneg _), hz]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl fun e _ =>
    (hsq _ (Finset.sum_nonneg fun _ _ => sq_nonneg _)).symm

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **The vector adjoint bound** (item C of the adjoint chain interface): coordinatewise scalar
weighted jet bounds with constant `K` give the inverse-mass weighted bound of the family assembled
in orthonormal bases, with constant `√(m+1)·K`. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

theorem planeHkAssemble_weightedJetNorm_le (π : ι → ℝ) {n : ι → Type*}
    [∀ x, Fintype (n x)] (B : ∀ x, OrthonormalBasis (n x) ℝ (h x)) (m : ℕ) (p ϖ : ℝ)
    (Φ : ∀ x, PlaneHk Set.univ m (h x)) (ψ : ∀ x, n x → PlaneHk Set.univ m ℝ) (Kc : ℝ)
    (hscalar : ∀ x e, weightedJetNorm (fun _ : Unit => (1 : ℝ)) p m ϖ 1
        (fun _ i w z => planeJetOrder (ψ x e) i w z) ≤
      ENNReal.ofReal Kc * weightedJetNorm (fun _ : Unit => (1 : ℝ)) p m ϖ 1
        (fun _ i w z => planeJetOrder (planeHkCoord (B x e) (Φ x)) i w z)) :
    weightedJetNorm π p m ϖ 1
        (fun x i w z => planeJetOrder (planeHkAssemble (B x) (ψ x)) i w z) ≤
      ENNReal.ofReal (Real.sqrt (m + 1)) * ENNReal.ofReal Kc *
        weightedJetNorm π p m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) := by
  have hwtc := weight_continuous ϖ p
  set wgt : ℕ → ℝ≥0∞ := fun a => ENNReal.ofReal ((1 : ℝ) ^ a / (a.factorial : ℝ)) with hwgt
  set X : (Σ x, n x) → ℕ → ℝ≥0∞ := fun xe a => eLpNorm (fun z =>
    (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖planeJetOrder (ψ xe.1 xe.2) a w z‖ ^ 2)) 2 volume
    with hXdef
  set Y : (Σ x, n x) → ℕ → ℝ≥0∞ := fun xe a => eLpNorm (fun z =>
    (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a,
        ‖planeJetOrder (planeHkCoord (B xe.1 xe.2) (Φ xe.1)) a w z‖ ^ 2)) 2 volume with hYdef
  have hcomp : ∀ xe : Σ x, n x, ∑ a ∈ Finset.range (m + 1), wgt a * X xe a ≤
      ENNReal.ofReal Kc * ∑ a ∈ Finset.range (m + 1), wgt a * Y xe a := by
    intro xe
    have h1 := hscalar xe.1 xe.2
    rw [weightedJetNorm_unit, weightedJetNorm_unit] at h1
    exact h1
  have key := familyNorm_orders_of_components (fun xe : Σ x, n x => ENNReal.ofReal ((π xe.1)⁻¹))
    m wgt X Y (ENNReal.ofReal Kc) hcomp
  have hL : weightedJetNorm π p m ϖ 1
      (fun x i w z => planeJetOrder (planeHkAssemble (B x) (ψ x)) i w z) =
      ∑ a ∈ Finset.range (m + 1), wgt a *
        familyNorm (fun xe : Σ x, n x => ENNReal.ofReal ((π xe.1)⁻¹)) (fun xe => X xe a) := by
    rw [weightedJetNorm_eq_familyNorm]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    refine family_order_sq_coords π _ hwtc a
      (fun x z w => planeJetOrder (planeHkAssemble (B x) (ψ x)) a w z)
      (fun xe z w => planeJetOrder (ψ xe.1 xe.2) a w z)
      (fun x w => planeJetOrder_aestronglyMeasurable _ a w)
      (fun xe w => planeJetOrder_aestronglyMeasurable _ a w) (fun x => ?_)
    filter_upwards [ae_all_iff.mpr fun w => planeJetOrder_assemble_ae (B x) (ψ x) a w]
      with z hz
    simp only [hz, norm_sq_sum_smul_basis]
    exact Finset.sum_comm
  have hR : weightedJetNorm π p m ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) =
      ∑ a ∈ Finset.range (m + 1), wgt a *
        familyNorm (fun xe : Σ x, n x => ENNReal.ofReal ((π xe.1)⁻¹)) (fun xe => Y xe a) := by
    rw [weightedJetNorm_eq_familyNorm]
    refine Finset.sum_congr rfl fun a _ => ?_
    congr 1
    refine family_order_sq_coords π _ hwtc a (fun x z w => planeJetOrder (Φ x) a w z)
      (fun xe z w => planeJetOrder (planeHkCoord (B xe.1 xe.2) (Φ xe.1)) a w z)
      (fun x w => planeJetOrder_aestronglyMeasurable _ a w)
      (fun xe w => planeJetOrder_aestronglyMeasurable _ a w) (fun x => ?_)
    filter_upwards [ae_all_iff.mpr fun e => ae_all_iff.mpr fun w =>
      planeJetOrder_coord_ae (B x e) (Φ x) a w] with z hz
    simp only [hz]
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun w _ => (sum_inner_sq_basis (B x) _).symm
  rw [hL, hR]
  exact key

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergyPlane
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **Rapidly decaying test families**: every ordered jet is in `L²` with every polynomial weight
`⟨ϖz⟩^q`. The class is stable under orthonormal coordinates and their reassembly; its scalar
members are exactly those with finite weighted factorial norms at every moment; and for its members
every negative-weight jet norm is finite. -/

theorem lintegral_sq_lt_top_of_memLp {f : Vec 2 → ℝ} (hf : MemLp f 2 volume) :
    ∫⁻ z, ENNReal.ofReal (f z ^ 2) < ⊤ := by
  rw [← eLpNorm_two_sq_real f hf.aestronglyMeasurable]
  exact ENNReal.pow_lt_top hf.eLpNorm_lt_top

theorem memLp_of_lintegral_sq_ne_top {f : Vec 2 → ℝ} (hm : AEStronglyMeasurable f volume)
    (hf : ∫⁻ z, ENNReal.ofReal (f z ^ 2) ≠ ⊤) : MemLp f 2 volume := by
  rw [memLp_iff, lt_top_iff_ne_top]
  intro ht
  apply hf
  rw [← eLpNorm_two_sq_real f hm, ht]
  simp

section Carrier

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

/-- A plane carrier is rapidly decaying at scale `ϖ`: every ordered jet is in `L²` with every
polynomial weight. -/
def IsRapidPlaneHk (ϖ : ℝ) {K : ℕ} (U : PlaneHk Set.univ K E) : Prop :=
  ∀ (q j : ℕ) (w : DerivativeWord2 j),
    MemLp (fun z => polynomialMomentRoot ϖ z ^ q * ‖planeJetOrder U j w z‖) 2 volume

theorem rapid_weight_aestronglyMeasurable (ϖ : ℝ) {K : ℕ} (U : PlaneHk Set.univ K E)
    (q j : ℕ) (w : DerivativeWord2 j) :
    AEStronglyMeasurable (fun z => polynomialMomentRoot ϖ z ^ q * ‖planeJetOrder U j w z‖)
      volume :=
  ((polynomialMomentRoot_continuous ϖ).pow q).aestronglyMeasurable.mul
    (planeJetOrder_aestronglyMeasurable U j w).norm

/-- The weighted factorial norms of a rapidly decaying carrier are finite at every moment. -/
theorem weightedFactorialNormSq_ne_top_of_rapid {ϖ : ℝ} {K : ℕ} (U : PlaneHk Set.univ K E)
    (hU : IsRapidPlaneHk ϖ U) (n : ℕ) (r : ℝ) : weightedFactorialNormSq n ϖ 0 r K U ≠ ⊤ := by
  unfold weightedFactorialNormSq
  refine ENNReal.sum_ne_top.mpr fun j _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  have hpt : ∀ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
      (z 1 - (0 : Vec 2) 1) ^ 2)) ^ n * ∑ w : DerivativeWord2 j, ‖planeJetOrder U j w z‖ ^ 2) =
      ∑ w : DerivativeWord2 j,
        ENNReal.ofReal ((polynomialMomentRoot ϖ z ^ n * ‖planeJetOrder U j w z‖) ^ 2) := by
    intro z
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg fun w _ => by positivity]
    refine Finset.sum_congr rfl fun w _ => ?_
    congr 1
    rw [mul_pow, polynomialMomentRoot_pow_sq]
    unfold Weighted.planeMomentPolynomial
    simp
  rw [lintegral_congr hpt, lintegral_finsetSum' _ fun w _ =>
    ((rapid_weight_aestronglyMeasurable ϖ U n j w).aemeasurable.pow_const 2).ennreal_ofReal]
  exact ENNReal.sum_ne_top.mpr fun w _ => (lintegral_sq_lt_top_of_memLp (hU n j w)).ne

/-- Finite weighted factorial norms at every moment make a carrier rapidly decaying. -/
theorem rapid_of_weightedFactorialNormSq {ϖ r : ℝ} (hr : 0 < r) {K : ℕ}
    (U : PlaneHk Set.univ K E) (hfin : ∀ n, weightedFactorialNormSq n ϖ 0 r K U ≠ ⊤) :
    IsRapidPlaneHk ϖ U := by
  intro q j w
  by_cases hj : j ≤ K
  · refine memLp_of_lintegral_sq_ne_top (rapid_weight_aestronglyMeasurable ϖ U q j w) ?_
    have h := hfin q
    unfold weightedFactorialNormSq at h
    have hterm := ENNReal.sum_ne_top.mp h j (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
    have hcoef : ENNReal.ofReal (r ^ (2 * j) / ((j.factorial : ℝ)) ^ 2) ≠ 0 := by
      rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
      have := Nat.factorial_pos j
      positivity
    have hint : ∫⁻ z, ENNReal.ofReal ((1 + ϖ ^ 2 * ((z 0 - (0 : Vec 2) 0) ^ 2 +
        (z 1 - (0 : Vec 2) 1) ^ 2)) ^ q * ∑ w : DerivativeWord2 j,
          ‖planeJetOrder U j w z‖ ^ 2) ≠ ⊤ := by
      intro htop
      rw [htop, ENNReal.mul_top hcoef] at hterm
      exact hterm rfl
    refine ne_top_of_le_ne_top hint (lintegral_mono fun z => ENNReal.ofReal_le_ofReal ?_)
    rw [mul_pow, polynomialMomentRoot_pow_sq]
    unfold Weighted.planeMomentPolynomial
    simp only [Pi.zero_apply, sub_zero]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (f := fun w => ‖planeJetOrder U j w z‖ ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ w))
      (by positivity)
  · have hz : (fun z => polynomialMomentRoot ϖ z ^ q * ‖planeJetOrder U j w z‖) = 0 := by
      funext z
      simp [planeJetOrder, hj]
    rw [hz]
    exact MemLp.zero

/-- Coordinates of a rapidly decaying carrier are rapidly decaying. -/
theorem rapid_coord {ϖ : ℝ} {K : ℕ} (e : E) (U : PlaneHk Set.univ K E)
    (hU : IsRapidPlaneHk ϖ U) : IsRapidPlaneHk ϖ (planeHkCoord e U) := by
  intro q j w
  refine ((hU q j w).const_mul ‖e‖).of_le (rapid_weight_aestronglyMeasurable ϖ _ q j w) ?_
  filter_upwards [planeJetOrder_coord_ae e U j w] with z hz
  have hroot : 0 ≤ polynomialMomentRoot ϖ z ^ q :=
    pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _
  rw [Real.norm_of_nonneg (mul_nonneg hroot (norm_nonneg _)),
    Real.norm_of_nonneg (mul_nonneg (norm_nonneg e) (mul_nonneg hroot (norm_nonneg _))), hz,
    Real.norm_eq_abs]
  calc polynomialMomentRoot ϖ z ^ q * |inner ℝ e (planeJetOrder U j w z)|
      ≤ polynomialMomentRoot ϖ z ^ q * (‖e‖ * ‖planeJetOrder U j w z‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm _ _) hroot
    _ = _ := by ring

/-- A family assembled from rapidly decaying coordinates is rapidly decaying. -/
theorem rapid_assemble {ϖ : ℝ} {n : Type*} [Fintype n] (B : OrthonormalBasis n ℝ E) {K : ℕ}
    (ψ : n → PlaneHk Set.univ K ℝ) (hψ : ∀ e, IsRapidPlaneHk ϖ (ψ e)) :
    IsRapidPlaneHk ϖ (planeHkAssemble B ψ) := by
  intro q j w
  refine (memLp_finsetSum Finset.univ fun e _ => hψ e q j w).of_le
    (rapid_weight_aestronglyMeasurable ϖ _ q j w) ?_
  filter_upwards [planeJetOrder_assemble_ae B ψ j w] with z hz
  have hroot : 0 ≤ polynomialMomentRoot ϖ z ^ q :=
    pow_nonneg (zero_le_one.trans (polynomialMomentRoot_one_le ϖ z)) _
  rw [Real.norm_of_nonneg (mul_nonneg hroot (norm_nonneg _)),
    Real.norm_of_nonneg (Finset.sum_nonneg fun e _ => mul_nonneg hroot (norm_nonneg _)), hz,
    ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ((norm_sum_le _ _).trans (le_of_eq ?_)) hroot
  refine Finset.sum_congr rfl fun e _ => ?_
  rw [norm_smul, B.orthonormal.1 e, mul_one]

end Carrier

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Every negative-weight jet norm of a family of plane carriers is finite. -/
theorem weightedJetNorm_neg_ne_top (π : ι → ℝ) {m : ℕ} (Φ : ∀ x, PlaneHk Set.univ m (h x))
    (p ϖ : ℝ) (hp : 0 ≤ p) (j : ℕ) :
    weightedJetNorm π (-p) j ϖ 1 (fun x i w z => planeJetOrder (Φ x) i w z) ≠ ⊤ := by
  rw [weightedJetNorm_eq_familyNorm]
  refine ENNReal.sum_ne_top.mpr fun a _ => ENNReal.mul_ne_top ENNReal.ofReal_ne_top ?_
  unfold familyNorm
  refine ENNReal.rpow_ne_top_of_nonneg (by norm_num) (ENNReal.sum_ne_top.mpr fun x _ =>
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.pow_ne_top ?_))
  have hnorm : ∀ w : DerivativeWord2 a,
      MemLp (fun z => ‖planeJetOrder (Φ x) a w z‖) 2 volume := by
    intro w
    by_cases ha : a ≤ m
    · exact (planeJetOrder_memLp ha (Φ x) w).norm
    · have hz : (fun z => ‖planeJetOrder (Φ x) a w z‖) = 0 := by
        funext z
        simp [planeJetOrder, ha]
      rw [hz]
      exact MemLp.zero
  have hbound : ∀ z, ‖(1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 a, ‖planeJetOrder (Φ x) a w z‖ ^ 2)‖ ≤
      ‖∑ w : DerivativeWord2 a, ‖planeJetOrder (Φ x) a w z‖‖ := by
    intro z
    have hq : 0 ≤ ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) :=
      mul_nonneg (sq_nonneg ϖ) (add_nonneg (sq_nonneg (z 0)) (sq_nonneg (z 1)))
    have hx1 : 1 ≤ 1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by linarith
    have hw1 : (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hx1 (by linarith)
    have hw0 : 0 ≤ (1 + ϖ ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) :=
      Real.rpow_nonneg (by linarith) _
    have hs0 : 0 ≤ Real.sqrt (∑ w : DerivativeWord2 a, ‖planeJetOrder (Φ x) a w z‖ ^ 2) :=
      Real.sqrt_nonneg _
    rw [Real.norm_of_nonneg (mul_nonneg hw0 hs0),
      Real.norm_of_nonneg (Finset.sum_nonneg fun w _ => norm_nonneg _)]
    calc _ ≤ 1 * Real.sqrt (∑ w : DerivativeWord2 a, ‖planeJetOrder (Φ x) a w z‖ ^ 2) :=
          mul_le_mul_of_nonneg_right hw1 hs0
      _ ≤ ∑ w : DerivativeWord2 a, ‖planeJetOrder (Φ x) a w z‖ := by
          rw [one_mul]
          refine (sqrt_sum_le_sum_sqrt _ _ fun _ _ => sq_nonneg _).trans (le_of_eq ?_)
          exact Finset.sum_congr rfl fun w _ => Real.sqrt_sq (norm_nonneg _)
  have hmem := (memLp_finsetSum Finset.univ fun w _ => hnorm w).of_le
    (weighted_word_norm_aestronglyMeasurable ϖ (-p) _ fun w =>
      planeJetOrder_aestronglyMeasurable _ a w) (Filter.Eventually.of_forall hbound)
  exact hmem.eLpNorm_ne_top

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleWords.Assembly
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! **The transposed letter preserves rapid decay**, for almost every time: its jets grow at most
like `⟨ϖz⟩^{K_s}` times the jets of the adjoint family. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] {D : ℕ}

theorem letterTransposeHk_rapid_ae {σ : Type*} (π : ι → ℝ) (hπ : ∀ x, 0 < π x)
    (L : CycleLetter ι h D) (a b : ℝ) (J H : ℕ)
    (hL : IsCycleLetter π L (Set.Icc a b ×ˢ Set.univ) J H) (ϖ ζ : ℝ) (hϖ : 0 < ϖ) (hϖ1 : ϖ ≤ 1)
    (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1) (X₀ : Vec 2) (κ : σ → ℕ) (a' b' : ι → σ) (n d : ℕ)
    (hJ : n + d ≤ J + 1) :
    ∀ᵐ s ∂volume.restrict (Set.Icc a b), ∀ (Ψ : ∀ v, PlaneHk Set.univ (n + d) (h v))
      (hreg : LetterTermRegular L (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ),
      (∀ v, IsRapidPlaneHk ϖ (Ψ v)) → ∀ u, IsRapidPlaneHk ϖ
        (letterTransposeHk π L κ a' b' (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ hreg u) := by
  have hsch := actualTaylorJetMatrix_schur_ae π hπ L (Set.Icc a b ×ˢ Set.univ) J H hL ϖ ζ hϖ hϖ1
    hζ hζ1
  have hC0 := (analyticOriginalSource_flagged_taylor_fast_price (ι := ι) (h := h) (D := D)
    (P := Unit) (Ctx := fun _ => Unit) L.positive L.slow J).1
  filter_upwards [ae_restrict_of_ae hsch, ae_restrict_mem measurableSet_Icc] with s hs hmem
  intro Ψ hreg hΨ u q j w
  by_cases hj : j ≤ n
  · have hdom : ∀ Y' : Vec 2, (s, Y') ∈ Set.Icc a b ×ˢ (Set.univ : Set (Vec 2)) :=
      fun Y' => ⟨hmem, Set.mem_univ _⟩
    set W := maskCount (n + d) * wordCount (n + d) with hWdef
    have hW : 0 ≤ W := mul_nonneg (maskCount_nonneg _) (wordCount_nonneg _)
    set Cp := originalFlaggedTaylorFastJetPriceConstant L.positive L.slow J *
      (if L.positive then ζ else 1) with hCpdef
    have hCp : 0 ≤ Cp := mul_nonneg hC0 (by split <;> positivity)
    have hθ := hL.theta_nonneg
    -- the constant of component `v`
    set Cv : ι → ℝ := fun v => W * Real.sqrt (π u / π v) *
      ((((n + d : ℕ) : ℝ)) * (Cp * (2 * L.theta))) with hCvdef
    have hCv : ∀ v, 0 ≤ Cv v := fun v => mul_nonneg (mul_nonneg hW (Real.sqrt_nonneg _))
      (mul_nonneg (Nat.cast_nonneg _) (mul_nonneg hCp (mul_nonneg (by norm_num) hθ)))
    -- the majorant
    have hmaj : MemLp (fun z => ∑ v, ∑ idx : JetIndex2 (n + d), Cv v *
        (polynomialMomentRoot ϖ z ^ (q + L.slow) *
          ‖planeJetOrder (Ψ v) idx.1.val idx.2 z‖)) 2 volume :=
      memLp_finsetSum Finset.univ fun v _ => memLp_finsetSum Finset.univ fun idx _ =>
        (hΨ v (q + L.slow) idx.1.val idx.2).const_mul _
    refine hmaj.of_le (rapid_weight_aestronglyMeasurable ϖ _ q j w) ?_
    filter_upwards [letterTransposeHk_jet_ae π L κ a' b' (if L.positive then 1 else 0) X₀
      (ζ * ϖ) s n d Ψ hreg u ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩] with z hz
    have hroot1 := polynomialMomentRoot_one_le ϖ z
    have hroot : ∀ k : ℕ, 0 ≤ polynomialMomentRoot ϖ z ^ k := fun k =>
      pow_nonneg (zero_le_one.trans hroot1) k
    set Y : ι → ℝ := fun v => ∑ idx : JetIndex2 (n + d), ‖(Ψ v).toFunction.jet idx z‖ with hYdef
    have hY0 : ∀ v, 0 ≤ Y v := fun v => Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hYb : ∀ v idx, ‖(Ψ v).toFunction.jet idx z‖ ≤ Y v := fun v idx =>
      Finset.single_le_sum (f := fun idx => ‖(Ψ v).toFunction.jet idx z‖)
        (fun _ _ => norm_nonneg _) (Finset.mem_univ idx)
    have hent := letterTransposeJet_norm_le π hπ L a b J H hL ϖ ζ X₀ κ a' b' n d hJ s hmem
      (fun v => (Ψ v).toFunction.jet) z Y hY0 hYb u ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩
    -- each Taylor jet matrix entry is bounded by its column sum
    have hB : ∀ v, ∑ l ∈ Finset.range (n + d), actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v u ≤
        ((n + d : ℕ) : ℝ) * (Cp * polynomialMomentRoot ϖ z ^ L.slow * (2 * L.theta)) := by
      intro v
      calc ∑ l ∈ Finset.range (n + d), actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v u
          ≤ ∑ _l ∈ Finset.range (n + d), Cp * polynomialMomentRoot ϖ z ^ L.slow *
              (2 * L.theta) := by
            refine Finset.sum_le_sum fun l hl => ?_
            have hM := hs hdom 0 X₀ l (by have := Finset.mem_range.mp hl; omega) z
            refine (Finset.single_le_sum (f := fun v' =>
              actualTaylorJetMatrix π L ϖ ζ s 0 X₀ z l v' u) (fun v' _ => hM.1 v' u)
              (Finset.mem_univ v)).trans (le_of_eq_of_le rfl (hM.2.2 u) |>.trans (le_of_eq ?_))
            unfold actualTaylorJetMatrixPrice
            rw [hCpdef]
        _ = _ := by rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hroot q) (norm_nonneg _)), Real.norm_eq_abs,
      abs_of_nonneg (Finset.sum_nonneg fun v _ => Finset.sum_nonneg fun idx _ =>
        mul_nonneg (hCv v) (mul_nonneg (hroot _) (norm_nonneg _)))]
    have hpj : planeJetOrder (letterTransposeHk π L κ a' b' (if L.positive then 1 else 0) X₀
        (ζ * ϖ) s n d Ψ hreg u) j w z = letterTransposeJet π L κ a' b'
          (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d (fun v => (Ψ v).toFunction.jet) u
            ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ z := by
      simp only [planeJetOrder, hj, dite_true]
      exact hz
    rw [hpj]
    have hYsum : ∀ v, polynomialMomentRoot ϖ z ^ (q + L.slow) * Y v =
        ∑ idx : JetIndex2 (n + d), polynomialMomentRoot ϖ z ^ (q + L.slow) *
          ‖planeJetOrder (Ψ v) idx.1.val idx.2 z‖ := by
      intro v
      rw [hYdef, Finset.mul_sum]
      refine Finset.sum_congr rfl fun idx _ => ?_
      simp only [planeJetOrder, Nat.le_of_lt_succ idx.1.isLt, dite_true]
    calc polynomialMomentRoot ϖ z ^ q * ‖letterTransposeJet π L κ a' b'
          (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d (fun v => (Ψ v).toFunction.jet) u
            ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ z‖
        ≤ polynomialMomentRoot ϖ z ^ q * (W * ∑ v, Real.sqrt (π u / π v) *
            (((n + d : ℕ) : ℝ) * (Cp * polynomialMomentRoot ϖ z ^ L.slow * (2 * L.theta))) *
              Y v) := by
          refine mul_le_mul_of_nonneg_left (hent.trans ?_) (hroot q)
          rw [← hWdef]
          refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun v _ => ?_) hW
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hB v)
            (Real.sqrt_nonneg _)) (hY0 v)
      _ = ∑ v, Cv v * (polynomialMomentRoot ϖ z ^ (q + L.slow) * Y v) := by
          rw [Finset.mul_sum, Finset.mul_sum]
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [hCvdef, pow_add]
          ring
      _ = _ := by
          refine Finset.sum_congr rfl fun v _ => ?_
          rw [hYsum, Finset.mul_sum]
  · have hz : (fun z => polynomialMomentRoot ϖ z ^ q * ‖planeJetOrder (letterTransposeHk π L κ a' b'
        (if L.positive then 1 else 0) X₀ (ζ * ϖ) s n d Ψ hreg u) j w z‖) = 0 := by
      funext z
      simp [planeJetOrder, hj]
    rw [hz]
    exact MemLp.zero

end AVRegularity.CycleWords.Seam
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.CycleWords.Seam

/-! # Tools for the negative and weighted norms

* Word slots shifted by a constant, and the pointwise minimum of two slot families, are word
  slots (`s3b_isWordSlots_add`, `s3b_isWordSlots_min`).
* The weight bound `(1 + |y|²)^{p/2} ≤ 3^p (1 + |y₀|^p + |y₁|^p)` (`s3b_weight_le`).
* The negative norm is at most the weighted `L²` norm of the same weight (the term `a = 0` of
  the test norm and the weighted pairing, `s3b_negJetNorm_le_weighted`), hence at most a constant
  times the moment norm of any order `n ≥ p` (`s3b_negJetNorm_le_momentNorm`).
* The negative norm is subadditive on square-integrable fields (`s3b_negJetNorm_sub_le`) and
  increases with the weight (`s3b_negJetNorm_mono`). -/

open AVRegularity.CycleWords.Assembly

/-! ## Slots -/

section Slots

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D Nw : ℕ} {letters : Fin Nw → CycleLetter ι h D}

theorem s3b_isWordSlots_add {κ : Fin (Nw + 1) → ι → ℕ} (hκ : IsWordSlots letters κ) (c : ℕ) :
    IsWordSlots letters fun j x => κ j x + c := fun j x y o hne => by
  have := hκ j x y o hne
  dsimp only
  omega

theorem s3b_isWordSlots_min {κ κ' : Fin (Nw + 1) → ι → ℕ} (hκ : IsWordSlots letters κ)
    (hκ' : IsWordSlots letters κ') : IsWordSlots letters fun j x => min (κ j x) (κ' j x) :=
  fun j x y o hne => by
    have h1 := hκ j x y o hne
    have h2 := hκ' j x y o hne
    dsimp only
    omega

end Slots

/-! ## The weight -/

/-- `(1 + a² + b²)^{p/2} ≤ 3^p (1 + |a|^p + |b|^p)`. -/
theorem s3b_weight_le (a b : ℝ) (p : ℕ) :
    (1 + (a ^ 2 + b ^ 2)) ^ ((p : ℝ) / 2) ≤ 3 ^ p * (1 + |a| ^ p + |b| ^ p) := by
  have ha := abs_nonneg a
  have hb := abs_nonneg b
  set M := max (max 1 |a|) |b| with hM
  have hM1 : 1 ≤ M := (le_max_left _ _).trans (le_max_left _ _)
  have hMa : |a| ≤ M := (le_max_right _ _).trans (le_max_left _ _)
  have hMb : |b| ≤ M := le_max_right _ _
  have h1 : 1 + (a ^ 2 + b ^ 2) ≤ (1 + |a| + |b|) ^ 2 := by
    have : a ^ 2 = |a| ^ 2 := (sq_abs a).symm
    have : b ^ 2 = |b| ^ 2 := (sq_abs b).symm
    nlinarith [mul_nonneg ha hb]
  have h2 : (1 + (a ^ 2 + b ^ 2)) ^ ((p : ℝ) / 2) ≤ (1 + |a| + |b|) ^ p := by
    calc (1 + (a ^ 2 + b ^ 2)) ^ ((p : ℝ) / 2) ≤ ((1 + |a| + |b|) ^ 2) ^ ((p : ℝ) / 2) :=
          Real.rpow_le_rpow (by positivity) h1 (by positivity)
      _ = (1 + |a| + |b|) ^ p := by
          rw [← Real.rpow_natCast (1 + |a| + |b|) 2, ← Real.rpow_mul (by positivity)]
          rw [show ((2 : ℕ) : ℝ) * ((p : ℝ) / 2) = (p : ℝ) by push_cast; ring, Real.rpow_natCast]
  have h3 : (1 + |a| + |b|) ^ p ≤ (3 * M) ^ p :=
    pow_le_pow_left₀ (by positivity) (by linarith) p
  have h4 : M ^ p ≤ 1 + |a| ^ p + |b| ^ p := by
    have hap : 0 ≤ |a| ^ p := by positivity
    have hbp : 0 ≤ |b| ^ p := by positivity
    rcases le_total (max 1 |a|) |b| with hmb | hmb
    · rw [hM, max_eq_right hmb]
      linarith
    · rw [hM, max_eq_left hmb]
      rcases le_total 1 |a| with hma | hma
      · rw [max_eq_right hma]
        linarith
      · rw [max_eq_left hma, one_pow]
        linarith
  calc _ ≤ (1 + |a| + |b|) ^ p := h2
    _ ≤ (3 * M) ^ p := h3
    _ = 3 ^ p * M ^ p := mul_pow _ _ _
    _ ≤ 3 ^ p * (1 + |a| ^ p + |b| ^ p) := mul_le_mul_of_nonneg_left h4 (by positivity)

/-- The weight of the norms, in the plane variable. -/
theorem s3b_weight_le' (s : ℝ) (z : Vec 2) (p : ℕ) :
    (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) ≤
      3 ^ p * (1 + |s * z 0| ^ p + |s * z 1| ^ p) := by
  have := s3b_weight_le (s * z 0) (s * z 1) p
  rwa [show (s * z 0) ^ 2 + (s * z 1) ^ 2 = s ^ 2 * (z 0 ^ 2 + z 1 ^ 2) by ring] at this

/-! ## The negative norm -/

section Negative

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)]

/-- The term `a = 0` of the test norm is the weighted `L²` norm of the test. -/
theorem s3b_test_term_le (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ) (φ : ∀ x, Vec 2 → h x) :
    familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm (fun z =>
        (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) * ‖φ x z‖) 2 volume) ≤
      weightedJetNorm π (-p) j s r (fun x _ wd z => orderedDerivative wd (φ x) z) := by
  unfold weightedJetNorm
  refine le_trans (le_of_eq ?_) (Finset.single_le_sum (f := fun a => ENNReal.ofReal
      (r ^ a / (a.factorial : ℝ)) * (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖orderedDerivative w (φ v) z‖ ^ 2)) 2 volume ^ 2) ^
            (1 / 2 : ℝ)) (fun _ _ => zero_le) (Finset.mem_range.2 (Nat.succ_pos j)))
  simp only [pow_zero, Nat.factorial_zero, Nat.cast_one, div_one, ENNReal.ofReal_one, one_mul]
  have hfun : ∀ v, (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) *
      Real.sqrt (∑ w : DerivativeWord2 0, ‖orderedDerivative w (φ v) z‖ ^ 2)) =
      fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (-p / 2) * ‖φ v z‖ := by
    intro v
    funext z
    rw [Fintype.sum_unique, Real.sqrt_sq (norm_nonneg _)]
    simp [orderedDerivative]
  simp only [hfun]
  rfl

/-- **First half**: the negative norm is at most the weighted `L²` norm of the same weight. -/
theorem s3b_negJetNorm_le_weighted (π : ι → ℝ) (hπ : ∀ x, 0 < π x) (p : ℝ) (j : ℕ) (s r : ℝ)
    (G : ∀ x, Vec 2 → h x) (hG : ∀ x, AEStronglyMeasurable (G x) volume) :
    negJetNorm π p j s r G ≤ familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm
      (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) * ‖G x z‖) 2 volume) := by
  unfold negJetNorm
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun htest => ?_
  refine (weighted_fun_family_pairing_le π hπ G φ hG
    (fun x => (hφ x).1.continuous.aestronglyMeasurable) p s).trans ?_
  calc _ ≤ familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm (fun z =>
        (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ (p / 2) * ‖G x z‖) 2 volume) * 1 :=
        mul_le_mul_right ((s3b_test_term_le π p j s r φ).trans htest) _
    _ = _ := mul_one _

/-- **Second half**: the weighted `L²` norm of weight `p` is at most `3^{p+1} p!` times the
moment norm of any order `n ≥ p`. -/
theorem s3b_weighted_le_momentNorm (π : ι → ℝ) {p n : ℕ} (hpn : p ≤ n) (s : ℝ)
    (G : ∀ x, Vec 2 → h x) (hG : ∀ x, AEStronglyMeasurable (G x) volume) :
    familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹)) (fun x => eLpNorm
      (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) * ‖G x z‖) 2 volume) ≤
      ENNReal.ofReal (3 ^ (p + 1) * p.factorial) * momentNorm π n s G := by
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hc
  let β : Fin 3 → ℕ × ℕ := ![(0, 0), (p, 0), (0, p)]
  have hβ : ∀ i, β i ∈ momentIndices n := by
    intro i
    fin_cases i <;> simp [β, momentIndices] <;> omega
  have hβf : ∀ i, ((β i).1.factorial * (β i).2.factorial : ℝ) ≤ p.factorial := by
    intro i
    fin_cases i <;> simp [β, Nat.one_le_iff_ne_zero, Nat.factorial_ne_zero]
  have hmaj := familyNorm_eLpNorm_majorant c Finset.univ (fun _ : Fin 3 => (3 : ℝ) ^ p)
    (fun _ _ => by positivity)
    (fun x z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) * ‖G x z‖)
    (fun x => ((weight_continuous s p).aestronglyMeasurable).mul (hG x).norm)
    (fun i x z => ‖((s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2) • G x z‖) (fun x z => ?_)
  · refine hmaj.trans ?_
    have hterm : ∀ i, familyNorm c (fun x => eLpNorm (fun z =>
        ‖((s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2) • G x z‖) 2 volume) ≤
        ENNReal.ofReal p.factorial * momentNorm π n s G := by
      intro i
      have hnorm : (fun x => eLpNorm (fun z =>
          ‖((s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2) • G x z‖) 2 volume) =
          fun x => eLpNorm (fun z => ((s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2) • G x z) 2
            volume := by
        funext x
        exact eLpNorm_norm _ (((by fun_prop : Continuous fun z : Vec 2 =>
          (s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2).aestronglyMeasurable).smul (hG x))
      rw [hnorm]
      have hfa : (0 : ℝ) < ((β i).1.factorial * (β i).2.factorial : ℕ) := by positivity
      have hone : familyNorm c (fun x => eLpNorm (fun z =>
          ((s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2) • G x z) 2 volume) =
          ENNReal.ofReal ((β i).1.factorial * (β i).2.factorial : ℕ) *
            (ENNReal.ofReal ((((β i).1.factorial * (β i).2.factorial : ℕ) : ℝ)⁻¹) *
              familyNorm c (fun x => eLpNorm (fun z =>
                ((s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2) • G x z) 2 volume)) := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul hfa.le, mul_inv_cancel₀ hfa.ne', ENNReal.ofReal_one,
          one_mul]
      rw [hone]
      refine mul_le_mul' (ENNReal.ofReal_le_ofReal (by exact_mod_cast hβf i)) ?_
      unfold momentNorm
      exact Finset.single_le_sum (f := fun β : ℕ × ℕ =>
        ENNReal.ofReal (((β.1.factorial * β.2.factorial : ℕ) : ℝ)⁻¹) *
          (∑ v, ENNReal.ofReal ((π v)⁻¹) *
            eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2) • G v z) 2 volume ^ 2) ^
              (1 / 2 : ℝ)) (fun _ _ => zero_le) (hβ i)
    calc ∑ i : Fin 3, ENNReal.ofReal ((3 : ℝ) ^ p) * familyNorm c (fun x => eLpNorm (fun z =>
          ‖((s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2) • G x z‖) 2 volume)
        ≤ ∑ _i : Fin 3, ENNReal.ofReal ((3 : ℝ) ^ p) *
            (ENNReal.ofReal p.factorial * momentNorm π n s G) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_right (hterm i) _
      _ = _ := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc,
            ← mul_assoc]
          congr 1
          rw [show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by positivity)]
          congr 1
          ring
  · -- the pointwise majorant
    have hw := s3b_weight_le' s z p
    have hw0 : 0 ≤ (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) := by positivity
    rw [abs_of_nonneg (mul_nonneg hw0 (norm_nonneg _))]
    simp only [Fin.sum_univ_three, β, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_zero, mul_one, one_mul,
      norm_smul, Real.norm_eq_abs, abs_pow]
    calc (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) * ‖G x z‖
        ≤ 3 ^ p * (1 + |s * z 0| ^ p + |s * z 1| ^ p) * ‖G x z‖ :=
          mul_le_mul_of_nonneg_right hw (norm_nonneg _)
      _ = _ := by ring

/-- **Negative norm by moment norm**: the negative norm of weight `p` is at most `3^{p+1} p!` times the moment norm of any
order `n ≥ p`. -/
theorem s3b_negJetNorm_le_momentNorm (π : ι → ℝ) (hπ : ∀ x, 0 < π x) {p n : ℕ} (hpn : p ≤ n)
    (j : ℕ) (s r : ℝ) (G : ∀ x, Vec 2 → h x) (hG : ∀ x, AEStronglyMeasurable (G x) volume) :
    negJetNorm π (p : ℝ) j s r G ≤
      ENNReal.ofReal (3 ^ (p + 1) * p.factorial) * momentNorm π n s G :=
  (s3b_negJetNorm_le_weighted π hπ p j s r G hG).trans (s3b_weighted_le_momentNorm π hpn s G hG)

/-- **Subadditivity** on square-integrable fields. -/
theorem s3b_negJetNorm_sub_le (π : ι → ℝ) (p : ℝ) (j : ℕ) (s r : ℝ) (g g' : ∀ x, Vec 2 → h x)
    (hg : ∀ x, MemLp (g x) 2 volume) (hg' : ∀ x, MemLp (g' x) 2 volume) :
    negJetNorm π p j s r (fun x z => g x z - g' x z) ≤
      negJetNorm π p j s r g + negJetNorm π p j s r g' := by
  unfold negJetNorm
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun htest => ?_
  have hint : ∀ G : ∀ x, Vec 2 → h x, (∀ x, MemLp (G x) 2 volume) →
      ∀ x, Integrable (fun z => inner ℝ (G x z) (φ x z)) volume := by
    intro G hG x
    have hφ2 : MemLp (φ x) 2 volume :=
      (hφ x).1.continuous.memLp_of_hasCompactSupport (hφ x).2
    refine (L2.integrable_inner (𝕜 := ℝ) ((hG x).toLp _) (hφ2.toLp _)).congr ?_
    filter_upwards [(hG x).coeFn_toLp, hφ2.coeFn_toLp] with z h1 h2
    rw [h1, h2]
  have hsplit : ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (g x z - g' x z) (φ x z) =
      (∑ x, (π x)⁻¹ * ∫ z, inner ℝ (g x z) (φ x z)) -
        ∑ x, (π x)⁻¹ * ∫ z, inner ℝ (g' x z) (φ x z) := by
    have hx : ∀ x, (π x)⁻¹ * ∫ z, inner ℝ (g x z - g' x z) (φ x z) =
        (π x)⁻¹ * (∫ z, inner ℝ (g x z) (φ x z)) -
          (π x)⁻¹ * ∫ z, inner ℝ (g' x z) (φ x z) := by
      intro x
      rw [← mul_sub, ← integral_sub (hint g hg x) (hint g' hg' x)]
      congr 2
      funext z
      rw [inner_sub_left]
    simp only [hx, Finset.sum_sub_distrib]
  rw [hsplit]
  have habs : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => by
    rw [sub_eq_add_neg, ← abs_neg b]
    exact abs_add_le a (-b)
  refine (ENNReal.ofReal_le_ofReal (habs _ _)).trans ?_
  rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
  exact add_le_add (le_iSup_of_le φ (le_iSup_of_le hφ (le_iSup_of_le htest le_rfl)))
    (le_iSup_of_le φ (le_iSup_of_le hφ (le_iSup_of_le htest le_rfl)))

/-- The test norm of a smooth test decreases as the (negative) weight decreases. -/
theorem s3b_weightedJetNorm_neg_anti (π : ι → ℝ) {p p' : ℝ} (hpp : p ≤ p') (j : ℕ) (s r : ℝ)
    (φ : ∀ x, Vec 2 → h x) (hφ : ∀ x, ContDiff ℝ (⊤ : ℕ∞) (φ x)) :
    weightedJetNorm π (-p') j s r (fun x _ wd z => orderedDerivative wd (φ x) z) ≤
      weightedJetNorm π (-p) j s r (fun x _ wd z => orderedDerivative wd (φ x) z) := by
  unfold weightedJetNorm
  refine Finset.sum_le_sum fun a _ => mul_le_mul_right ?_ _
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ =>
    mul_le_mul_right (pow_le_pow_left₀ zero_le ?_ 2) _) (by norm_num)
  have hcont : Continuous fun z => Real.sqrt (∑ w : DerivativeWord2 a,
      ‖orderedDerivative w (φ v) z‖ ^ 2) :=
    Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ =>
      ((orderedDerivative_continuous w ((hφ v).of_le (by exact_mod_cast le_top))).norm).pow 2)
  refine eLpNorm_mono_real (((weight_continuous s (-p')).mul hcont).aestronglyMeasurable)
    fun z => ?_
  have hb : 1 ≤ 1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by
    have : 0 ≤ s ^ 2 * (z 0 ^ 2 + z 1 ^ 2) := by positivity
    linarith
  rw [Real.norm_of_nonneg (mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.sqrt_nonneg _))]
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hb (by linarith))
    (Real.sqrt_nonneg _)

/-- **Monotonicity in the weight.** -/
theorem s3b_negJetNorm_mono (π : ι → ℝ) {p p' : ℝ} (hpp : p ≤ p') (j : ℕ) (s r : ℝ)
    (g : ∀ x, Vec 2 → h x) : negJetNorm π p j s r g ≤ negJetNorm π p' j s r g := by
  unfold negJetNorm
  refine iSup_le fun φ => iSup_le fun hφ => iSup_le fun htest => ?_
  exact le_iSup_of_le φ (le_iSup_of_le hφ (le_iSup_of_le
    ((s3b_weightedJetNorm_neg_anti π hpp j s r φ fun x => (hφ x).1).trans htest) le_rfl))

end Negative

/-! ## The weighted output norm by the molecular output norm -/

section Output

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]

/-- One order `a`, one moment `β`: the weighted term with the monomial weight is `β!` times the
term of the output norm. -/
theorem s3b_output_term_eq (π : ι → ℝ) (s r : ℝ) (hr : 0 ≤ r) (a : ℕ) (β : ℕ × ℕ)
    (S : ι → Vec 2 → ℝ) :
    ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
        familyNorm (fun x => ENNReal.ofReal ((π x)⁻¹))
          (fun v => eLpNorm (fun z => (s * z 0) ^ β.1 * (s * z 1) ^ β.2 * S v z) 2 volume) =
      ENNReal.ofReal ((β.1.factorial * β.2.factorial : ℕ) : ℝ) *
        (ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) *
          (∑ v, ENNReal.ofReal ((π v)⁻¹) *
            eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a) * S v z) 2 volume ^ 2) ^
              (1 / 2 : ℝ)) := by
  have hra : 0 ≤ r ^ a := pow_nonneg hr a
  have he : ∀ v, eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a) * S v z) 2 volume =
      ENNReal.ofReal (r ^ a) *
        eLpNorm (fun z => (s * z 0) ^ β.1 * (s * z 1) ^ β.2 * S v z) 2 volume := by
    intro v
    have hf : (fun z : Vec 2 => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a) * S v z) =
        (r ^ a) • fun z => (s * z 0) ^ β.1 * (s * z 1) ^ β.2 * S v z := by
      funext z
      simp only [Pi.smul_apply, smul_eq_mul]
      ring
    rw [hf, eLpNorm_const_smul, Real.enorm_eq_ofReal hra]
  have hfam := familyNorm_mul (fun x => ENNReal.ofReal ((π x)⁻¹))
    (fun v => eLpNorm (fun z => (s * z 0) ^ β.1 * (s * z 1) ^ β.2 * S v z) 2 volume)
    (ENNReal.ofReal (r ^ a))
  unfold familyNorm at hfam
  simp only [he]
  rw [hfam]
  unfold familyNorm
  rw [← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by positivity),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 2
  have h1 : (0 : ℝ) < β.1.factorial := by exact_mod_cast Nat.factorial_pos _
  have h2 : (0 : ℝ) < β.2.factorial := by exact_mod_cast Nat.factorial_pos _
  have h3 : (0 : ℝ) < a.factorial := by exact_mod_cast Nat.factorial_pos _
  push_cast
  field_simp

/-- **Weighted output norm by molecular output norm**: the weighted output norm of weight `p`, truncated at the orders `K_out x`, is at most
`3^{p+1} p!` times the molecular output norm with `p` moments. -/
theorem s3b_weightedJetNorm_le_jetOutputNorm (π : ι → ℝ) (p M : ℕ) (s r : ℝ) (hr : 0 ≤ r)
    (Kout : ι → ℕ) (J : ∀ v, ∀ a : ℕ, DerivativeWord2 a → Vec 2 → h v)
    (hJ : ∀ v a w, AEStronglyMeasurable (J v a w) volume) :
    weightedJetNorm π (p : ℝ) M s r (fun x a wd z => if a ≤ Kout x then J x a wd z else 0) ≤
      ENNReal.ofReal (3 ^ (p + 1) * p.factorial) * jetOutputNorm π p M s r J := by
  set c : ι → ℝ≥0∞ := fun x => ENNReal.ofReal ((π x)⁻¹) with hc
  let β : Fin 3 → ℕ × ℕ := ![(0, 0), (p, 0), (0, p)]
  have hβ : ∀ i, β i ∈ momentIndices p := by
    intro i
    fin_cases i <;> simp [β, momentIndices]
  have hβf : ∀ i, ((β i).1.factorial * (β i).2.factorial : ℝ) ≤ p.factorial := by
    intro i
    fin_cases i <;> simp [β, Nat.one_le_iff_ne_zero, Nat.factorial_ne_zero]
  -- the term of the output norm
  let T : (ℕ × ℕ) → ℕ → ℝ≥0∞ := fun β a =>
    ENNReal.ofReal ((((β.1.factorial * β.2.factorial * a.factorial : ℕ)) : ℝ)⁻¹) *
      (∑ v, ENNReal.ofReal ((π v)⁻¹) *
        eLpNorm (fun z => ((s * z 0) ^ β.1 * (s * z 1) ^ β.2 * r ^ a) *
          Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ)
  have hT : ∀ i, ∑ a ∈ Finset.range (M + 1), T (β i) a ≤ jetOutputNorm π p M s r J := by
    intro i
    unfold jetOutputNorm
    exact Finset.single_le_sum (f := fun β : ℕ × ℕ => ∑ a ∈ Finset.range (M + 1), T β a)
      (fun _ _ => zero_le) (hβ i)
  -- one order
  have hone : ∀ a, ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) *
      (∑ v, c v * eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) *
        Real.sqrt (∑ w : DerivativeWord2 a,
          ‖(if a ≤ Kout v then J v a w z else 0)‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ) ≤
      ∑ i : Fin 3, ENNReal.ofReal (3 ^ p * p.factorial) * T (β i) a := by
    intro a
    set S : ι → Vec 2 → ℝ := fun v z => Real.sqrt (∑ w : DerivativeWord2 a, ‖J v a w z‖ ^ 2)
      with hS
    have hSm : ∀ v, AEStronglyMeasurable (S v) volume := fun v =>
      Real.continuous_sqrt.comp_aestronglyMeasurable
        (Finset.aestronglyMeasurable_fun_sum _ fun w _ => ((hJ v a w).norm.pow 2))
    have hTm : ∀ v (w : DerivativeWord2 a), AEStronglyMeasurable
        (fun z => if a ≤ Kout v then J v a w z else 0) volume := fun v w => by
      split_ifs
      · exact hJ v a w
      · exact aestronglyMeasurable_const
    have htr : (∑ v, c v * eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) *
        Real.sqrt (∑ w : DerivativeWord2 a,
          ‖(if a ≤ Kout v then J v a w z else 0)‖ ^ 2)) 2 volume ^ 2) ^ (1 / 2 : ℝ) ≤
        familyNorm c (fun v => eLpNorm (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^
          ((p : ℝ) / 2) * S v z) 2 volume) := by
      refine familyNorm_mono c fun v => ?_
      refine eLpNorm_mono_real ((weight_continuous s p).aestronglyMeasurable.mul
        (Real.continuous_sqrt.comp_aestronglyMeasurable (Finset.aestronglyMeasurable_fun_sum _
          fun w _ => ((hTm v w).norm.pow 2)))) fun z => ?_
      have hw0 : 0 ≤ (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) := by positivity
      rw [Real.norm_of_nonneg (mul_nonneg hw0 (Real.sqrt_nonneg _))]
      refine mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt (Finset.sum_le_sum fun w _ => ?_)) hw0
      split_ifs
      · exact le_rfl
      · simp
    -- the majorant
    have hmaj := familyNorm_eLpNorm_majorant c Finset.univ (fun _ : Fin 3 => (3 : ℝ) ^ p)
      (fun _ _ => by positivity)
      (fun v z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) * S v z)
      (fun v => (weight_continuous s p).aestronglyMeasurable.mul (hSm v))
      (fun i v z => |(s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2| * S v z) (fun v z => by
        have hw := s3b_weight_le' s z p
        have hw0 : 0 ≤ (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) := by positivity
        have hS0 : 0 ≤ S v z := Real.sqrt_nonneg _
        rw [abs_of_nonneg (mul_nonneg hw0 hS0)]
        simp only [Fin.sum_univ_three, β, Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons, pow_zero, mul_one, one_mul,
          abs_pow]
        calc (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) * S v z
            ≤ 3 ^ p * (1 + |s * z 0| ^ p + |s * z 1| ^ p) * S v z :=
              mul_le_mul_of_nonneg_right hw hS0
          _ = _ := by ring)
    have hterm : ∀ i, ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) * familyNorm c
        (fun v => eLpNorm (fun z => |(s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2| * S v z) 2
          volume) ≤ ENNReal.ofReal p.factorial * T (β i) a := by
      intro i
      have habs : (fun v => eLpNorm (fun z => |(s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2| *
          S v z) 2 volume) = fun v => eLpNorm (fun z => (s * z 0) ^ (β i).1 *
            (s * z 1) ^ (β i).2 * S v z) 2 volume := by
        funext v
        have hmono : Continuous fun z : Vec 2 => (s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2 := by
          fun_prop
        refine eLpNorm_congr_norm_ae ((continuous_abs.comp hmono).aestronglyMeasurable.mul
          (hSm v)) (hmono.aestronglyMeasurable.mul (hSm v))
          (Filter.Eventually.of_forall fun z => ?_)
        simp only [Real.norm_eq_abs, abs_mul, abs_abs]
      rw [habs, s3b_output_term_eq π s r hr a (β i) S]
      exact mul_le_mul' (ENNReal.ofReal_le_ofReal (by exact_mod_cast hβf i)) le_rfl
    calc _ ≤ ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) * familyNorm c (fun v => eLpNorm
          (fun z => (1 + s ^ 2 * (z 0 ^ 2 + z 1 ^ 2)) ^ ((p : ℝ) / 2) * S v z) 2 volume) :=
          mul_le_mul_right htr _
      _ ≤ ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) * ∑ i : Fin 3,
            ENNReal.ofReal ((3 : ℝ) ^ p) * familyNorm c (fun v => eLpNorm (fun z =>
              |(s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2| * S v z) 2 volume) :=
          mul_le_mul_right hmaj _
      _ = ∑ i : Fin 3, ENNReal.ofReal ((3 : ℝ) ^ p) *
            (ENNReal.ofReal (r ^ a / (a.factorial : ℝ)) * familyNorm c (fun v => eLpNorm
              (fun z => |(s * z 0) ^ (β i).1 * (s * z 1) ^ (β i).2| * S v z) 2 volume)) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          ring
      _ ≤ ∑ i : Fin 3, ENNReal.ofReal ((3 : ℝ) ^ p) * (ENNReal.ofReal p.factorial * T (β i) a) :=
          Finset.sum_le_sum fun i _ => mul_le_mul_right (hterm i) _
      _ = _ := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity)]
  -- all orders
  unfold weightedJetNorm
  calc _ ≤ ∑ a ∈ Finset.range (M + 1), ∑ i : Fin 3,
        ENNReal.ofReal (3 ^ p * p.factorial) * T (β i) a := Finset.sum_le_sum fun a _ => hone a
    _ = ENNReal.ofReal (3 ^ p * p.factorial) *
          ∑ i : Fin 3, ∑ a ∈ Finset.range (M + 1), T (β i) a := by
        rw [Finset.sum_comm, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
    _ ≤ ENNReal.ofReal (3 ^ p * p.factorial) * ∑ _i : Fin 3, jetOutputNorm π p M s r J :=
        mul_le_mul_right (Finset.sum_le_sum fun i _ => hT i) _
    _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ← mul_assoc]
        congr 1
        rw [show ((3 : ℕ) : ℝ≥0∞) = ENNReal.ofReal 3 by simp, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end Output

end AVRegularity.CycleWords.Seam
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.Weighted
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergyPlane AVRegularity.CoupledEnergyPlane.Fourier
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords.Seam

/-! The backward real Bloch field of a test `g` is the reversed scalar chain with datum `g`: at every
reversed time its trace is the value of any solution of
`IsPlaneChain (homogeneousChainData (G(-τ))) … (-b) (-a) (-v(-τ))` with datum `g`, at any order.
This identifies the adjoint field of the word Duhamel formulas (`wordChain_component_duhamel`) with
the solutions bounded by the package's negative-weight adjoint propagation. -/

theorem backwardField_trace_eq_reversedChain {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (Cr : ℝ) (hCrpos : 0 < Cr)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (m : ℕ) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw)
    (τ : CellCompactTime (-b) (-a)) :
    planeHkValueOperator 0 (cellEnergyPlaneRealTrace (neg_le_neg hab)
        (planeBlochBackwardRealField hab G hG v hv V hb (planeHkValueOperator m (g ()))) τ) =
      planeHkValueOperator m (ψ 0 () τ) := by
  unfold planeBlochBackwardRealField
  rw [planeBlochEnergyRealTrace_value]
  have h := scalarRealPlaneChain_blochValue (ι := Unit) (-b) (-a) (neg_le_neg hab)
    (fun _ _ => m) (fun t => G (-t)) (cellMetric_timeReverse hG)
    (fun τ z => -(v (-τ) z)) (cellDrift_timeReverse hv) V (planeBlochReversedDrift_bound hb)
    Cr hCrpos hCr _ (fun q => ψ q.1 q.2) (fun q => ψw q.1 q.2) hψ ((0 : Fin 1), ()) τ
  exact h.symm

/-- The `H¹` state of the backward field is the reversed chain, almost everywhere in time. -/
theorem backwardField_h1State_eq_reversedChain {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (Cr : ℝ) (hCrpos : 0 < Cr)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (m : ℕ) (hm : 1 ≤ m) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw) :
    ∀ᵐ τ ∂volume.restrict (Set.Icc (-b) (-a)),
      cellEnergyPlaneRealH1State (neg_le_neg hab)
          (planeBlochBackwardRealField hab G hG v hv V hb (planeHkValueOperator m (g ()))) τ =
        truncatePlaneHk hm (ψ 0 () τ) := by
  filter_upwards [cellEnergyPlaneRealH1State_value (neg_le_neg hab)
      (planeBlochBackwardRealField hab G hG v hv V hb (planeHkValueOperator m (g ()))),
    ae_restrict_mem measurableSet_Icc] with τ hτ hmem
  apply PlaneHk.ext_value isOpen_univ
  apply univToPlane.injective
  change planeHkValueOperator 1 (cellEnergyPlaneRealH1State (neg_le_neg hab)
      (planeBlochBackwardRealField hab G hG v hv V hb (planeHkValueOperator m (g ()))) τ) =
    planeHkValueOperator 1 (truncatePlaneHk hm (ψ 0 () τ))
  rw [planeHkValueOperator_truncate, hτ,
    ← backwardField_trace_eq_reversedChain hab G hG v hv V hb Cr hCrpos hCr m g ψ ψw hψ ⟨τ, hmem⟩]
  exact (planeL2ZeroCarrier_value _).symm

/-- The almost-everywhere identification at reflected times. -/
theorem backwardField_h1State_eq_reversedChain_neg {a b : ℝ} (hab : a ≤ b)
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (hG : IsCellMetric (fun t _ => G t))
    (v : ℝ → Vec 2 → Vec 2) (hv : IsCellDrift v) (V : ℝ)
    (hb : ∀ t x, ∑ i, v t x i ^ 2 ≤ V ^ 2)
    (Cr : ℝ) (hCrpos : 0 < Cr)
    (hCr : ∀ t i z, ‖cellDriftTorusSymbol (fun r x => -v (-r) x) t i z‖ ≤ Cr)
    (m : ℕ) (hm : 1 ≤ m) (g : ∀ _ : Unit, PlaneHk Set.univ m ℝ)
    (ψ : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ m ℝ)
    (ψw : ∀ (_ : Fin 1) (_ : Unit), ℝ → PlaneHk Set.univ (m + 1) ℝ)
    (hψ : IsPlaneChain (homogeneousChainData (fun τ _ => G (-τ))) (fun _ _ => m) (-b) (-a)
      (fun τ z => -(v (-τ) z)) g (fun _ _ _ => 0) ψ ψw) :
    ∀ᵐ r ∂volume, r ∈ Set.Icc a b →
      cellEnergyPlaneRealH1State (neg_le_neg hab)
          (planeBlochBackwardRealField hab G hG v hv V hb (planeHkValueOperator m (g ()))) (-r) =
        truncatePlaneHk hm (ψ 0 () (-r)) := by
  have h := backwardField_h1State_eq_reversedChain hab G hG v hv V hb Cr hCrpos hCr m hm g ψ ψw hψ
  rw [ae_restrict_iff' measurableSet_Icc] at h
  have h' := (Measure.measurePreserving_neg (volume : Measure ℝ)).quasiMeasurePreserving.ae h
  filter_upwards [h'] with r hr hmem
  exact hr ⟨neg_le_neg hmem.2, neg_le_neg hmem.1⟩

end AVRegularity.CycleWords.Seam
end
