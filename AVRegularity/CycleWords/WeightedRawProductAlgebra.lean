-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleWords.LowerCarrierTimeIntegrability
import AVRegularity.CycleEvolution.CellDriftSmoothEnergy
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.CoupledEnergy.AdmissibleOrders
import AVRegularity.Weighted.PlaneH1Readouts
import AVRegularity.CycleComparison.Residual.ChartTransport.Piola
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The actual native truncation commutes with finite error combinations. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem truncatePlaneHk_sub_sum {K : ℕ} {L : Type*} [Fintype L]
    (U : PlaneHk Set.univ (K + 1) E) (Z : L → PlaneHk Set.univ (K + 1) E) :
    truncatePlaneHk (Nat.le_succ K) (U - ∑ j, Z j) =
      truncatePlaneHk (Nat.le_succ K) U - ∑ j, truncatePlaneHk (Nat.le_succ K) (Z j) := by
  classical
  let R : PlaneHk Set.univ (K + 1) E →L[ℝ] PlaneHk Set.univ K E := truncatePlaneHk (Nat.le_succ K)
  change R (U - ∑ j, Z j) = R U - ∑ j, R (Z j)
  calc
    _ = R U - R (∑ j, Z j) := R.map_sub _ _
    _ = _ := congrArg (fun x => R U - x) (map_sum R.toLinearMap.toAddMonoidHom Z Finset.univ)

theorem native_sub_sum_congr {K : ℕ} {L : Type*} [Fintype L]
    (U V : PlaneHk Set.univ K E) (Z W : L → PlaneHk Set.univ K E)
    (hU : U = V) (hZ : ∀ j, Z j = W j) :
    U - ∑ j, Z j = V - ∑ j, W j := by
  classical
  exact congrArg₂ (fun u w : PlaneHk Set.univ K E => u - w) hU
    (Finset.sum_congr rfl (fun j _ => hZ j))

theorem truncatePlaneHk_sub_sum_eq {K : ℕ} {L : Type*} [Fintype L]
    (U : PlaneHk Set.univ (K + 1) E) (Z : L → PlaneHk Set.univ (K + 1) E)
    (V : PlaneHk Set.univ K E) (W : L → PlaneHk Set.univ K E)
    (hU : truncatePlaneHk (Nat.le_succ K) U = V)
    (hZ : ∀ j, truncatePlaneHk (Nat.le_succ K) (Z j) = W j) :
    truncatePlaneHk (Nat.le_succ K) (U - ∑ j, Z j) = V - ∑ j, W j := by
  rw [truncatePlaneHk_sub_sum]
  exact native_sub_sum_congr _ _ _ _ hU hZ

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVenhance.Infra.Torus
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! Exact periodic transfer preserves parallel invariance without any global regularity premise. -/

theorem periodicToTorus_parallel_invariant
    (e : Fin 2) (c : Vec 2 → ℂ) (hp : IsZdPeriodic c)
    (ht : ∀ (z : Vec 2) (s : ℝ), c (z + s • basisVec e) = c z)
    (y : UnitAddTorus (Fin 2)) (s : ℝ) :
    periodicToTorus c (y + torusQuotient (s • basisVec e)) = periodicToTorus c y := by
  let z := unitTorusRepresentative 2 y
  have hy : torusQuotient z = y := toUnitTorus_unitTorusRepresentative 2 y
  have he : torusQuotient (z + s • basisVec e) = y + torusQuotient (s • basisVec e) := by
    rw [map_add, hy]
  have hread (x : Vec 2) : periodicToTorus c (torusQuotient x) = c x :=
    congrFun (fromUnitTorus_periodicToTorus hp) x
  rw [← he, hread, ht z s]
  rfl

theorem periodicToTorus_parallel_fourier_zero
    (e : Fin 2) (c : Vec 2 → ℂ) (hp : IsZdPeriodic c)
    (ht : ∀ (z : Vec 2) (s : ℝ), c (z + s • basisVec e) = c z)
    (n : Fin 2 → ℤ) (hn : n e ≠ 0) : mFourierCoeff (periodicToTorus c) n = 0 :=
  mFourierCoeff_eq_zero_of_parallel_invariant e (periodicToTorus c)
    (periodicToTorus_parallel_invariant e c hp ht) n hn

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory Set
namespace AVRegularity.CycleWords

/-! A translated cell realizes any prescribed lattice coordinate. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem planeFrequencyCell_translated_indicator_coeff
    (a θ : Vec 2) (P : ℝ) (hP : 0 < P) (hθ : θ ∈ planeFrequencyCell a P)
    (g : Vec 2 → E) (m n : Fin 2 → ℤ) :
    (planeFrequencyCell a P).indicator g
      (planeLatticeEmbedding P n + θ - planeLatticeEmbedding P m) =
      (Pi.single m (g θ) : (Fin 2 → ℤ) → E) n := by
  classical
  have hx : planeLatticeEmbedding P n + θ - planeLatticeEmbedding P m =
      planeLatticeEmbedding P (n - m) + θ := by
    rw [map_sub]
    abel
  rw [hx, planeFrequencyCell_indicator_coeff a θ P hP hθ g (n - m)]
  by_cases hn : n = m
  · subst n
    simp
  · have hnm : n - m ≠ 0 := sub_ne_zero.mpr hn
    simp [hn, hnm]

theorem planeFrequencyCell_translated_indicator_fibre
    (a θ : Vec 2) (P : ℝ) (hP : 0 < P) (hθ : θ ∈ planeFrequencyCell a P)
    (g : Vec 2 → E) (m : Fin 2 → ℤ) :
    planeFrequencyFibre P (fun x => (planeFrequencyCell a P).indicator g
      (x - planeLatticeEmbedding P m)) θ =
      lp.single (E := fun _ : Fin 2 → ℤ => E) 2 m (g θ) := by
  have he : (fun n : Fin 2 → ℤ => (planeFrequencyCell a P).indicator g
      (planeLatticeEmbedding P n + θ - planeLatticeEmbedding P m)) =
      (Pi.single m (g θ) : (Fin 2 → ℤ) → E) := by
    funext n
    exact planeFrequencyCell_translated_indicator_coeff a θ P hP hθ g m n
  have hm : Memℓp (fun n : Fin 2 → ℤ => (planeFrequencyCell a P).indicator g
      (planeLatticeEmbedding P n + θ - planeLatticeEmbedding P m)) 2 := by
    rw [he]
    exact (lp.single (E := fun _ : Fin 2 → ℤ => E) 2 m (g θ)).property
  unfold planeFrequencyFibre
  rw [dite_eq_left hm]
  apply Subtype.ext
  exact he

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A genuine L2 field of lattice fibres with exactly the plane L2 norm. -/

variable {E : Type*} [NormedAddCommGroup E]

theorem planeFrequencyFibre_eLpNorm (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    eLpNorm (planeFrequencyFibre P f) 2 (volume.restrict (planeFrequencyCell a P)) =
      eLpNorm f 2 volume := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    (planeFrequencyFibre_aestronglyMeasurable a P hP f hf),
    eLpNorm_eq_lintegral_rpow_enorm_toReal
    (by norm_num : (2 : ℝ≥0∞) ≠ 0) (by norm_num : (2 : ℝ≥0∞) ≠ ⊤)
    hf.aestronglyMeasurable]
  simp only [ENNReal.toReal_ofNat]
  rw [planeFrequencyFibre_square_integral a P hP f hf]

def planeFrequencyFibreL2 (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp E 2 (volume : Measure (Vec 2))) :
    Lp (lp (fun _ : Fin 2 → ℤ => E) 2) 2 (volume.restrict (planeFrequencyCell a P)) :=
  (planeFrequencyFibre_memLp a P hP f (Lp.memLp f)).toLp (planeFrequencyFibre P f)

theorem planeFrequencyFibreL2_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp E 2 (volume : Measure (Vec 2))) :
    planeFrequencyFibreL2 a P hP f =ᵐ[volume.restrict (planeFrequencyCell a P)]
      planeFrequencyFibre P f :=
  (planeFrequencyFibre_memLp a P hP f (Lp.memLp f)).coeFn_toLp

theorem planeFrequencyFibreL2_norm (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f : Lp E 2 (volume : Measure (Vec 2))) :
    ‖planeFrequencyFibreL2 a P hP f‖ = ‖f‖ := by
  unfold planeFrequencyFibreL2
  rw [Lp.norm_toLp, planeFrequencyFibre_eLpNorm a P hP f (Lp.memLp f), Lp.norm_def]

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Continuity and time integrability of literal Sobolev truncations. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K L : ℕ}

theorem continuousOn_truncatePlaneHk (hKL : K ≤ L) {u : ℝ → PlaneHk Set.univ L E}
    {I : Set ℝ} (hu : ContinuousOn u I) :
    ContinuousOn (fun t => truncatePlaneHk hKL (u t)) I :=
  (truncatePlaneHk hKL).continuous.comp_continuousOn hu

theorem memLp_truncatePlaneHk (hKL : K ≤ L) {u : ℝ → PlaneHk Set.univ L E}
    {μ : Measure ℝ} (hu : MemLp u 2 μ) :
    MemLp (fun t => truncatePlaneHk hKL (u t)) 2 μ :=
  (truncatePlaneHk hKL).comp_memLp' hu

theorem initial_truncatePlaneHk (hKL : K ≤ L) {u f : PlaneHk Set.univ L E}
    (hu : u = f) : truncatePlaneHk hKL u = truncatePlaneHk hKL f :=
  congrArg (fun z : PlaneHk Set.univ L E => truncatePlaneHk hKL z) hu

theorem trace_truncatePlaneHk (hKL : K ≤ L)
    {w : PlaneHk Set.univ (L + 1) E} {u : PlaneHk Set.univ L E}
    (hw : truncatePlaneHk (Nat.le_succ L) w = u) :
    truncatePlaneHk (Nat.le_succ K)
      (truncatePlaneHk (Nat.succ_le_succ hKL) w) = truncatePlaneHk hKL u := by
  rw [← hw]
  apply Subtype.ext
  apply PiLp.ext
  intro a
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The order-zero representative uniquely determines the native plane weak graph. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

omit [FiniteDimensional ℝ E] in
theorem planeValue_eq_stored {K : ℕ} (U : PlaneHk Set.univ K E) :
    planeValue U = (U.val (valueIndex2 K) : Vec 2 → E) := by
  funext x
  simp only [planeValue, planeJetOrder, Nat.zero_le, dite_true]
  rfl

theorem planeHk_eq_of_planeValue_ae {K : ℕ} {U V : PlaneHk Set.univ K E}
    (h : planeValue U =ᵐ[volume] planeValue V) : U = V := by
  rw [planeValue_eq_stored, planeValue_eq_stored] at h
  apply PlaneHk.ext_value isOpen_univ
  apply Lp.ext
  simpa only [Measure.restrict_univ] using h

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A common polynomial bound on chart jets costs only the finite input derivative reserve. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem smooth_composition_polynomial_word_norm_bound {f : Vec 2 → E} {X : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (B : ℕ → ℝ) (n : ℕ) (w : DerivativeWord2 n) (z : Vec 2) (P : ℝ) (hP : 1 ≤ P)
    (hB : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P) :
    ‖orderedDerivative w (f ∘ X) z‖ ≤ P ^ n *
      ∑ c : OrderedFinpartition n,
        (∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
          ∏ i : Fin c.length, B (c.partSize i) := by
  apply (smooth_composition_pointwise_word_norm_bound hf hX (fun j => B j * P) n w z hb).trans
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro c _
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hc : 0 ≤ (∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
      ∏ i : Fin c.length, B (c.partSize i) :=
    mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg (fun i _ => hB _ (c.partSize_pos i) (c.partSize_le i)))
  calc
    _ = ((∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
        ∏ i : Fin c.length, B (c.partSize i)) * P ^ c.length := by ring
    _ ≤ ((∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
        ∏ i : Fin c.length, B (c.partSize i)) * P ^ n :=
      mul_le_mul_of_nonneg_left (pow_le_pow_right₀ hP c.length_le) hc
    _ = _ := mul_comm _ _

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.CycleEvolution
namespace AVRegularity.CycleWords

/-! Uniform geometric classical jet bounds give smooth periodic literal bivariate series. -/

theorem bivariate_geometric_summable (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q < 1) :
    Summable (fun p : ℕ × ℕ => q ^ (p.1 + p.2)) := by
  have hs := summable_geometric_of_norm_lt_one
    (by simpa only [Real.norm_eq_abs, abs_of_nonneg hq0] using hq1 : ‖q‖ < 1)
  exact (hs.mul_of_nonneg hs (fun n => pow_nonneg hq0 n) (fun n => pow_nonneg hq0 n)).congr
    (fun p => (pow_add q p.1 p.2).symm)

theorem fibreSeriesFun_contDiff_of_geometric_jets
    (a : ℕ × ℕ → ℝ → Vec 2 → ℂ) (t : ℝ)
    (ha : ∀ p, ContDiff ℝ (⊤ : ℕ∞) (a p t))
    (A : ℝ) (hA : 0 ≤ A) (C : ℕ → ℝ)
    (hb : ∀ j p x, ‖iteratedFDeriv ℝ j (a p t) x‖ ≤ C j * A ^ (p.1 + p.2))
    (ξ : Fin 2 → ℂ) (hξ : A * ‖ξ‖ < 1) :
    ContDiff ℝ (⊤ : ℕ∞) (fibreSeriesFun a ξ t) := by
  let v := fun j (p : ℕ × ℕ) => C j * (A * ‖ξ‖) ^ (p.1 + p.2)
  have hs (j : ℕ) : Summable (v j) :=
    (bivariate_geometric_summable (A * ‖ξ‖) (mul_nonneg hA (norm_nonneg ξ)) hξ).mul_left (C j)
  unfold fibreSeriesFun
  change ContDiff ℝ (⊤ : ℕ∞) (fun x => ∑' p, (fibreMonomial ξ p) • a p t x)
  apply contDiff_tsum (v := v)
    (fun p => (ha p).const_smul (fibreMonomial ξ p)) (fun j _ => hs j)
  intro j p x _
  have hc : ContDiffAt ℝ (j : WithTop ℕ∞) (a p t) x :=
    ((ha p).of_le (by simp)).contDiffAt
  rw [iteratedFDeriv_const_smul_apply' hc, norm_smul]
  have hn := mul_le_mul_of_nonneg_left (hb j p x) (norm_nonneg (fibreMonomial ξ p))
  have hC : 0 ≤ C j * A ^ (p.1 + p.2) := (norm_nonneg _).trans (hb j p x)
  have hm := mul_le_mul_of_nonneg_right (fibreMonomial_norm_le_pi ξ p) hC
  exact (hn.trans hm).trans_eq (by dsimp only [v]; rw [mul_pow]; ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus AVenhance.Infra.Torus
open AVRegularity.Analysis.Convolution
namespace AVRegularity.CycleWords

/-! The actual measurable periodic drift has a bounded torus symbol in every coordinate. -/

def cellDriftTorusSymbol (v : ℝ → Vec 2 → Vec 2) (t : ℝ) (i : Fin 2) :
    UnitAddTorus (Fin 2) → ℂ := periodicToTorus (fun x => (v t x i : ℂ))

theorem cellDriftTorusSymbol_joint_measurable (v : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift v) (i : Fin 2) :
    Measurable (fun p : ℝ × UnitAddTorus (Fin 2) => cellDriftTorusSymbol v p.1 i p.2) := by
  have hq : Measurable (fun p : ℝ × UnitAddTorus (Fin 2) =>
      (p.1, unitTorusRepresentative 2 p.2)) :=
    measurable_fst.prodMk ((measurable_unitTorusRepresentative 2).comp measurable_snd)
  exact Complex.continuous_ofReal.measurable.comp
    ((measurable_pi_apply i).comp (hv.1.comp hq))

theorem cellDriftTorusSymbol_measurable (v : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift v) (t : ℝ) (i : Fin 2) : Measurable (cellDriftTorusSymbol v t i) :=
  (cellDriftTorusSymbol_joint_measurable v hv i).comp
    (measurable_const.prodMk measurable_id)

theorem cellDriftTorusSymbol_plane (v : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift v) (t : ℝ) (i : Fin 2) (x : Vec 2) :
    cellDriftTorusSymbol v t i (torusQuotient x) = (v t x i : ℂ) := by
  have hp : IsZdPeriodic (fun x => (v t x i : ℂ)) := by
    apply (isZdPeriodic_iff_frozen _).mpr
    intro n z
    exact congrArg (fun w : Vec 2 => (w i : ℂ)) (hv.2.2.1 t n z)
  exact congrFun (fromUnitTorus_periodicToTorus hp) x

theorem cellDriftTorusSymbol_bound (v : ℝ → Vec 2 → Vec 2)
    (hv : IsCellDrift v) : ∃ C : ℝ, 0 < C ∧ ∀ t i z, ‖cellDriftTorusSymbol v t i z‖ ≤ C := by
  obtain ⟨M, hM⟩ := hv.2.1
  refine ⟨|M| + 1, by positivity, ?_⟩
  intro t i z
  let x := unitTorusRepresentative 2 z
  have hi : (v t x i) ^ 2 ≤ ∑ j : Fin 2, (v t x j) ^ 2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg (v t x j)) (Finset.mem_univ i)
  have ha : |v t x i| ≤ |M| := by
    apply (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mp
    simpa only [sq_abs] using hi.trans (hM t x)
  change ‖(v t x i : ℂ)‖ ≤ |M| + 1
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact ha.trans (le_add_of_nonneg_right (by norm_num))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Finite graph depth supplies an actual topological rank with the same reserve. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

def familyDepthSet (F : ChartedFamily ι h D P Ctx) (H : ℕ) (v : ι) : Finset ℕ := by
  classical
  exact (Finset.range (H + 1)).filter (fun n => familyReachableDepth F n v)

theorem familyDepthSet_nonempty (F : ChartedFamily ι h D P Ctx) (H : ℕ) (v : ι) :
    (familyDepthSet F H v).Nonempty := by
  classical
  refine ⟨0, ?_⟩
  simp only [familyDepthSet, Finset.mem_filter, Finset.mem_range]
  exact ⟨by omega, familyReachableDepth_zero F v⟩

def familyDepthRank (F : ChartedFamily ι h D P Ctx) (H : ℕ) (v : ι) : ℕ :=
  (familyDepthSet F H v).max' (familyDepthSet_nonempty F H v)

theorem familyDepthRank_reachable (F : ChartedFamily ι h D P Ctx) (H : ℕ) (v : ι) :
    familyReachableDepth F (familyDepthRank F H v) v := by
  classical
  have hm := Finset.max'_mem (familyDepthSet F H v) (familyDepthSet_nonempty F H v)
  exact (Finset.mem_filter.mp hm).2

theorem familyDepthRank_le (F : ChartedFamily ι h D P Ctx) (H : ℕ) (v : ι) :
    familyDepthRank F H v ≤ H := by
  classical
  unfold familyDepthRank
  have hm := Finset.max'_mem (familyDepthSet F H v) (familyDepthSet_nonempty F H v)
  have hr := Finset.mem_range.mp (Finset.mem_filter.mp hm).1
  omega

theorem familyDepthRank_strict (F : ChartedFamily ι h D P Ctx) (H : ℕ)
    (hdepth : F.HasDepthAtMost H) {u v : ι} (he : Nonempty (F.Γ v u)) :
    familyDepthRank F H u < familyDepthRank F H v := by
  have hn := familyReachableDepth_succ F (familyDepthRank_reachable F H u) he
  have hu : familyDepthRank F H u + 1 ≤ H := by
    have hb := familyDepthRank_le F H u
    by_contra hh
    have heq : familyDepthRank F H u = H := by omega
    rw [heq] at hn
    exact familyReachableDepth_not_succ_depth F H hdepth v hn
  have hm : familyDepthRank F H u + 1 ∈ familyDepthSet F H v := by
    simp only [familyDepthSet, Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hn⟩
  exact Nat.lt_of_succ_le (Finset.le_max' _ _ hm)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.CycleWords

/-! Descending slots retain every current order of each original constituent exactly once. -/

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

theorem original_order_reindex (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (hdesc : F.IsDescending K) (v u : ι) {M : Type*} [AddCommMonoid M]
    (f : F.Γ v u → ℕ → M) :
    (∑ d : admissibleOrders K D v u, ∑ γ : F.Γ v u,
      if d.1 ≤ (F.identity v u γ).maxOrder then f γ d.1 else 0) =
      ∑ γ : F.Γ v u, ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder, f γ d := by
  classical
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro γ _
  rw [Finset.sum_coe_sort (admissibleOrders K D v u)
    (fun d => if d ≤ (F.identity v u γ).maxOrder then f γ d else 0), ← Finset.sum_filter]
  have he : (admissibleOrders K D v u).filter (fun d => d ≤ (F.identity v u γ).maxOrder) =
      Finset.Icc 2 (F.identity v u γ).maxOrder := by
    ext d
    simp only [Finset.mem_filter, admissibleOrders, Finset.mem_Icc]
    constructor
    · intro hd
      exact ⟨hd.1.1.1, hd.2⟩
    · intro hd
      have hD := (F.identity v u γ).le_D
      have hk := hdesc v u γ
      exact ⟨⟨⟨hd.1, hd.2.trans hD⟩, by omega⟩, hd.2⟩
  rw [he]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory UnitAddTorus
open AVRegularity.CoupledEnergyPlane
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Genuine unitary multiplication by an integer lattice Fourier mode on plane L2. -/

theorem cellComplexFourierMode_memLp_top (n : Fin 2 → ℤ) :
    MemLp (cellComplexFourierMode n) ∞ (volume : Measure (Vec 2)) :=
  memLp_top_of_bound (cellComplexFourierMode_contDiff n).continuous.aestronglyMeasurable 1
    (Filter.Eventually.of_forall (cellComplexFourierMode_norm_le_one n))

def planeIntegerModulationOperator (n : Fin 2 → ℤ) :
    Lp ℂ 2 (volume : Measure (Vec 2)) →L[ℂ] Lp ℂ 2 (volume : Measure (Vec 2)) :=
  L2Multiplier.operator (cellComplexFourierMode n) (cellComplexFourierMode_memLp_top n)

theorem planeIntegerModulationOperator_ae (n : Fin 2 → ℤ)
    (f : Lp ℂ 2 (volume : Measure (Vec 2))) :
    planeIntegerModulationOperator n f =ᵐ[volume]
      fun x => cellComplexFourierMode n x * f x :=
  L2Multiplier.operator_ae _ _ f

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Literal ordered jet readouts agree through the retained Sobolev order. -/

theorem planeJetOrder_truncate {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    {K L r : ℕ} (hKL : K ≤ L) (hr : r ≤ K) (f : PlaneHk Set.univ L E)
    (w : DerivativeWord2 r) :
    planeJetOrder (truncatePlaneHk hKL f) r w = planeJetOrder f r w := by
  funext x
  simp only [planeJetOrder, dite_eq_left hr, dite_eq_left (hr.trans hKL)]
  rfl

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Subtraction of native fields agrees with subtraction of their weak representatives. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem planeJetOrder_sub_ae {K j : ℕ} (hj : j ≤ K) (U V : PlaneHk Set.univ K E)
    (w : DerivativeWord2 j) :
    planeJetOrder (U - V) j w =ᵐ[volume] fun x => planeJetOrder U j w x - planeJetOrder V j w x := by
  rw [planeJetOrder_eq_stored hj, planeJetOrder_eq_stored hj, planeJetOrder_eq_stored hj]
  have hh := Lp.coeFn_sub (U.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩)
    (V.val ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩)
  simp only [Measure.restrict_univ] at hh
  filter_upwards [hh] with x hx
  exact hx

theorem planeValue_sub_ae {K : ℕ} (U V : PlaneHk Set.univ K E) :
    planeValue (U - V) =ᵐ[volume] fun x => planeValue U x - planeValue V x :=
  planeJetOrder_sub_ae (Nat.zero_le K) U V Fin.elim0

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Explicit chart growth and weight comparison bound every literal weighted smooth composition jet. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_smooth_composition_word_norm_bound
    {f : Vec 2 → E} {X : Vec 2 → Vec 2}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hX : ContDiff ℝ (⊤ : ℕ∞) X)
    (B : ℕ → ℝ) (n : ℕ) (w : DerivativeWord2 n) (z : Vec 2)
    (P qout qin L : ℝ) (hP : 1 ≤ P) (hout : 0 ≤ qout) (hin : 0 ≤ qin)
    (hB : ∀ j, 1 ≤ j → j ≤ n → 0 ≤ B j)
    (hb : ∀ j, 1 ≤ j → j ≤ n → ‖iteratedFDeriv ℝ j X z‖ ≤ B j * P)
    (hweight : qout * P ^ n ≤ L * qin) :
    ‖qout • orderedDerivative w (f ∘ X) z‖ ≤
      L * ∑ c : OrderedFinpartition n,
        (∑ v : DerivativeWord2 c.length, ‖qin • orderedDerivative v f (X z)‖) *
          ∏ i : Fin c.length, B (c.partSize i) := by
  let S := ∑ c : OrderedFinpartition n,
    (∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
      ∏ i : Fin c.length, B (c.partSize i)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun c _ =>
    mul_nonneg (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg (fun i _ => hB _ (c.partSize_pos i) (c.partSize_le i))))
  have hec (c : OrderedFinpartition n) :
      (∑ v : DerivativeWord2 c.length, ‖qin • orderedDerivative v f (X z)‖) *
        ∏ i : Fin c.length, B (c.partSize i) =
      qin * ((∑ v : DerivativeWord2 c.length, ‖orderedDerivative v f (X z)‖) *
        ∏ i : Fin c.length, B (c.partSize i)) := by
    simp_rw [norm_smul, Real.norm_of_nonneg hin]
    rw [← Finset.mul_sum]
    ring
  have he : (∑ c : OrderedFinpartition n,
      (∑ v : DerivativeWord2 c.length, ‖qin • orderedDerivative v f (X z)‖) *
        ∏ i : Fin c.length, B (c.partSize i)) = qin * S := by
    simp_rw [hec]
    exact (Finset.mul_sum _ _ _).symm
  rw [norm_smul, Real.norm_of_nonneg hout, he]
  calc
    _ ≤ qout * (P ^ n * S) := mul_le_mul_of_nonneg_left
      (smooth_composition_polynomial_word_norm_bound hf hX B n w z P hP hB hb) hout
    _ = (qout * P ^ n) * S := by ring
    _ ≤ (L * qin) * S := mul_le_mul_of_nonneg_right hweight hS
    _ = _ := by ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Solving the genuine scalar mean equation with a measurable time coefficient. -/

open AVRegularity.CycleEvolution

theorem complexHomogeneous_strongTime_evolution {a b : ℝ} (hab : a ≤ b)
    (lam u : ℝ → ℂ) (hlam : IntervalIntegrable lam volume a b)
    (hu : StrongTimeRegularity a b u (fun t => lam t * u t)) :
    u b = Complex.exp (∫ t in a..b, lam t) * u a := by
  have hphase := complexPrimitivePhase_strongTime hab (fun t => -lam t) hlam.neg
  have hp := hphase.complex_mul hu
  have hz : (fun t => (Complex.exp (∫ r in a..t, -lam r) * -lam t) * u t +
      Complex.exp (∫ r in a..t, -lam r) * (lam t * u t)) = (fun _ => (0 : ℂ)) := by
    funext t
    ring
  rw [hz] at hp
  have he := hp.complex_increment (intervalIntegrable_const :
    IntervalIntegrable (fun _ : ℝ => (0 : ℂ)) volume a b)
  simp only [intervalIntegral.integral_zero, intervalIntegral.integral_same,
    Complex.exp_zero, one_mul, intervalIntegral.integral_neg] at he
  have heq := sub_eq_zero.mp he
  have hi : Complex.exp (∫ t in a..b, lam t) * Complex.exp (-(∫ t in a..b, lam t)) = 1 := by
    rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]
  calc
    u b = (Complex.exp (∫ t in a..b, lam t) * Complex.exp (-(∫ t in a..b, lam t))) * u b :=
      by rw [hi, one_mul]
    _ = Complex.exp (∫ t in a..b, lam t) *
        (Complex.exp (-(∫ t in a..b, lam t)) * u b) := mul_assoc _ _ _
    _ = _ := by rw [heq]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization Filter AVRegularity.Sobolev
open scoped Topology
namespace AVRegularity.CycleWords

/-! Actual expanding cutoff coefficients have uniform finite jet budgets, including the identity limit. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def expandingPlaneCoefficient (n : ℕ) (x : Vec 2) : E →L[ℝ] E :=
  expandingPlaneCutoff n x • ContinuousLinearMap.id ℝ E

theorem expandingPlaneCoefficient_contDiff (n : ℕ) :
    ContDiff ℝ (⊤ : ℕ∞) (expandingPlaneCoefficient (E := E) n) :=
  (expandingPlaneCutoff_contDiff n).smul contDiff_const

theorem exists_expandingPlaneCoefficient_budget (K : ℕ) :
    ∃ A : Fin (K + 1) → ℝ, (∀ l, 0 ≤ A l) ∧
      (∀ n l x, ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n) l.val x‖ ≤ A l) ∧
      (∀ l x, ‖coefficientDerivativeArray (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E)
        l.val x‖ ≤ A l) := by
  let φ : ContDiffBump (0 : Vec 2) := default
  let C : Vec 2 → E →L[ℝ] E := fun x => φ x • ContinuousLinearMap.id ℝ E
  have hC : ContDiff ℝ (⊤ : ℕ∞) C := φ.contDiff.smul contDiff_const
  have hc : HasCompactSupport C := φ.hasCompactSupport.smul_right
  obtain ⟨A, hA, hb⟩ := exists_smoothCompact_coefficient_rescale_bound C hC hc K
  have hn (n : ℕ) (l : Fin (K + 1)) (x : Vec 2) :
      ‖coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n) l.val x‖ ≤ A l := by
    have hρ : 0 ≤ ((n : ℝ) + 1)⁻¹ := by positivity
    have hρ1 : ((n : ℝ) + 1)⁻¹ ≤ 1 := by
      exact inv_le_one_of_one_le₀ (le_add_of_nonneg_left (Nat.cast_nonneg n))
    exact hb _ hρ hρ1 l x
  refine ⟨A, hA, hn, ?_⟩
  intro l x
  have he : ∀ᶠ n : ℕ in atTop, ∀ w : DerivativeWord2 l.val,
      orderedCoefficientDerivative (expandingPlaneCoefficient (E := E) n) l.val w x =
      orderedCoefficientDerivative (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) l.val w x :=
    eventually_all.mpr (fun w => expandingPlaneCutoff_coefficient_jet_eventually_eq x l.val w)
  obtain ⟨n, hne⟩ := he.exists
  have ha : coefficientDerivativeArray (expandingPlaneCoefficient (E := E) n) l.val x =
      coefficientDerivativeArray (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) l.val x := by
    ext e w
    exact congrArg (fun L : E →L[ℝ] E => L e) (hne w)
  rw [← ha]
  exact hn n l x

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Uniform derivative growth of a fixed-degree multilinear polynomial. -/

theorem homogeneousPolynomial_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ a : ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ,
      ∀ j ≤ J, ∀ z : Vec 2,
        ‖iteratedFDeriv ℝ j (fun z => a (fun _ => z)) z‖ ≤ C * ‖a‖ * (1 + ‖z‖) ^ r := by
  have hm (w : DerivativeWord2 r) := Weighted.coordinate_monomial_jet_growth J w 1
  choose A hA hb using hm
  refine ⟨∑ w, A w, Finset.sum_nonneg (fun w _ => hA w), ?_⟩
  intro a j hj z
  have he : (fun z => a (fun _ => z)) =
      fun z => ∑ w : DerivativeWord2 r, a (fun i => basisVec (w i)) * ∏ i, z (w i) := by
    funext z
    have hh := Weighted.multilinear_diagonal_coordinate_expansion a z 1
    simp only [one_smul, one_mul, smul_eq_mul] at hh
    simpa only [mul_comm] using hh
  rw [he]
  rw [show (fun z : Vec 2 => ∑ w : DerivativeWord2 r,
      a (fun i => basisVec (w i)) * ∏ i, z (w i)) =
      (∑ w : DerivativeWord2 r, (fun z => a (fun i => basisVec (w i)) * ∏ i, z (w i))) by
    funext z
    simp only [Finset.sum_apply]]
  rw [iteratedFDeriv_sum_apply]
  · calc
      _ ≤ ∑ w : DerivativeWord2 r,
          ‖iteratedFDeriv ℝ j (fun z => a (fun i => basisVec (w i)) * ∏ i, z (w i)) z‖ :=
        norm_sum_le _ _
      _ ≤ ∑ w : DerivativeWord2 r, A w * ‖a‖ * (1 + ‖z‖) ^ r := by
        apply Finset.sum_le_sum
        intro w _
        have hpoly : ContDiff ℝ (j : ℕ) (fun z : Vec 2 => ∏ i, z (w i)) :=
          contDiff_prod (fun i _ => (ContinuousLinearMap.proj (R := ℝ)
            (φ := fun _ : Fin 2 => ℝ) (w i)).contDiff)
        have hc : (fun z : Vec 2 => a (fun i => basisVec (w i)) * ∏ i, z (w i)) =
            a (fun i => basisVec (w i)) • (fun z => ∏ i, z (w i)) := rfl
        rw [hc, iteratedFDeriv_const_smul_apply hpoly.contDiffAt, norm_smul]
        have ha : ‖a (fun i => basisVec (w i))‖ ≤ ‖a‖ := by
          simpa [AVRegularity.ChartTransport.norm_basisVec] using a.le_opNorm (fun i => basisVec (w i))
        have hmono : ‖iteratedFDeriv ℝ j (fun z => ∏ i, z (w i)) z‖ ≤ A w * (1 + ‖z‖) ^ r := by
          simpa only [one_mul] using hb w j hj z
        simpa only [mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul ha hmono (norm_nonneg _) (norm_nonneg _)
      _ = _ := by rw [Finset.sum_mul, Finset.sum_mul]
  · intro w _
    apply ContDiffAt.mul contDiffAt_const
    exact (contDiff_prod (fun i _ => (ContinuousLinearMap.proj (R := ℝ)
      (φ := fun _ : Fin 2 => ℝ) (w i)).contDiff)).contDiffAt

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! Genuine lattice fibres also preserve the complex scalar action. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem planeFrequencyFibre_complex_smul_ae (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (c : ℂ) (f : Vec 2 → E) (hf : MemLp f 2 volume) :
    planeFrequencyFibre P (fun x => c • f x) =ᵐ[volume.restrict (planeFrequencyCell a P)]
      fun θ => c • planeFrequencyFibre P f θ := by
  filter_upwards [planeFrequency_L2_fibre_memℓp a P hP f hf] with θ hθf
  have hθsmul : Memℓp (fun n : Fin 2 → ℤ => c • f (planeLatticeEmbedding P n + θ)) 2 :=
    Memℓp.const_smul (f := fun n : Fin 2 → ℤ => f (planeLatticeEmbedding P n + θ)) hθf c
  simp only [planeFrequencyFibre, dite_eq_left hθsmul, dite_eq_left hθf]
  apply Subtype.ext
  rfl


theorem planeFrequencyFibreL2_complex_smul (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (c : ℂ) (f : Lp E 2 (volume : Measure (Vec 2))) :
    planeFrequencyFibreL2 a P hP (c • f) = c • planeFrequencyFibreL2 a P hP f := by
  apply Lp.ext
  have hraw := (planeFrequencyFibre_congr_ae a P (Lp.coeFn_smul c f)).trans
    (planeFrequencyFibre_complex_smul_ae a P hP c f (Lp.memLp f))
  filter_upwards [planeFrequencyFibreL2_ae a P hP (c • f), hraw,
    planeFrequencyFibreL2_ae a P hP f, Lp.coeFn_smul c (planeFrequencyFibreL2 a P hP f)]
    with θ hcf hr hf hs
  change (c • planeFrequencyFibreL2 a P hP f) θ = c • planeFrequencyFibreL2 a P hP f θ at hs
  rw [hcf, hs, hf]
  exact hr

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! The exact lattice fibre rearrangement as a real linear L2 isometry. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

omit [NormedSpace ℝ E] in
theorem planeFrequencyFibreL2_add (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (f g : Lp E 2 (volume : Measure (Vec 2))) :
    planeFrequencyFibreL2 a P hP (f + g) =
      planeFrequencyFibreL2 a P hP f + planeFrequencyFibreL2 a P hP g := by
  apply Lp.ext
  have hraw := (planeFrequencyFibre_congr_ae a P (Lp.coeFn_add f g)).trans
    (planeFrequencyFibre_add_ae a P hP f g (Lp.memLp f) (Lp.memLp g))
  filter_upwards [planeFrequencyFibreL2_ae a P hP (f + g), hraw,
    planeFrequencyFibreL2_ae a P hP f, planeFrequencyFibreL2_ae a P hP g,
    Lp.coeFn_add (planeFrequencyFibreL2 a P hP f) (planeFrequencyFibreL2 a P hP g)]
    with θ hfg hr hf hg hs
  change (planeFrequencyFibreL2 a P hP f + planeFrequencyFibreL2 a P hP g) θ =
    planeFrequencyFibreL2 a P hP f θ + planeFrequencyFibreL2 a P hP g θ at hs
  rw [hfg, hs, hf, hg]
  exact hr

theorem planeFrequencyFibreL2_smul (a : Vec 2) (P : ℝ) (hP : 0 < P)
    (c : ℝ) (f : Lp E 2 (volume : Measure (Vec 2))) :
    planeFrequencyFibreL2 a P hP (c • f) = c • planeFrequencyFibreL2 a P hP f := by
  apply Lp.ext
  have hraw := (planeFrequencyFibre_congr_ae a P (Lp.coeFn_smul c f)).trans
    (planeFrequencyFibre_smul_ae a P hP c f (Lp.memLp f))
  filter_upwards [planeFrequencyFibreL2_ae a P hP (c • f), hraw,
    planeFrequencyFibreL2_ae a P hP f, Lp.coeFn_smul c (planeFrequencyFibreL2 a P hP f)]
    with θ hcf hr hf hs
  change (c • planeFrequencyFibreL2 a P hP f) θ = c • planeFrequencyFibreL2 a P hP f θ at hs
  rw [hcf, hs, hf]
  exact hr

def planeFrequencyL2Isometry (a : Vec 2) (P : ℝ) (hP : 0 < P) :
    Lp E 2 (volume : Measure (Vec 2)) →ₗᵢ[ℝ]
      Lp (lp (fun _ : Fin 2 → ℤ => E) 2) 2 (volume.restrict (planeFrequencyCell a P)) where
  toFun := planeFrequencyFibreL2 a P hP
  map_add' := planeFrequencyFibreL2_add a P hP
  map_smul' := planeFrequencyFibreL2_smul a P hP
  norm_map' := planeFrequencyFibreL2_norm a P hP

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Polynomial chart jet growth and explicit weight transfer preserve the required smooth L2 jets. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem weighted_smooth_composition_word_memLp
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
    MemLp (fun z => qout z • orderedDerivative w (f ∘ X) z) 2 volume := by
  let g (z : Vec 2) := L * ∑ c : OrderedFinpartition n,
    (∑ v : DerivativeWord2 c.length, ‖qin (X z) • orderedDerivative v f (X z)‖) *
      ∏ i : Fin c.length, B (c.partSize i)
  have hg : MemLp g 2 volume := by
    apply MemLp.const_mul
    apply memLp_finsetSum Finset.univ
    intro c _
    apply MemLp.mul_const
    apply memLp_finsetSum Finset.univ
    intro v _
    exact ((hw c.length c.length_le v).comp_measurePreserving hμ).norm
  have hgn (z : Vec 2) : 0 ≤ g z := mul_nonneg hL
    (Finset.sum_nonneg (fun c _ => mul_nonneg
      (Finset.sum_nonneg (fun _ _ => norm_nonneg _))
      (Finset.prod_nonneg (fun i _ => hB _ (c.partSize_pos i) (c.partSize_le i)))))
  have hm : AEStronglyMeasurable (fun z => qout z • orderedDerivative w (f ∘ X) z) volume :=
    (hqout.smul (ChartTransport.contDiff_orderedDerivative (p := 0) w
      ((hf.comp hX).of_le (by simp))).continuous).aestronglyMeasurable
  apply hg.of_le hm
  apply Filter.Eventually.of_forall
  intro z
  rw [Real.norm_of_nonneg (hgn z)]
  exact weighted_smooth_composition_word_norm_bound hf hX B n w z (P z)
    (qout z) (qin (X z)) L (hP z) (hout z) (hin (X z)) hB
    (fun j hj hn => hb j hj hn z) (hweight z)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! The factorial normalization pays every coefficient derivative in a product. -/

theorem factorialRootWeight_product_le {ρ : ℝ} (hρ : 0 ≤ ρ) (l r : ℕ) :
    factorialRootWeight ρ (l + r) ≤ ρ ^ l * factorialRootWeight ρ r := by
  unfold factorialRootWeight
  rw [pow_add, ← mul_div_assoc]
  apply div_le_div_of_nonneg_left (mul_nonneg (pow_nonneg hρ l) (pow_nonneg hρ r))
    (by positivity : (0 : ℝ) < (r.factorial : ℝ))
  exact_mod_cast Nat.factorial_le (Nat.le_add_left r l)

theorem factorialWeight_product_le {ρ : ℝ} (hρ : 0 ≤ ρ) (l r : ℕ) :
    factorialWeight ρ (l + r) ≤ (ρ ^ l) ^ 2 * factorialWeight ρ r := by
  have hh := (sq_le_sq₀
    (div_nonneg (pow_nonneg hρ (l + r)) (Nat.cast_nonneg _))
    (mul_nonneg (pow_nonneg hρ l) (div_nonneg (pow_nonneg hρ r) (Nat.cast_nonneg _)))).mpr
      (factorialRootWeight_product_le hρ l r)
  simpa only [factorialRootWeight, factorialWeight, mul_pow, div_pow, ← pow_mul, Nat.mul_comm] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Weak-jet uniqueness identifies the literal identity product with the supplied native jet. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem identityCoefficient_rawJet_ae {K : ℕ} (U : PlaneHk Set.univ K E)
    (A : Fin (K + 1) → ℝ)
    (hb : ∀ l x, ‖coefficientDerivativeArray (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E)
      l.val x‖ ≤ A l) (a : JetIndex2 K) :
    multiplicationRawJet (fun _ : Vec 2 => ContinuousLinearMap.id ℝ E) U.toFunction.jet a
      =ᵐ[volume.restrict Set.univ] U.toFunction.jet a := by
  let C : Vec 2 → E →L[ℝ] E := fun _ => ContinuousLinearMap.id ℝ E
  have hc : ContDiff ℝ (K : ℕ) C := contDiff_const
  have hm := multiplicationRawJet_memL2On hc U.toFunction.memL2 hb
  have hw := multiplicationRawJet_hasOrderedWeakJetOn hc U.toFunction.hasWeakJet
    (jet_scalar_locallyIntegrable U.toFunction.memL2)
  have h0 : multiplicationRawJet C U.toFunction.jet (valueIndex2 K)
      =ᵐ[volume.restrict Set.univ] U.toFunction.jet (valueIndex2 K) := by
    apply Filter.Eventually.of_forall
    intro x
    rw [multiplicationRawJet_value]
    rfl
  exact orderedWeakJet_unique isOpen_univ hm U.toFunction.memL2 hw U.toFunction.hasWeakJet h0 a

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! Molecular normalization cancels the exact positive derivative reserve cost. -/

open AVRegularity.Sobolev

theorem molecular_scaling_price (ν e E ρ : ℝ) (hν : 0 < ν) (he : 0 < e)
    (hE : 0 < E) (hρ : 0 < ρ) (K d j a b : ℕ) :
    ((ρ / e) ^ (a + b) * (e / E) ^ a) /
        (ν * e ^ d * (E⁻¹) ^ (j + a)) *
        ((ρ ^ (a + b)) / ((a.factorial : ℝ) * (b.factorial : ℝ) * e ^ b))⁻¹ *
        (ν * ρ ^ d) * ((K.factorial : ℝ) / ((K + d).factorial : ℝ)) *
        derivativeReserveFactor (ρ / e) K d =
      (a.factorial : ℝ) * (b.factorial : ℝ) * E ^ j := by
  have ha : (a.factorial : ℝ) ≠ 0 := by positivity
  have hb : (b.factorial : ℝ) ≠ 0 := by positivity
  have hK : (K.factorial : ℝ) ≠ 0 := by positivity
  have hKd : ((K + d).factorial : ℝ) ≠ 0 := by positivity
  unfold derivativeReserveFactor
  simp only [div_pow, pow_add, inv_pow]
  field_simp

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! Truncation leaves every retained literal polynomial factorial energy unchanged. -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]

theorem weightedFactorialNormSq_truncate {K L R : ℕ} (hKL : K ≤ L) (hR : R ≤ K)
    (U : PlaneHk Set.univ L E) (n : ℕ) (ϖ r : ℝ) (zc : Vec 2) :
    weightedFactorialNormSq n ϖ zc r R (truncatePlaneHk hKL U) =
      weightedFactorialNormSq n ϖ zc r R U := by
  unfold weightedFactorialNormSq
  apply Finset.sum_congr rfl
  intro j hj
  have hJK : j ≤ K := (Nat.le_of_lt_succ (Finset.mem_range.mp hj)).trans hR
  simp_rw [planeJetOrder_truncate hKL hJK U]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleWords

/-! A uniform polynomial jet constant linear in the actual coefficient jet budget. -/

theorem variableMultilinear_polynomial_jet_budget (r J : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {T : Type*}
      (a : T → Vec 2 → ContinuousMultilinearMap ℝ (fun _ : Fin r => Vec 2) ℝ),
      (∀ t, ContDiff ℝ (J : ℕ) (a t)) → ∀ B : ℝ, 0 ≤ B →
      (∀ t (w : DerivativeWord2 r) j, j ≤ J → ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => a t x (fun i => basisVec (w i))) x‖ ≤ B) →
      ∀ t j, j ≤ J → ∀ x,
        ‖iteratedFDeriv ℝ j (fun x => a t x (fun _ => x)) x‖ ≤ C * B * (1 + ‖x‖) ^ r := by
  have hm (w : DerivativeWord2 r) := Weighted.coordinate_monomial_jet_growth J w 1
  choose A hA hb using hm
  let S : ℝ := ∑ j ∈ Finset.range (J + 1), (J.choose j : ℝ)
  let C : ℝ := S * ∑ w, A w
  have hS : 0 ≤ S := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
  refine ⟨C, mul_nonneg hS (Finset.sum_nonneg (fun w _ => hA w)), ?_⟩
  intro T a ha B hB hab t j hj x
  let m := fun (w : DerivativeWord2 r) (x : Vec 2) => ∏ i, x (w i)
  let b := fun (w : DerivativeWord2 r) (x : Vec 2) => a t x (fun i => basisVec (w i))
  have hmono (w : DerivativeWord2 r) : ContDiff ℝ (J : ℕ) (m w) :=
    contDiff_prod (fun i _ => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => ℝ) (w i)).contDiff)
  have hcoef (w : DerivativeWord2 r) : ContDiff ℝ (J : ℕ) (b w) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin r => Vec 2) ℝ
      (fun i => basisVec (w i))).contDiff.comp (ha t)
  have hterm (w : DerivativeWord2 r) := Weighted.growing_scalar_jet_product_bound J r 0
    (m w) (b w) (hmono w) (hcoef w) (A w) B (hA w) hB
    (by intro k hk y; simpa only [m, one_mul] using hb w k hk y)
    (by intro k hk y; simpa only [pow_zero, mul_one] using hab t w k hk y)
  have hsum := Weighted.growing_scalar_jet_sum_bound Finset.univ J r
    (fun w x => m w x * b w x) (fun w _ => (hmono w).mul (hcoef w))
    (fun w => S * A w * B) (by intro w _ k hk y; simpa only [Nat.add_zero] using hterm w k hk y) j hj x
  have he : (fun x : Vec 2 => a t x (fun _ => x)) =
      (fun x => ∑ w : DerivativeWord2 r, m w x * b w x) := by
    funext x
    simpa only [one_smul, one_mul, smul_eq_mul] using
      Weighted.multilinear_diagonal_coordinate_expansion (a t x) x 1
  rw [he]
  convert hsum using 1
  dsimp only [C]
  rw [← Finset.sum_mul, ← Finset.mul_sum]

/-! Pointwise weights commute with the literal coefficient action on every stored product jet. -/

section
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem multiplicationRawJet_pointwise_weight {K : ℕ}
    (C : Vec 2 → E →L[ℝ] F) (D : RawJet2 K E) (q : Vec 2 → ℝ)
    (a : JetIndex2 K) (x : Vec 2) :
    q x • multiplicationRawJet C D a x =
      multiplicationRawJet C (fun b y => q y • D b y) a x := by
  unfold multiplicationRawJet multiplicationTerm
  rw [Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro m _
  exact (map_smul _ _ _).symm
end

end AVRegularity.CycleWords
end
end
