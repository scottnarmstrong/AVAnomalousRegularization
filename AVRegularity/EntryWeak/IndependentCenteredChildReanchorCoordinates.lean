-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeak.IndependentScaledDifferenceSegmentDerivativeJets
import AVRegularity.EntryWeak.MolecularUlFluxNormBound

@[expose] public noncomputable section

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Finite scalar families retain genuine joint reserves through their actual coordinate inclusions. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {ι : Type*} [Fintype ι] [DecidableEq ι]

def independentSourcePiReserve (H : ℕ) (f : ι → ℝ → Vec 2 → P → ℝ)
    (Q : ∀ i, IndependentParameterSourceReserve H (f i)) :
    IndependentParameterSourceReserve H (fun t z Y i => f i t z Y) := by
  let F := fun i t z Y => scalarCoordinateInjection i (f i t z Y)
  have he : (fun t z Y => ∑ i : ι, F i t z Y) = fun t z Y i => f i t z Y := by
    funext t z Y j
    rw [Finset.sum_apply]
    change (∑ i : ι, (scalarCoordinateInjection i (f i t z Y)) j) = f j t z Y
    have hterm (i : ι) : (scalarCoordinateInjection i (f i t z Y)) j =
        if j = i then f i t z Y else 0 := by
      by_cases h : j = i
      · simp only [scalarCoordinateInjection, ContinuousLinearMap.pi_apply, h, ite_true,
          ContinuousLinearMap.id_apply]
      · simp only [scalarCoordinateInjection, ContinuousLinearMap.pi_apply, h, ite_false,
          zero_apply]
    simp_rw [hterm]
    simp
  exact (IndependentParameterSourceReserve.fintypeSum H F
    (fun i => (Q i).map (scalarCoordinateInjection i))).congrSource he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory
namespace AVRegularity.EntryWeakProofs

/-! Produced full-parameter sources give actual zero-slow samples without losing stored derivatives or weights. -/

variable {d H : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]

omit [SecondCountableTopology E] in
theorem IndependentParameterSourceReserve.joint_measurable
    {f : ℝ → Vec 2 → Vec d → E} (Q : IndependentParameterSourceReserve H f) :
    Measurable (fun X : ℝ × (Vec 2 × Vec d) => f X.1 X.2.1 X.2.2) := by
  let g := fun Y : Vec 2 × Vec d => fun t : ℝ => f t Y.1 Y.2
  have hc t : Continuous (fun Y => g Y t) := (Q.regular t).continuous
  have hm Y : Measurable (g Y) := (Q.measurable Y.2).comp (measurable_id.prodMk measurable_const)
  exact (measurable_uncurry_of_continuous_of_measurable hc hm).comp measurable_swap

omit [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentParameterSourceReserve.zeroSlow_contDiff
    {f : ℝ → Vec 2 → Vec (2 + d) → E} (Q : IndependentParameterSourceReserve H f) (t : ℝ) :
    ContDiff ℝ (H : ℕ∞) (fun P => f t 0 (independentIntrinsicParameterPacking d 0 P)) := by
  have hh := (Q.regular t).comp (independentStoredZeroFastEmbedding d).contDiff
  simpa only [Function.comp_def, independentStoredZeroFastEmbedding, ContinuousLinearMap.prod_apply,
    zero_apply, independentStoredParameterEmbedding_eq_packing] using hh

omit [BorelSpace E] [SecondCountableTopology E] in
theorem IndependentParameterSourceReserve.zeroSlow_jet_bound
    {f : ℝ → Vec 2 → Vec (2 + d) → E} (Q : IndependentParameterSourceReserve H f)
    (t : ℝ) (n : ℕ) (hn : n ≤ H) (P : Vec d) :
    ‖iteratedFDeriv ℝ n (fun X => f t 0 (independentIntrinsicParameterPacking d 0 X)) P‖ ≤ Q.budget n := by
  let g := fun X : Vec 2 × Vec (2 + d) => f t X.1 X.2
  let L := independentStoredZeroFastEmbedding d
  have hh := finite_affine_derivative_norm_le g n ((Q.regular t).of_le (by exact_mod_cast hn))
    L (independentStoredZeroFastEmbedding_norm_le d) 0 P
  have he : (fun X => g (L X + 0)) = fun X => f t 0 (independentIntrinsicParameterPacking d 0 X) := by
    funext X
    simp only [g, L, add_zero, independentStoredZeroFastEmbedding, ContinuousLinearMap.prod_apply,
      zero_apply, independentStoredParameterEmbedding_eq_packing]
  rw [he] at hh
  exact hh.trans (Q.derivative_bound n hn t (L P + 0))

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! The uniform higher trace estimate applies to every actual molecular raw solution. -/

theorem dataActual_flux_higher_trace_bound {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ} {initial : ComplexCellL2}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsm : Measurable (Function.uncurry src))
    (hfm : Measurable (Function.uncurry flux))
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hdiv : IsCellDrift P.v) (hm : cellMean initial = 0)
    (hsrc : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (u₀ : TorusHk K ℂ) (hinit : initial = torusHkValueCLM u₀)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (B : ℝ) (hB : 0 ≤ B)
    (hshort : ∀ s ∈ Icc a b, ∀ t ∈ Icc a b, s ≤ t → t - s ≤ 1 →
      (∫ r in s..t, 4 * (factorialNormSq 1 (S r).val + factorialNormSq 1 (F r).val)) ≤ B)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] initial) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧
        ‖w‖ ≤ Real.sqrt ((factorialNormSq 1 u₀.val +
          B / (1 - Real.exp (-(1 / 2))) + B) / factorialWeightMin 1 K) := by
  obtain ⟨u, slice, _, hU, hu0, hbnd⟩ := dataRegular_flux_exists_uniform hlt
    hsm hfm hsp hfp hdiv hm hsrc K Cv hCv hv hp hb S hs F hS hF hf
    u₀ hinit hsmall B hB hshort
  obtain ⟨R, hR, htrace⟩ := dataWeakHilbert_exists_raw_solution P src flux hsp hfp
    u slice hU
  have hri : cellValue R a =ᵐ[volume.restrict AVenhance.unitCube] initial :=
    (htrace a).symm.trans (Filter.EventuallyEq.of_eq
      (congrArg (fun z : ComplexCellL2 => (z : Vec 2 → ℂ)) hu0))
  have hu := dataActual_unique_raw hlt.le P src flux hsp hfp D R hD hR (hi.trans hri.symm)
  intro t ht
  obtain ⟨w, hw, hn⟩ := hbnd t ht
  refine ⟨w, hw.trans ?_, hn⟩
  apply Lp.ext
  exact (htrace t).trans ((hu t ht).symm.trans
    (cellRawTrace_ae D t (hD.2.2.1 t ht).1).symm)

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! The independent spatial-difference slice retains every family parameter. -/

variable (P V : Type*) [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def independentSpatialDifferenceCoordinates : (P × (V × V)) →L[ℝ] ((P × V) × (P × V)) :=
  ((ContinuousLinearMap.fst ℝ P (V × V)).prod
    ((ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ P (V × V)))).prod
  ((0 : (P × (V × V)) →L[ℝ] P).prod
    ((ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ P (V × V))))

theorem independentSpatialDifferenceCoordinates_apply (Y : P × (V × V)) :
    independentSpatialDifferenceCoordinates P V Y = ((Y.1, Y.2.1), (0, Y.2.2)) := rfl

theorem independentSpatialDifferenceCoordinates_norm_le :
    ‖independentSpatialDifferenceCoordinates P V‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, independentSpatialDifferenceCoordinates_apply]
  simp only [Prod.norm_def, norm_zero, max_eq_right (norm_nonneg _)]
  exact max_le (max_le (le_max_left _ _) ((le_max_left _ _).trans (le_max_right _ _)))
    ((le_max_right _ _).trans (le_max_right _ _))

end AVRegularity.EntryWeakProofs
end

section
open Homogenization
namespace AVRegularity.EntryWeakProofs

/-! Actual coordinate injections give finite-vector source budgets. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem independentSourcePiReserve_budget (H : ℕ) (f : ι → ℝ → Vec 2 → P → ℝ)
    (Q : ∀ i, IndependentParameterSourceReserve H (f i)) (r : ℕ) :
    (independentSourcePiReserve H f Q).budget r =
      ∑ i : ι, ‖scalarCoordinateInjection (ι := ι) i‖ * (Q i).budget r := by
  unfold independentSourcePiReserve
  rw [IndependentParameterSourceReserve.congrSource_budget, IndependentParameterSourceReserve.fintypeSum_budget]
  rfl

theorem independentSourcePiReserve_uniform_budget (H : ℕ) (f : ι → ℝ → Vec 2 → P → ℝ)
    (Q : ∀ i, IndependentParameterSourceReserve H (f i)) (B : ℝ)
    (hQ : ∀ i r, r ≤ H → (Q i).budget r ≤ B) (r : ℕ) (hr : r ≤ H) :
    (independentSourcePiReserve H f Q).budget r ≤ Fintype.card ι * B := by
  rw [independentSourcePiReserve_budget]
  calc
    _ ≤ ∑ i : ι, B := Finset.sum_le_sum (fun i _ =>
      (mul_le_of_le_one_left ((Q i).budget_nonneg r) (scalarCoordinateInjection_norm_le_one i)).trans
        (hQ i r hr))
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Full independent-family jets of a normalized spatial difference. -/

variable {P V E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_spatial_difference_joint_jet_bound (f : P × V → E) (n : ℕ)
    (hf : ContDiff ℝ ((n + 1 : ℕ) : ℕ∞) f) (C : ℝ)
    (ρ : ℝ) (hρ : ρ ≠ 0) (hρ₁ : |ρ| ≤ 1) (p : P) (X W : V)
    (hb₀ : n ≠ 0 → ‖iteratedFDeriv ℝ n f (p, X + ρ • W)‖ ≤ C)
    (hb₁ : ∀ Y ∈ segment ℝ (p, X) (p, X + ρ • W),
      ‖iteratedFDeriv ℝ (n + 1) f Y‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun Y : P × (V × V) =>
      ρ⁻¹ • (f (Y.1, Y.2.1 + ρ • Y.2.2) - f (Y.1, Y.2.1))) (p, X, W)‖ ≤
        (2 : ℝ) ^ n * C * (‖W‖ + n) := by
  let F : (P × V) × (P × V) → E := fun Y => ρ⁻¹ • (f (Y.1 + ρ • Y.2) - f Y.1)
  let L := independentSpatialDifferenceCoordinates P V
  have hreg : ContDiff ℝ (n : ℕ∞) f := hf.of_le (by exact_mod_cast Nat.le_succ n)
  have hF : ContDiff ℝ (n : ℕ∞) F :=
    ((hreg.comp (contDiff_fst.add (contDiff_snd.const_smul ρ))).sub
      (hreg.comp contDiff_fst)).const_smul _
  have he : (fun Y : P × (V × V) =>
      ρ⁻¹ • (f (Y.1, Y.2.1 + ρ • Y.2.2) - f (Y.1, Y.2.1))) = F ∘ L := by
    funext Y
    simp only [Function.comp_apply, L, independentSpatialDifferenceCoordinates_apply, F,
      Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero]
  rw [he, L.iteratedFDeriv_comp_right hF (p, X, W) (le_refl _)]
  have hh := (iteratedFDeriv ℝ n F (L (p, X, W))).norm_compContinuousLinearMap_le
    (fun _ : Fin n => L)
  have hp : (∏ _ : Fin n, ‖L‖) ≤ 1 :=
    (Finset.prod_le_prod₀ (fun _ _ => norm_nonneg L)
      (fun _ _ => independentSpatialDifferenceCoordinates_norm_le P V)).trans_eq (by simp)
  have hh' := hh.trans (mul_le_mul_of_nonneg_left hp (norm_nonneg _))
  rw [mul_one] at hh'
  apply hh'.trans
  have hb := independent_scaled_difference_segment_derivative_jet_bound f n hf C ρ hρ hρ₁
    (p, X) (0, W) (by
      simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using hb₀) (by
      simpa only [Prod.smul_mk, Prod.mk_add_mk, smul_zero, add_zero] using hb₁)
  simpa only [L, independentSpatialDifferenceCoordinates_apply, F, Prod.norm_def,
    norm_zero, max_eq_right (norm_nonneg _)] using hb

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Genuine coordinate-word primitive data meet the triangular inverse hypotheses. -/

variable {d H : ℕ}

def coordinateWordDirections (w : List (Fin d)) : Fin w.length → Vec d :=
  fun i => basisVec (w.get i)

theorem coordinateWordDirections_norm (w : List (Fin d)) (i : Fin w.length) :
    ‖coordinateWordDirections w i‖ ≤ 1 := by
  simp [coordinateWordDirections, basisVec, Pi.norm_single]

def coordinateMetricWord (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ)
    (w : List (Fin d)) (Y : Vec d) : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ :=
  fun t _ => independentMetricWordJet G w.length (coordinateWordDirections w) Y t

def coordinateSourceWord {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℝ → Vec 2 → Vec d → E) (w : List (Fin d)) (Y : Vec d) : ℝ → Vec 2 → E :=
  fun t z => realWordJet (f t z) w.length (coordinateWordDirections w) Y

theorem coordinate_word_primitive_data
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    (w : List (Fin d)) (hw : w.length ≤ H) (Y : Vec d) :
    cellMetricSupNorm (coordinateMetricWord G w Y) < ⊤ ∧
    Measurable (Function.uncurry (coordinateMetricWord G w Y)) ∧
    cellUlNorm univ (coordinateSourceWord f w Y) < ⊤ ∧
    cellUlNorm univ (coordinateSourceWord F w Y) < ⊤ ∧
    AEStronglyMeasurable (Function.uncurry (coordinateSourceWord f w Y))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) ∧
    AEStronglyMeasurable (Function.uncurry (coordinateSourceWord F w Y))
      ((volume.restrict univ).prod (volume.restrict AVenhance.unitCube)) := by
  let qf := Qf.wordJet w.length 0 (by omega) (coordinateWordDirections w)
    (coordinateWordDirections_norm w)
  let qF := QF.wordJet w.length 0 (by omega) (coordinateWordDirections w)
    (coordinateWordDirections_norm w)
  refine ⟨?_, ?_, (qf.ul_norm_bound Y).trans_lt ENNReal.ofReal_lt_top,
    (qF.ul_norm_bound Y).trans_lt ENNReal.ofReal_lt_top,
    (qf.measurable Y).aestronglyMeasurable, (qF.measurable Y).aestronglyMeasurable⟩
  · apply lt_of_le_of_lt (b := ENNReal.ofReal (QG.budget w.length)) _ ENNReal.ofReal_lt_top
    apply iSup_le
    intro t
    apply iSup_le
    intro z
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    change ‖independentMetricWordJet G w.length (coordinateWordDirections w) Y t i j‖ₑ ≤ _
    rw [← ofReal_norm, Real.norm_eq_abs]
    exact ENNReal.ofReal_le_ofReal
      (QG.word_entry_bound w.length hw _ (coordinateWordDirections_norm w) Y t i j)
  · apply Measurable.of_eval
    intro i
    apply Measurable.of_eval
    intro j
    exact (QG.word_entry_measurable w.length _ Y i j).comp measurable_fst

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set
open scoped ContDiff
namespace AVRegularity.EntryWeakProofs

/-! True local metric jets construct the global independent metric reserve used by molecular production. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

def cutoffIndependentMetricReserve (H : ℕ) (χ : P → ℝ) (hχ : ContDiff ℝ ∞ χ)
    (hχrange : ∀ Y, χ Y ∈ Icc 0 1) (U : Set P) (hsupport : tsupport χ ⊆ U)
    (G : ℝ → P → Matrix (Fin 2) (Fin 2) ℝ) (a b : ℝ) (hab : a ≤ b)
    (hs : ∀ t i j, ContDiff ℝ ∞ (fun Y => G t Y i j))
    (hm : ∀ Y i j, Measurable (fun t => G t Y i j))
    (hsy : ∀ t ∈ Icc a b, ∀ Y, (G t Y).IsSymm)
    (he : ∀ t ∈ Icc a b, ∀ Y, ∀ ξ : Vec 2,
      (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, G t Y i j * ξ i * ξ j ∧
      (∑ i, ∑ j, G t Y i j * ξ i * ξ j) ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (A B : ℕ → ℝ) (hA : ∀ n, 0 ≤ A n) (hB : ∀ n, 0 ≤ B n)
    (hbχ : ∀ n ≤ H, ∀ Y, ‖iteratedFDeriv ℝ n χ Y‖ ≤ A n)
    (hbG : ∀ n ≤ H, ∀ t ∈ Icc a b, ∀ Y ∈ U, ∀ i j,
      ‖iteratedFDeriv ℝ n (fun X => G t X i j) Y‖ ≤ B n) :
    IndependentParameterMetricReserve H (clampedParameterMetric (cutoffParameterMetric χ G) a b) where
  regular t i j := by
    change ContDiff ℝ ∞ (fun Y => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
      χ Y * (G (max a (min b t)) Y i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    exact contDiff_const.add (hχ.mul ((hs _ i j).sub contDiff_const))
  measurable Y i j := by
    change Measurable (fun t => (1 : Matrix (Fin 2) (Fin 2) ℝ) i j +
      χ Y * (G (max a (min b t)) Y i j - (1 : Matrix (Fin 2) (Fin 2) ℝ) i j))
    exact measurable_const.add (measurable_const.mul
      (((hm Y i j).comp (measurable_const.max (measurable_const.min measurable_id))).sub measurable_const))
  metric Y := cutoffParameterMetric_clamped_isCellMetric χ hχrange G a b hab hm hsy he Y
  budget := independentCutoffUnitBudget ℝ A B
  budget_nonneg := independentCutoffUnitBudget_nonneg A B hA hB
  derivative_bound n hn t Y i j := by
    let e : ℝ := (1 : Matrix (Fin 2) (Fin 2) ℝ) i j
    have he : ‖e‖ ≤ 1 := by
      simp only [e, Matrix.one_apply]
      split_ifs <;> norm_num
    change ‖iteratedFDeriv ℝ n
      (independentCutoffExtension χ (fun X => G (max a (min b t)) X i j) e) Y‖ ≤ _
    exact independentCutoffExtension_jet_bound_one χ _ e he H n
      (hχ.of_le (by simp)) ((hs _ i j).of_le (by simp)) hn U hsupport A B hA hB hbχ
      (fun n hn X hX => hbG n hn _ (metric_clamp_mem a b hab t) X hX i j) Y

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! One local finite derivative menu controls the full family/spatial difference. -/

variable {P V E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem independent_spatial_difference_joint_menu_bound (f : P × V → E) (K n : ℕ)
    (hf : ContDiff ℝ ((K + 1 : ℕ) : ℕ∞) f) (hn : n ≤ K) (C : ℝ) (hC : 0 ≤ C)
    (ρ : ℝ) (hρ : ρ ≠ 0) (hρ₁ : |ρ| ≤ 1) (p : P) (X W : V)
    (R : ℝ) (hW : ‖W‖ ≤ R)
    (hb : ∀ i, 1 ≤ i → i ≤ K + 1 → ∀ Y ∈ segment ℝ (p, X) (p, X + ρ • W),
      ‖iteratedFDeriv ℝ i f Y‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (fun Y : P × (V × V) =>
      ρ⁻¹ • (f (Y.1, Y.2.1 + ρ • Y.2.2) - f (Y.1, Y.2.1))) (p, X, W)‖ ≤
        (2 : ℝ) ^ K * C * (R + K) := by
  have hh := independent_spatial_difference_joint_jet_bound f n
    (hf.of_le (by exact_mod_cast (show n + 1 ≤ K + 1 by omega))) C ρ hρ hρ₁ p X W
    (fun hn₀ => hb n (by omega) (by omega) _ (right_mem_segment ℝ _ _))
    (hb (n + 1) (by omega) (by omega))
  have hp : (2 : ℝ) ^ n ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hn
  have hs : ‖W‖ + (n : ℝ) ≤ R + K := add_le_add hW (by exact_mod_cast hn)
  exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hp hC) hs (by positivity) (by positivity))

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Every zero-start solution retains higher trace bounds linear in its scalar-and-flux source budget. -/

theorem dataActual_flux_higher_zero_bound {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsm : Measurable (Function.uncurry src))
    (hfm : Measurable (Function.uncurry flux))
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hdiv : IsCellDrift P.v)
    (hsrc : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (Ng : ℝ) (hNg : 0 ≤ Ng)
    (hSb : ∀ t ∈ Icc a b, ‖S t‖ ≤ Ng)
    (hFb : ∀ t ∈ Icc a b, ‖F t‖ ≤ Ng)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧ ‖w‖ ≤ fluxProductionConstant K * Ng := by
  let Q := 2 * factorialWeightMax 1 K * Ng ^ 2
  have hW := factorialWeightMax_nonneg_local K
  have hQ : 0 ≤ Q := by dsimp only [Q]; positivity
  have hpoint : ∀ t ∈ Icc a b,
      factorialNormSq 1 (S t).val + factorialNormSq 1 (F t).val ≤ Q := by
    intro t ht
    have hs := (factorialNormSq_upper 1 (S t).val).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hSb t ht) 2) hW)
    have hf := (factorialNormSq_upper 1 (F t).val).trans
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (norm_nonneg _) (hFb t ht) 2) hW)
    dsimp only [Q]
    linarith
  have hshort := higher_forcing_unit_window_budget hlt.le K 1 S F hS hF Q hQ hpoint
  have hmean : cellMean (0 : ComplexCellL2) = 0 :=
    (integral_congr_ae (Lp.coeFn_zero _ _ _)).trans (integral_zero _ _)
  have hinit : (0 : ComplexCellL2) = torusHkValueCLM (0 : TorusHk K ℂ) := (map_zero _).symm
  have hi' : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] (0 : ComplexCellL2) :=
    hi.trans (Lp.coeFn_zero _ _ _).symm
  obtain hbound := dataActual_flux_higher_trace_bound hlt hsm hfm hsp hfp hdiv hmean hsrc
    K Cv hCv hv hp hb S hs F hS hF hf 0 hinit hsmall (4 * Q) (by positivity)
    hshort D hD hi'
  intro t ht
  obtain ⟨w, hw, hn⟩ := hbound t ht
  refine ⟨w, hw, ?_⟩
  have he : Real.sqrt ((factorialNormSq 1 (0 : TorusHk K ℂ).val +
      (4 * Q) / (1 - Real.exp (-(1 / 2))) + 4 * Q) / factorialWeightMin 1 K) =
      fluxProductionConstant K * Ng := by
    have hz : factorialNormSq 1 (0 : TorusHk K ℂ).val = 0 := by
      change factorialNormSq 1 (0 : JetL2 (volume.restrict AVenhance.unitCube) K ℂ) = 0
      simp [factorialNormSq, derivativeNormSq]
    have hB : 4 * Q = 8 * factorialWeightMax 1 K * Ng ^ 2 := by dsimp only [Q]; ring
    rw [hz, zero_add, hB]
    exact fluxProduction_sqrt_scale K Ng hNg
  exact hn.trans_eq he

end AVRegularity.EntryWeakProofs
end

section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Literal coordinate-word cons indices are the genuine primitive parameter derivatives. -/

section
variable {d H : ℕ}

theorem coordinateWordDirections_cons (i : Fin d) (w : List (Fin d)) :
    coordinateWordDirections (i :: w) = Fin.cons (basisVec i) (coordinateWordDirections w) := by
  funext j
  refine Fin.cases ?_ (fun k => ?_) j <;> rfl

theorem coordinate_metric_word_cons
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G)
    (i : Fin d) (w : List (Fin d)) (Y : Vec d) (t : ℝ) (z : Vec 2) (a b : Fin 2) :
    coordinateMetricWord G (i :: w) Y t z a b =
      fderiv ℝ (fun X => coordinateMetricWord G w X t z a b) Y (basisVec i) := by
  change realWordJet (fun X => G t X a b) (w.length + 1)
    (coordinateWordDirections (i :: w)) Y = _
  rw [coordinateWordDirections_cons]
  exact independentMetricWordJet_cons Q w.length (coordinateWordDirections w) (basisVec i) Y t a b

theorem coordinate_source_word_cons {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → Vec 2 → Vec d → E} (Q : IndependentParameterSourceReserve H f)
    (i : Fin d) (w : List (Fin d)) (hw : w.length + 1 ≤ H)
    (Y : Vec d) (t : ℝ) (z : Vec 2) :
    coordinateSourceWord f (i :: w) Y t z =
      fderiv ℝ (fun X => coordinateSourceWord f w X t z) Y (basisVec i) := by
  change realWordJet (f t z) (w.length + 1) (coordinateWordDirections (i :: w)) Y = _
  rw [coordinateWordDirections_cons]
  have hr : ContDiff ℝ ((w.length + 1 : ℕ) : ℕ∞)
      (fun Z : Vec 2 × Vec d => f t Z.1 Z.2) :=
    (Q.regular t).of_le (by exact_mod_cast hw)
  exact finite_realWordJet_cons_eq_fderiv (f t z) w.length
    (hr.comp₂ contDiff_const contDiff_id) (coordinateWordDirections w) (basisVec i) Y
end

/-! Genuine primitive parameter derivatives preserve their source window support. -/

section
variable {d : ℕ} {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem coordinate_source_word_zero {f : ℝ → Vec 2 → Vec d → E}
    (t : ℝ) (z : Vec 2) (hz : ∀ Y, f t z Y = 0)
    (w : List (Fin d)) (Y : Vec d) : coordinateSourceWord f w Y t z = 0 := by
  have he : f t z = fun _ => (0 : E) := funext hz
  unfold coordinateSourceWord realWordJet
  rw [he]
  have hzero (n : ℕ) (v : Fin n → Vec d) :
      iteratedFDeriv ℝ n (fun _ : Vec d => (0 : E)) Y v = 0 := by
    cases n with
    | zero => simp only [iteratedFDeriv_zero_apply]
    | succ n => simp only [iteratedFDeriv_succ_const, Pi.zero_apply, zero_apply]
  exact hzero w.length _
end

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory AVenhance
namespace AVRegularity.EntryWeakProofs

/-! Coordinate window estimates assemble into a vector reserve without unfolding its source. -/

variable {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]

theorem windowIndependentVectorReserve (H : ℕ) (I : Set ℝ) (hI : MeasurableSet I)
    (f : ℝ → Vec 2 → P → Vec 2)
    (hf : ∀ a t, ContDiff ℝ (H : ℕ∞) (fun X : Vec 2 × P => f t X.1 X.2 a))
    (hp : ∀ a t Y, IsZ2Periodic (fun z => f t z Y a))
    (hm : ∀ a Y, Measurable (fun X : ℝ × Vec 2 => f X.1 X.2 Y a))
    (θ : ℝ) (hθ : 0 ≤ θ) (price : ℕ → ℝ) (hprice : ∀ n, 0 ≤ price n)
    (hb : ∀ a n, n ≤ H → ∀ t ∈ I, ∀ X : Vec 2 × P,
      ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × P => f t Z.1 Z.2 a) X‖ ≤ θ * price n) :
    ∃ R : IndependentParameterSourceReserve H
      (fun t z Y a => independentTimeWindowSource I (fun t z Y => f t z Y a) t z Y),
      ∀ n ≤ H, R.budget n ≤ θ * (2 * ∑ j : Fin (H + 1), price j.val) := by
  let g := fun a t z Y => independentTimeWindowSource I (fun t z Y => f t z Y a) t z Y
  let Q : ∀ a : Fin 2, IndependentParameterSourceReserve H (g a) :=
    fun a => windowIndependentSourceReserve H I hI (fun t z Y => f t z Y a)
      (fun t _ => hf a t) (fun t _ Y => hp a t Y) (hm a)
      (fun n => θ * price n) (fun n => mul_nonneg hθ (hprice n)) (hb a)
  refine ⟨independentSourcePiReserve H g Q, ?_⟩
  intro n hn
  have hentry j (hj : j ≤ H) : price j ≤ ∑ k : Fin (H + 1), price k.val :=
    Finset.single_le_sum (fun (k : Fin (H + 1)) _ => hprice k.val)
      (Finset.mem_univ (⟨j, by omega⟩ : Fin (H + 1)))
  have hbound : ∀ a j, j ≤ H → (Q a).budget j ≤ θ * ∑ k : Fin (H + 1), price k.val :=
    fun _ j hj => mul_le_mul_of_nonneg_left (hentry j hj) hθ
  have hh := independentSourcePiReserve_uniform_budget H g Q _ hbound n hn
  simp only [Fintype.card_fin, Nat.cast_ofNat] at hh
  exact hh.trans_eq (by ring)

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set Filter Topology AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Genuine reserved coordinate words are continuous in the actual inverse forcing norms. -/

section
variable {d H : ℕ}

theorem coordinate_metric_word_norm_continuous
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G)
    (w : List (Fin d)) (hw : w.length + 1 ≤ H) (Y : Vec d) :
    Tendsto (fun X => cellMetricSupNorm (coordinateMetricWord G w X - coordinateMetricWord G w Y))
      (𝓝 Y) (𝓝 0) := by
  have hb (X : Vec d) : cellMetricSupNorm
      (coordinateMetricWord G w X - coordinateMetricWord G w Y) ≤
      ENNReal.ofReal (Q.budget (w.length + 1) * ‖X - Y‖) := by
    apply iSup_le
    intro t
    apply iSup_le
    intro z
    apply iSup_le
    intro i
    apply iSup_le
    intro j
    change ‖independentMetricWordJet G w.length (coordinateWordDirections w) X t i j -
      independentMetricWordJet G w.length (coordinateWordDirections w) Y t i j‖ₑ ≤ _
    rw [← ofReal_norm]
    apply ENNReal.ofReal_le_ofReal
    apply independent_parameter_lipschitz
      (fun Z => independentMetricWordJet G w.length (coordinateWordDirections w) Z t i j)
      (finite_realWordJet_contDiff _ w.length 1 ((Q.regular t i j).of_le (by simp)) _)
    intro Z
    simpa only [norm_iteratedFDeriv_one] using Q.word_derivative_bound w.length 1 hw
      (coordinateWordDirections w) (coordinateWordDirections_norm w) Z t i j
  have ht : Tendsto (fun X : Vec d => ENNReal.ofReal (Q.budget (w.length + 1) * ‖X - Y‖))
      (𝓝 Y) (𝓝 0) := by
    have hc : Continuous (fun X : Vec d => ENNReal.ofReal
        (Q.budget (w.length + 1) * ‖X - Y‖)) := ENNReal.continuous_ofReal.comp
      ((continuous_id.sub continuous_const).norm.const_mul (Q.budget (w.length + 1)))
    simpa only [sub_self, norm_zero, mul_zero, ENNReal.ofReal_zero] using hc.tendsto Y
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ht (fun _ => bot_le) hb

theorem coordinate_source_word_norm_continuous {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → Vec 2 → Vec d → E} (Q : IndependentParameterSourceReserve H f)
    (w : List (Fin d)) (hw : w.length + 1 ≤ H) (Y : Vec d) :
    Tendsto (fun X => cellUlNorm univ (coordinateSourceWord f w X - coordinateSourceWord f w Y))
      (𝓝 Y) (𝓝 0) := by
  let q := Q.wordJet w.length 1 hw (coordinateWordDirections w) (coordinateWordDirections_norm w)
  simpa only [coordinateSourceWord, Pi.sub_def] using q.norm_difference_tendsto_zero (by omega) Y
end

/-! Primitive coordinate-word quotients converge to the exact next word. -/

section
variable {d H : ℕ}

theorem coordinate_source_word_quotient_tendsto {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E]
    [BorelSpace E] [SecondCountableTopology E]
    {f : ℝ → Vec 2 → Vec d → E} (Q : IndependentParameterSourceReserve H f)
    (i : Fin d) (w : List (Fin d)) (hw : w.length + 2 ≤ H) (Y : Vec d) :
    Tendsto (fun h : ℝ => cellUlNorm univ
      (h⁻¹ • (coordinateSourceWord f w (Y + h • basisVec i) - coordinateSourceWord f w Y) -
        coordinateSourceWord f (i :: w) Y)) (𝓝[≠] 0) (𝓝 0) := by
  let q := Q.wordJet w.length 2 hw (coordinateWordDirections w) (coordinateWordDirections_norm w)
  have he : coordinateSourceWord f (i :: w) Y = fun t z =>
      fderiv ℝ (fun X => coordinateSourceWord f w X t z) Y (basisVec i) := by
    funext t z
    exact coordinate_source_word_cons Q i w (by omega) Y t z
  rw [he]
  simpa only [coordinateSourceWord, Pi.sub_def, Pi.smul_def] using
    q.quotient_error_ul_tendsto_zero (by omega) Y (basisVec i)

theorem coordinate_metric_word_quotient_bound
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G)
    (i : Fin d) (w : List (Fin d)) (hw : w.length + 2 ≤ H)
    (Y : Vec d) (h : ℝ) (hh : h ≠ 0) :
    cellMetricSupNorm (h⁻¹ • (coordinateMetricWord G w (Y + h • basisVec i) -
      coordinateMetricWord G w Y) - coordinateMetricWord G (i :: w) Y) ≤
      ENNReal.ofReal (Q.budget (w.length + 2) * |h| * ‖(basisVec i : Vec d)‖ ^ 2) := by
  apply iSup_le
  intro t
  apply iSup_le
  intro z
  apply iSup_le
  intro a
  apply iSup_le
  intro b
  change ‖h⁻¹ • (coordinateMetricWord G w (Y + h • basisVec i) t z a b -
    coordinateMetricWord G w Y t z a b) - coordinateMetricWord G (i :: w) Y t z a b‖ₑ ≤ _
  rw [← ofReal_norm, coordinate_metric_word_cons Q]
  apply ENNReal.ofReal_le_ofReal
  apply independent_parameter_quotient_bound
    (fun X => coordinateMetricWord G w X t z a b)
    (finite_realWordJet_contDiff _ w.length 2 ((Q.regular t a b).of_le (by simp)) _)
    (Q.budget (w.length + 2)) (Q.budget_nonneg _) _ Y (basisVec i) h hh
  intro X
  have hb := Q.word_derivative_bound w.length 2 hw (coordinateWordDirections w)
    (coordinateWordDirections_norm w) X t a b
  rw [← norm_iteratedFDeriv_fderiv (n := 1), norm_iteratedFDeriv_one] at hb
  exact hb

theorem coordinate_metric_word_quotient_tendsto
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    (Q : IndependentParameterMetricReserve H G)
    (i : Fin d) (w : List (Fin d)) (hw : w.length + 2 ≤ H) (Y : Vec d) :
    Tendsto (fun h : ℝ => cellMetricSupNorm
      (h⁻¹ • (coordinateMetricWord G w (Y + h • basisVec i) - coordinateMetricWord G w Y) -
        coordinateMetricWord G (i :: w) Y)) (𝓝[≠] 0) (𝓝 0) := by
  have hc : Continuous (fun h : ℝ => ENNReal.ofReal
      (Q.budget (w.length + 2) * |h| * ‖(basisVec i : Vec d)‖ ^ 2)) :=
    ENNReal.continuous_ofReal.comp (by fun_prop)
  have ht : Tendsto (fun h : ℝ => ENNReal.ofReal
      (Q.budget (w.length + 2) * |h| * ‖(basisVec i : Vec d)‖ ^ 2)) (𝓝[≠] 0) (𝓝 0) := by
    simpa only [abs_zero, mul_zero, zero_mul, ENNReal.ofReal_zero] using
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds ht
    (Filter.Eventually.of_forall fun _ => bot_le)
  filter_upwards [self_mem_nhdsWithin] with h hh
  exact coordinate_metric_word_quotient_bound Q i w hw Y h hh
end

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational AVenhance.Infra.ODE
namespace AVRegularity.EntryWeakProofs

/-! Higher production for the actual almost-measurable raw flux, without imposing a representative. -/

theorem dataActual_flux_higher_zero_bound_ae {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hdiv : IsCellDrift P.v)
    (hsrc : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (Ng : ℝ) (hNg : 0 ≤ Ng)
    (hSb : ∀ t ∈ Icc a b, ‖S t‖ ≤ Ng)
    (hFb : ∀ t ∈ Icc a b, ‖F t‖ ≤ Ng)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧ ‖w‖ ≤ fluxProductionConstant K * Ng := by
  let sm := hsp.aestronglyMeasurable.mk (Function.uncurry src)
  let src' := fun t x => sm (t, x)
  have hes : Function.uncurry src =ᵐ[
      (volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)]
      Function.uncurry src' := hsp.aestronglyMeasurable.ae_eq_mk
  have hsm : Measurable (Function.uncurry src') :=
    hsp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hsp' := hsp.ae_eq hes
  have hscalar := cellSourceSlice_congr_ae (Icc a b) src src' hsp hsp' hes
  have hs' : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src' t := by
    filter_upwards [hs, hscalar] with t ht he
    exact ht.trans he
  have hsrc' : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src' t) = 0 := by
    filter_upwards [hsrc, hscalar] with t ht he
    rw [← he]
    exact ht
  let m := hfp.aestronglyMeasurable.mk (Function.uncurry flux)
  let flux' := fun t x => m (t, x)
  have he : Function.uncurry flux =ᵐ[
      (volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)]
      Function.uncurry flux' := hfp.aestronglyMeasurable.ae_eq_mk
  have hfm : Measurable (Function.uncurry flux') :=
    hfp.aestronglyMeasurable.stronglyMeasurable_mk.measurable
  have hfp' := hfp.ae_eq he
  have hsec := Measure.ae_ae_of_ae_prod he
  have hcoord (j : Fin 2) : cellSourceSlice (fun s x => flux s x j) =ᵐ[
      volume.restrict (Icc a b)] cellSourceSlice (fun s x => flux' s x j) :=
    cellSourceSlice_congr_ae (Icc a b) _ _
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hfp)
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).comp_memLp' hfp')
      (he.fun_comp (fun v => v j))
  have hf' : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux' s x j) t := by
    filter_upwards [hf, (Filter.eventually_all_finset (Finset.univ : Finset (Fin 2))).2 (fun j _ => hcoord j)] with t ht heq
    intro j
    exact (ht j).trans (heq j (Finset.mem_univ j))

  have hD' := cellSolution_source_congr_sections (Icc a b) (dataCoefficients P)
    src src' flux flux' D (Measure.ae_ae_of_ae_prod hes) hsec hD
  exact dataActual_flux_higher_zero_bound hlt hsm hfm hsp' hfp' hdiv hsrc' K Cv hCv
    hv hp hb S hs' F hS hF hf' hsmall Ng hNg hSb hFb D hD' hi

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution AVRegularity.CoupledEnergy.Galerkin
open AVRegularity.CoupledEnergy.Variational
namespace AVRegularity.EntryWeakProofs

/-! Higher production uses the literal readouts of bounded source carriers. -/

theorem dataActual_flux_higher_zero_carrier_bound {a b : ℝ} (hlt : a < b)
    {P : MolecularData} {src : ℝ → Vec 2 → ℂ}
    {flux : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (hsp : MemLp (Function.uncurry src) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hfp : MemLp (Function.uncurry flux) 2
      ((volume.restrict (Icc a b)).prod (volume.restrict AVenhance.unitCube)))
    (hdiv : IsCellDrift P.v)
    (K : ℕ) (Cv : ℝ) (hCv : 0 ≤ Cv)
    (hv : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t))
    (hp : ∀ t, AVenhance.IsZ2Periodic (P.v t))
    (hb : ∀ t j, j ≤ K → ∀ k x, ‖iteratedFDeriv ℝ j (fun y => P.v t y k) x‖ ≤ Cv)
    (S : ℝ → TorusHk K ℂ) (hs : ∀ᵐ t ∂volume.restrict (Icc a b),
      torusHkValueCLM (S t) =ᵐ[volume.restrict AVenhance.unitCube] src t)
    (hm : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (torusHkValueCLM (S t)) = 0)
    (F : ℝ → TorusHk K (PiLp 2 (fun _ : Fin 2 => ℂ)))
    (hS : MemLp S 2 (volume.restrict (Icc a b)))
    (hF : MemLp F 2 (volume.restrict (Icc a b)))
    (hf : ∀ᵐ t ∂volume.restrict (Icc a b),
      torusHkValueCLM (F t) =ᵐ[volume.restrict AVenhance.unitCube] flux t)
    (hsmall : (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
      finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8)
    (Ng : ℝ) (hNg : 0 ≤ Ng)
    (hSb : ∀ t ∈ Icc a b, ‖S t‖ ≤ Ng)
    (hFb : ∀ t ∈ Icc a b, ‖F t‖ ≤ Ng)
    (D : ℝ → RawJet2 1 ℂ)
    (hD : IsCellSolution (Icc a b) (dataCoefficients P) src flux D)
    (hi : cellValue D a =ᵐ[volume.restrict AVenhance.unitCube] 0) :
    ∀ t ∈ Icc a b, ∃ w : TorusHk K ℂ,
      torusHkValueCLM w = cellRawTrace D t ∧ ‖w‖ ≤ fluxProductionConstant K * Ng := by
  have hs' : ∀ᵐ t ∂volume.restrict (Icc a b),
      (S t).val (valueIndex2 K) = cellSourceSlice src t := by
    filter_upwards [hs] with t ht
    exact (cellSourceSlice_eq_of_ae src t (torusHkValueCLM (S t)) ht).symm
  have hm' : ∀ᵐ t ∂volume.restrict (Icc a b), cellMean (cellSourceSlice src t) = 0 := by
    filter_upwards [hs', hm] with t ht hmt
    rw [← ht]
    exact hmt
  have hf' : ∀ᵐ t ∂volume.restrict (Icc a b), ∀ j,
      ((PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j).compLpL
        2 (volume.restrict AVenhance.unitCube)) ((F t).val (valueIndex2 K)) =
          cellSourceSlice (fun s x => flux s x j) t := by
    filter_upwards [hf] with t ht
    intro j
    apply (cellSourceSlice_eq_of_ae _ t _ ?_).symm
    exact (ContinuousLinearMap.coeFn_compLpL
      (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => ℂ) j) (torusHkValueCLM (F t))).trans
      (ht.fun_comp (fun v => v j))
  exact dataActual_flux_higher_zero_bound_ae hlt hsp hfp hdiv hm' K Cv hCv
    hv hp hb S hs' F hS hF hf' hsmall Ng hNg hSb hFb D hD hi

end AVRegularity.EntryWeakProofs
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.EntryWeakProofs

/-! Genuine finite primitive reserves produce every ordered coordinate inverse equation. -/

variable {d H : ℕ}

theorem coordinateMetricWord_nil
    (G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ) (Y : Vec d) :
    coordinateMetricWord G [] Y = fun t (_ : Vec 2) => G t Y := by
  funext t z i j
  exact iteratedFDeriv_zero_apply _

theorem coordinate_word_inverse_family_exists
    {G : ℝ → Vec d → Matrix (Fin 2) (Fin 2) ℝ}
    {f : ℝ → Vec 2 → Vec d → ℂ}
    {F : ℝ → Vec 2 → Vec d → PiLp 2 (fun _ : Fin 2 => ℂ)}
    (QG : IndependentParameterMetricReserve H G)
    (Qf : IndependentParameterSourceReserve H f)
    (QF : IndependentParameterSourceReserve H F)
    {v : ℝ → Vec 2 → Vec 2} (hv : IsCellDrift v) :
    ∃ c : List (Fin d) → Vec d → ℝ → RawJet2 1 ℂ,
      ∀ Y w, w.length ≤ H →
        IsCellInverseValue ⟨(fun t _ => G t Y), v, 0, 0⟩
          (fun t => cellQ0 (coordinateSourceWord f w Y t))
          (coordinateSourceWord F w Y + independentWordMetricFlux
            (fun p => coordinateMetricWord G p Y) (fun p => c p Y) w) (c w Y) := by
  have hex (Y : Vec d) := independent_word_inverse_family_exists H
    (fun w => coordinateMetricWord G w Y) (fun w => coordinateSourceWord f w Y)
    (fun w => coordinateSourceWord F w Y)
    (by rw [coordinateMetricWord_nil]; exact QG.metric Y) hv
    (fun w hw => coordinate_word_primitive_data QG Qf QF w hw Y)
  choose c hc using hex
  refine ⟨fun w Y => c Y w, ?_⟩
  intro Y w hw
  have hh := hc Y w hw
  rw [coordinateMetricWord_nil] at hh
  exact hh

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! The centered return-map composition keeps full independent family derivatives. -/

variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def centeredReturnInputProjection : (P × (V × V)) →L[ℝ] (P × V) :=
  (ContinuousLinearMap.fst ℝ P (V × V)).prod
    ((ContinuousLinearMap.fst ℝ V V).comp (ContinuousLinearMap.snd ℝ P (V × V)))

theorem centeredReturnInputProjection_apply (Y : P × (V × V)) :
    centeredReturnInputProjection Y = (Y.1, Y.2.1) := rfl

theorem centeredReturnInputProjection_norm_le :
    ‖centeredReturnInputProjection (P := P) (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, centeredReturnInputProjection_apply, Prod.norm_def]
  exact max_le (norm_fst_le Y) ((norm_fst_le Y.2).trans (norm_snd_le Y))

def centeredReturnInnerMap (Fa : P × V → V) (Y : P × (V × V)) : P × (V × V) :=
  (Y.1, Fa (Y.1, Y.2.1), Y.2.2)

def independentCenteredReturn (Fi Fa : P × V → V) (θ : ℝ)
    (Y : P × (V × V)) : V :=
  θ⁻¹ • (Fi (Y.1, Fa (Y.1, Y.2.1) + θ • Y.2.2) - Fi (Y.1, Fa (Y.1, Y.2.1)))

theorem centeredReturnInnerMap_contDiff (Fa : P × V → V)
    (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) :
    ContDiff ℝ (⊤ : ℕ∞) (centeredReturnInnerMap Fa) :=
  contDiff_fst.prodMk ((hFa.comp centeredReturnInputProjection.contDiff).prodMk
    (contDiff_snd.comp contDiff_snd))

theorem independentCenteredReturn_contDiff (Fi Fa : P × V → V)
    (hFi : ContDiff ℝ (⊤ : ℕ∞) Fi) (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (θ : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (independentCenteredReturn Fi Fa θ) := by
  have hA := hFa.comp centeredReturnInputProjection.contDiff
  exact ((hFi.comp (contDiff_fst.prodMk
    (hA.add ((contDiff_snd.comp contDiff_snd).const_smul θ)))).sub
    (hFi.comp (contDiff_fst.prodMk hA))).const_smul _

end AVRegularity.EntryWeakProofs
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.EntryWeakProofs

/-! Finite-order drift data for the small-transport molecular production estimate. -/

structure MolecularFiniteDriftBudget (P : MolecularData) (K : ℕ) where
  Cv : ℝ
  nonneg : 0 ≤ Cv
  admissible : IsCellDrift P.v
  smooth : ∀ t, ContDiff ℝ (K : ℕ∞) (P.v t)
  periodic : ∀ t, AVenhance.IsZ2Periodic (P.v t)
  bound : ∀ t j, j ≤ K → ∀ i x, ‖iteratedFDeriv ℝ j (fun y => P.v t y i) x‖ ≤ Cv
  small : (∑ j : Fin (K + 1), factorialRootWeight 1 j.val *
    finiteTransportBudget (E := ℂ) K Cv j) ≤ 1 / 8

end AVRegularity.EntryWeakProofs
end

section
namespace AVRegularity.EntryWeakProofs

/-! Fresh center, phase and native spatial displacement are independent coordinates. -/

section
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def centeredChildCenterProjection : (P × (V × (V × V))) →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ V (V × V)).comp (ContinuousLinearMap.snd ℝ P (V × (V × V)))

def centeredChildPhaseProjection : (P × (V × (V × V))) →L[ℝ] V :=
  (ContinuousLinearMap.fst ℝ V V).comp
    ((ContinuousLinearMap.snd ℝ V (V × V)).comp (ContinuousLinearMap.snd ℝ P (V × (V × V))))

def centeredChildSlowProjection : (P × (V × (V × V))) →L[ℝ] V :=
  (ContinuousLinearMap.snd ℝ V V).comp
    ((ContinuousLinearMap.snd ℝ V (V × V)).comp (ContinuousLinearMap.snd ℝ P (V × (V × V))))

def centeredChildReturnProjection : (P × (V × (V × V))) →L[ℝ] (P × (V × V)) :=
  (ContinuousLinearMap.fst ℝ P (V × (V × V))).prod
    (centeredChildCenterProjection.prod centeredChildSlowProjection)

theorem centeredChildCenterProjection_apply (Y : P × (V × (V × V))) :
    centeredChildCenterProjection Y = Y.2.1 := rfl

theorem centeredChildPhaseProjection_apply (Y : P × (V × (V × V))) :
    centeredChildPhaseProjection Y = Y.2.2.1 := rfl

theorem centeredChildSlowProjection_apply (Y : P × (V × (V × V))) :
    centeredChildSlowProjection Y = Y.2.2.2 := rfl

theorem centeredChildReturnProjection_apply (Y : P × (V × (V × V))) :
    centeredChildReturnProjection Y = (Y.1, Y.2.1, Y.2.2.2) := rfl

theorem centeredChildCenterProjection_norm_le :
    ‖centeredChildCenterProjection (P := P) (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, centeredChildCenterProjection_apply]
  exact (norm_fst_le Y.2).trans (norm_snd_le Y)

theorem centeredChildPhaseProjection_norm_le :
    ‖centeredChildPhaseProjection (P := P) (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, centeredChildPhaseProjection_apply]
  exact (norm_fst_le Y.2.2).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))

theorem centeredChildSlowProjection_norm_le :
    ‖centeredChildSlowProjection (P := P) (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, centeredChildSlowProjection_apply]
  exact (norm_snd_le Y.2.2).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))

theorem centeredChildReturnProjection_norm_le :
    ‖centeredChildReturnProjection (P := P) (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, centeredChildReturnProjection_apply, Prod.norm_def, Prod.norm_def]
  exact max_le (norm_fst_le Y) (max_le
    ((norm_fst_le Y.2).trans (norm_snd_le Y))
    ((norm_snd_le Y.2.2).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))))
end

/-! Pairing the parent chart with retained family and displacement coordinates costs no dimension factor. -/

section
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem centeredReturnInnerMap_positive_jet_bound (Fa : P × V → V)
    (hFa : ContDiff ℝ (⊤ : ℕ∞) Fa) (n : ℕ) (hn : 1 ≤ n)
    (Y : P × (V × V)) (C : ℝ) (hC : 1 ≤ C)
    (hb : ‖iteratedFDeriv ℝ n Fa (Y.1, Y.2.1)‖ ≤ C) :
    ‖iteratedFDeriv ℝ n (centeredReturnInnerMap Fa) Y‖ ≤ C := by
  let A := centeredReturnInputProjection (P := P) (V := V)
  let Q : (P × (V × V)) →L[ℝ] P := ContinuousLinearMap.fst ℝ P (V × V)
  let S : (P × (V × V)) →L[ℝ] V :=
    (ContinuousLinearMap.snd ℝ V V).comp (ContinuousLinearMap.snd ℝ P (V × V))
  have hQ : ‖Q‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Z => by
    rw [one_mul]; exact norm_fst_le Z)
  have hS : ‖S‖ ≤ 1 := ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun Z => by
    rw [one_mul]; exact (norm_snd_le Z.2).trans (norm_snd_le Z))
  have hFaN : ContDiff ℝ (n : ℕ∞) Fa := hFa.of_le (by simp)
  have hA : ContDiff ℝ (n : ℕ∞) (Fa ∘ A) := hFaN.comp A.contDiff
  have hQN : ContDiff ℝ (n : ℕ∞) Q := Q.contDiff
  have hSN : ContDiff ℝ (n : ℕ∞) S := S.contDiff
  have hbA : ‖iteratedFDeriv ℝ n (Fa ∘ A) Y‖ ≤ C := by
    have hh := finite_affine_derivative_norm_le Fa n hFaN A
      centeredReturnInputProjection_norm_le 0 Y
    simp only [add_zero] at hh
    exact hh.trans hb
  have hbQ : ‖iteratedFDeriv ℝ n Q Y‖ ≤ C :=
    (linear_positive_derivative_norm_le Q n hn Y).trans (hQ.trans hC)
  have hbS : ‖iteratedFDeriv ℝ n S Y‖ ≤ C :=
    (linear_positive_derivative_norm_le S n hn Y).trans (hS.trans hC)
  have hbAS : ‖iteratedFDeriv ℝ n (fun Z => ((Fa ∘ A) Z, S Z)) Y‖ ≤ C :=
    (independent_joint_pair_jet_bound (Fa ∘ A) S n hA hSN Y).trans (max_le hbA hbS)
  exact (independent_joint_pair_jet_bound Q (fun Z => ((Fa ∘ A) Z, S Z)) n
    hQN (hA.prodMk hSN) Y).trans (max_le hbQ hbAS)
end

/-! Re-anchoring uses the phase as both phase and center in a harmless norm-one slice. -/

section
variable {P V : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

def centeredChildDuplicatePhaseProjection : (P × (V × (V × V))) →L[ℝ] (P × (V × (V × V))) :=
  (ContinuousLinearMap.fst ℝ P (V × (V × V))).prod
    (centeredChildPhaseProjection.prod (centeredChildPhaseProjection.prod centeredChildSlowProjection))

theorem centeredChildDuplicatePhaseProjection_apply (Y : P × (V × (V × V))) :
    centeredChildDuplicatePhaseProjection Y = (Y.1, Y.2.2.1, Y.2.2.1, Y.2.2.2) := rfl

theorem centeredChildDuplicatePhaseProjection_norm_le :
    ‖centeredChildDuplicatePhaseProjection (P := P) (V := V)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro Y
  rw [one_mul, centeredChildDuplicatePhaseProjection_apply]
  simp only [Prod.norm_def]
  have hφ := (norm_fst_le Y.2.2).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))
  have hX := (norm_snd_le Y.2.2).trans ((norm_snd_le Y.2).trans (norm_snd_le Y))
  exact max_le (norm_fst_le Y) (max_le hφ (max_le hφ hX))
end

end AVRegularity.EntryWeakProofs
end
