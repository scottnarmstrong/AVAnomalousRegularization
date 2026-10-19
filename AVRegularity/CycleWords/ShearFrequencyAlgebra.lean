-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import Mathlib.MeasureTheory.Function.LpSeminorm.LpNorm
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Tactic.Monotonicity.Lemmas
public import Mathlib.Analysis.Fourier.AddCircleMulti
public import Homogenization.Ambient.Basic
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Topology.UniformSpace.Uniformizable

section
section
@[expose] public noncomputable section
open scoped ENNReal Classical
namespace AVRegularity.CycleWords

/-! Norm-one coordinate projections on an actual Hilbert basis, including infinite sectors. -/

def l2CoordinateRestriction {ι : Type*} (s : Set ι) :
    lp (fun _ : ι => ℂ) 2 →L[ℂ] lp (fun _ : ι => ℂ) 2 := by
  classical
  let L : lp (fun _ : ι => ℂ) 2 →ₗ[ℂ] lp (fun _ : ι => ℂ) 2 :=
    { toFun := fun f => ⟨fun i => if i ∈ s then f i else 0,
        f.property.mono' (fun i => by split_ifs <;> simp)⟩
      map_add' := fun f g => by
        apply lp.ext
        funext i
        change (if i ∈ s then f i + g i else 0) =
          (if i ∈ s then f i else 0) + (if i ∈ s then g i else 0)
        split_ifs <;> simp
      map_smul' := fun c f => by
        apply lp.ext
        funext i
        change (if i ∈ s then c • f i else 0) = c • (if i ∈ s then f i else 0)
        split_ifs <;> simp }
  exact L.mkContinuous 1 (fun f => by
    rw [one_mul]
    apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
    intro i
    change ‖if i ∈ s then f i else 0‖ ≤ ‖f i‖
    split_ifs <;> simp)

variable {H ι : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

def hilbertBasisSectorProjection (b : HilbertBasis ι ℂ H) (s : Set ι) : H →L[ℂ] H :=
  b.repr.symm.toLinearIsometry.toContinuousLinearMap.comp
    ((l2CoordinateRestriction s).comp b.repr.toLinearIsometry.toContinuousLinearMap)

theorem hilbertBasisSectorProjection_repr (b : HilbertBasis ι ℂ H) (s : Set ι)
    (f : H) (i : ι) :
    b.repr (hilbertBasisSectorProjection b s f) i = if i ∈ s then b.repr f i else 0 := by
  change b.repr (b.repr.symm (l2CoordinateRestriction s (b.repr f))) i = _
  rw [b.repr.apply_symm_apply]
  rfl

theorem hilbertBasisSectorProjection_norm_le (b : HilbertBasis ι ℂ H) (s : Set ι)
    (f : H) : ‖hilbertBasisSectorProjection b s f‖ ≤ ‖f‖ := by
  rw [← b.repr.norm_map (hilbertBasisSectorProjection b s f), ← b.repr.norm_map f]
  apply lp.norm_mono (by norm_num : (2 : ℝ≥0∞) ≠ 0)
  intro i
  rw [hilbertBasisSectorProjection_repr]
  split_ifs <;> simp

theorem hilbertBasisSectorProjection_idempotent (b : HilbertBasis ι ℂ H) (s : Set ι)
    (f : H) : hilbertBasisSectorProjection b s (hilbertBasisSectorProjection b s f) =
      hilbertBasisSectorProjection b s f := by
  apply b.repr.injective
  apply lp.ext
  funext i
  simp only [hilbertBasisSectorProjection_repr]
  split_ifs <;> rfl

theorem hilbertBasisSectorProjection_eq_self (b : HilbertBasis ι ℂ H) (s : Set ι)
    (f : H) (hf : ∀ i, i ∉ s → b.repr f i = 0) :
    hilbertBasisSectorProjection b s f = f := by
  apply b.repr.injective
  apply lp.ext
  funext i
  rw [hilbertBasisSectorProjection_repr]
  split_ifs with hi
  · rfl
  · exact (hf i hi).symm

theorem hilbertBasisSectorProjection_basis (b : HilbertBasis ι ℂ H) (s : Set ι)
    (i : ι) : hilbertBasisSectorProjection b s (b i) = if i ∈ s then b i else 0 := by
  apply b.repr.injective
  apply lp.ext
  funext k
  rw [hilbertBasisSectorProjection_repr]
  by_cases hki : k = i
  · subst k
    split_ifs <;> simp [b.repr_self]
  · split_ifs <;> simp [b.repr_self, lp.single_apply, hki]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Native Hilbert weak residuals vanish once every genuine Fourier basis test vanishes. -/

theorem hilbertBasis_clm_eq_zero {ι H F : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [NormedAddCommGroup F] [NormedSpace ℂ F]
    (b : HilbertBasis ι ℂ H) (L : H →L[ℂ] F) (hL : ∀ i, L (b i) = 0) : L = 0 := by
  have hs : Submodule.span ℂ (Set.range b) ≤ L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hL i
  have hc : closure (Submodule.span ℂ (Set.range b) : Set H) ⊆ L.toLinearMap.ker :=
    closure_minimal hs L.isClosed_ker
  apply ContinuousLinearMap.ext
  intro e
  have he : e ∈ closure (Submodule.span ℂ (Set.range b) : Set H) := by
    rw [← Submodule.topologicalClosure_coe, b.dense_span]
    exact Submodule.mem_top
  exact hc he

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! Countable Hilbert coordinates recover strong time measurability from weak scalar measurability. -/

theorem hilbert_time_aestronglyMeasurable_of_coordinates
    {X E ι : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [CompleteSpace E] [Countable ι] (b : HilbertBasis ι ℝ E)
    (μ : Measure X) (F : X → E)
    (hF : ∀ i, AEStronglyMeasurable (fun t => inner ℝ (b i) (F t)) μ) :
    AEStronglyMeasurable F μ := by
  classical
  have hm : ∀ S : Finset ι, AEStronglyMeasurable
      (fun t => ∑ i ∈ S, inner ℝ (b i) (F t) • b i) μ := by
    intro S
    induction S using Finset.induction_on with
    | empty => simpa only [Finset.sum_empty] using (aestronglyMeasurable_const :
        AEStronglyMeasurable (fun _ : X => (0 : E)) μ)
    | @insert i S hi ih =>
      simp only [Finset.sum_insert hi]
      exact ((hF i).smul aestronglyMeasurable_const).add ih
  apply aestronglyMeasurable_of_tendsto_ae (SummationFilter.unconditional ι).filter hm
  exact Eventually.of_forall (fun t => by
    simpa only [HasSum, b.repr_apply_apply] using b.hasSum_repr (F t))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! The odd enlarged pulse windows intersecting a bounded time interval have the required join count. -/

def interiorPulseIndices (τ a b : ℝ) : Finset ℤ :=
  Finset.Icc ⌈(a / τ - 7 / 4) / 2⌉ ⌊(b / τ - 1 / 4) / 2⌋

theorem interiorPulseIndices_mem_iff {τ a b : ℝ} (hτ : 0 < τ) (n : ℤ) :
    n ∈ interiorPulseIndices τ a b ↔
      a - 3 / 4 * τ ≤ (2 * (n : ℝ) + 1) * τ ∧
      (2 * (n : ℝ) + 1) * τ ≤ b + 3 / 4 * τ := by
  rw [interiorPulseIndices, Finset.mem_Icc, Int.ceil_le, Int.le_floor]
  constructor
  · rintro ⟨hlo, hhi⟩
    have hl := mul_le_mul_of_nonneg_right ((div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hlo) hτ.le
    have hh := mul_le_mul_of_nonneg_right ((le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mp hhi) hτ.le
    rw [sub_mul, div_mul_cancel₀ _ hτ.ne'] at hl hh
    constructor <;> linarith
  · rintro ⟨hlo, hhi⟩
    have hl : a / τ ≤ 2 * (n : ℝ) + 7 / 4 :=
      (div_le_iff₀ hτ).mpr (by linarith)
    have hh : 2 * (n : ℝ) + 1 / 4 ≤ b / τ :=
      (le_div_iff₀ hτ).mpr (by linarith)
    constructor
    · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      linarith
    · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 2)).mpr
      linarith

theorem interiorPulseIndices_join_bound {τ a b : ℝ} (hτ : 0 < τ) (hab : a ≤ b) :
    2 * ((interiorPulseIndices τ a b).card : ℝ) ≤ (b - a) / τ + 4 := by
  let L : ℤ := ⌈(a / τ - 7 / 4) / 2⌉
  let U : ℤ := ⌊(b / τ - 1 / 4) / 2⌋
  change 2 * ((Finset.Icc L U).card : ℝ) ≤ _
  by_cases hLU : L ≤ U
  · have hc : ((Finset.Icc L U).card : ℝ) = (U : ℝ) + 1 - (L : ℝ) := by
      exact_mod_cast Int.card_Icc_of_le L U (hLU.trans (by omega : U ≤ U + 1))
    have hl : (a / τ - 7 / 4) / 2 ≤ (L : ℝ) := Int.le_ceil _
    have hu : (U : ℝ) ≤ (b / τ - 1 / 4) / 2 := Int.floor_le _
    rw [hc, sub_div]
    linarith
  · have he : Finset.Icc L U = ∅ := Finset.Icc_eq_empty_of_lt (lt_of_not_ge hLU)
    rw [he, Finset.card_empty, Nat.cast_zero, mul_zero]
    have hd : 0 ≤ (b - a) / τ := div_nonneg (sub_nonneg.mpr hab) hτ.le
    linarith

/-! The endpoint quiet condition selects the required buffer; otherwise the buffer is zero. -/

def interiorQuietBuffer (τ a b : ℝ) (quiet : Set ℝ) : ℝ := by
  classical
  exact if Set.Icc a (a + τ / 4) ∪ Set.Icc (b - τ / 4) b ⊆ quiet then
    min (τ / 4) (b - a) else 0

theorem interiorQuietBuffer_bounds {τ a b : ℝ} (hτ : 0 < τ) (hab : a ≤ b) (quiet : Set ℝ) :
    0 ≤ interiorQuietBuffer τ a b quiet ∧
      interiorQuietBuffer τ a b quiet ≤ τ / 4 ∧
      interiorQuietBuffer τ a b quiet ≤ b - a := by
  classical
  by_cases hq : Set.Icc a (a + τ / 4) ∪ Set.Icc (b - τ / 4) b ⊆ quiet
  · simp only [interiorQuietBuffer, ite_eq_left hq]
    exact ⟨le_min (by positivity) (sub_nonneg.mpr hab), min_le_left _ _, min_le_right _ _⟩
  · simp only [interiorQuietBuffer, ite_eq_right hq]
    exact ⟨le_rfl, by positivity, sub_nonneg.mpr hab⟩

theorem interiorQuietBuffer_lower (τ a b : ℝ) (quiet : Set ℝ)
    (hq : Set.Icc a (a + τ / 4) ∪ Set.Icc (b - τ / 4) b ⊆ quiet) :
    min (τ / 4) (b - a) ≤ interiorQuietBuffer τ a b quiet := by
  simp only [interiorQuietBuffer, ite_eq_left hq, le_refl]

theorem interiorQuietBuffer_left {τ a b : ℝ} (hτ : 0 < τ) (hab : a ≤ b) (quiet : Set ℝ) :
    Set.Ico a (a + interiorQuietBuffer τ a b quiet) ⊆ quiet := by
  classical
  intro t ht
  by_cases hq : Set.Icc a (a + τ / 4) ∪ Set.Icc (b - τ / 4) b ⊆ quiet
  · apply hq
    left
    exact ⟨ht.1, le_of_lt (ht.2.trans_le (add_le_add le_rfl
      (interiorQuietBuffer_bounds hτ hab quiet).2.1))⟩
  · simp only [interiorQuietBuffer, ite_eq_right hq, add_zero] at ht
    exact False.elim ((not_lt_of_ge ht.1) ht.2)

theorem interiorQuietBuffer_right {τ a b : ℝ} (hτ : 0 < τ) (hab : a ≤ b) (quiet : Set ℝ) :
    Set.Ioc (b - interiorQuietBuffer τ a b quiet) b ⊆ quiet := by
  classical
  intro t ht
  by_cases hq : Set.Icc a (a + τ / 4) ∪ Set.Icc (b - τ / 4) b ⊆ quiet
  · apply hq
    right
    exact ⟨le_of_lt ((sub_le_sub_left (interiorQuietBuffer_bounds hτ hab quiet).2.1 b).trans_lt ht.1), ht.2⟩
  · simp only [interiorQuietBuffer, ite_eq_right hq, sub_zero] at ht
    exact False.elim ((not_lt_of_ge ht.2) ht.1)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped ENNReal Topology
namespace AVRegularity.CycleWords

/-! Dominated convergence in the L2 seminorm, for countably generated filters. -/

variable {X I E F : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedAddCommGroup F]
    {μ : Measure X} {l : Filter I} [l.IsCountablyGenerated]

theorem tendsto_lpNorm_two_of_dominated (f : I → X → E) (g : X → F)
    (hf : ∀ i, MemLp (f i) 2 μ) (hg : MemLp g 2 μ)
    (hb : ∀ i, ∀ᵐ x ∂μ, ‖f i x‖ ≤ ‖g x‖)
    (ht : ∀ᵐ x ∂μ, Tendsto (fun i => f i x) l (𝓝 0)) :
    Tendsto (fun i => lpNorm (f i) 2 μ) l (𝓝 0) := by
  have hi : Integrable (fun x => ‖g x‖ ^ (2 : ℕ)) μ := hg.integrable_norm_pow (by decide)
  have hconv : Tendsto (fun i => ∫ x, ‖f i x‖ ^ (2 : ℕ) ∂μ) l (𝓝 0) := by
    have hh := tendsto_integral_filter_of_dominated_convergence
      (μ := μ) (l := l) (F := fun i x => ‖f i x‖ ^ (2 : ℕ)) (f := fun _ => (0 : ℝ))
      (fun x => ‖g x‖ ^ (2 : ℕ))
      (Eventually.of_forall fun i => (hf i).aestronglyMeasurable.norm.pow 2)
      (Eventually.of_forall fun i => ?_) hi ?_
    · simpa using hh
    · filter_upwards [hb i] with x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      exact pow_le_pow_left₀ (norm_nonneg _) hx 2
    · filter_upwards [ht] with x hx
      simpa using (hx.norm.pow 2)
  have hh := hconv.rpow_const (p := (1 / 2 : ℝ)) (Or.inr (by norm_num))
  have he (i : I) : lpNorm (f i) 2 μ =
      (∫ x, ‖f i x‖ ^ (2 : ℕ) ∂μ) ^ (1 / 2 : ℝ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num)
      (hf i).aestronglyMeasurable]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two]
    norm_num
  simpa only [← he, Real.zero_rpow (by norm_num : (1 / 2 : ℝ) ≠ 0)] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! Simultaneous native and weighted L2 limits identify multiplication by any fixed finite real weight. -/

variable {X E : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] {μ : Measure X}

theorem L2_weighted_limit_ae (U V : ℕ → Lp E 2 μ) (u v : Lp E 2 μ) (q : X → ℝ)
    (hU : Tendsto U atTop (𝓝 u)) (hV : Tendsto V atTop (𝓝 v))
    (hr : ∀ n, V n =ᵐ[μ] (fun x => q x • U n x)) :
    v =ᵐ[μ] (fun x => q x • u x) := by
  obtain ⟨ns, hns, hu⟩ := (tendstoInMeasure_of_tendsto_Lp hU).exists_seq_tendsto_ae
  have hvn : Tendsto (fun n => V (ns n)) atTop (𝓝 v) := hV.comp hns.tendsto_atTop
  obtain ⟨ms, hms, hv⟩ := (tendstoInMeasure_of_tendsto_Lp hvn).exists_seq_tendsto_ae
  have hall : ∀ᵐ x ∂μ, ∀ n, V n x = q x • U n x := ae_all_iff.mpr hr
  filter_upwards [hu, hv, hall] with x hu' hv' hr'
  have hs := (hu'.comp hms.tendsto_atTop).const_smul (q x)
  have ht : Tendsto (fun n => q x • U (ns (ms n)) x) atTop (𝓝 (v x)) :=
    hv'.congr (fun n => hr' (ns (ms n)))
  exact tendsto_nhds_unique ht hs

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! A pointwise linear isometry gives a genuine linear isometry of L2 fields. -/

variable {X E F : Type*} [MeasurableSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

def liftLinearIsometryL2 (μ : Measure X) (L : E →ₗᵢ[ℝ] F) : Lp E 2 μ →ₗᵢ[ℝ] Lp F 2 μ where
  toLinearMap := L.toContinuousLinearMap.compLpₗ 2 μ
  norm_map' f := by
    change ‖L.toContinuousLinearMap.compLp f‖ = ‖f‖
    rw [Lp.norm_def, Lp.norm_def]
    congr 1
    apply eLpNorm_congr_norm_ae (Lp.aestronglyMeasurable _) (Lp.aestronglyMeasurable f)
    filter_upwards [L.toContinuousLinearMap.coeFn_compLp f] with x hx
    rw [hx]
    exact L.norm_map (f x)

theorem liftLinearIsometryL2_ae (μ : Measure X) (L : E →ₗᵢ[ℝ] F) (f : Lp E 2 μ) :
    liftLinearIsometryL2 μ L f =ᵐ[μ] fun x => L (f x) :=
  L.toContinuousLinearMap.coeFn_compLp f

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! A proved isometric fibre embedding has a contractive exact reconstruction on its range. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

def isometryAdjointReconstruct (L : E →ₗᵢ[ℝ] F) : F →L[ℝ] E :=
  ContinuousLinearMap.adjoint L.toContinuousLinearMap

theorem isometryAdjointReconstruct_leftInverse (L : E →ₗᵢ[ℝ] F) (x : E) :
    isometryAdjointReconstruct L (L x) = x := by
  have hh := (ContinuousLinearMap.norm_map_iff_adjoint_comp_self L.toContinuousLinearMap).mp
    (fun y => L.norm_map y)
  have he := congrArg (fun A : E →L[ℝ] E => A x) hh
  exact he

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Split a literal flux lower integral from a measurable state budget. -/

theorem lintegral_ofReal_sum_with_measurable_right
    {X : Type*} [MeasurableSpace X] (μ : Measure X) (f g : X → ℝ)
    (hf : ∀ t, 0 ≤ f t) (hg : ∀ t, 0 ≤ g t) (hgm : AEMeasurable g μ)
    (a c : ℝ) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (∫⁻ t, ENNReal.ofReal (a * f t + c * g t) ∂μ) =
      ENNReal.ofReal a * (∫⁻ t, ENNReal.ofReal (f t) ∂μ) +
      ENNReal.ofReal c * (∫⁻ t, ENNReal.ofReal (g t) ∂μ) := by
  simp_rw [ENNReal.ofReal_add (mul_nonneg ha (hf _)) (mul_nonneg hc (hg _)),
    ENNReal.ofReal_mul ha, ENNReal.ofReal_mul hc]
  have hm : AEMeasurable (fun t => ENNReal.ofReal c * ENNReal.ofReal (g t)) μ :=
    aemeasurable_const.mul hgm.ennreal_ofReal
  rw [lintegral_add_right' _ hm,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
    lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Contractive finite-coordinate truncations in the Hilbert sequence norm. -/

variable {I : Type*} [DecidableEq I] {E : I → Type*} [∀ i, NormedAddCommGroup (E i)]

theorem lp_coordinate_remainder_norm_le (f : lp E 2) (s : Finset I) :
    ‖f - ∑ i ∈ s, lp.single 2 i (f i)‖ ≤ ‖f‖ := by
  classical
  have he := lp.norm_compl_sum_single (by norm_num : 0 < (2 : ℝ≥0∞).toReal) f s
  simp only [ENNReal.toReal_ofNat, Real.rpow_two] at he
  have hs : 0 ≤ ∑ i ∈ s, ‖f i‖ ^ (2 : ℕ) := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hsq : ‖f - ∑ i ∈ s, lp.single 2 i (f i)‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    rw [he]
    exact sub_le_self _ hs
  exact (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory Filter
open scoped Topology
namespace AVRegularity.CycleWords

/-! A finite pointwise norm budget is closed under strong L2 convergence. -/

variable {A E F ι : Type*} [MeasurableSpace A] [NormedAddCommGroup E]
  [NormedAddCommGroup F] [Fintype ι]

def l2NormReadout (μ : Measure A) (f : Lp E 2 μ) : Lp ℝ 2 μ :=
  lipschitzWith_one_norm.compLp norm_zero f

theorem l2NormReadout_ae (μ : Measure A) (f : Lp E 2 μ) :
    l2NormReadout μ f =ᵐ[μ] fun x => ‖f x‖ :=
  lipschitzWith_one_norm.coeFn_compLp norm_zero f

theorem l2NormReadout_continuous (μ : Measure A) :
    Continuous (l2NormReadout μ : Lp E 2 μ → Lp ℝ 2 μ) :=
  lipschitzWith_one_norm.continuous_compLp norm_zero

theorem finite_norm_majorant_iff_Lp_order (μ : Measure A) (f : Lp E 2 μ)
    (g : ι → Lp F 2 μ) (c : ι → ℝ) :
    (∀ᵐ x ∂μ, ‖f x‖ ≤ ∑ i, c i * ‖g i x‖) ↔
      l2NormReadout μ f ≤ ∑ i, c i • l2NormReadout μ (g i) := by
  have hna : ∀ᵐ x ∂μ, ∀ i, l2NormReadout μ (g i) x = ‖g i x‖ :=
    ae_all_iff.mpr (fun i => l2NormReadout_ae μ (g i))
  have hsum := (Lp.coeFn_finsetSum (Finset.univ : Finset ι)
    (fun i => c i • l2NormReadout μ (g i))).trans
      (eventuallyEq_sum (fun i _ => Lp.coeFn_smul (c i) (l2NormReadout μ (g i))))
  rw [← Lp.coeFn_le]
  constructor <;> intro h <;>
    filter_upwards [h, l2NormReadout_ae μ f, hna, hsum] with x hx hf hg hs
  · simpa only [hf, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg] using hx
  · simpa only [hf, hs, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, hg] using hx

theorem finite_norm_majorant_closed (μ : Measure A) (fN : ℕ → Lp E 2 μ)
    (gN : ℕ → ι → Lp F 2 μ) (f : Lp E 2 μ) (g : ι → Lp F 2 μ) (c : ι → ℝ)
    (hf : Tendsto fN atTop (𝓝 f)) (hg : ∀ i, Tendsto (fun N => gN N i) atTop (𝓝 (g i)))
    (hb : ∀ N, ∀ᵐ x ∂μ, ‖fN N x‖ ≤ ∑ i, c i * ‖gN N i x‖) :
    ∀ᵐ x ∂μ, ‖f x‖ ≤ ∑ i, c i * ‖g i x‖ := by
  apply (finite_norm_majorant_iff_Lp_order μ f g c).mpr
  apply le_of_tendsto_of_tendsto
    ((l2NormReadout_continuous μ).tendsto f |>.comp hf)
    (tendsto_finsetSum _ (fun i _ => tendsto_const_nhds.smul
      ((l2NormReadout_continuous μ).tendsto (g i) |>.comp (hg i))))
  exact Filter.Eventually.of_forall (fun N =>
    (finite_norm_majorant_iff_Lp_order μ (fN N) (gN N) c).mp (hb N))

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A measurable curve can be bounded by a literal, possibly nonmeasurable, lower-integral majorant. -/

theorem memLp_two_of_lower_integral_majorant
    {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E]
    (μ : Measure X) (F : X → E) (hF : AEStronglyMeasurable F μ)
    (A : X → ℝ≥0∞) (hA : (∫⁻ t, A t ∂μ) < ⊤)
    (hb : ∀ t, ENNReal.ofReal (‖F t‖ ^ 2) ≤ A t) : MemLp F 2 μ := by
  apply (memLp_two_iff_integrable_sq_norm hF).mpr
  refine ⟨hF.norm.pow 2, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun t => sq_nonneg ‖F t‖))).mpr
  exact lt_of_le_of_lt (lintegral_mono hb) hA

theorem lower_integral_two_majorants_finite
    {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (A B : X → ℝ≥0∞) (hAm : AEMeasurable A μ)
    (hA : (∫⁻ t, A t ∂μ) < ⊤) (hB : (∫⁻ t, B t ∂μ) < ⊤)
    (c d : ℝ≥0∞) (hc : c ≠ ⊤) (hd : d ≠ ⊤) :
    (∫⁻ t, c * A t + d * B t ∂μ) < ⊤ := by
  have hm : AEMeasurable (fun t => c * A t) μ := aemeasurable_const.mul hAm
  rw [lintegral_add_left' hm,
    lintegral_const_mul' c A hc, lintegral_const_mul' d B hd]
  exact ENNReal.add_lt_top.mpr ⟨ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hc) hA,
    ENNReal.mul_lt_top (lt_top_iff_ne_top.mpr hd) hB⟩

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Normalizing a genuine forced energy estimate keeps the original row
coefficients and the preceding response contribution separate. -/

theorem normalized_forced_component_budget (α A θ : ℝ) (_hA : 0 ≤ A)
    (energy data forcing row previous : ℝ≥0∞)
    (he : energy ≤ ENNReal.ofReal A * (data + 16 * forcing))
    (hf : ENNReal.ofReal α * forcing ≤ 2 * (ENNReal.ofReal θ * row) + 2 * previous) :
    ENNReal.ofReal α * energy ≤ ENNReal.ofReal A *
      (ENNReal.ofReal α * data + 32 * ENNReal.ofReal θ * row + 32 * previous) := by
  have hh := mul_le_mul_right he (ENNReal.ofReal α)
  have hlin := mul_le_mul_right hf 16
  calc
    _ ≤ _ := hh
    _ = ENNReal.ofReal A * (ENNReal.ofReal α * data +
        16 * (ENNReal.ofReal α * forcing)) := by ring
    _ ≤ ENNReal.ofReal A * (ENNReal.ofReal α * data +
        16 * (2 * (ENNReal.ofReal θ * row) + 2 * previous)) :=
      mul_le_mul_right (add_le_add_right hlin _) _
    _ = _ := by ring

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open MeasureTheory
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Native square integrability implies the literal lower integral used by the scalar estimate is finite. -/

theorem nativeTimeNorm_lower_integral_lt_top {X E : Type*} [MeasurableSpace X]
    [NormedAddCommGroup E] {μ : Measure X} {f : X → E} (hf : MemLp f 2 μ) :
    (∫⁻ t, ENNReal.ofReal (‖f t‖ ^ 2) ∂μ) < ⊤ := by
  have hi := (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mp hf
  exact (hasFiniteIntegral_iff_ofReal (Filter.Eventually.of_forall
    (fun t => sq_nonneg ‖f t‖))).mp hi.hasFiniteIntegral

end AVRegularity.CycleWords
end
end

section
public section
open MeasureTheory Set
namespace AVRegularity.CycleWords

/-! The actual correction growth weight has a uniformly bounded time integral. -/

theorem negativeExponential_integral (a b : ℝ) :
    (∫ t in a..b, Real.exp (-4 * (t - a))) = (1 - Real.exp (-4 * (b - a))) / 4 := by
  have hd : ∀ t ∈ uIcc a b, HasDerivAt (fun t : ℝ => Real.exp (-4 * (t - a)) / (-4))
      (Real.exp (-4 * (t - a))) t := by
    intro t _
    simpa only [id_eq, mul_one, mul_div_cancel_right₀ _ (by norm_num : (-4 : ℝ) ≠ 0)] using
      (((((hasDerivAt_id t).sub_const a).const_mul (-4)).exp).div_const (-4))
  have hi : IntervalIntegrable (fun t : ℝ => Real.exp (-4 * (t - a))) volume a b :=
    (Real.continuous_exp.comp (continuous_const.mul (continuous_id.sub continuous_const))).intervalIntegrable _ _
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd hi]
  simp only [sub_self, mul_zero, Real.exp_zero]
  ring

theorem negativeExponential_integral_le (a b : ℝ) :
    (∫ t in a..b, Real.exp (-4 * (t - a))) ≤ 1 / 4 := by
  rw [negativeExponential_integral]
  exact div_le_div_of_nonneg_right (sub_le_self _ (Real.exp_pos _).le) (by norm_num)

theorem negativeExponential_weight_lower (a b t : ℝ) (ht : t ≤ b) :
    Real.exp (-4 * (b - a)) ≤ Real.exp (-4 * (t - a)) :=
  Real.exp_le_exp.mpr (by linarith only [ht])

theorem negativeExponential_cancel (D x B : ℝ)
    (h : Real.exp (-4 * D) * x ≤ B) : x ≤ Real.exp (4 * D) * B := by
  have he : Real.exp (4 * D) * Real.exp (-4 * D) = 1 := by
    rw [← Real.exp_add]
    have hz : 4 * D + -4 * D = 0 := by ring
    rw [hz, Real.exp_zero]
  calc
    x = Real.exp (4 * D) * (Real.exp (-4 * D) * x) := by rw [← mul_assoc, he, one_mul]
    _ ≤ Real.exp (4 * D) * B := mul_le_mul_of_nonneg_left h (Real.exp_pos _).le

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! A continuous radial clipping map with an exact fixed-ball property. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

def normBallClip (C : ℝ) (z : E) : E := (C / max C ‖z‖) • z

theorem continuous_normBallClip (C : ℝ) (hC : 0 < C) :
    Continuous (normBallClip (E := E) C) := by
  apply Continuous.smul _ continuous_id
  apply continuous_const.div (continuous_const.max continuous_norm)
  intro z
  exact ne_of_gt (lt_of_lt_of_le hC (le_max_left C ‖z‖))

theorem norm_normBallClip_le (C : ℝ) (hC : 0 < C) (z : E) :
    ‖normBallClip C z‖ ≤ C := by
  have hd : 0 < max C ‖z‖ := lt_of_lt_of_le hC (le_max_left C ‖z‖)
  rw [normBallClip, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg hC.le hd.le), div_mul_eq_mul_div, div_le_iff₀ hd]
  exact mul_le_mul_of_nonneg_left (le_max_right C ‖z‖) hC.le

theorem normBallClip_eq_self (C : ℝ) (hC : 0 < C) (z : E) (hz : ‖z‖ ≤ C) :
    normBallClip C z = z := by
  rw [normBallClip, max_eq_left hz, div_self hC.ne', one_smul]

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Radius normalization turns the enhancement displacement into a bounded shift. -/

theorem abs_le_one_add_of_sq_le {x C : ℝ} (_hC : 0 ≤ C) (hx : x ^ 2 ≤ C) :
    |x| ≤ 1 + C := by
  have ha := abs_nonneg x
  have hs : |x| ^ 2 ≤ C := by simpa only [sq_abs] using hx
  nlinarith only [hs, ha, sq_nonneg C]

theorem normalized_displacement_sq_le {d C B T L : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C) (hL : L ≤ T)
    (hd : d ^ 2 ≤ C * B * L) :
    (d / Real.sqrt (B * T)) ^ 2 ≤ C := by
  rw [div_pow, Real.sq_sqrt (mul_pos hB hT).le]
  apply (div_le_iff₀ (mul_pos hB hT)).2
  exact hd.trans (by simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hL (mul_nonneg hC hB.le))

theorem normalized_displacement_abs_le {d C B T L : ℝ}
    (hB : 0 < B) (hT : 0 < T) (hC : 0 ≤ C) (hL : L ≤ T)
    (hd : d ^ 2 ≤ C * B * L) :
    |d / Real.sqrt (B * T)| ≤ 1 + C :=
  abs_le_one_add_of_sq_le hC (normalized_displacement_sq_le hB hT hC hL hd)

/-! Polynomial contrast factors and exponential gap factors pass exactly between norm and energy prices. -/

theorem polynomial_decay_square_price (B p γ τ : ℝ) (J : ℕ) (hB : 0 ≤ B) :
    (Real.sqrt B * p ^ J * Real.exp (-γ * τ / 2)) ^ 2 =
      B * p ^ (2 * J) * Real.exp (-γ * τ) := by
  have he : (Real.exp (-γ * τ / 2)) ^ 2 = Real.exp (-γ * τ) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [mul_pow, mul_pow, Real.sq_sqrt hB, he, ← pow_mul]
  rw [Nat.mul_comm J 2]

/-! The derivative of a polynomial power has a uniform logarithmic gradient budget. -/

theorem polynomial_power_gradient_budget {U A E : ℝ} (n : ℕ)
    (hE : E ≤ A * U ^ 2) :
    ((n : ℝ) * U ^ (n - 1)) ^ 2 * E ≤ (n : ℝ) ^ 2 * A * (U ^ n) ^ 2 := by
  cases n with
  | zero => simp
  | succ n =>
    have hh := mul_le_mul_of_nonneg_left hE
      (sq_nonneg (((n + 1 : ℕ) : ℝ) * U ^ n))
    simp only [Nat.add_sub_cancel, pow_succ] at hh ⊢
    convert hh using 1
    ring

/-! Real power algebra for polynomial adjoint weight defects. -/

theorem polynomial_power_defect_budget (U A B L E : ℝ) (n : ℕ)
    (hU : 1 ≤ U) (hA : 0 ≤ A) (_hB : 0 ≤ B)
    (hL : L ≤ B * U) (hE : E ≤ A * U ^ 2) :
    (n : ℝ) * U ^ (n - 1) * L +
        (n : ℝ) * (n - 1 : ℕ) * U ^ (n - 2) * E ≤
      ((n : ℝ) * B + (n : ℝ) ^ 2 * A) * U ^ n := by
  have hUp : 0 ≤ U := by linarith
  cases n with
  | zero => simp
  | succ n =>
    cases n with
    | zero =>
      simp only [Nat.reduceAdd, Nat.cast_one, Nat.sub_self, pow_zero, one_mul,
        Nat.cast_zero, mul_zero, zero_mul, add_zero, pow_one]
      exact hL.trans (by nlinarith only [mul_nonneg hA hUp])
    | succ n =>
      have h1 := mul_le_mul_of_nonneg_left hL
        (show 0 ≤ ((n + 1 + 1 : ℕ) : ℝ) * U ^ n.succ by positivity)
      have h2 := mul_le_mul_of_nonneg_left hE
        (show 0 ≤ ((n + 1 + 1 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) * U ^ n by positivity)
      have hh := add_le_add h1 h2
      simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one] at hh ⊢
      have hid1 : (↑n + 1 + 1) * U ^ (n + 1) * (B * U) =
          (↑n + 1 + 1) * B * U ^ (n + 1 + 1) := by
        simp only [pow_succ]; ring
      have hid2 : (↑n + 1 + 1) * (↑n + 1) * U ^ n * (A * U ^ 2) =
          (↑n + 1 + 1) * (↑n + 1) * A * U ^ (n + 1 + 1) := by
        simp only [pow_succ]; ring
      rw [hid1, hid2] at hh
      exact hh.trans (by
        have hp := mul_nonneg hA (pow_nonneg hUp (n + 1 + 1))
        have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
        nlinarith only [hp, mul_nonneg hn hp])

/-! Polynomial weights remain comparable under a bounded coordinate displacement. -/

theorem polynomial_base_shift_bound (x y u v L : ℝ)
    (hL : 0 ≤ L) (hu : |u - x| ≤ L) (hv : |v - y| ≤ L) :
    1 + u ^ 2 + v ^ 2 ≤ (2 + 4 * L ^ 2) * (1 + x ^ 2 + y ^ 2) := by
  have hu2 : (u - x) ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (u - x)) hL).2 hu
  have hv2 : (v - y) ^ 2 ≤ L ^ 2 := by
    simpa only [sq_abs] using (sq_le_sq₀ (abs_nonneg (v - y)) hL).2 hv
  nlinarith only [hu2, hv2, sq_nonneg (u - 2 * x), sq_nonneg (v - 2 * y),
    sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg L) (sq_nonneg x),
    mul_nonneg (sq_nonneg L) (sq_nonneg y)]

theorem polynomial_weight_shift_upper (x y u v L : ℝ) (n : ℕ)
    (hL : 0 ≤ L) (hu : |u - x| ≤ L) (hv : |v - y| ≤ L) :
    (1 + u ^ 2 + v ^ 2) ^ n ≤
      (2 + 4 * L ^ 2) ^ n * (1 + x ^ 2 + y ^ 2) ^ n := by
  rw [← mul_pow]
  exact pow_le_pow_left₀ (by positivity) (polynomial_base_shift_bound x y u v L hL hu hv) n

theorem polynomial_weight_shift_lower (x y u v L : ℝ) (n : ℕ)
    (hL : 0 ≤ L) (hu : |u - x| ≤ L) (hv : |v - y| ≤ L) :
    ((2 + 4 * L ^ 2) ^ n)⁻¹ * (1 + x ^ 2 + y ^ 2) ^ n ≤
      (1 + u ^ 2 + v ^ 2) ^ n := by
  have hh := polynomial_weight_shift_upper u v x y L n hL
    (by simpa only [abs_sub_comm] using hu) (by simpa only [abs_sub_comm] using hv)
  have hc : 0 < (2 + 4 * L ^ 2) ^ n := by positivity
  exact (inv_mul_le_iff₀ hc).mpr hh

/-! A positive polynomial degree pays one geometric ratio and its moment degree. -/

theorem smallRatio_degree_le {ζ L t : ℝ} (hζ : 0 ≤ ζ) (hζ1 : ζ ≤ 1)
    (hL : 1 ≤ L) (ht : 0 ≤ t) (htL : t ≤ ζ * L)
    {j K : ℕ} (hj : 1 ≤ j) (hjK : j ≤ K) : t ^ j ≤ ζ * L ^ K := by
  have hz : ζ ^ j ≤ ζ := by
    obtain ⟨d, hd⟩ := Nat.exists_eq_add_of_le hj
    rw [hd, pow_add, pow_one]
    simpa only [mul_one] using mul_le_mul_of_nonneg_left (pow_le_one₀ hζ hζ1 (n := d)) hζ
  calc
    t ^ j ≤ (ζ * L) ^ j := pow_le_pow_left₀ ht htL _
    _ = ζ ^ j * L ^ j := mul_pow _ _ _
    _ ≤ ζ * L ^ K := mul_le_mul hz (pow_le_pow_right₀ hL hjK) (by positivity) hζ

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A selected constituent of a positive dependent order sum is bounded before cancellation. -/

theorem positive_constituent_term_le {Γ : Type*} [Fintype Γ]
    {W : ℕ → Type*} [∀ d, Fintype (W d)] (root : ℝ≥0∞) (m : Γ → ℝ≥0∞)
    (orders : Γ → Finset ℕ) (term : ∀ _γ : Γ, ∀ d : ℕ, W d → ℝ≥0∞)
    (γ : Γ) (d : ℕ) (hd : d ∈ orders γ) (I : W d) :
    root * m γ * term γ d I ≤ root * ∑ γ', m γ' * ∑ d' ∈ orders γ', ∑ I', term γ' d' I' := by
  have hi : term γ d I ≤ ∑ I', term γ d I' :=
    Finset.single_le_sum (fun _ _ => by positivity) (Finset.mem_univ I)
  have ho : (∑ I', term γ d I') ≤ ∑ d' ∈ orders γ, ∑ I', term γ d' I' :=
    Finset.single_le_sum (f := fun d' => ∑ I', term γ d' I') (fun _ _ => by positivity) hd
  have hg : m γ * (∑ d' ∈ orders γ, ∑ I', term γ d' I') ≤
      ∑ γ', m γ' * ∑ d' ∈ orders γ', ∑ I', term γ' d' I' :=
    Finset.single_le_sum (f := fun γ' => m γ' * ∑ d' ∈ orders γ', ∑ I', term γ' d' I')
      (fun _ _ => by positivity) (Finset.mem_univ γ)
  rw [mul_assoc]
  exact mul_le_mul_right ((mul_le_mul_right (hi.trans ho) _).trans hg) _

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Elementary quadratic budgets for polynomial adjoint weights. -/

theorem abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  have hs := sq_nonneg (|x| - 1 / 2)
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith only [hs, hsq]

theorem quadratic_coordinate_defect_bound {x y r s A D E : ℝ}
    (hA : 0 ≤ A) (hD : 0 ≤ D) (hr : |r| ≤ D) (hs : |s| ≤ D) (hE : E ≤ A) :
    2 * x * r + 2 * y * s + 2 * E ≤ (4 * D + 2 * A) * (1 + x ^ 2 + y ^ 2) := by
  have hx : x * r ≤ (1 + x ^ 2) * D :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul (abs_le_one_add_sq x) hr (abs_nonneg _) (by positivity))
  have hy : y * s ≤ (1 + y ^ 2) * D :=
    (le_abs_self _).trans (by
      rw [abs_mul]
      exact mul_le_mul (abs_le_one_add_sq y) hs (abs_nonneg _) (by positivity))
  nlinarith only [hx, hy, hE, mul_nonneg hD (sq_nonneg x), mul_nonneg hD (sq_nonneg y),
    mul_nonneg hA (sq_nonneg x), mul_nonneg hA (sq_nonneg y)]

theorem quadratic_coordinate_gradient_bound (x y a b c d : ℝ) :
    (2 * x * a + 2 * y * b) ^ 2 + (2 * x * c + 2 * y * d) ^ 2 ≤
      4 * (1 + x ^ 2 + y ^ 2) * (a ^ 2 + b ^ 2 + c ^ 2 + d ^ 2) := by
  nlinarith only [sq_nonneg (x * b - y * a), sq_nonneg (x * d - y * c),
    sq_nonneg a, sq_nonneg b, sq_nonneg c, sq_nonneg d]

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! A retained half-production bound controls the separate supremum and full production. -/

theorem quarter_production_supremum_le {T : Type*} (I : Set T) (b : T) (hb : b ∈ I)
    (e : T → ℝ≥0∞) (D R : ℝ≥0∞)
    (h : ∀ t ∈ I, e t + ENNReal.ofReal (1 / 4 : ℝ) * D ≤ R) :
    (⨆ t ∈ I, e t) + D ≤ 5 * R := by
  have he : (⨆ t ∈ I, e t) ≤ R := by
    apply iSup_le
    intro t
    apply iSup_le
    intro ht
    exact le_self_add.trans (h t ht)
  have hd : D ≤ 4 * R := by
    have hh := mul_le_mul' (le_rfl : (4 : ℝ≥0∞) ≤ 4) (le_add_self.trans (h b hb))
    have htwo : (4 : ℝ≥0∞) * ENNReal.ofReal (1 / 4 : ℝ) = 1 := by
      rw [← ENNReal.ofReal_ofNat 4, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4)]
      norm_num
    simpa only [← mul_assoc, htwo, one_mul] using hh
  exact (add_le_add he hd).trans_eq (by ring)

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! The absorbed real factorial bound retains its production in extended real form. -/

theorem quarter_retained_factorial_energy_to_ennreal {e d i f A : ℝ}
    (he : 0 ≤ e) (hd : 0 ≤ d) (hi : 0 ≤ i) (hf : 0 ≤ f)
    (h : e + d / 4 ≤ A * (i + 16 * f)) :
    ENNReal.ofReal e + ENNReal.ofReal (1 / 4 : ℝ) * ENNReal.ofReal d ≤
      ENNReal.ofReal A * (ENNReal.ofReal i + 16 * ENNReal.ofReal f) := by
  have hh := ENNReal.ofReal_le_ofReal h
  rw [mul_comm A] at hh
  have hhalf : d / 4 = (1 / 4 : ℝ) * d := by ring
  rw [hhalf, ENNReal.ofReal_add he (by positivity),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 4),
    ENNReal.ofReal_mul (add_nonneg hi (mul_nonneg (by norm_num) hf)),
    ENNReal.ofReal_add hi (mul_nonneg (by norm_num) hf),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 16)] at hh
  simpa only [ENNReal.ofReal_ofNat, mul_comm] using hh

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Nonnegative weight comparisons preserve the absorbed full interval production. -/

theorem quarter_scaled_retained_energy_transfer {e d ec dc i f i₀ f₀ C A : ℝ≥0∞}
    (he : e ≤ C * ec) (hd : d ≤ C * dc)
    (h : ec + ENNReal.ofReal (1 / 4 : ℝ) * dc ≤ A * (i + 16 * f))
    (hi : i ≤ C * i₀) (hf : f ≤ C * f₀) :
    e + ENNReal.ofReal (1 / 4 : ℝ) * d ≤ C * C * A * (i₀ + 16 * f₀) := by
  calc
    _ ≤ C * ec + ENNReal.ofReal (1 / 4 : ℝ) * (C * dc) :=
      add_le_add he (mul_le_mul' le_rfl hd)
    _ = C * (ec + ENNReal.ofReal (1 / 4 : ℝ) * dc) := by ring
    _ ≤ C * (A * (i + 16 * f)) := mul_le_mul' le_rfl h
    _ ≤ C * (A * (C * i₀ + 16 * (C * f₀))) :=
      mul_le_mul' le_rfl (mul_le_mul' le_rfl (add_le_add hi (mul_le_mul' le_rfl hf)))
    _ = _ := by ring

end AVRegularity.CycleWords
end
end

section
@[expose] public section
open MeasureTheory
namespace AVRegularity.CycleWords

/-! Nonzero cell time dilation preserves all full-measure coefficient budgets. -/

theorem ae_real_time_dilation (s : ℝ) (hs : s ≠ 0) (P : ℝ → Prop)
    (hP : ∀ᵐ t ∂volume, P t) : ∀ᵐ t ∂volume, P (s * t) := by
  simpa only [smul_eq_mul] using (Measure.quasiMeasurePreserving_smul volume hs).ae hP

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Scalar coefficient algebra for the two omitted remainders. -/

theorem ofReal_square_product (A z : ℝ) :
    ENNReal.ofReal ((A * z) ^ 2) = ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (z ^ 2) := by
  rw [mul_pow, ENNReal.ofReal_mul (sq_nonneg A)]

theorem metricRemainder_coefficient_le (A g z : ℝ) (hg : 0 ≤ g) (hg1 : g ≤ 1) :
    ENNReal.ofReal (A ^ 2 * (g * z) ^ 2) ≤
      ENNReal.ofReal (A ^ 2) * ENNReal.ofReal (z ^ 2) := by
  rw [← ENNReal.ofReal_mul (sq_nonneg A)]
  apply ENNReal.ofReal_le_ofReal
  have hg2 : g ^ 2 ≤ 1 := by nlinarith
  have hh := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hg2 (sq_nonneg z)) (sq_nonneg A)
  simpa only [mul_pow, one_mul, mul_assoc] using hh

def finiteResponseRemainderConstant (J : ℕ) (C A B T : ℝ) : ℝ :=
  1 + 4 * (J + 1 : ℝ) ^ 2 * (A ^ 2 + B ^ 2) * C ^ (J + 1) + 2 * T ^ 2 * C ^ (J + 1)

theorem finiteResponseRemainderConstant_ge_one (J : ℕ) (C A B T : ℝ) (hC : 0 ≤ C) :
    1 ≤ finiteResponseRemainderConstant J C A B T := by
  unfold finiteResponseRemainderConstant
  have hp := pow_nonneg hC (J + 1)
  have h1 : 0 ≤ 4 * (J + 1 : ℝ) ^ 2 * (A ^ 2 + B ^ 2) * C ^ (J + 1) := by positivity
  have h2 : 0 ≤ 2 * T ^ 2 * C ^ (J + 1) := by positivity
  linarith

theorem finiteResponseRemainderConstant_ofReal (J : ℕ) (C A B T : ℝ) (hC : 0 ≤ C) :
    1 + 4 * (J + 1 : ℝ≥0∞) ^ 2 * (ENNReal.ofReal (A ^ 2) + ENNReal.ofReal (B ^ 2)) *
        (ENNReal.ofReal C) ^ (J + 1) + 2 * ENNReal.ofReal (T ^ 2) * (ENNReal.ofReal C) ^ (J + 1) =
      ENNReal.ofReal (finiteResponseRemainderConstant J C A B T) := by
  have hcast : ENNReal.ofReal ((J : ℝ) + 1) = (J : ℝ≥0∞) + 1 := by
    rw [ENNReal.ofReal_add (Nat.cast_nonneg J) zero_le_one]
    simp
  unfold finiteResponseRemainderConstant
  rw [ENNReal.ofReal_add (by positivity : 0 ≤ 1 + 4 * (J + 1 : ℝ) ^ 2 * (A ^ 2 + B ^ 2) * C ^ (J + 1))
      (by positivity : 0 ≤ 2 * T ^ 2 * C ^ (J + 1)),
    ENNReal.ofReal_add zero_le_one (by positivity : 0 ≤ 4 * (J + 1 : ℝ) ^ 2 * (A ^ 2 + B ^ 2) * C ^ (J + 1))]
  simp only [ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (J + 1 : ℝ) ^ 2 * (A ^ 2 + B ^ 2)),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 4 * (J + 1 : ℝ) ^ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 4),
    ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * T ^ 2),
    ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
    ENNReal.ofReal_add (sq_nonneg A) (sq_nonneg B), ENNReal.ofReal_pow hC,
    ENNReal.ofReal_pow (by positivity : (0 : ℝ) ≤ J + 1), hcast,
    ENNReal.ofReal_ofNat, ENNReal.ofReal_one]

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
namespace AVRegularity.CycleWords

/-! The literal response insertion sum selects exactly the previous level. -/

open scoped BigOperators Classical

theorem responsePreviousLevel_sum_zero {J : ℕ} {E : Type*} [AddCommMonoid E]
    (j : Fin (J + 1)) (hj : j.val = 0) (f : Fin (J + 1) → E) :
    (∑ j', if j.val = j'.val + 1 then f j' else 0) = 0 := by
  apply Finset.sum_eq_zero
  intro j' _
  have hh : j.val ≠ j'.val + 1 := by omega
  simp only [hh, ite_false]

theorem responsePreviousLevel_sum_eq {J : ℕ} {E : Type*} [AddCommMonoid E]
    (j : Fin (J + 1)) (hj : j.val ≠ 0) (f : Fin (J + 1) → E) :
    (∑ j', if j.val = j'.val + 1 then f j' else 0) =
      f ⟨j.val - 1, by have hh := j.isLt; omega⟩ := by
  classical
  let jp : Fin (J + 1) := ⟨j.val - 1, by have hh := j.isLt; omega⟩
  rw [Finset.sum_eq_single jp]
  · have hh : j.val = jp.val + 1 := by dsimp [jp]; omega
    rw [ite_eq_left hh]
  · intro j' _ hne
    have hh : j.val ≠ j'.val + 1 := by
      intro he
      apply hne
      apply Fin.ext
      dsimp [jp]
      omega
    simp only [hh, ite_false]
  · simp

end AVRegularity.CycleWords
end
end
end

section
@[expose] public section
open scoped ENNReal
namespace AVRegularity.CycleWords

/-! Uniform scalar prices turn the normalized source and metric contributions
into the graph recurrence used for the weighted response estimates. -/

theorem response_row_coefficient_budget (A S M B ε energy data row previous : ℝ≥0∞)
    (hA : A ≤ B) (hS : A * S ≤ B) (hM : A * M ≤ B)
    (he : energy ≤ A * (data + S * row + M * ε * previous)) :
    energy ≤ B * data + B * ε * previous + B * row := by
  apply he.trans
  calc
    _ = A * data + (A * M) * ε * previous + (A * S) * row := by ring
    _ ≤ _ := add_le_add
      (add_le_add (mul_le_mul_left hA data) (mul_le_mul_left (mul_le_mul_left hM ε) previous))
      (mul_le_mul_left hS row)

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open UnitAddTorus
namespace AVRegularity.CycleWords

/-! Equality of continuous symbol maps follows from equality on actual Fourier modes. -/

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℂ F]

theorem scalarTorusFourierModeCLM_ext
    (L R : C(UnitAddTorus (Fin 2), ℂ) →L[ℂ] F)
    (h : ∀ m : Fin 2 → ℤ, L (mFourier m) = R (mFourier m)) : L = R := by
  let S := Submodule.span ℂ (Set.range (mFourier (d := Fin 2)))
  have hs : S ≤ (L - R).toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨m, rfl⟩
    change L (mFourier m) - R (mFourier m) = 0
    exact sub_eq_zero.mpr (h m)
  have hc : closure (S : Set C(UnitAddTorus (Fin 2), ℂ)) ⊆ (L - R).toLinearMap.ker :=
    closure_minimal hs (L - R).isClosed_ker
  apply ContinuousLinearMap.ext
  intro b
  have hb : b ∈ closure (S : Set C(UnitAddTorus (Fin 2), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe]
    change b ∈ (Submodule.span ℂ (Set.range (mFourier (d := Fin 2)))).topologicalClosure
    rw [span_mFourier_closure_eq_top]
    exact Submodule.mem_top
  have hk := hc hb
  change L b - R b = 0 at hk
  exact sub_eq_zero.mp hk

end AVRegularity.CycleWords
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory
namespace AVRegularity.CycleWords

/-! The actual seam multiplier has compact support and finite polynomial moments. -/

theorem seamCutoff_hasCompactSupport (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0) : HasCompactSupport m := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall (0 : Vec 2) (|R| + 1))
  intro ξ hξ
  change dist ξ 0 ≤ |R| + 1
  rw [dist_zero_right]
  apply le_of_not_gt
  intro hnorm
  apply hξ
  apply hm
  have hcoord : ∀ j : Fin 2, |ξ j| ≤ Real.sqrt (vecDot ξ ξ) := by
    intro j
    have hs : (ξ j) ^ 2 ≤ vecDot ξ ξ := by
      unfold vecDot
      simpa only [← sq] using Finset.single_le_sum (fun i _ => sq_nonneg (ξ i)) (Finset.mem_univ j)
    have hpos : 0 ≤ vecDot ξ ξ := by unfold vecDot; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
    have hsqrt := Real.sq_sqrt hpos
    nlinarith [Real.sqrt_nonneg (vecDot ξ ξ), sq_abs (ξ j)]
  have hnormR : ‖ξ‖ ≤ Real.sqrt (vecDot ξ ξ) := by
    exact (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).mpr (fun j => by simpa only [Real.norm_eq_abs] using hcoord j)
  exact (le_abs_self R).trans ((by linarith : |R| ≤ ‖ξ‖).trans hnormR)

theorem seamCutoff_polynomial_integrable (m : Vec 2 → ℝ) (R : ℝ)
    (hm : ∀ ξ, R ≤ Real.sqrt (vecDot ξ ξ) → m ξ = 0)
    (hs : Continuous m) (n : ℕ) : Integrable (fun ξ => ‖ξ‖ ^ n * ‖m ξ‖) :=
  ((continuous_norm.pow n).mul hs.norm).integrable_of_hasCompactSupport
    (seamCutoff_hasCompactSupport m R hm).norm.mul_left

end AVRegularity.CycleWords
end
end

section
@[expose] public section
namespace AVRegularity.CycleWords

/-! Cancellation of the shear frequency against the molecular memory rate. -/

theorem shear_frequency_memory_cancel (e ν a : ℝ) (he : 0 < e) (hν : 0 < ν) :
    (4 * Real.pi ^ 2 * ν / e ^ 2)⁻¹ *
      |(2 * Real.pi * a * e⁻¹) * (2 * Real.pi * e⁻¹)| = |a| / ν := by
  have hfreq : 0 ≤ (2 * Real.pi * e⁻¹) ^ 2 := sq_nonneg _
  have hi : (2 * Real.pi * a * e⁻¹) * (2 * Real.pi * e⁻¹) =
      a * (2 * Real.pi * e⁻¹) ^ 2 := by ring
  rw [hi, abs_mul, abs_of_nonneg hfreq]
  field_simp
  ring

theorem shear_displacement_memory_cancel (e ν a : ℝ) (he : 0 < e) (hν : 0 < ν) :
    (4 * Real.pi ^ 2 * ν / e ^ 2)⁻¹ * |2 * Real.pi * a * e⁻¹| =
      |(2 * Real.pi * a / e) / (4 * Real.pi ^ 2 * ν / e ^ 2)| := by
  have hμ : 0 < 4 * Real.pi ^ 2 * ν / e ^ 2 := by positivity
  rw [abs_div, abs_of_pos hμ]
  simp only [div_eq_mul_inv]
  ring

end AVRegularity.CycleWords
end
end
