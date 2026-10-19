-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.CovarianceMatrix
public import AVRegularity.CycleComparison.Coarse.Adj.MulOp
public import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Normed.Lp.SmoothApprox
import Mathlib.MeasureTheory.Function.UnifTight
import Mathlib.MeasureTheory.Measure.SeparableMeasure

section
@[expose] public noncomputable section

section
open MeasureTheory
namespace AVRegularity.CycleComparison.Coarse

/-! Lifting measurability through a countable separating family of continuous coordinates.

If `X` is a Polish normed space and `Φ n : X → ℝ` is a countable family of continuous functions
which separates points, then a map `G : α → X` is a.e. strongly measurable as soon as every
`Φ n ∘ G` is a.e. measurable (continuous injective maps between Polish spaces are measurable
embeddings, Lusin–Souslin). -/

/-- A map into a Polish normed space is a.e. strongly measurable if the coordinates of a
countable separating family of continuous functionals are a.e. measurable. -/
theorem aestronglyMeasurable_of_separating_coords {α X : Type*} [MeasurableSpace α]
    [NormedAddCommGroup X] [SecondCountableTopology X] [CompleteSpace X]
    {μ : Measure α} (Φ : ℕ → X → ℝ) (hΦ : ∀ n, Continuous (Φ n))
    (hsep : ∀ x y : X, (∀ n, Φ n x = Φ n y) → x = y) (G : α → X)
    (hG : ∀ n, AEMeasurable (fun a => Φ n (G a)) μ) :
    AEStronglyMeasurable G μ := by
  let _ : MeasurableSpace X := borel X
  have : BorelSpace X := ⟨rfl⟩
  have : PolishSpace X := inferInstance
  let Ψ : X → ℕ → ℝ := fun x n => Φ n x
  have hΨc : Continuous Ψ := continuous_pi hΦ
  have hΨi : Function.Injective Ψ := fun x y h => hsep x y (fun n => congrFun h n)
  have hemb : MeasurableEmbedding Ψ := hΨc.measurableEmbedding hΨi
  have hcomp : AEMeasurable (Ψ ∘ G) μ := aemeasurable_pi_iff.mpr hG
  exact (hemb.aemeasurable_comp_iff.mp hcomp).aestronglyMeasurable

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVenhance.Infra.Parabolic.FourierGalerkin
namespace AVRegularity.CycleComparison.Coarse

/-! Smooth compactly supported fields in the open unit cell extend to smooth `Z²`-periodic fields
agreeing with them on the cell. -/

/-- Scalar periodization of a function supported in the open cell agrees with it on the cell. -/
theorem compactTestPeriodization_eq_of_tsupport {φ : Vec 2 → ℝ}
    (hφ : tsupport φ ⊆ AVenhance.unitCube) {x : Vec 2} (hx : x ∈ AVenhance.unitCube) :
    compactTestPeriodization φ x = φ x := by
  classical
  unfold compactTestPeriodization
  rw [finsum_eq_single _ (0 : WeakGradientPeriodization.PeriodTranslations)]
  · simp
  · intro z hz
    by_contra hne
    have hmem : x + (z : Vec 2) ∈ AVenhance.unitCube :=
      hφ (subset_tsupport φ (Function.mem_support.mpr hne))
    have hz' : (z : Vec 2) ∈ WeakGradientPeriodization.PeriodLattice := z.2
    have hint : ∀ i, ∃ m : ℤ, (z : Vec 2) i = m := by
      have h := ((Pi.basisFun ℝ (Fin 2)).mem_span_iff_repr_mem ℤ (z : Vec 2)).mp hz'
      intro i
      obtain ⟨m, hm⟩ := h i
      exact ⟨m, by simpa [Pi.basisFun_repr] using hm.symm⟩
    apply hz
    apply Subtype.ext
    funext i
    obtain ⟨m, hm⟩ := hint i
    have h1 := hmem i (Set.mem_univ i)
    have h2 := hx i (Set.mem_univ i)
    simp only [Set.mem_Ioo, Pi.add_apply, hm] at h1 h2
    have hm0 : m = 0 := by
      have a : (-1 : ℝ) < m := by linarith [h1.1, h2.2]
      have b : (m : ℝ) < 1 := by linarith [h1.2, h2.1]
      have a' : (-1 : ℤ) < m := by exact_mod_cast a
      have b' : m < (1 : ℤ) := by exact_mod_cast b
      omega
    simp [hm, hm0]

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- A smooth compactly supported vector field with support in the open cell has a smooth
`Z²`-periodic extension equal to it on the cell. -/
theorem exists_periodic_extension {ψ : Vec 2 → F} (hs : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hc : HasCompactSupport ψ) (hsupp : tsupport ψ ⊆ AVenhance.unitCube) :
    ∃ ψ' : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧ AVenhance.IsZ2Periodic ψ' ∧
      ∀ x ∈ AVenhance.unitCube, ψ' x = ψ x := by
  let b := stdOrthonormalBasis ℝ F
  let c : Fin (Module.finrank ℝ F) → Vec 2 → ℝ := fun i y => inner ℝ (b i) (ψ y)
  have hcs : ∀ i, ContDiff ℝ (⊤ : ℕ∞) (c i) := fun i =>
    contDiff_const.inner ℝ hs
  have hcc : ∀ i, HasCompactSupport (c i) := fun i =>
    hc.mono (fun y hy => by
      by_contra h
      exact hy (by simp [c, Function.notMem_support.mp h]))
  have hct : ∀ i, tsupport (c i) ⊆ AVenhance.unitCube := fun i =>
    (closure_mono (fun y hy => by
      by_contra h
      exact hy (by simp [c, Function.notMem_support.mp h]))).trans hsupp
  refine ⟨fun x => ∑ i, compactTestPeriodization (c i) x • b i, ?_, ?_, ?_⟩
  · exact ContDiff.sum fun i _ =>
      (compactTestPeriodization_contDiff (hcc i) (hcs i)).smul contDiff_const
  · intro n x
    simp only [compactTestPeriodization_periodic n x]
  · intro x hx
    simp only [compactTestPeriodization_eq_of_tsupport (hct _) hx, c]
    simpa [mul_comm] using (b.sum_repr' (ψ x))

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization Filter Topology
open scoped ENNReal NNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Smooth `Z²`-periodic fields are dense in `L²(unitCube; F)`.

Smooth compactly supported fields are dense in `L²`; multiplying by cutoffs supported in the
open cell and periodizing (`Periodize`) gives smooth periodic fields converging to them. -/

/-- Cutoffs in the open unit cell, equal to one on the closed shrunken cell of radius `1/(n+2)`. -/
theorem exists_cell_cutoff (n : ℕ) :
    ∃ χ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) χ ∧ (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧
      tsupport χ ⊆ AVenhance.unitCube ∧ HasCompactSupport χ ∧
      ∀ x ∈ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2))),
        χ x = 1 := by
  set a : ℝ := 1 / ((n : ℝ) + 3) with ha
  set b : ℝ := 1 / ((n : ℝ) + 2) with hb
  have ha0 : 0 < a := by positivity
  have hab : a < b := by
    rw [ha, hb]
    exact one_div_lt_one_div_of_lt (by positivity) (by linarith)
  have hb2 : b ≤ 1 / 2 := by
    rw [hb]
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hs : IsOpen (Set.pi Set.univ (fun _ : Fin 2 => Set.Ioo a (1 - a))) :=
    isOpen_set_pi Set.finite_univ (fun _ _ => isOpen_Ioo)
  have ht : IsClosed (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc b (1 - b))) :=
    isClosed_set_pi (fun _ _ => isClosed_Icc)
  have hts : Set.pi Set.univ (fun _ : Fin 2 => Set.Icc b (1 - b)) ⊆
      Set.pi Set.univ (fun _ : Fin 2 => Set.Ioo a (1 - a)) := by
    intro x hx i hi
    have := hx i hi
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  obtain ⟨χ, hχs, hχr, hχsupp, hχ1⟩ := exists_contDiff_support_eq_eq_one_iff
    (n := (⊤ : ℕ∞)) hs ht hts
  have hC : IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc a (1 - a))) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  have hts' : tsupport χ ⊆ Set.pi Set.univ (fun _ : Fin 2 => Set.Icc a (1 - a)) := by
    unfold tsupport
    rw [hχsupp]
    exact closure_minimal (Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self))
      hC.isClosed
  refine ⟨χ, hχs, fun x => hχr ⟨x, rfl⟩, ?_, hC.of_isClosed_subset isClosed_closure hts', ?_⟩
  · intro x hx i hi
    have := hts' hx i hi
    exact ⟨by linarith [this.1], by linarith [this.2]⟩
  · intro x hx
    exact (hχ1 x).mp hx

instance isFiniteMeasure_restrict_unitCube :
    IsFiniteMeasure (volume.restrict AVenhance.unitCube : Measure (Vec 2)) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  exact lt_of_le_of_lt (measure_mono (Set.pi_mono (fun _ _ => Set.Ioo_subset_Icc_self)))
    hc.measure_lt_top

theorem measurableSet_unitCube : MeasurableSet AVenhance.unitCube :=
  MeasurableSet.univ_pi (fun _ => measurableSet_Ioo)

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]

/-- Smooth periodic fields (as `L²` classes on the cell) are dense in `L²(unitCube; F)`. -/
theorem dense_smooth_periodic_lp :
    Dense {f : Lp F 2 (volume.restrict AVenhance.unitCube) |
      ∃ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ AVenhance.IsZ2Periodic ψ ∧
        f =ᵐ[volume.restrict AVenhance.unitCube] ψ} := by
  set μ : Measure (Vec 2) := volume.restrict AVenhance.unitCube with hμ
  set S := {f : Lp F 2 μ | ∃ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ AVenhance.IsZ2Periodic ψ ∧
        f =ᵐ[μ] ψ} with hS
  have hD := MeasureTheory.Lp.dense_hasCompactSupport_contDiff (E := Vec 2) (F := F) (μ := μ)
    (p := 2) (by simp)
  have hsub : ∀ f ∈ {f : Lp F 2 μ | ∃ (g : Vec 2 → F), f =ᵐ[μ] g ∧ HasCompactSupport g ∧
      ContDiff ℝ (⊤ : ℕ∞) g}, f ∈ closure S := by
    rintro f ⟨g, hfg, hgc, hgs⟩
    have hgcont : Continuous g := hgs.continuous
    have hgL : MemLp g 2 μ := (hgcont.memLp_of_hasCompactSupport hgc).restrict _
    obtain ⟨M, hM⟩ := hgcont.bounded_above_of_compact_support hgc
    choose χ hχs hχr hχt hχc hχ1 using exists_cell_cutoff
    let ψ : ℕ → Vec 2 → F := fun n x => χ n x • g x
    have hψs : ∀ n, ContDiff ℝ (⊤ : ℕ∞) (ψ n) := fun n => (hχs n).smul hgs
    have hψc : ∀ n, HasCompactSupport (ψ n) := fun n => hgc.mono' (by
      intro x hx
      refine subset_closure ?_
      intro h
      exact hx (by simp [ψ, h]))
    have hψt : ∀ n, tsupport (ψ n) ⊆ AVenhance.unitCube := fun n =>
      (tsupport_smul_subset_left (χ n) g).trans (hχt n)
    have hψL : ∀ n, MemLp (ψ n) 2 μ := fun n =>
      ((hψs n).continuous.memLp_of_hasCompactSupport (hψc n)).restrict _
    have hlim : Tendsto (fun n => (hψL n).toLp (ψ n)) atTop (𝓝 (hgL.toLp g)) := by
      rw [Lp.tendsto_Lp_iff_tendsto_eLpNorm'' (fi := atTop) (f := ψ) (hψL) g hgL]
      refine tendsto_Lp_of_tendsto_ae (by norm_num) (by simp)
        (fun n => (hψL n).aestronglyMeasurable) hgL ?_ ?_ ?_
      · refine unifIntegrable_of (by norm_num) (by simp)
          (fun n => (hψL n).aestronglyMeasurable) (fun ε hε => ⟨(M + 1).toNNReal, fun n => ?_⟩)
        have : {x | (M + 1).toNNReal ≤ ‖ψ n x‖₊} = ∅ := by
          ext x
          simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          have h1 : ‖ψ n x‖ ≤ M := by
            calc ‖ψ n x‖ = |χ n x| * ‖g x‖ := by simp [ψ, norm_smul]
              _ ≤ 1 * ‖g x‖ := by
                gcongr
                rw [abs_of_nonneg (hχr n x).1]
                exact (hχr n x).2
              _ ≤ M := by simpa using hM x
          have h2 : ‖ψ n x‖ < M + 1 := by linarith
          rw [← NNReal.coe_lt_coe]
          simpa [Real.coe_toNNReal _ (by linarith [norm_nonneg (ψ n x), h1] : 0 ≤ M + 1)] using h2
        rw [this]
        simp
      · intro ε hε
        refine ⟨Set.univ, measure_ne_top _ _, fun n => ?_⟩
        simp
      · have hmem : ∀ᵐ x ∂μ, x ∈ AVenhance.unitCube :=
          ae_restrict_mem measurableSet_unitCube
        filter_upwards [hmem] with x hx
        have hev : ∀ᶠ n in atTop, χ n x = 1 := by
          have h : ∀ i : Fin 2, ∀ᶠ n : ℕ in atTop,
              x i ∈ Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)) := by
            intro i
            have hi := hx i (Set.mem_univ i)
            have ht0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
              have := tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)
              have h2 := (tendsto_add_atTop_iff_nat (f := fun n : ℕ => 1 / ((n : ℝ) + 1)) 1).mpr
                this
              simpa [add_assoc, one_add_one_eq_two] using h2
            have e1 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 2) < x i :=
              ht0.eventually (gt_mem_nhds hi.1)
            have e2 : ∀ᶠ n : ℕ in atTop, 1 / ((n : ℝ) + 2) < 1 - x i :=
              ht0.eventually (gt_mem_nhds (by linarith [hi.2]))
            filter_upwards [e1, e2] with n h1 h2
            exact ⟨h1.le, by linarith⟩
          have hall : ∀ᶠ n : ℕ in atTop, ∀ i : Fin 2,
              x i ∈ Set.Icc (1 / ((n : ℝ) + 2)) (1 - 1 / ((n : ℝ) + 2)) :=
            (eventually_all).mpr h
          filter_upwards [hall] with n hn
          exact hχ1 n x (fun i _ => hn i)
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [hev] with n hn
        simp [ψ, hn]
    have hext : ∀ n, ∃ ψ' : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ' ∧ AVenhance.IsZ2Periodic ψ' ∧
        ∀ x ∈ AVenhance.unitCube, ψ' x = ψ n x := fun n =>
      exists_periodic_extension (hψs n) (hψc n) (hψt n)
    choose ψ' hψ's hψ'p hψ'e using hext
    have hmemS : ∀ n, (hψL n).toLp (ψ n) ∈ S := fun n =>
      ⟨ψ' n, hψ's n, hψ'p n, (hψL n).coeFn_toLp.trans
        ((ae_restrict_of_forall_mem measurableSet_unitCube
          (fun x hx => (hψ'e n x hx).symm)))⟩
    have hfeq : f = hgL.toLp g := by
      apply Lp.ext
      exact hfg.trans hgL.coeFn_toLp.symm
    rw [hfeq]
    exact mem_closure_of_tendsto hlim (Eventually.of_forall hmemS)
  intro f
  exact closure_minimal hsub isClosed_closure (hD f)

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization Filter Topology
namespace AVRegularity.CycleComparison.Coarse

/-! Joint measurability toolkit on the subtype domain `Set.Icc t₀ t₁ × Vec 2`.

`JointlyMeas t₀ t₁ Ψ` says that `(s, x) ↦ Ψ s x` is Borel measurable on `Set.Icc t₀ t₁ × Vec 2`,
the form of the coefficient premises of the coarse setting. We prove closure under the operations
used by the test-field operators of the coarse fluxes, the continuity of the covariance matrix, and
a bridge to a.e. strong measurability for the product measure of the window and the unit cell. -/

/-- `Ψ` is jointly (Borel) measurable on `Set.Icc t₀ t₁ × Vec 2`. -/
def JointlyMeas {F : Type*} [MeasurableSpace F] (t₀ t₁ : ℝ) (Ψ : ℝ → Vec 2 → F) : Prop :=
  Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => Ψ q.1 q.2

namespace JointlyMeas

variable {t₀ t₁ : ℝ}

section Basic

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F]

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [BorelSpace F] [SecondCountableTopology F] in
theorem const (c : F) : JointlyMeas t₀ t₁ fun _ _ => c := measurable_const

omit [NormedSpace ℝ F] in
theorem add {Ψ Φ : ℝ → Vec 2 → F} (hΨ : JointlyMeas t₀ t₁ Ψ) (hΦ : JointlyMeas t₀ t₁ Φ) :
    JointlyMeas t₀ t₁ fun s x => Ψ s x + Φ s x := Measurable.add hΨ hΦ

omit [NormedSpace ℝ F] in
theorem sub {Ψ Φ : ℝ → Vec 2 → F} (hΨ : JointlyMeas t₀ t₁ Ψ) (hΦ : JointlyMeas t₀ t₁ Φ) :
    JointlyMeas t₀ t₁ fun s x => Ψ s x - Φ s x := Measurable.sub hΨ hΦ

omit [NormedSpace ℝ F] [SecondCountableTopology F] in
theorem neg {Ψ : ℝ → Vec 2 → F} (hΨ : JointlyMeas t₀ t₁ Ψ) :
    JointlyMeas t₀ t₁ fun s x => -Ψ s x := Measurable.neg hΨ

omit [NormedSpace ℝ F] in
theorem sum {ι : Type*} (S : Finset ι) {Ψ : ι → ℝ → Vec 2 → F}
    (h : ∀ i ∈ S, JointlyMeas t₀ t₁ (Ψ i)) :
    JointlyMeas t₀ t₁ fun s x => ∑ i ∈ S, Ψ i s x :=
  Finset.measurable_sum S h

/-- Real scalar multiples by a function of time which is measurable on the window. -/
theorem smul {c : ℝ → ℝ} (hc : Measurable fun s : Set.Icc t₀ t₁ => c s) {Ψ : ℝ → Vec 2 → F}
    (hΨ : JointlyMeas t₀ t₁ Ψ) : JointlyMeas t₀ t₁ fun s x => c s • Ψ s x :=
  (hc.comp measurable_fst).smul hΨ

omit [NormedSpace ℝ F] [SecondCountableTopology F] in
/-- A time-independent continuous field. -/
theorem of_continuous {Φ : Vec 2 → F} (hΦ : Continuous Φ) : JointlyMeas t₀ t₁ fun _ x => Φ x :=
  hΦ.measurable.comp measurable_snd

omit [NormedAddCommGroup F] [NormedSpace ℝ F] [BorelSpace F] [SecondCountableTopology F] in
/-- Joint measurability gives measurability of each frozen-time slice at a window time. -/
theorem slice {Ψ : ℝ → Vec 2 → F} (hΨ : JointlyMeas t₀ t₁ Ψ) {s : ℝ} (hs : s ∈ Set.Icc t₀ t₁) :
    Measurable (Ψ s) :=
  hΨ.comp (measurable_const.prodMk measurable_id : Measurable fun x : Vec 2 => ((⟨s, hs⟩ :
    Set.Icc t₀ t₁), x))

/-- A matrix coefficient with measurable entries applied to a jointly measurable field. -/
theorem mulVec {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hJ : ∀ i j, Measurable fun t => Jm t i j)
    {Ψ : ℝ → Vec 2 → Vec 2} (hΨ : JointlyMeas t₀ t₁ Ψ) :
    JointlyMeas t₀ t₁ fun s x => (Jm s).mulVec (Ψ s x) := by
  unfold JointlyMeas
  refine measurable_pi_iff.mpr fun i => ?_
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.measurable_sum _ fun j _ => ?_
  exact ((hJ i j).comp (measurable_subtype_coe.comp measurable_fst)).mul
    ((measurable_pi_apply j).comp hΨ)

end Basic

section Clm

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

omit [FiniteDimensional ℝ F] in
/-- Application of a jointly measurable `CLM`-valued coefficient to a jointly measurable field. -/
theorem clm_apply {A : ℝ → Vec 2 → (E →L[ℝ] F)} {Ψ : ℝ → Vec 2 → E}
    (hA : JointlyMeas t₀ t₁ A) (hΨ : JointlyMeas t₀ t₁ Ψ) :
    JointlyMeas t₀ t₁ fun s x => A s x (Ψ s x) := by
  unfold JointlyMeas at *
  have hc : Continuous fun p : (E →L[ℝ] F) × E => p.1 p.2 :=
    continuous_fst.clm_apply continuous_snd
  exact hc.measurable.comp (hA.prodMk hΨ)

end Clm

section Adjoint

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]

/-- The adjoint of a jointly measurable `CLM`-valued coefficient. -/
theorem adjoint {A : ℝ → Vec 2 → (E →L[ℝ] F)} (hA : JointlyMeas t₀ t₁ A) :
    JointlyMeas t₀ t₁ fun s x => (A s x).adjoint := by
  unfold JointlyMeas at *
  exact (ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)).continuous.measurable.comp hA

end Adjoint

section Deriv

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F]
  [BorelSpace F] [SecondCountableTopology F]

/-- Directional derivative of a jointly measurable family of differentiable fields. -/
theorem fderiv_apply {Ψ : ℝ → Vec 2 → F} (hΨ : JointlyMeas t₀ t₁ Ψ)
    (hd : ∀ s ∈ Set.Icc t₀ t₁, Differentiable ℝ (Ψ s)) (v : Vec 2) :
    JointlyMeas t₀ t₁ fun s x => fderiv ℝ (Ψ s) x v := by
  unfold JointlyMeas at *
  refine measurable_of_tendsto_metrizable
    (f := fun (n : ℕ) (q : Set.Icc t₀ t₁ × Vec 2) =>
      (((n : ℝ) + 1)⁻¹)⁻¹ • (Ψ q.1 (q.2 + ((n : ℝ) + 1)⁻¹ • v) - Ψ q.1 q.2)) (fun n => ?_) ?_
  · have hm : Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => (q.1, q.2 + ((n : ℝ) + 1)⁻¹ • v) :=
      measurable_fst.prodMk (measurable_snd.add_const _)
    exact ((hΨ.comp hm).sub hΨ).const_smul _
  · refine tendsto_pi_nhds.2 fun q => ?_
    have hq := (hd q.1 q.1.2) q.2
    have h1 : HasDerivAt (fun r : ℝ => q.2 + r • v) v 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const v).const_add q.2
    have h2 : HasDerivAt (fun r : ℝ => Ψ q.1 (q.2 + r • v)) (fderiv ℝ (Ψ q.1) q.2 v) 0 := by
      exact hq.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) h1 (by simp)
    have h3 := h2.tendsto_slope_zero
    have h4 : Tendsto (fun n : ℕ => ((n : ℝ) + 1)⁻¹) atTop (𝓝[≠] 0) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, Eventually.of_forall fun n => ?_⟩
      · exact tendsto_inv_atTop_zero.comp
          (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
      · simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        positivity
    refine (h3.comp h4).congr fun n => ?_
    simp

theorem fderiv_basis {Ψ : ℝ → Vec 2 → F} (hΨ : JointlyMeas t₀ t₁ Ψ)
    (hd : ∀ s ∈ Set.Icc t₀ t₁, Differentiable ℝ (Ψ s)) (i : Fin 2) :
    JointlyMeas t₀ t₁ fun s x => fderiv ℝ (Ψ s) x (basisVec i) :=
  fderiv_apply hΨ hd _

end Deriv

end JointlyMeas

/-- Bridge: a jointly measurable field is a.e. strongly measurable for the product of the
restricted window measure and the restricted cell measure. -/
theorem JointlyMeas.aestronglyMeasurable_prod {F : Type*} [NormedAddCommGroup F]
    [MeasurableSpace F] [BorelSpace F] [SecondCountableTopology F] {t₀ t₁ : ℝ} (h : t₀ ≤ t₁)
    {Ψ : ℝ → Vec 2 → F} (hΨ : JointlyMeas t₀ t₁ Ψ) :
    AEStronglyMeasurable (fun p : ℝ × Vec 2 => Ψ p.1 p.2)
      ((volume.restrict (Set.Icc t₀ t₁)).prod (volume.restrict AVenhance.unitCube)) := by
  have hm : Measurable fun p : ℝ × Vec 2 => ((Set.projIcc t₀ t₁ h p.1, p.2) :
      Set.Icc t₀ t₁ × Vec 2) :=
    ((continuous_projIcc (h := h)).measurable.comp measurable_fst).prodMk measurable_snd
  refine (hΨ.comp hm).aestronglyMeasurable.congr ?_
  have hae : ∀ᵐ p ∂((volume.restrict (Set.Icc t₀ t₁)).prod
      (volume.restrict AVenhance.unitCube)), p.1 ∈ Set.Icc t₀ t₁ :=
    Measure.quasiMeasurePreserving_fst.ae (ae_restrict_mem measurableSet_Icc)
  filter_upwards [hae] with p hp
  simp [Function.comp, Set.projIcc_of_mem h hp]

/-- The covariance matrix is continuous on the window for a bounded measurable `Jm`. -/
theorem continuousOn_covarianceMatrix {t₀ t₁ : ℝ} (h : t₀ ≤ t₁) (B : ℝ)
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} (hJ : ∀ i j, Measurable fun t => Jm t i j)
    {M : ℝ} (hM : ∀ t ∈ Set.Icc t₀ t₁, ∀ i j, |Jm t i j| ≤ M) :
    ContinuousOn (fun s => covarianceMatrix Jm B t₀ s) (Set.Icc t₀ t₁) := by
  refine continuousOn_pi.2 fun i => continuousOn_pi.2 fun j => ?_
  unfold covarianceMatrix
  simp only [Matrix.of_apply]
  have hint : IntervalIntegrable (fun s => Jm s i j - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j)
      volume t₀ t₁ := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le h]
    refine Measure.integrableOn_of_bounded (M := M + |B * (1 : Matrix (Fin 2) (Fin 2) ℝ) i j|)
      (by simp) ((hJ i j).sub measurable_const).aestronglyMeasurable ?_
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
    rw [Real.norm_eq_abs]
    exact (abs_sub _ _).trans (by linarith [hM t ht i j])
  have := intervalIntegral.continuousOn_primitive_interval' hint
    (a := t₀) (by simp [h])
  rwa [Set.uIcc_of_le h] at this

end AVRegularity.CycleComparison.Coarse
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Weak measurability criterion for `TorusHk`-valued maps.

A map `G : α → TorusHk K F` into the periodic Sobolev space is a.e. strongly measurable as soon
as every pairing `a ↦ cellInner (tval (G a)) ψ` with a smooth `Z²`-periodic test field `ψ` is a.e.
measurable. The value map `TorusHk K F → L²(cell; F)` is continuous and injective
(`TorusHk.ext_value`), smooth periodic fields are dense in `L²`, and a countable family of
pairings separates points, so Lusin–Souslin applies. -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- The value class of a periodic Sobolev field in `L²(cell; F)`. -/
def tvalL2 {K : ℕ} (U : TorusHk K F) : Lp F 2 (volume.restrict AVenhance.unitCube) :=
  U.val (valueIndex2 K)

theorem continuous_tvalL2 {K : ℕ} : Continuous (tvalL2 (K := K) (F := F)) :=
  (PiLp.continuous_apply 2 _ (valueIndex2 K)).comp continuous_subtype_val

theorem tvalL2_ae {K : ℕ} (U : TorusHk K F) :
    tval U =ᵐ[volume.restrict AVenhance.unitCube] ⇑(tvalL2 U) :=
  periodicJetRepresentative_ae U.val (valueIndex2 K)

theorem tvalL2_injective {K : ℕ} : Function.Injective (tvalL2 (K := K) (F := F)) :=
  fun _ _ h => TorusHk.ext_value h

theorem inner_tvalL2 {K : ℕ} (U : TorusHk K F) (ψ : Lp F 2 (volume.restrict AVenhance.unitCube))
    (ψ' : Vec 2 → F) (h : ψ =ᵐ[volume.restrict AVenhance.unitCube] ψ') :
    inner ℝ (tvalL2 U) ψ = cellInner (tval U) ψ' := by
  rw [L2.inner_def, cellInner]
  apply integral_congr_ae
  filter_upwards [tvalL2_ae U, h] with x h1 h2
  rw [h1, h2]

/-- Weak measurability: a `TorusHk`-valued map whose pairings with smooth periodic test fields are
a.e. measurable is a.e. strongly measurable. -/
theorem aestronglyMeasurable_of_weak {α : Type*} [MeasurableSpace α] {μ : Measure α} {K : ℕ}
    {G : α → TorusHk K F}
    (h : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      AEStronglyMeasurable (fun a => cellInner (tval (G a)) ψ) μ) :
    AEStronglyMeasurable G μ := by
  set S := {f : Lp F 2 (volume.restrict AVenhance.unitCube) |
      ∃ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ ∧ AVenhance.IsZ2Periodic ψ ∧
        f =ᵐ[volume.restrict AVenhance.unitCube] ψ} with hS
  have hdense : Dense S := dense_smooth_periodic_lp
  have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
  have : SecondCountableTopology (Lp F 2 (volume.restrict AVenhance.unitCube)) := inferInstance
  obtain ⟨t, hts, htc, hSt⟩ :=
    (TopologicalSpace.IsSeparable.of_separableSpace S).exists_countable_dense_subset
  have h0 : (0 : Lp F 2 (volume.restrict AVenhance.unitCube)) ∈ S :=
    ⟨0, contDiff_const, fun _ _ => rfl, Lp.coeFn_zero _ _ _⟩
  have htne : t.Nonempty := by
    by_contra hne
    rw [Set.not_nonempty_iff_eq_empty] at hne
    have := hSt h0
    simp [hne] at this
  obtain ⟨d, hd⟩ := htc.exists_eq_range htne
  have hdS : ∀ n, d n ∈ S := fun n => hts (by rw [hd]; exact ⟨n, rfl⟩)
  have hdd : Dense (Set.range d) := by
    rw [Dense, ← hd] at *
    intro x
    exact closure_minimal hSt isClosed_closure (hdense x)
  have : PolishSpace (TorusHk K F) := (ClosedSubmodule.isClosed _).polishSpace
  refine aestronglyMeasurable_of_separating_coords (fun n U => inner ℝ (tvalL2 U) (d n))
    (fun n => continuous_tvalL2.inner continuous_const) ?_ G ?_
  · intro x y hxy
    apply tvalL2_injective
    have hc : Continuous (fun w : Lp F 2 (volume.restrict AVenhance.unitCube) =>
        inner ℝ (tvalL2 x - tvalL2 y) w) := continuous_const.inner continuous_id
    have hz : (fun w : Lp F 2 (volume.restrict AVenhance.unitCube) =>
        inner ℝ (tvalL2 x - tvalL2 y) w) = fun _ => 0 := by
      refine hc.ext_on hdd continuous_const ?_
      rintro _ ⟨n, rfl⟩
      simp [inner_sub_left, hxy n]
    have := congrFun hz (tvalL2 x - tvalL2 y)
    simpa [inner_self_eq_zero, sub_eq_zero] using this
  · intro n
    obtain ⟨ψ, hψs, hψp, hψe⟩ := hdS n
    refine (h ψ hψs hψp).aemeasurable.congr (Eventually.of_forall fun a => ?_)
    exact (inner_tvalL2 (G a) (d n) ψ hψe).symm

/-- A bounded a.e. strongly measurable map on a finite-measure set is in `L²`. -/
theorem memLp_two_of_bound {X : Type*} [NormedAddCommGroup X] {I : Set ℝ}
    (hI : MeasurableSet I) (hfin : volume I < ∞) {G : ℝ → X} {M : ℝ}
    (hG : AEStronglyMeasurable G (volume.restrict I)) (hb : ∀ s ∈ I, ‖G s‖ ≤ M) :
    MemLp G 2 (volume.restrict I) := by
  have : IsFiniteMeasure (volume.restrict I) := ⟨by simpa using hfin⟩
  exact MemLp.of_bound hG M (ae_restrict_of_forall_mem hI hb)

end AVRegularity.CycleComparison.Coarse
end
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev Filter Topology
open scoped ENNReal
namespace AVRegularity.CycleComparison.Coarse

/-! Measurability of adjoint pairings in time.

If `U : ℝ → TorusHk K' E` is continuous on a measurable set `I` and `T s` acts on test fields
through a jointly measurable bounded kernel, then `s ↦ cellInner (tval (U s)) (T s ψ)` is a.e.
strongly measurable on `I`. Combined with `aestronglyMeasurable_of_weak`, a family `G s` whose
pairings are given by this formula is a.e. strongly measurable. -/

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [MeasurableSpace E] [BorelSpace E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F] [FiniteDimensional ℝ F]
  [MeasurableSpace F] [BorelSpace F]

/-- Pairing of a continuous `TorusHk`-valued curve with a jointly measurable field whose slices
are in `L²` of the cell. -/
theorem aestronglyMeasurable_cellInner_of_memLp {K : ℕ} {I : Set ℝ}
    (hI : MeasurableSet I) {U : ℝ → TorusHk K E} (hU : ContinuousOn U I)
    {W : ℝ → Vec 2 → E}
    (hW : AEStronglyMeasurable (fun p : ℝ × Vec 2 => W p.1 p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hL : ∀ s ∈ I, MemLp (W s) 2 (volume.restrict AVenhance.unitCube)) :
    AEStronglyMeasurable (fun s => cellInner (tval (U s)) (W s)) (volume.restrict I) := by
  classical
  set μc : Measure (Vec 2) := volume.restrict AVenhance.unitCube with hμc
  -- classes of `W s`
  have hmem : ∀ᵐ s ∂(volume.restrict I), MemLp (W s) 2 μc := by
    filter_upwards [ae_restrict_mem hI] with s hsI
    exact hL s hsI
  let w : ℝ → Lp E 2 μc := fun s =>
    if h : MemLp (W s) 2 μc then h.toLp (W s) else 0
  have hwae : ∀ᵐ s ∂(volume.restrict I), (w s : Vec 2 → E) =ᵐ[μc] W s := by
    filter_upwards [hmem] with s hs
    simp only [w, hs, dite_true]
    exact hs.coeFn_toLp
  have hwmeas : AEStronglyMeasurable w (volume.restrict I) := by
    have : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by simp⟩
    obtain ⟨d, hd⟩ := TopologicalSpace.exists_dense_seq (Lp E 2 μc)
    refine aestronglyMeasurable_of_separating_coords (fun n h => inner ℝ h (d n))
      (fun n => continuous_id.inner continuous_const) ?_ w ?_
    · intro x y hxy
      have hc : Continuous (fun v : Lp E 2 μc => inner ℝ (x - y) v) :=
        continuous_const.inner continuous_id
      have hz : (fun v : Lp E 2 μc => inner ℝ (x - y) v) = fun _ => 0 := by
        refine hc.ext_on hd continuous_const ?_
        rintro _ ⟨n, rfl⟩
        simp [inner_sub_left, hxy n]
      have := congrFun hz (x - y)
      simpa [inner_self_eq_zero, sub_eq_zero] using this
    · intro n
      have hprod : AEStronglyMeasurable (fun p : ℝ × Vec 2 => inner ℝ (W p.1 p.2) (d n p.2))
          ((volume.restrict I).prod μc) :=
        hW.inner ((Lp.stronglyMeasurable (d n)).aestronglyMeasurable.comp_quasiMeasurePreserving
          (Measure.quasiMeasurePreserving_snd))
      have hint := hprod.integral_prod_right'
      refine hint.aemeasurable.congr ?_
      filter_upwards [hwae] with s hs
      rw [L2.inner_def]
      apply integral_congr_ae
      filter_upwards [hs] with x hx
      rw [hx]
  have hVU : ContinuousOn (fun s => tvalL2 (U s)) I := continuous_tvalL2.comp_continuousOn hU
  refine ((hVU.aestronglyMeasurable hI).inner hwmeas).congr ?_
  filter_upwards [hwae] with s hs
  exact inner_tvalL2 (U s) (w s) (W s) hs

/-- A continuous field is in `L²` of the cell. -/
theorem memLp_two_cell_of_continuous {E : Type*} [NormedAddCommGroup E] {W : Vec 2 → E}
    (hW : Continuous W) : MemLp W 2 (volume.restrict AVenhance.unitCube) := by
  have hc : IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc (0 : ℝ) 1)) :=
    isCompact_univ_pi (fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn hW.continuousOn
  refine MemLp.of_bound hW.aestronglyMeasurable C ?_
  exact ae_restrict_of_forall_mem measurableSet_unitCube fun x hx =>
    hC x (fun i _ => Set.Ioo_subset_Icc_self (hx i (Set.mem_univ i)))

/-- Pairing of a continuous `TorusHk`-valued curve with a jointly measurable field whose slices
are continuous (for `s ∈ I`). -/
theorem aestronglyMeasurable_cellInner_of_jointly_measurable {K : ℕ} {I : Set ℝ}
    (hI : MeasurableSet I) {U : ℝ → TorusHk K E} (hU : ContinuousOn U I)
    {W : ℝ → Vec 2 → E}
    (hW : AEStronglyMeasurable (fun p : ℝ × Vec 2 => W p.1 p.2)
      ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hc : ∀ s ∈ I, Continuous (W s)) :
    AEStronglyMeasurable (fun s => cellInner (tval (U s)) (W s)) (volume.restrict I) :=
  aestronglyMeasurable_cellInner_of_memLp hI hU hW fun s hs => memLp_two_cell_of_continuous (hc s hs)

/-- Application form: a family `G s` whose pairings with smooth periodic test fields are
`cellInner (tval (U s)) (T s ψ)`, for `U` continuous on `I` and `T s ψ` a jointly measurable family
of continuous fields, is a.e. strongly measurable on `I`. -/
theorem aestronglyMeasurable_of_adjoint_pairing {K K' : ℕ} {I : Set ℝ} (hI : MeasurableSet I)
    {U : ℝ → TorusHk K' E} (hU : ContinuousOn U I) {G : ℝ → TorusHk K F}
    {T : ℝ → (Vec 2 → F) → (Vec 2 → E)}
    (hT : ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      AEStronglyMeasurable (fun p : ℝ × Vec 2 => T p.1 ψ p.2)
        ((volume.restrict I).prod (volume.restrict AVenhance.unitCube)))
    (hTc : ∀ s ∈ I, ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      Continuous (T s ψ))
    (hG : ∀ s ∈ I, ∀ ψ : Vec 2 → F, ContDiff ℝ (⊤ : ℕ∞) ψ → AVenhance.IsZ2Periodic ψ →
      cellInner (tval (G s)) ψ = cellInner (tval (U s)) (T s ψ)) :
    AEStronglyMeasurable G (volume.restrict I) := by
  refine aestronglyMeasurable_of_weak fun ψ hs hp => ?_
  exact (aestronglyMeasurable_cellInner_of_jointly_measurable hI hU (W := fun s => T s ψ)
    (hT ψ hs hp) (fun s hsI => hTc s hsI ψ hs hp)).congr
    (ae_restrict_of_forall_mem hI fun s hsI => (hG s hsI ψ hs hp).symm)

end AVRegularity.CycleComparison.Coarse
end
end
