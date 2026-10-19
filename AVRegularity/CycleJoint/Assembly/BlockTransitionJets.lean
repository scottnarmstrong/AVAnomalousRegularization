-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleJoint.Assembly.BlockLetterPropertiesOfIngredients
import AVRegularity.CycleJoint.OriginalFamilyNaturalRemainderDescendingIdentity

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! Finite-order, Schur and graph properties of the literal block letters. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- A source edge retains one of the family's identities. -/
theorem mem_blockSourceEdges (F : ChartedFamily ι h D P Ctx) (pieces : Finset P)
    (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E timeScale : ℝ)
    (v u : ι) (d : Finset.Icc 2 D) (c : Constituent d.val (h u) (h v))
    (hc : c ∈ blockSourceEdges F pieces actual hφ W l σ yc e E timeScale v u d) :
    ∃ γ : F.Γ v u, ∃ hd : d.val ≤ (F.identity v u γ).maxOrder,
      c = sourceConstituent F pieces actual hφ v u γ d.val hd W l σ yc e E timeScale := by
  obtain ⟨γ, _, hγ⟩ := List.mem_filterMap.mp hc
  split_ifs at hγ with hd
  · exact ⟨γ, hd, (Option.some.inj hγ).symm⟩

/-- Empty identity entries stay empty after the block readout. -/
theorem blockSourceEdges_eq_nil (F : ChartedFamily ι h D P Ctx) (pieces : Finset P)
    (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E timeScale : ℝ)
    (v u : ι) (hi : IsEmpty (F.Γ v u)) (d : Finset.Icc 2 D) :
    blockSourceEdges F pieces actual hφ W l σ yc e E timeScale v u d = [] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro c hc
  obtain ⟨γ, _, _⟩ := mem_blockSourceEdges F pieces actual hφ W l σ yc e E timeScale v u d c hc
  exact hi.false γ

/-- The source letter inherits the same finite graph depth and Schur sums. -/
theorem blockSourceLetter_skeleton [Fintype ι] (F : ChartedFamily ι h D P Ctx) (pieces : Finset P)
    (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (W : Set ℝ) (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E timeScale : ℝ)
    (Ks H : ℕ) (θ C : ℝ) (B : ι → ι → ℝ) (hD : 2 ≤ D)
    (hC : 0 ≤ C) (hθ : 0 ≤ θ) (hB : ∀ v u, 0 ≤ B v u)
    (hrow : ∀ v, ∑ u, B v u ≤ θ) (hcol : ∀ u, ∑ v, B v u ≤ θ)
    (hdepth : F.HasDepthAtMost H) :
    BlockLetterSkeleton (blockSourceLetter F pieces actual hφ W l σ yc e E timeScale
      Ks (C * θ) (fun v u => C * B v u)) H := by
  refine ⟨hD, le_rfl, ?_, mul_nonneg hC hθ, ?_, ?_, ?_, ?_⟩
  · intro v u d hd
    exact False.elim (not_lt_of_ge (Finset.mem_Icc.mp d.property).2 hd)
  · intro v u
    exact mul_nonneg hC (hB v u)
  · intro v
    change ∑ u, C * B v u ≤ C * θ
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hrow v) hC
  · intro u
    change ∑ v, C * B v u ≤ C * θ
    rw [← Finset.mul_sum]
    exact mul_le_mul_of_nonneg_left (hcol u) hC
  · intro _ p
    obtain ⟨k, hk⟩ := hdepth p
    exact ⟨k, fun d => blockSourceEdges_eq_nil F pieces actual hφ W l σ yc e E timeScale _ _ hk d⟩

/-- The diagonal positive metric letter has the claimed order and Schur sums. -/
theorem blockMetricLetter_skeleton [Fintype ι] [DecidableEq ι] (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (X₀ : Vec 2) (δ : ℝ) (Ks H : ℕ) (C g : ℝ) (hD : 2 ≤ D) (hC : 0 ≤ C) (hg : 0 ≤ g) :
    BlockLetterSkeleton (blockMetricLetter (D := D) (h := h) G X₀ δ Ks (C * g)
      (fun v u => if v = u then C * g else 0)) H := by
  refine ⟨le_rfl, hD, ?_, mul_nonneg hC hg, ?_, ?_, ?_, ?_⟩
  · intro v u d hd
    have hn : d.val ≠ 2 := ne_of_gt hd
    simp only [blockMetricLetter, metricEdges, hn, and_false, dite_false]
  · intro v u
    change 0 ≤ if v = u then C * g else 0
    split_ifs
    · exact mul_nonneg hC hg
    · exact le_rfl
  · intro v
    change (∑ u, if v = u then C * g else 0) ≤ C * g
    simp
  · intro u
    change (∑ v, if v = u then C * g else 0) ≤ C * g
    simp
  · intro hfalse
    cases hfalse

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! Fast-variable invariances and time measurability of block coefficients. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- Transported fields are evaluated at a fixed slow point when only time varies. -/
theorem blockLetterCoefficient_measurable (F : ChartedFamily ι h D P Ctx)
    (hmeas : F.IsTimeMeasurable) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (p : P) (c : Ctx p) (v u : ι) (γ : F.Γ v u) (l : ℤ) (σ : ℝ)
    (yc : Vec 2) (e E timeScale : ℝ) (d : ℕ) (I : DerivativeWord2 (d - 1)) (X z : Vec 2) :
    Measurable (fun t => blockLetterCoefficient F hφ p c v u γ l σ yc e E timeScale d I t X z) := by
  have hclock : Measurable (fun t : ℝ => timeScale * t) := measurable_const.mul measurable_id
  unfold blockLetterCoefficient
  split_ifs
  · exact (hmeas p c v u γ d I X (z + e⁻¹ • yc)).comp hclock
  · apply Measurable.of_eval
    intro a
    unfold transportedCoeff
    apply Finset.measurable_sum
    intro d' hd'
    apply Finset.measurable_sum
    intro I' hI'
    apply Finset.measurable_sum
    intro k hk
    have hm := (hmeas p c v u γ d' I'
      (E⁻¹ • streamFlow φ hφ (F.piece p).anchor
        (yc + e • ((e / E)⁻¹ • (X - E⁻¹ • yc))) σ) 0).comp hclock
    exact (measurable_const.mul ((measurable_pi_apply k).comp hm)).mul_const _

/-- A finite weighted block sum is measurable at every slow and fast point. -/
theorem sourceConstituent_measurable (F : ChartedFamily ι h D P Ctx)
    (hmeas : F.IsTimeMeasurable) (hwmeas : ∀ p, Measurable (F.weight p))
    (pieces : Finset P) (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (hd : d ≤ (F.identity v u γ).maxOrder)
    (W : Set ℝ) (hW : MeasurableSet W) (l : ℤ) (σ : ℝ) (yc : Vec 2)
    (e E timeScale : ℝ) (I : DerivativeWord2 (d - 1)) (X z : Vec 2) :
    Measurable (fun t => (sourceConstituent F pieces actual hφ v u γ d hd W l σ yc e E timeScale).coeff
      I t X z) := by
  apply Finset.measurable_sum
  intro p hp
  exact (((hwmeas p).indicator hW).comp (measurable_const.mul measurable_id)).smul
    (blockLetterCoefficient_measurable F hmeas hφ p (actual p) v u γ l σ yc e E timeScale d I X z)

/-- The source readout preserves fast independence on the physical preimage of quiet times. -/
theorem sourceConstituent_fastIndependent (F : ChartedFamily ι h D P Ctx)
    (pieces : Finset P) (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (hd : d ≤ (F.identity v u γ).maxOrder)
    (W S Q : Set ℝ) (hF : F.IsFastIndependentOn (S ∩ W))
    (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E timeScale : ℝ)
    (hQ : ∀ t ∈ Q, timeScale * t ∈ S) (I : DerivativeWord2 (d - 1)) :
    IsFastIndependentOn Q
      ((sourceConstituent F pieces actual hφ v u γ d hd W l σ yc e E timeScale).coeff I) := by
  intro t ht X z z'
  change ∑ p ∈ pieces, _ = ∑ p ∈ pieces, _
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hW : timeScale * t ∈ W
  · rw [Set.indicator_of_mem hW]
    by_cases hout : timeScale * t ∈ (F.piece p).output
    · unfold blockLetterCoefficient
      split_ifs
      · rw [hF p (actual p) v u γ d I _ ⟨⟨hQ t ht, hW⟩, hout⟩]
      · rfl
    · simp only [F.weight_zero p _ hout, zero_smul]
  · simp only [Set.indicator_of_notMem hW, zero_smul]

/-- The aligned part commutes with fast translations; every other part is fast independent. -/
theorem sourceConstituent_transverse (F : ChartedFamily ι h D P Ctx)
    (pieces : Finset P) (actual : ∀ p, Ctx p) {φ : ℝ → Vec 2 → ℝ} (hφ : IsAdmissibleStream φ)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (hd : d ≤ (F.identity v u γ).maxOrder)
    (W T Q : Set ℝ) (o : Fin 2)
    (hF : ∀ p I, IsTransverseOn o (T ∩ ((F.piece p).output ∩ W)) (F.flux p (actual p) v u γ d I))
    (l : ℤ) (σ : ℝ) (yc : Vec 2) (e E timeScale : ℝ)
    (hQ : ∀ t ∈ Q, timeScale * t ∈ T) (I : DerivativeWord2 (d - 1)) :
    IsTransverseOn o Q
      ((sourceConstituent F pieces actual hφ v u γ d hd W l σ yc e E timeScale).coeff I) := by
  intro t ht X z s
  change ∑ p ∈ pieces, _ = ∑ p ∈ pieces, _
  apply Finset.sum_congr rfl
  intro p hp
  by_cases hW : timeScale * t ∈ W
  · rw [Set.indicator_of_mem hW]
    by_cases hout : timeScale * t ∈ (F.piece p).output
    · unfold blockLetterCoefficient
      split_ifs
      · rw [show z + s • basisVec o + e⁻¹ • yc = (z + e⁻¹ • yc) + s • basisVec o by abel]
        rw [hF p I _ ⟨hQ t ht, hout, hW⟩ X (z + e⁻¹ • yc) s]
      · rfl
    · simp only [F.weight_zero p _ hout, zero_smul]
  · simp only [Set.indicator_of_notMem hW, zero_smul]

/-- Every metric edge coefficient is independent of its fast argument. -/
theorem metricEdges_fastIndependent [DecidableEq ι]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (X₀ : Vec 2) (δ : ℝ)
    (v u : ι) (d : Finset.Icc 2 D) (c : Constituent d.val (h u) (h v))
    (hc : c ∈ metricEdges G X₀ δ v u d) (I : DerivativeWord2 (d.val - 1)) :
    ∀ t X z z', c.coeff I t X z = c.coeff I t X z' := by
  rcases d with ⟨d, hdD⟩
  by_cases hvu : v = u
  · subst u
    by_cases hd : d = 2
    · subst d
      simp only [metricEdges, and_self, dite_true] at hc
      change c ∈ [metricConstituent (h v) G X₀ δ] at hc
      have he := List.mem_singleton.mp hc
      subst c
      intros
      rfl
    · simp only [metricEdges, hd, and_false, dite_false, List.not_mem_nil] at hc
  · simp only [metricEdges, hvu, false_and, dite_false, List.not_mem_nil] at hc

/-- Time measurability of metric entries passes to every constituent. -/
theorem metricEdges_measurable [DecidableEq ι]
    (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ)
    (hG : ∀ X i j, Measurable fun t => G t X i j) (X₀ : Vec 2) (δ : ℝ)
    (v u : ι) (d : Finset.Icc 2 D) (c : Constituent d.val (h u) (h v))
    (hc : c ∈ metricEdges G X₀ δ v u d) (I : DerivativeWord2 (d.val - 1)) (X z : Vec 2) :
    Measurable (fun t => c.coeff I t X z) := by
  rcases d with ⟨d, hdD⟩
  by_cases hvu : v = u
  · subst u
    by_cases hd : d = 2
    · subst d
      simp only [metricEdges, and_self, dite_true] at hc
      change c ∈ [metricConstituent (h v) G X₀ δ] at hc
      have he := List.mem_singleton.mp hc
      subst c
      apply Measurable.of_eval
      intro k
      exact (hG (δ⁻¹ • (X - X₀)) k (I ⟨0, Nat.one_pos⟩)).fun_sub
        (hG 0 k (I ⟨0, Nat.one_pos⟩))
    · simp only [metricEdges, hd, and_false, dite_false, List.not_mem_nil] at hc
  · simp only [metricEdges, hvu, false_and, dite_false, List.not_mem_nil] at hc

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVRegularity.CycleWords
namespace AVRegularity.CycleJointProofs.Assembly

/-! Original molecular prices for block remainders: the finite slow-order sum
is taken before the mass Schur estimate, without a piece or identity count. -/

variable {ι : Type*} {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- One price controls both kinds of block remainder on each original identity. -/
def blockOriginalIdentityPrice (F : ChartedFamily ι h D P Ctx) (K : ι → ℕ)
    (Ks Kmax : ℕ) (dom : F.Domain) (ν e E ρ Cjet ζ : ℝ) (v u : ι) (γ : F.Γ v u) : ℝ :=
  Real.sqrt (multiplicationDensityBudget (K v)) * Cjet * ζ ^ (Ks + 1) *
    (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I (Ks + 1)) *
          ‖(F.identity v u γ).map‖

theorem blockOriginalIdentityPrice_nonneg
    {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ}
    {dom : F.Domain} {ν e E ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}
    (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (Ks : ℕ) (Cjet ζ : ℝ) (hC : 0 ≤ Cjet) (hζ : 0 ≤ ζ) (v u : ι) (γ : F.Γ v u) :
    0 ≤ blockOriginalIdentityPrice F K Ks Kmax dom ν e E ρ Cjet ζ v u γ := by
  have hn (d : ℕ) (I : DerivativeWord2 (d - 1)) :
      0 ≤ blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I (Ks + 1) := by
    unfold blockSlowJetNumerator
    apply Finset.sum_nonneg
    intro j _
    exact mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg data.slow_pos.le _))
      (molecularRealPrice_nonneg ν ρ data.nu_pos.le data.radius_pos.le _ _ _)
  unfold blockOriginalIdentityPrice
  exact mul_nonneg (mul_nonneg (by positivity)
    (Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun I _ =>
      Finset.sum_nonneg (fun _ _ => hn d I))))) (norm_nonneg _)

/-- Exchange the finite slow-order sum with all original constituent indices. -/
theorem blockEdge_original_price_sum_comm (F : ChartedFamily ι h D P Ctx)
    (v u : ι) (L : ℕ) (A : ℝ)
    (f : ∀ _γ : F.Γ v u, ∀ d : ℕ, DerivativeWord2 (d - 1) → ℕ → ℝ) :
    (∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          ∑ j ∈ Finset.range (L + 1), A * f γ d I j) =
    2 * A * ∑ j ∈ Finset.range (L + 1), ∑ γ : F.Γ v u,
      ‖(F.identity v u γ).map‖ *
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), f γ d I j := by
  classical
  have hi γ d I : (∑ _i : Fin 2, ∑ j ∈ Finset.range (L + 1), A * f γ d I j) =
      (2 * A) * ∑ j ∈ Finset.range (L + 1), f γ d I j := by
    simp only [Fin.sum_univ_two, ← Finset.mul_sum]
    ring
  have hd (γ : F.Γ v u) (d : ℕ) :
      (∑ I : DerivativeWord2 (d - 1), ∑ j ∈ Finset.range (L + 1), f γ d I j) =
        ∑ j ∈ Finset.range (L + 1), ∑ I : DerivativeWord2 (d - 1), f γ d I j :=
    Finset.sum_comm
  have hg (γ : F.Γ v u) :
      (∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
        ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
          ∑ j ∈ Finset.range (L + 1), A * f γ d I j) =
      (2 * A) * ∑ j ∈ Finset.range (L + 1),
        ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
          ∑ I : DerivativeWord2 (d - 1), f γ d I j := by
    simp_rw [hi, ← Finset.mul_sum, hd]
    congr 1
    exact Finset.sum_comm
  simp_rw [hg]
  calc
    _ = (2 * A) * ∑ γ : F.Γ v u, ∑ j ∈ Finset.range (L + 1),
        ‖(F.identity v u γ).map‖ *
          ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
            ∑ I : DerivativeWord2 (d - 1), f γ d I j := by
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro γ _
      ring_nf
    _ = _ := by congr 1; exact Finset.sum_comm

/-- A constant containing only reserves and the supplied jet constants. -/
def blockRemainderGraphConstant (Ks Kmax : ℕ) (Cjet : ℝ) (Cm : ℕ → ℝ) : ℝ :=
  2 * (∑ n ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget n)) *
    |Cjet| * (Kmax.factorial : ℝ) ^ 2 * ∑ j ∈ Finset.range (Ks + 2), |Cm j|

theorem blockRemainderGraphConstant_nonneg (Ks Kmax : ℕ) (Cjet : ℝ) (Cm : ℕ → ℝ) :
    0 ≤ blockRemainderGraphConstant Ks Kmax Cjet Cm := by
  unfold blockRemainderGraphConstant
  positivity

/-- The slow-order sum is paid by the original pointwise envelope, including order zero. -/
theorem blockOriginalIdentityPrice_sum_envelope_le
    (F : ChartedFamily ι h D P Ctx) (π : ι → ℝ) (K : ι → ℕ) (Ks Kmax : ℕ)
    (hK : ∀ v, K v ≤ Kmax) (dom : F.Domain) (ν e E ρ Cjet ζ : ℝ)
    (hν : 0 < ν) (hE : 0 < E) (hρ : 0 < ρ) (hC : 0 ≤ Cjet) (hζ : 0 ≤ ζ)
    (Cm : ℕ → ℝ) (J : ℕ) (B : ι → ι → ℝ) (hLJ : Ks + 1 ≤ J)
    (henv : IsPointwiseMolecularEnvelope F π K dom ν e E ρ Cm J B)
    (v u : ι) (hB : 0 ≤ B v u) :
    Real.sqrt (π u / π v) *
      (∑ γ : F.Γ v u, blockOriginalIdentityPrice F K Ks Kmax dom ν e E ρ Cjet ζ v u γ) ≤
      ζ ^ (Ks + 1) * blockRemainderGraphConstant Ks Kmax Cjet Cm * B v u := by
  classical
  let f := fun (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) (j : ℕ) =>
    E ^ j * molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I))
  let Sj := fun j => ∑ γ : F.Γ v u, ‖(F.identity v u γ).map‖ *
    ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), f γ d I j
  have hs : (∑ γ : F.Γ v u,
      blockOriginalIdentityPrice F K Ks Kmax dom ν e E ρ Cjet ζ v u γ) =
      (Real.sqrt (multiplicationDensityBudget (K v)) * Cjet * ζ ^ (Ks + 1)) *
        (2 * (Kmax.factorial : ℝ) ^ 2 * ∑ j ∈ Finset.range (Ks + 2), Sj j) := by
    have he := blockEdge_original_price_sum_comm F v u (Ks + 1) ((Kmax.factorial : ℝ) ^ 2) f
    change _ = 2 * (Kmax.factorial : ℝ) ^ 2 * ∑ j ∈ Finset.range (Ks + 2), Sj j at he
    rw [← he, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro γ _
    unfold blockOriginalIdentityPrice blockSlowJetNumerator
    dsimp only [f]
    simp only [mul_assoc]
    ring
  have hj (j : ℕ) (hj : j ∈ Finset.range (Ks + 2)) :
      Real.sqrt (π u / π v) * Sj j ≤ |Cm j| * B v u :=
    pointwiseMolecularRealEnvelope_scaled_sum_le F π K dom ν e E ρ hν hE hρ Cm J B henv
      v u hB j (by have hjs := Finset.mem_range.mp hj; omega)
  have hh := Finset.sum_le_sum (fun j hj' => hj j hj')
  rw [← Finset.mul_sum, ← Finset.sum_mul] at hh
  have hroot : Real.sqrt (multiplicationDensityBudget (K v)) ≤
      ∑ n ∈ Finset.range (Kmax + 1), Real.sqrt (multiplicationDensityBudget n) :=
    Finset.single_le_sum (fun _ _ => Real.sqrt_nonneg _)
      (Finset.mem_range.mpr (by have hv := hK v; omega))
  have hroot' := mul_le_mul_of_nonneg_right hroot
    (by positivity : 0 ≤ Cjet * ζ ^ (Ks + 1) * 2 * (Kmax.factorial : ℝ) ^ 2 *
      (∑ j ∈ Finset.range (Ks + 2), |Cm j|) * B v u)
  rw [hs]
  calc
    _ = (Real.sqrt (multiplicationDensityBudget (K v)) * Cjet * ζ ^ (Ks + 1) *
        2 * (Kmax.factorial : ℝ) ^ 2) * (Real.sqrt (π u / π v) * ∑ j ∈ Finset.range (Ks + 2), Sj j) := by ring
    _ ≤ (Real.sqrt (multiplicationDensityBudget (K v)) * Cjet * ζ ^ (Ks + 1) *
        2 * (Kmax.factorial : ℝ) ^ 2) * ((∑ j ∈ Finset.range (Ks + 2), |Cm j|) * B v u) :=
      mul_le_mul_of_nonneg_left hh (by positivity)
    _ ≤ _ := by
      simpa only [blockRemainderGraphConstant, abs_of_nonneg hC, mul_assoc, mul_left_comm, mul_comm] using hroot'

variable {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ}
  {dom : F.Domain} {ν e E ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}

/-- Every slow-order price, in particular the original top Taylor remainder,
is included in the finite numerator. -/
theorem blockSlowJetNumerator_term_le
    (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (v u : ι) (γ : F.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (j L : ℕ) (hj : j ≤ L) :
    (Kmax.factorial : ℝ) ^ 2 * E ^ j *
      molecularRealPrice ν ρ (K v) (d - 2)
        (pointwiseMolecularJet ρ e (K v) j (fun x : F.Index => dom x.1 x.2)
          (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)) ≤
      blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I L := by
  unfold blockSlowJetNumerator
  exact Finset.single_le_sum (f := fun a => (Kmax.factorial : ℝ) ^ 2 * E ^ a *
    molecularRealPrice ν ρ (K v) (d - 2)
      (pointwiseMolecularJet ρ e (K v) a (fun x : F.Index => dom x.1 x.2)
        (fun x => F.dimFlux ν e E x.1 x.2 v u γ d I)))
    (fun a _ => mul_nonneg (mul_nonneg (sq_nonneg _) (pow_nonneg data.slow_pos.le a))
      (molecularRealPrice_nonneg ν ρ data.nu_pos.le data.radius_pos.le _ _ _))
    (Finset.mem_range.mpr (by omega : j < L + 1))

/-- The old natural remainder is bounded by the new common identity price. -/
theorem blockEdge_natural_price_le
    (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (Ks : ℕ) (Cnat Cjet ζ : ℝ) (hCnat : 0 ≤ Cnat) (hC : Cnat ≤ Cjet) (hζ : 0 ≤ ζ)
    (v u : ι) (γ : F.Γ v u) :
    pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom ν e E ρ Cnat ζ v u γ ≤
      blockOriginalIdentityPrice F K Ks Kmax dom ν e E ρ Cjet ζ v u γ := by
  classical
  have hs := Finset.sum_le_sum (s := Finset.Icc 2 (F.identity v u γ).maxOrder)
    (fun d _ => Finset.sum_le_sum (s := Finset.univ) (fun I _ =>
      Finset.sum_le_sum (s := Finset.univ) (fun _i : Fin 2 => fun _ =>
        blockSlowJetNumerator_term_le data v u γ d I (Ks + 1) (Ks + 1) le_rfl)))
  simp only [← Finset.mul_sum, mul_assoc] at hs
  let S := ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I (Ks + 1)
  have hS : 0 ≤ S := Finset.sum_nonneg (fun d _ => Finset.sum_nonneg (fun I _ =>
    Finset.sum_nonneg (fun _ _ => blockSlowJetNumerator_nonneg data v u γ d I (Ks + 1))))
  have hp := mul_le_mul_of_nonneg_left hs
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg (multiplicationDensityBudget (K v))) hCnat) (pow_nonneg hζ (Ks + 1)))
  have hc := mul_le_mul_of_nonneg_right hC (mul_nonneg (pow_nonneg hζ (Ks + 1)) hS)
  have hc' := mul_le_mul_of_nonneg_left hc (Real.sqrt_nonneg (multiplicationDensityBudget (K v)))
  have hh := hp.trans (by simpa only [S, mul_assoc] using hc')
  have hfinal := mul_le_mul_of_nonneg_right hh (norm_nonneg (F.identity v u γ).map)
  convert hfinal using 1
  · unfold pointwiseOriginalIdentityRemainderPrice
    simp only [← Finset.mul_sum]
    ring
  · unfold blockOriginalIdentityPrice
    ring

/-- Reassociate a scalar price comparison in an abstract real context. -/
theorem blockEdge_price_reassociate (s gain cmap A C ns na : ℝ)
    (hs : 0 ≤ s * gain * cmap) (h : A * ns ≤ C * na) :
    (s * gain * cmap) * (A * ns) ≤ s * C * gain * na * cmap :=
  (mul_le_mul_of_nonneg_left h hs).trans_eq (by ring)

/-- The transported remainder density price is controlled by the same original
identity price, with only the fixed native-coordinate count. -/
theorem blockEdge_transported_density_price_le
    (data : BlockMolecularInputs F π K Kmax dom ν e E ρ Cm J B)
    (Ks N M Jchart : ℕ) (Cchart : ℕ → ℝ) (Cjet ζ : ℝ) (hζ : 0 ≤ ζ)
    (hC : 2 ^ (D + 1) * 2 ^ Kmax * blockEdgeTransportPrice N D M Jchart Cchart *
      blockEdgeSamplingPrice M Jchart Cchart ≤ Cjet)
    (v u : ι) (γ : F.Γ v u) (r : ℕ) (hr : 1 ≤ r) (hrD : r ≤ D) :
    2 ^ (r + 1) * Real.sqrt (multiplicationDensityBudget (K v)) *
        (blockTransportedTaylorJetPrice F K Kmax dom ν e E ρ Ks N M Jchart Cchart ζ v u γ r *
          derivativeReserveFactor (ρ / e) (K v) (r - 1) * ‖(F.identity v u γ).map‖) ≤
      blockOriginalIdentityPrice F K Ks Kmax dom ν e E ρ Cjet ζ v u γ := by
  classical
  let ns := ∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I (Ks + 1)
  let na := ∑ d ∈ Finset.Icc 2 (F.identity v u γ).maxOrder,
    ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I (Ks + 1)
  have hn (d : ℕ) : 0 ≤ (∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
      blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I (Ks + 1)) :=
    Finset.sum_nonneg (fun I _ => Finset.sum_nonneg (fun _ _ =>
      blockSlowJetNumerator_nonneg data v u γ d I (Ks + 1)))
  have hns : 0 ≤ ns := Finset.sum_nonneg (fun d _ => hn d)
  have hna : 0 ≤ na := Finset.sum_nonneg (fun d _ => hn d)
  have hsub : ns ≤ na := Finset.sum_le_sum_of_subset_of_nonneg
    (by intro d hd; rcases Finset.mem_Icc.mp hd with ⟨hdlo, hdhi⟩; exact Finset.mem_Icc.mpr ⟨by omega, hdhi⟩)
    (fun d _ _ => hn d)
  have hcard : (2 : ℝ) ^ (r + 1) ≤ 2 ^ (D + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have hkp : (2 : ℝ) ^ (K v) ≤ 2 ^ Kmax := pow_le_pow_right₀ (by norm_num) (data.slot_le v)
  have ht := blockEdgeTransportPrice_nonneg N D M Jchart Cchart
  have hs := blockEdgeSamplingPrice_nonneg M Jchart Cchart
  have hc : 2 ^ (r + 1) * 2 ^ (K v) * blockEdgeTransportPrice N D M Jchart Cchart *
      blockEdgeSamplingPrice M Jchart Cchart ≤ Cjet :=
    (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul hcard hkp (by positivity) (by positivity)) ht) hs).trans hC
  have hc0 : 0 ≤ 2 ^ (r + 1) * 2 ^ (K v) * blockEdgeTransportPrice N D M Jchart Cchart *
      blockEdgeSamplingPrice M Jchart Cchart := by positivity
  have hCjet : 0 ≤ Cjet := hc0.trans hc
  have hh := mul_le_mul hc hsub hns hCjet
  have hrad := div_pos data.radius_pos data.cell_pos
  have hres : derivativeReserveFactor (ρ / e) (K v) (r - 1) ≠ 0 := by
    unfold derivativeReserveFactor
    positivity
  have he : 2 ^ (r + 1) * Real.sqrt (multiplicationDensityBudget (K v)) *
      (blockTransportedTaylorJetPrice F K Kmax dom ν e E ρ Ks N M Jchart Cchart ζ v u γ r *
        derivativeReserveFactor (ρ / e) (K v) (r - 1) * ‖(F.identity v u γ).map‖) =
      (Real.sqrt (multiplicationDensityBudget (K v)) * ζ ^ (Ks + 1) * ‖(F.identity v u γ).map‖) *
        ((2 ^ (r + 1) * 2 ^ (K v) * blockEdgeTransportPrice N D M Jchart Cchart *
          blockEdgeSamplingPrice M Jchart Cchart) * ns) := by
    unfold blockTransportedTaylorJetPrice
    change _ = _ * (_ * (∑ d ∈ Finset.Icc (r + 1) (F.identity v u γ).maxOrder,
      ∑ I : DerivativeWord2 (d - 1), ∑ _i : Fin 2,
        blockSlowJetNumerator F K Kmax dom ν e E ρ v u γ d I (Ks + 1)))
    field_simp [hres]
  rw [he]
  change _ ≤ Real.sqrt (multiplicationDensityBudget (K v)) * Cjet * ζ ^ (Ks + 1) * na * ‖(F.identity v u γ).map‖
  exact blockEdge_price_reassociate _ _ _ _ _ _ _
    (mul_nonneg (mul_nonneg (Real.sqrt_nonneg (multiplicationDensityBudget (K v)))
      (pow_nonneg hζ (Ks + 1))) (norm_nonneg (F.identity v u γ).map)) hh

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleWords
open AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleJointProofs.Assembly

/-! Selecting the natural remainder on aligned pieces and the ordinary
transported remainder on other pieces, with one common original identity price. -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}
  {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}
  {F : ChartedFamily ι h D P Ctx} {π : ι → ℝ} {K : ι → ℕ} {Kmax : ℕ}
  {ν e ρ : ℝ} {Cm : ℕ → ℝ} {J : ℕ} {B : ι → ι → ℝ}

local notation "E₀" => ocEpsilon q Λ (m - 1)
local notation "dom₀" => ChartedFamily.Domain.onWindow F (Set.Icc tS tZ)

/-- The natural remainder constant is fixed before the physical and family data. -/
def blockNaturalChartPrice (Ks Kmax D Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  let Cflow := 1 + ∑ j ∈ Finset.range (Jchart + 2), |preparationFlowJetConstant Cchart j|
  nativeArrayUniformTransportPrice (Kmax + D) D Kmax (compConst Cflow (Kmax + D) * Cflow) *
    naturalRemainderChartPrice Ks Kmax Jchart Cchart

theorem blockNaturalChartPrice_nonneg (Ks Kmax D Jchart : ℕ) (Cchart : ℕ → ℝ) :
    0 ≤ blockNaturalChartPrice Ks Kmax D Jchart Cchart := by
  unfold blockNaturalChartPrice
  apply mul_nonneg _ (naturalRemainderChartPrice_nonneg Ks Kmax Jchart Cchart)
  apply nativeArrayUniformTransportPrice_nonneg
  exact mul_nonneg (compConst_nonneg (one_le_jetConst _ _) _) (zero_le_one.trans (one_le_jetConst _ _))

/-- One scalar price pays both the aligned and misaligned pieces. -/
def blockCommonChartPrice (Ks Kmax D M Jchart : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  blockNaturalChartPrice Ks Kmax D Jchart Cchart +
    2 ^ (D + 1) * 2 ^ Kmax * blockEdgeTransportPrice (M + D) D M Jchart Cchart *
      blockEdgeSamplingPrice M Jchart Cchart

theorem blockCommonChartPrice_nonneg (Ks Kmax D M Jchart : ℕ) (Cchart : ℕ → ℝ) :
    0 ≤ blockCommonChartPrice Ks Kmax D M Jchart Cchart := by
  have ht := blockEdgeTransportPrice_nonneg (M + D) D M Jchart Cchart
  have hs := blockEdgeSamplingPrice_nonneg M Jchart Cchart
  unfold blockCommonChartPrice
  exact add_nonneg (blockNaturalChartPrice_nonneg Ks Kmax D Jchart Cchart) (by positivity)

omit [Fintype ι] in
/-- All selected piece maps exist with one common original density price. -/
theorem exists_blockPieceRemainder_maps
    (data : BlockMolecularInputs F π K Kmax dom₀ ν e E₀ ρ Cm J B)
    (hw : ∀ p, Measurable (F.weight p)) (hm : F.IsTimeMeasurable)
    (hdesc : F.IsDescending K) (Ks M : ℕ) (hKs : Ks + 1 ≤ J)
    (hKM : Kmax ≤ M) (hLM : Ks + 1 ≤ M) (hchart : M + D ≤ Jchart)
    (pieces : Finset P) (actual : ∀ p, Ctx p) (l : ℤ) (σ : ℝ)
    (charts : ∀ p : pieces, BlockSourceChartInputs α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart
      (F.piece p.val).anchor σ)
    (timeScale a b : ℝ) (htime : ∀ τ ∈ Set.Icc a b, timeScale * τ ∈ Set.Icc tS tZ)
    (yc : Vec 2) (hρE : ρ ≤ E₀) (ζ ϖ : ℝ) (hζ : 0 < ζ) (hζ1 : ζ ≤ 1) (hϖ : 0 < ϖ)
    (hδ : e / E₀ = ζ * ϖ) (hfit : (ρ / e) * ϖ ≤ 1) (μ : Measure ℝ) :
    let Cjet := blockCommonChartPrice Ks Kmax D M Jchart Cchart
    ∃ T : ∀ v u, F.Γ v u → Fin D → pieces →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
      (∀ v u γ j p, IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
        (fun x τ z => blockPieceRemainderNativeArray Ks F p.val (actual p.val) v u γ hφ l σ e E₀
          timeScale a b yc (j.val + 1) τ z (WithLp.toLp 2 (fun I => planeJetOrder
            (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) (j.val + 1) I z)))
        (T v u γ j p)) ∧
      (∀ v u γ j p x, ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
        planeFactorialDensity (ρ / e)
          (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T v u γ j p x) τ) z ≤
        F.weight p.val (timeScale * τ) ^ 2 *
          (blockOriginalIdentityPrice F K Ks Kmax dom₀ ν e E₀ ρ Cjet ζ v u γ ^ 2 *
            ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
              planeGradFactorialDensity (ρ / e)
                (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) z))) := by
  classical
  dsimp only
  let Cnat := blockNaturalChartPrice Ks Kmax D Jchart Cchart
  let Ct := 2 ^ (D + 1) * 2 ^ Kmax * blockEdgeTransportPrice (M + D) D M Jchart Cchart *
    blockEdgeSamplingPrice M Jchart Cchart
  let Cjet := blockCommonChartPrice Ks Kmax D M Jchart Cchart
  have hCn : 0 ≤ Cnat := blockNaturalChartPrice_nonneg Ks Kmax D Jchart Cchart
  have hCt : 0 ≤ Ct := by
    have ht := blockEdgeTransportPrice_nonneg (M + D) D M Jchart Cchart
    have hs := blockEdgeSamplingPrice_nonneg M Jchart Cchart
    dsimp only [Ct]
    positivity
  have hCj : 0 ≤ Cjet := blockCommonChartPrice_nonneg Ks Kmax D M Jchart Cchart
  have hCnC : Cnat ≤ Cjet := le_add_of_nonneg_right hCt
  have hCtC : Ct ≤ Cjet := le_add_of_nonneg_left hCn
  have hprice v u γ : 0 ≤ blockOriginalIdentityPrice F K Ks Kmax dom₀ ν e E₀ ρ Cjet ζ v u γ :=
    blockOriginalIdentityPrice_nonneg data Ks Cjet ζ hCj hζ.le v u γ
  have hex (v u : ι) (γ : F.Γ v u) (j : Fin D) (p : pieces) :
      ∃ T : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ,
        IsPlaneTimeAllMomentRawLinearMap (K v) ϖ (ρ / e) 0 μ
          (fun x τ z => blockPieceRemainderNativeArray Ks F p.val (actual p.val) v u γ hφ l σ e E₀
            timeScale a b yc (j.val + 1) τ z (WithLp.toLp 2 (fun I => planeJetOrder
              (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) (j.val + 1) I z))) T ∧
        ∀ x, ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
          planeFactorialDensity (ρ / e) (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T x) τ) z ≤
          F.weight p.val (timeScale * τ) ^ 2 *
            (blockOriginalIdentityPrice F K Ks Kmax dom₀ ν e E₀ ρ Cjet ζ v u γ ^ 2 *
              ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
                planeGradFactorialDensity (ρ / e) (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) z)) := by
    let chart := charts p
    by_cases hl : (F.piece p.val).label = l
    · obtain ⟨T, hT, hden⟩ := exists_originalFamilyNaturalRemainder_descending_identity_density_map
        Ks F hw hm π data.mass_pos K Kmax data.slot_le (Set.Icc tS tZ) ν e E₀ ρ
        data.nu_pos data.cell_pos data.slow_pos data.radius_pos Cm J B data.molecular v u γ hKs p.val (actual p.val)
        hdesc (rjet := j.val + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt j.isLt)
        chart.flow chart.amplitude_nonneg (F.piece p.val).anchor σ chart.anchor_padded chart.reference_padded chart.age
        ((div_le_div_iff_of_pos_right data.cell_pos).mpr hρE) ϖ ζ hϖ hfit hζ.le hδ
        (by have hk := data.slot_le v; omega) timeScale a b htime (Kmax + D) (by omega)
        (by have hk := data.slot_le v; have hD := (F.identity v u γ).le_D; omega) data.slow_pos yc μ
      refine ⟨T, ?_, ?_⟩
      · simpa only [blockPieceRemainderNativeArray, ite_eq_left hl, naturalFamilyRemainderNativeArray] using hT
      · intro x
        have hp := blockEdge_natural_price_le data Ks Cnat Cjet ζ hCn hCnC hζ.le v u γ
        have hp0 := pointwiseOriginalIdentityRemainderPrice_nonneg F K Ks Kmax dom₀ ν e E₀ ρ Cnat ζ
          data.nu_pos.le data.slow_pos.le data.radius_pos.le hCn hζ.le v u γ
        have hd := hden x
        change ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume, _ ≤ F.weight p.val (timeScale * τ) ^ 2 *
          (pointwiseOriginalIdentityRemainderPrice F K Ks Kmax dom₀ ν e E₀ ρ Cnat ζ v u γ ^ 2 *
            ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 * _)) at hd
        filter_upwards [hd] with τ ht
        filter_upwards [ht] with z hz
        exact hz.trans (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp0 hp 2)
            (mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _))) (sq_nonneg _))
    · by_cases hγ : (F.identity v u γ).map = 0
      · refine ⟨0, ?_, ?_⟩
        · apply planeRaw_allMoment_zero_map
          intro x τ z
          simp only [blockPieceRemainderNativeArray, ite_eq_right hl, hγ,
            nativeArrayAssembly_zero_component_map, zero_apply]
        · intro x
          simp only [LinearMap.zero_apply]
          filter_upwards [planeTimeAllMomentCarrier_zero_representative
            (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ 0 rfl] with τ ht
          rw [ht]
          filter_upwards [planeFactorialDensity_zero_ae
            (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
          rw [hz]
          exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
            (mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _)))
      · by_cases hord : j.val + 1 < (F.identity v u γ).maxOrder
        · obtain ⟨T, hT, hden⟩ := exists_blockTransportedRemainder_density_map data chart hw hm p.val (actual p.val)
            v u γ hγ timeScale a b htime yc Ks (M + D) M (j.val + 1)
            (by have hd := hdesc v u γ; omega) hchart le_rfl (Nat.succ_pos _)
            ((data.slot_le v).trans hKM) hLM hKs hρE ζ ϖ hζ hζ1 hϖ hδ hfit μ
          refine ⟨T, ?_, ?_⟩
          · simpa only [blockPieceRemainderNativeArray, ite_eq_right hl] using hT
          · intro x
            have hp := blockEdge_transported_density_price_le data Ks (M + D) M Jchart Cchart Cjet ζ hζ.le hCtC
              v u γ (j.val + 1) (Nat.succ_pos _) (Nat.succ_le_of_lt j.isLt)
            have hrad := (div_pos data.radius_pos data.cell_pos).le
            have hp0 : 0 ≤ 2 ^ (j.val + 1 + 1) * Real.sqrt (multiplicationDensityBudget (K v)) *
                (blockTransportedTaylorJetPrice F K Kmax dom₀ ν e E₀ ρ Ks (M + D) M Jchart Cchart ζ v u γ (j.val + 1) *
                  derivativeReserveFactor (ρ / e) (K v) (j.val + 1 - 1) * ‖(F.identity v u γ).map‖) := by
              have ht := blockTransportedTaylorJetPrice_nonneg data Ks (M + D) M Jchart Cchart ζ hζ.le v u γ (j.val + 1)
              unfold derivativeReserveFactor
              positivity
            filter_upwards [hden x] with τ ht
            filter_upwards [ht] with z hz
            exact hz.trans (mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hp0 hp 2)
                (mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _))) (sq_nonneg _))
        · have hlarge : (F.identity v u γ).maxOrder ≤ j.val + 1 := by omega
          refine ⟨0, ?_, ?_⟩
          · apply planeRaw_allMoment_zero_map
            intro x τ z
            simp only [blockPieceRemainderNativeArray, ite_eq_right hl]
            have hc : (fun k I => F.weight p.val (timeScale * τ) * blockTransportedTimeRemainder Ks F hφ
                p.val (actual p.val) v u γ (F.piece p.val).anchor σ e E₀ timeScale a b yc (j.val + 1) I k τ z) = 0 := by
              funext k I
              rw [blockTransportedTimeRemainder_zero_at_or_above F hφ p.val (actual p.val) v u γ
                (F.piece p.val).anchor σ e E₀ timeScale a b yc Ks (j.val + 1) hlarge I k τ]
              simp only [mul_zero, Pi.zero_apply]
            rw [hc, map_zero, zero_apply]
          · intro x
            simp only [LinearMap.zero_apply]
            filter_upwards [planeTimeAllMomentCarrier_zero_representative
              (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ 0 rfl] with τ ht
            rw [ht]
            filter_upwards [planeFactorialDensity_zero_ae
              (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) (ρ / e)] with z hz
            rw [hz]
            exact mul_nonneg (sq_nonneg _) (mul_nonneg (sq_nonneg _)
              (mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _)))
  choose T hT hden using hex
  exact ⟨T, hT, hden⟩

/-- Positive piece assembly and the fixed order count give the complete mass
moment estimate; identities are summed before either Schur bound. -/
theorem blockRemainder_piece_order_mass_budget
    (data : BlockMolecularInputs F π K Kmax dom₀ ν e E₀ ρ Cm J B)
    (Ks : ℕ) (hKs : Ks + 1 ≤ J) (Cjet ζ ϖ : ℝ) (hC : 0 ≤ Cjet) (hζ : 0 ≤ ζ)
    (μ : Measure ℝ) (pieces : Finset P) (timeScale : ℝ)
    (θ : ℝ) (hθ : 0 ≤ θ) (hB : ∀ v u, 0 ≤ B v u)
    (hrow : ∀ v, ∑ u, B v u ≤ θ) (hcol : ∀ u, ∑ v, B v u ≤ θ)
    (T : ∀ v u, F.Γ v u → Fin D → pieces →
      PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ →ₗ[ℝ]
        PlaneTimeAllMomentCarrier (E := PiLp 2 (fun _ : Fin 2 => h v)) (K v) ϖ (ρ / e) 0 μ)
    (hpiece : ∀ v u γ j p x, ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ (T v u γ j p x) τ) z ≤
      F.weight p.val (timeScale * τ) ^ 2 *
        (blockOriginalIdentityPrice F K Ks Kmax dom₀ ν e E₀ ρ Cjet ζ v u γ ^ 2 *
          ((polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
            planeGradFactorialDensity (ρ / e)
              (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) z)))
    (Z : ∀ u, PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ) (n : ℕ) :
    (∫⁻ τ, ∑ v, ENNReal.ofReal ((π v)⁻¹) * weightedFactorialNormSq n ϖ 0 (ρ / e) (K v)
      (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ
        (nativeFamilyEdgeForcingMap (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p) v Z) τ) ∂μ) ≤
    ENNReal.ofReal ((ζ ^ (Ks + 1) * (((D : ℝ) * blockRemainderGraphConstant Ks Kmax Cjet Cm) * θ)) ^ 2) *
      ∫⁻ τ, ∑ u, ENNReal.ofReal ((π u)⁻¹) * weightedGradFactorialNormSq (n + (Ks + 1))
        ϖ 0 (ρ / e) (K u) (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ (Z u) τ) ∂μ := by
  classical
  let R := fun v u γ => blockOriginalIdentityPrice F K Ks Kmax dom₀ ν e E₀ ρ Cjet ζ v u γ
  let G := fun u (x : PlaneTimeAllMomentCarrier (E := h u) (K u + 1) ϖ (ρ / e) 0 μ) τ z =>
    (polynomialMomentRoot ϖ z ^ (Ks + 1)) ^ 2 *
      planeGradFactorialDensity (ρ / e) (planeTimeAllMomentCarrierToLp (K u + 1) ϖ (ρ / e) 0 μ x τ) z
  let price := fun v u => (D : ℝ) * ∑ γ : F.Γ v u, R v u γ
  let Cg := blockRemainderGraphConstant Ks Kmax Cjet Cm
  let bound := ζ ^ (Ks + 1) * ((D : ℝ) * Cg * θ)
  have hR v u γ : 0 ≤ R v u γ := blockOriginalIdentityPrice_nonneg data Ks Cjet ζ hC hζ v u γ
  have hG u x : ∀ᵐ τ ∂μ, ∀ z, 0 ≤ G u x τ z :=
    Filter.Eventually.of_forall (fun _ z => mul_nonneg (sq_nonneg _) (planeGradFactorialDensity_nonneg _ _ _))
  have hp v u : 0 ≤ price v u := mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg (fun γ _ => hR v u γ))
  have hpoint v u : Real.sqrt (π u / π v) * price v u ≤ ζ ^ (Ks + 1) * ((D : ℝ) * Cg) * B v u := by
    have hh := mul_le_mul_of_nonneg_left
      (blockOriginalIdentityPrice_sum_envelope_le F π K Ks Kmax data.slot_le dom₀ ν e E₀ ρ Cjet ζ
        data.nu_pos data.slow_pos data.radius_pos hC hζ Cm J B hKs data.molecular v u (hB v u))
      (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
    convert hh using 1 <;> dsimp only [price, R, Cg] <;> ring
  have hCg : 0 ≤ Cg := blockRemainderGraphConstant_nonneg Ks Kmax Cjet Cm
  have hfac : 0 ≤ ζ ^ (Ks + 1) * ((D : ℝ) * Cg) := by positivity
  have hb : 0 ≤ bound := mul_nonneg (pow_nonneg hζ _) (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hCg) hθ)
  have hrow' v : ∑ u, Real.sqrt (π u / π v) * price v u ≤ bound := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun u _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [bound, mul_assoc] using mul_le_mul_of_nonneg_left (hrow v) hfac)
  have hcol' u : ∑ v, Real.sqrt (π u / π v) * price v u ≤ bound := by
    have hh := Finset.sum_le_sum (s := Finset.univ) (fun v _ => hpoint v u)
    rw [← Finset.mul_sum] at hh
    exact hh.trans (by simpa only [bound, mul_assoc] using mul_le_mul_of_nonneg_left (hcol u) hfac)
  have hpieces v u γ j := familyPositive_allMoment_map_density_le F pieces (K v) timeScale ϖ (ρ / e) 0 μ
    (T v u γ j) (fun x τ z => R v u γ ^ 2 * G u x τ z)
    (fun x => (hG u x).mono (fun τ ht z => mul_nonneg (sq_nonneg _) (ht z))) (hpiece v u γ j)
  have horders v u γ := planeAllMoment_map_sum_positive_price_density (K v) ϖ (ρ / e) 0 μ
    (fun j : Fin D => ∑ p, T v u γ j p) (fun _ => R v u γ) (fun _ => hR v u γ) (G u) (hG u)
    (hpieces v u γ)
  have horder' v u γ x : ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ ((∑ j, ∑ p, T v u γ j p) x) τ) z ≤
        ((D : ℝ) * R v u γ) ^ 2 * G u x τ z := by
    simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using horders v u γ x
  have hid v u := planeAllMoment_map_sum_positive_price_density (K v) ϖ (ρ / e) 0 μ
    (fun γ : F.Γ v u => ∑ j, ∑ p, T v u γ j p) (fun γ => (D : ℝ) * R v u γ)
    (fun γ => mul_nonneg (Nat.cast_nonneg _) (hR v u γ)) (G u) (hG u) (horder' v u)
  have hd v u : ∀ᵐ τ ∂μ, ∀ᵐ z ∂volume,
      planeFactorialDensity (ρ / e)
        (planeTimeAllMomentCarrierToLp (K v) ϖ (ρ / e) 0 μ ((∑ γ, ∑ j, ∑ p, T v u γ j p) (Z u)) τ) z ≤
      price v u ^ 2 * G u (Z u) τ z := by
    simpa only [← Finset.mul_sum, price] using hid v u (Z u)
  exact planeAllMoment_edgeMap_mass_moment_budget K ϖ (ρ / e) μ
    (fun v u => ∑ γ, ∑ j, ∑ p, T v u γ j p) Z π data.mass_pos price hp bound hb hrow' hcol' (Ks + 1) n hd

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! All block-letter properties other than the quantitative analytic envelopes. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- The finite graph, Schur and qualitative ingredient is unconditional. -/
theorem blockLettersStructural : BlockLettersStructuralStatement.{u, v, w, x} := by
  classical
  intro D Kmax Ks Ls Jm Jchart qJ Jstar hJs hqJ hJchart Ca Cm Cchart CG CL hCL
    α q Λ m ζfast Φ hφ tS tZ Cpad Cage Npad l₀ P ν Bcover ρ g g0 strain B₀ lam Cb y₀
    cov hΛ heE haOld hg0 hD
    ι instFintype instDecidable h instNorm instInner instFinite instMeas instBorel instComplete
    P' Ctx F hmeas hwmeas π hπ K hK actual A Θ Cth H hθ hc hcoverage henv hdepth htransverse
    S hquiet ic a b hab hwindow l σ hσ hσmem hblock
  dsimp only
  let e := ocEpsilon q Λ m
  let E := ocEpsilon q Λ (m - 1)
  let pieces := (F.locally_finite tS tZ).toFinset
  let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀ ic
  let G := windowCoverCellMetric α q Λ m (Φ (m - 1)) hφ l₀ P ν y₀ ic
  have hclock : ocEll q Λ m ν ^ 2 = ν⁻¹ * e ^ 2 := by
    rw [CycleReference.ocEll_sq_eq cov.pos.1, div_eq_mul_inv, mul_comm]
  refine ⟨blockSourceLetter_skeleton F pieces actual hφ (Set.Icc tS tZ) l σ yc e E
      (ν⁻¹ * e ^ 2) Ks H (Cth * Θ) CL _ hD hCL hθ henv.nonneg henv.row_sum henv.col_sum hdepth,
    blockMetricLetter_skeleton G (E⁻¹ • yc) (e / E) Ks H CL g hD hCL cov.g_range.1,
    ?_, ?_, ?_, ?_⟩
  · intro κ pulse orient hpulse
    constructor
    · intro p v u d c hc I
      obtain ⟨γ, hd, rfl⟩ := mem_blockSourceEdges F pieces actual hφ (Set.Icc tS tZ) l σ yc
        e E (ν⁻¹ * e ^ 2) v u d c hc
      obtain ⟨k, hk, hp, ho⟩ := hpulse p
      rw [ho]
      apply sourceConstituent_transverse F pieces actual hφ v u γ d.val hd (Set.Icc tS tZ)
        (Set.Icc (((k : ℝ) - 3 / 4) * ocTau α q Λ m)
          (((k : ℝ) + 3 / 4) * ocTau α q Λ m)) (pulse p)
      · intro p' I' t ht X z s
        exact htransverse ⟨k, hk⟩ p' (actual p') v u γ d.val I' t
          ⟨⟨ht.1, ht.2.2⟩, ht.2.1⟩ X z s
      · intro t ht
        have hh := abs_le.mp (hp t ht)
        rw [hclock] at hh
        constructor <;> linarith [hh.1, hh.2]
    · intro p v u d c hc I t ht X z s
      exact metricEdges_fastIndependent G (E⁻¹ • yc) (e / E) v u d c hc I t X _ _
  · intro Q hQ hw
    constructor
    · refine ⟨hw, ?_⟩
      intro v u d c hc I
      obtain ⟨γ, hd, rfl⟩ := mem_blockSourceEdges F pieces actual hφ (Set.Icc tS tZ) l σ yc
        e E (ν⁻¹ * e ^ 2) v u d c hc
      exact sourceConstituent_fastIndependent F pieces actual hφ v u γ d.val hd
        (Set.Icc tS tZ) S Q hquiet l σ yc e E (ν⁻¹ * e ^ 2)
        (fun t ht => by simpa only [mul_assoc] using hQ t ht) I
    · refine ⟨hw, ?_⟩
      intro v u d c hc I t ht X z z'
      exact metricEdges_fastIndependent G (E⁻¹ • yc) (e / E) v u d c hc I t X z z'
  · intro v u d c hc I X z
    obtain ⟨γ, hd, rfl⟩ := mem_blockSourceEdges F pieces actual hφ (Set.Icc tS tZ) l σ yc
      e E (ν⁻¹ * e ^ 2) v u d c hc
    exact sourceConstituent_measurable F hmeas hwmeas pieces actual hφ v u γ d.val hd
      (Set.Icc tS tZ) measurableSet_Icc l σ yc e E (ν⁻¹ * e ^ 2) I X z
  · intro v u d c hc I X z
    apply metricEdges_measurable G _ (E⁻¹ • yc) (e / E) v u d c hc I X z
    intro X i j
    exact cellMetric_time_slice_measurable α q Λ m hφ (l₀ - 1 + ic) ν yc X i j

/-- Only the closed uniform analytic estimate remains in the block-letter assembly. -/
theorem blockLetters_of_analytic (ha : BlockLettersAnalyticStatement.{u, v, w, x}) :
    BlockLettersStatement.{u, v, w, x} :=
  blockLetters_of_ingredients ha blockLettersStructural

end AVRegularity.CycleJointProofs.Assembly
end
end

section
/-! **Level C, the chart transition at the renewal: statement**.

`BlockTransitionStatement`: the transition operator from the reference
cell chart of block `l₀` (centre `yc`) to the following cell chart of block `l₀ + 1` (centre
`ycpost`), at a transition time `t` of the window, acts on values as the composition with a point
map `Υ` (`fF z = U (Υ z)`, the form `cycle_seam` consumes). `Υ` is a centred transition
(`IsCenteredTransition`) at the finite order `Jchart + 1` with strain `g + A τ''` (cover strain plus
the age bound of the flow certificate) and scale `δ = e / E`, with a constant `CU` fixed after
`Cchart`, `Cpad`, `Cage` and before the family, and `Υinv` is smooth (`hΥs`). The orders
available are exactly those of `IsPreparationFlowJets.jets`. -/

@[expose] public noncomputable section

open Homogenization MeasureTheory AVenhance AVRegularity.Sobolev AVRegularity.CycleJointProofs

universe u v w x

namespace AVRegularity.CycleJointProofs.Assembly

/-- **The chart transition at the renewal.** -/
def BlockTransitionStatement : Prop :=
  ∀ (Kmax Jchart : ℕ) (Cchart CG : ℕ → ℝ) (Cpad Cage : ℝ),
    ∃ CU : ℝ, 0 < CU ∧
    ∀ (α q : ℝ) (Λ m : ℕ) (ζfast : ℝ → ℝ) (Φ : ℕ → ℝ → Vec 2 → ℝ)
      (hφ : IsAdmissibleStream (Φ (m - 1)))
      (tS tZ : ℝ) (Npad : ℕ) (l₀ : ℤ) (P : ℕ)
      (ν Bcover ρ g g0 strain B₀ lam Cb : ℝ) (qJ : ℕ) (y₀ : Vec 2)
      (cov : IsWindowCover α q Λ m ζfast Φ hφ ν Bcover tS tZ ρ g g0 strain B₀ lam Cb qJ Kmax CG
        l₀ P y₀)
      (hΛ : 1 ≤ Λ) (ha : 0 ≤ ocA α q Λ (m - 1)) (_hg0 : g0 ≤ 1 / 4),
    ∀ {ι : Type u} {h : ι → Type v} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
      {D : ℕ} {P' : Type w} {Ctx : P' → Type x} (F : ChartedFamily ι h D P' Ctx)
      (hprep : IsPreparationChartCertificate α q Λ m (Φ (m - 1)) hφ tS tZ Cpad Cage Npad Jchart
        Cchart l₀ P F)
      (hcover : Set.Icc tS tZ ⊆ ⋃ p, (F.piece p).output)
      (hnext : ((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m ∈ Set.Icc tS tZ)
      (t : ℝ) (ht : t ∈ Set.Icc tS tZ)
      (_htblock : ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m - ocTauP α q Λ m ≤ t ∧
        t ≤ ((l₀ : ℝ) + 1 / 2) * ocTauPP α q Λ m + ocTauP α q Λ m),
    let yc := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      (windowCoverReferenceChartIndex P)
    let ycpost := windowCoverChartCentre α q Λ m (Φ (m - 1)) hφ l₀ P y₀
      (windowCoverFollowingChartIndex P cov.P_pos)
    ∃ Υ Υinv : Vec 2 → Vec 2,
      (∀ {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
        [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] (J : ℕ) (hJ : J ≤ Jchart + 1)
        (U : PlaneHk Set.univ J E),
        planeValue (preparationReferenceCellTransitionOperator hprep hcover
          (Construction.Stream.ocTauPP_pos hΛ).le ha J hJ
          (((l₀ + 1 : ℤ) : ℝ) * ocTauPP α q Λ m) hnext (ocEpsilon q Λ m)
          (Construction.Stream.ocEpsilon_pos hΛ).ne' yc ycpost t ht U) =ᵐ[volume]
          fun z => planeValue U (Υ z)) ∧
      IsCenteredTransition Υ Υinv (g + ocA α q Λ (m - 1) * ocTauPP α q Λ m)
        (ocEpsilon q Λ m / ocEpsilon q Λ (m - 1)) CU (Jchart + 1) ∧
      ContDiff ℝ (⊤ : ℕ∞) Υinv

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance MeasureTheory AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! Exact affine conjugation of smooth reference-chart transitions. -/

/-- The transition between the two centred cell coordinates of a physical point map. -/
def blockTransitionAffine (f : Vec 2 → Vec 2) (e : ℝ) (yc yc' : Vec 2) : Vec 2 → Vec 2 :=
  fun z => e⁻¹ • (f (yc' + e • z) - yc)

/-- Affine conjugation preserves smoothness. -/
theorem blockTransitionAffine_smooth (f : Vec 2 → Vec 2) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (e : ℝ) (yc yc' : Vec 2) : ContDiff ℝ (⊤ : ℕ∞) (blockTransitionAffine f e yc yc') :=
  ((hf.comp (contDiff_const.add (contDiff_id.const_smul e))).sub contDiff_const).const_smul e⁻¹

/-- The dilation factors cancel in the first derivative. -/
theorem blockTransitionAffine_fderiv (f : Vec 2 → Vec 2) (hf : ContDiff ℝ (⊤ : ℕ∞) f)
    (e : ℝ) (he : e ≠ 0) (yc yc' z : Vec 2) :
    fderiv ℝ (blockTransitionAffine f e yc yc') z = fderiv ℝ f (yc' + e • z) := by
  have hin : HasFDerivAt (fun z : Vec 2 => yc' + e • z)
      (e • ContinuousLinearMap.id ℝ (Vec 2)) z := by
    exact ((hasFDerivAt_id z).const_smul e).const_add yc'
  have hout := (((hf.differentiable (by simp) _).hasFDerivAt.comp z hin).sub_const yc).const_smul e⁻¹
  have hcalc := hout.fderiv
  change fderiv ℝ (blockTransitionAffine f e yc yc') z =
    e⁻¹ • ((fderiv ℝ f (yc' + e • z)).comp (e • ContinuousLinearMap.id ℝ (Vec 2))) at hcalc
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.comp_id, smul_smul,
    inv_mul_cancel₀ he, one_smul] using hcalc

/-- Every higher derivative retains exactly one fewer dilation factor. -/
theorem blockTransitionAffine_iteratedFDeriv (f : Vec 2 → Vec 2)
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (e : ℝ) (he : e ≠ 0) (yc yc' z : Vec 2)
    (j : ℕ) (hj : 1 ≤ j) :
    iteratedFDeriv ℝ j (blockTransitionAffine f e yc yc') z =
      e ^ (j - 1) • iteratedFDeriv ℝ j f (yc' + e • z) := by
  have hfn : ContDiff ℝ (j : ℕ) (fun z => f (yc' + e • z)) :=
    (hf.comp (contDiff_const.add (contDiff_id.const_smul e))).of_le (by simp)
  unfold blockTransitionAffine
  rw [iteratedFDeriv_const_smul_apply' (hfn.sub contDiff_const).contDiffAt]
  change e⁻¹ • iteratedFDeriv ℝ j ((fun x => f (yc' + e • x)) - (fun _ => yc)) z = _
  rw [iteratedFDeriv_sub_apply hfn.contDiffAt contDiffAt_const,
    congrFun (iteratedFDeriv_const_of_ne (by omega : j ≠ 0) yc) z, Pi.zero_apply, sub_zero]
  have hshift : ContDiff ℝ (j : ℕ) (fun y => f (yc' + y)) :=
    (hf.comp (contDiff_const.add contDiff_id)).of_le (by simp)
  have hscale := congrFun (iteratedFDeriv_comp_const_smul e hshift) z
  change iteratedFDeriv ℝ j (fun z => f (yc' + e • z)) z =
    e ^ j • iteratedFDeriv ℝ j (fun y => f (yc' + y)) (e • z) at hscale
  rw [hscale, iteratedFDeriv_comp_add_left, smul_smul]
  congr 1
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  rw [Nat.succ_eq_add_one, Nat.add_sub_cancel, pow_succ, mul_comm (e ^ k) e,
    ← mul_assoc, inv_mul_cancel₀ he, one_mul]

/-- The affine conjugates of inverse point maps are inverse point maps. -/
theorem blockTransitionAffine_inverse (f finv : Vec 2 → Vec 2)
    (hleft : Function.LeftInverse finv f) (e : ℝ) (he : e ≠ 0) (yc yc' z : Vec 2) :
    blockTransitionAffine finv e yc' yc (blockTransitionAffine f e yc yc' z) = z := by
  unfold blockTransitionAffine
  rw [smul_smul, mul_inv_cancel₀ he, one_smul]
  rw [show yc + (f (yc' + e • z) - yc) = f (yc' + e • z) by abel, hleft]
  rw [add_sub_cancel_left, smul_smul, inv_mul_cancel₀ he, one_smul]

end AVRegularity.CycleJointProofs.Assembly
end
end

section
@[expose] public noncomputable section
open Homogenization AVenhance AVRegularity.Sobolev
namespace AVRegularity.CycleJointProofs.Assembly

/-! The finite certificate gives strain-proportional jets after the exact cell conjugation. -/

/-- One constant dominates every reserved certificate coefficient. -/
def blockTransitionConstant (J : ℕ) (Cchart : ℕ → ℝ) : ℝ :=
  1 + ∑ j ∈ Finset.range (J + 1), |Cchart j|

/-- The chosen constant is positive, and dominates each reserved coefficient. -/
theorem blockTransitionConstant_bounds (J : ℕ) (Cchart : ℕ → ℝ) :
    1 ≤ blockTransitionConstant J Cchart ∧ ∀ j ≤ J, Cchart j ≤ blockTransitionConstant J Cchart := by
  have hn : 0 ≤ ∑ j ∈ Finset.range (J + 1), |Cchart j| :=
    Finset.sum_nonneg (fun j _ => abs_nonneg _)
  refine ⟨by unfold blockTransitionConstant; linarith, ?_⟩
  intro j hj
  exact (le_abs_self _).trans ((Finset.single_le_sum (fun k _ => abs_nonneg (Cchart k))
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))).trans (le_add_of_nonneg_left (by norm_num)))

variable {α q : ℝ} {Λ m : ℕ} {φ : ℝ → Vec 2 → ℝ} {hφ : IsAdmissibleStream φ}
  {tS tZ Cpad Cage : ℝ} {Jchart : ℕ} {Cchart : ℕ → ℝ}

/-- The first derivative deviation keeps the duration and background amplitude factors. -/
theorem blockTransition_flow_deviation
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (T : ℝ) (hspan : |r - σ| ≤ T) (g : ℝ) (hg : 0 ≤ g)
    (e : ℝ) (he : e ≠ 0) (yc yc' z : Vec 2) :
    ‖fderiv ℝ (blockTransitionAffine (fun x => streamFlow φ hφ r x σ) e yc yc') z -
      ContinuousLinearMap.id ℝ (Vec 2)‖ ≤
      blockTransitionConstant Jchart Cchart * (g + ocA α q Λ (m - 1) * T) := by
  rw [blockTransitionAffine_fderiv _ (CycleReference.streamFlow_spatial_smooth hφ r σ) e he]
  have hd := hc.jets r hr σ hσ hage 0 (Nat.zero_le _) (yc' + e • z)
  simp only [norm_iteratedFDeriv_zero, Nat.factorial_zero, Nat.cast_one, pow_zero, mul_one] at hd
  have hC := blockTransitionConstant_bounds Jchart Cchart
  have hC0 : 0 ≤ blockTransitionConstant Jchart Cchart := zero_le_one.trans hC.1
  calc
    _ ≤ Cchart 0 * (ocA α q Λ (m - 1) * |r - σ|) := by simpa only [mul_assoc] using hd
    _ ≤ blockTransitionConstant Jchart Cchart * (ocA α q Λ (m - 1) * |r - σ|) :=
      mul_le_mul_of_nonneg_right (hC.2 0 (Nat.zero_le _)) (mul_nonneg ha (abs_nonneg _))
    _ ≤ blockTransitionConstant Jchart Cchart * (g + ocA α q Λ (m - 1) * T) :=
      mul_le_mul_of_nonneg_left
        ((mul_le_mul_of_nonneg_left hspan ha).trans (le_add_of_nonneg_left hg)) hC0

/-- Positive higher jets keep the same strain, with precisely the cell length scale e/E. -/
theorem blockTransition_flow_higher_jets
    (hc : IsPreparationFlowJets α q Λ m φ hφ tS tZ Cpad Cage Jchart Cchart)
    (ha : 0 ≤ ocA α q Λ (m - 1)) (r σ : ℝ)
    (hr : r ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hσ : σ ∈ preparationPaddedWindow tS tZ Cpad (ocTauPP α q Λ m))
    (hage : |r - σ| ≤ 2 * Cage * ocTauPP α q Λ m)
    (T : ℝ) (hspan : |r - σ| ≤ T) (g : ℝ) (hg : 0 ≤ g)
    (e : ℝ) (he : 0 < e) (hE : 0 < ocEpsilon q Λ (m - 1)) (yc yc' : Vec 2)
    (j : ℕ) (hj : 2 ≤ j) (hjJ : j ≤ Jchart + 1) (z : Vec 2) :
    ‖iteratedFDeriv ℝ j (blockTransitionAffine (fun x => streamFlow φ hφ r x σ) e yc yc') z‖ ≤
      blockTransitionConstant Jchart Cchart * (g + ocA α q Λ (m - 1) * T) *
        ((j - 1).factorial : ℝ) *
          (blockTransitionConstant Jchart Cchart * (e / ocEpsilon q Λ (m - 1))) ^ (j - 1) := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : j ≠ 0)
  have hk : k ≠ 0 := by omega
  have hkJ : k ≤ Jchart := by omega
  let f := fun x => streamFlow φ hφ r x σ
  have hf : ContDiff ℝ (⊤ : ℕ∞) f := CycleReference.streamFlow_spatial_smooth hφ r σ
  have hdf : ContDiff ℝ (k : ℕ) (fderiv ℝ f) :=
    hf.fderiv_right (by simp)
  have hd := hc.jets r hr σ hσ hage k hkJ (yc' + e • z)
  change ‖iteratedFDeriv ℝ k ((fderiv ℝ f) -
    (fun _ => ContinuousLinearMap.id ℝ (Vec 2))) (yc' + e • z)‖ ≤ _ at hd
  rw [iteratedFDeriv_sub_apply hdf.contDiffAt contDiffAt_const,
    congrFun (iteratedFDeriv_const_of_ne hk (ContinuousLinearMap.id ℝ (Vec 2))) (yc' + e • z),
    Pi.zero_apply, sub_zero, norm_iteratedFDeriv_fderiv] at hd
  rw [blockTransitionAffine_iteratedFDeriv f hf e he.ne' yc yc' z (k + 1) (by omega),
    Nat.add_sub_cancel, norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos he k)]
  let C := blockTransitionConstant Jchart Cchart
  have hC := blockTransitionConstant_bounds Jchart Cchart
  have hC0 : 0 ≤ C := zero_le_one.trans hC.1
  have hδ : 0 ≤ e / ocEpsilon q Λ (m - 1) := (div_pos he hE).le
  have hT : 0 ≤ T := (abs_nonneg _).trans hspan
  calc
    _ ≤ e ^ k * (Cchart k * (k.factorial : ℝ) * (ocEpsilon q Λ (m - 1))⁻¹ ^ k *
        ocA α q Λ (m - 1) * |r - σ|) := mul_le_mul_of_nonneg_left hd (pow_nonneg he.le _)
    _ = Cchart k * (ocA α q Λ (m - 1) * |r - σ|) * (k.factorial : ℝ) *
        (e / ocEpsilon q Λ (m - 1)) ^ k := by rw [div_eq_mul_inv, mul_pow]; ring
    _ ≤ C * (ocA α q Λ (m - 1) * |r - σ|) * (k.factorial : ℝ) *
        (e / ocEpsilon q Λ (m - 1)) ^ k := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (hC.2 k hkJ) (mul_nonneg ha (abs_nonneg _))) (by positivity))
        (pow_nonneg hδ _)
    _ ≤ C * (g + ocA α q Λ (m - 1) * T) * (k.factorial : ℝ) *
        (e / ocEpsilon q Λ (m - 1)) ^ k := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left
            ((mul_le_mul_of_nonneg_left hspan ha).trans (le_add_of_nonneg_left hg)) hC0)
          (by positivity)) (pow_nonneg hδ _)
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ hδ (le_mul_of_one_le_left hδ hC.1) k)
      (mul_nonneg (mul_nonneg hC0 (add_nonneg hg (mul_nonneg ha hT))) (by positivity))

end AVRegularity.CycleJointProofs.Assembly
end
end
