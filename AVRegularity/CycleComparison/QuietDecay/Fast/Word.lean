-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.QuietDecay.Engine.Induction
import AVRegularity.CycleComparison.QuietDecay.Translate.Main
import AVRegularity.CycleEvolution.CellEnergySpaceRawDirectionalLimit

section
@[expose] public noncomputable section

section
open MeasureTheory Set Homogenization
open scoped ENNReal
namespace AVRegularity.QuietDecay

/-! Iterated fast difference quotients of periodic fields of one variable: they stay smooth and
periodic, commute with derivatives, and their cell `L²` norms are bounded by the cell `L²` norm of
the derivative (letters in reversed order). -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Iterated fast difference quotients along the list `m` (first letter first). -/
def fastDiffs (m : List (Fin 2)) (h : ℝ) (g : Vec 2 → E) : Vec 2 → E :=
  m.foldl (fun g' i => sdiff i h g') g

/-- Iterated derivatives along the list `m` (first letter first). -/
def fastDerivs (m : List (Fin 2)) (g : Vec 2 → E) : Vec 2 → E :=
  m.foldl (fun g' i => fun z => fderiv ℝ g' z (basisVec i)) g

theorem fastDiffs_append (m : List (Fin 2)) (i : Fin 2) (h : ℝ) (g : Vec 2 → E) :
    fastDiffs (m ++ [i]) h g = sdiff i h (fastDiffs m h g) := by
  simp [fastDiffs, List.foldl_append]

theorem fastDerivs_cons (m : List (Fin 2)) (i : Fin 2) (g : Vec 2 → E) :
    fastDerivs (i :: m) g = fastDerivs m (fun z => fderiv ℝ g z (basisVec i)) := rfl

theorem fastDerivs_reverse_append (m : List (Fin 2)) (i : Fin 2) (g : Vec 2 → E) :
    fastDerivs (m ++ [i]).reverse g =
      fastDerivs m.reverse (fun z => fderiv ℝ g z (basisVec i)) := by
  simp [fastDerivs_cons]

theorem isZ2Periodic_sdiff {g : Vec 2 → E} (hp : AVenhance.IsZ2Periodic g) (i : Fin 2) (h : ℝ) :
    AVenhance.IsZ2Periodic (sdiff i h g) := by
  intro n z
  simp only [sdiff]
  rw [add_right_comm, hp n (z + h • basisVec i), hp n z]

theorem isZ2Periodic_fastDiffs {g : Vec 2 → E} (hp : AVenhance.IsZ2Periodic g) (m : List (Fin 2))
    (h : ℝ) : AVenhance.IsZ2Periodic (fastDiffs m h g) := by
  induction m using List.reverseRecOn with
  | nil => exact hp
  | append_singleton m i ih => rw [fastDiffs_append]; exact isZ2Periodic_sdiff ih i h

theorem isZ2Periodic_fderiv_apply {g : Vec 2 → E} (hp : AVenhance.IsZ2Periodic g) (i : Fin 2) :
    AVenhance.IsZ2Periodic (fun z => fderiv ℝ g z (basisVec i)) := by
  intro n z
  have : g = fun y => g (y + AVenhance.latticeShift n) := funext fun y => (hp n y).symm
  conv_rhs => rw [this]
  beta_reduce
  rw [fderiv_comp_add_right]

theorem contDiff_sdiff {n : WithTop ℕ∞} {g : Vec 2 → E} (hg : ContDiff ℝ n g) (i : Fin 2) (h : ℝ) :
    ContDiff ℝ n (sdiff i h g) := by
  unfold sdiff
  exact ((hg.comp (contDiff_id.add contDiff_const)).sub hg).const_smul h⁻¹

theorem contDiff_fastDiffs {n : WithTop ℕ∞} {g : Vec 2 → E} (hg : ContDiff ℝ n g)
    (m : List (Fin 2)) (h : ℝ) : ContDiff ℝ n (fastDiffs m h g) := by
  induction m using List.reverseRecOn with
  | nil => exact hg
  | append_singleton m i ih => rw [fastDiffs_append]; exact contDiff_sdiff ih i h

theorem contDiff_fderiv_apply {n : WithTop ℕ∞} {g : Vec 2 → E} (hg : ContDiff ℝ (n + 1) g)
    (i : Fin 2) : ContDiff ℝ n (fun z => fderiv ℝ g z (basisVec i)) :=
  (hg.fderiv_right le_rfl).clm_apply contDiff_const

/-- A derivative of a one-step difference quotient is the difference quotient of the derivative. -/
theorem fderiv_sdiff_apply {g : Vec 2 → E} (hg : Differentiable ℝ g) (i j : Fin 2) (h : ℝ) :
    (fun z => fderiv ℝ (sdiff i h g) z (basisVec j)) =
      sdiff i h (fun z => fderiv ℝ g z (basisVec j)) := by
  funext z
  have hadd : HasFDerivAt (fun X' : Vec 2 => X' + h • basisVec i)
      (ContinuousLinearMap.id ℝ (Vec 2)) z := (hasFDerivAt_id z).add_const _
  have hd1 : HasFDerivAt (fun X' => g (X' + h • basisVec i))
      (fderiv ℝ g (z + h • basisVec i)) z := by
    have := HasFDerivAt.comp z (hg (z + h • basisVec i)).hasFDerivAt hadd
    simpa [Function.comp_def] using this
  have hd : HasFDerivAt (fun X' => h⁻¹ • (g (X' + h • basisVec i) - g X'))
      (h⁻¹ • (fderiv ℝ g (z + h • basisVec i) - fderiv ℝ g z)) z :=
    (hd1.sub (hg z).hasFDerivAt).const_smul h⁻¹
  change fderiv ℝ (fun X' => h⁻¹ • (g (X' + h • basisVec i) - g X')) z (basisVec j) = _
  rw [hd.fderiv]
  rfl

theorem fderiv_fastDiffs_apply {n : ℕ} {g : Vec 2 → E} (hg : ContDiff ℝ ((n : WithTop ℕ∞) + 1) g)
    (m : List (Fin 2)) (h : ℝ) (j : Fin 2) :
    (fun z => fderiv ℝ (fastDiffs m h g) z (basisVec j)) =
      fastDiffs m h (fun z => fderiv ℝ g z (basisVec j)) := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m i ih =>
      rw [fastDiffs_append, fastDiffs_append, fderiv_sdiff_apply, ih]
      exact (contDiff_fastDiffs hg m h).differentiable (by simp)

end AVRegularity.QuietDecay
end

section
open MeasureTheory Set Filter Topology Homogenization
namespace AVRegularity.QuietDecay

/-! Iterated fast difference quotients of a `C^{|m|}` field (no extra derivative) converge, locally
uniformly, to the derivatives in reversed letter order. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- Locally uniform convergence of iterated fast difference quotients. -/
theorem fastDiffs_locUnif_sharp :
    ∀ (m : List (Fin 2)) (g : Vec 2 → E), ContDiff ℝ (m.length : WithTop ℕ∞) g →
      ∀ (z : Vec 2) (ε : ℝ), 0 < ε → ∃ δ > 0, ∀ h : ℝ, h ≠ 0 → |h| < δ → ∀ y : Vec 2,
        dist y z < δ → ‖fastDiffs m h g y - fastDerivs m.reverse g z‖ < ε := by
  intro m
  induction m using List.reverseRecOn with
  | nil =>
      intro g hg z ε hε
      have hc : ContinuousAt g z := (hg.continuous).continuousAt
      obtain ⟨δ, hδ, hball⟩ := Metric.continuousAt_iff.1 hc ε hε
      refine ⟨δ, hδ, fun h _ _ y hy => ?_⟩
      simpa [fastDiffs, fastDerivs, dist_eq_norm] using hball hy
  | append_singleton m i ih =>
      intro g hg z ε hε
      have hlen : (((m ++ [i]).length : ℕ) : WithTop ℕ∞) =
          (m.length : WithTop ℕ∞) + 1 := by simp
      rw [hlen] at hg
      have hg' : ContDiff ℝ (m.length : WithTop ℕ∞) (fun z => fderiv ℝ g z (basisVec i)) :=
        contDiff_fderiv_apply hg i
      obtain ⟨δ₀, hδ₀, hδ₀b⟩ := ih _ hg' z (ε / 2) (by linarith)
      refine ⟨δ₀ / 2, by linarith, fun h hh hhδ y hy => ?_⟩
      have h1 : (1 : WithTop ℕ∞) ≤ (m.length : WithTop ℕ∞) + 1 := by
        norm_cast; omega
      have hd := contDiff_fastDiffs (hg.of_le h1) m h
      have hdiff : Differentiable ℝ (fastDiffs m h g) := hd.differentiable (by simp)
      have hcont : Continuous fun X' => fderiv ℝ (fastDiffs m h g) X' (basisVec i) :=
        (hd.continuous_fderiv (by simp)).clm_apply continuous_const
      have hrep := sdiff_eq_integral i hh hdiff hcont y
      have hcomm : ∀ Y', fderiv ℝ (fastDiffs m h g) Y' (basisVec i) =
          fastDiffs m h (fun z => fderiv ℝ g z (basisVec i)) Y' := fun Y' =>
        congrFun (fderiv_fastDiffs_apply (n := m.length) hg m h i) Y'
      set c := fastDerivs m.reverse (fun z => fderiv ℝ g z (basisVec i)) z
      have hpt : ∀ θ ∈ Set.uIcc (0 : ℝ) 1,
          ‖fastDiffs m h (fun z => fderiv ℝ g z (basisVec i)) (y + (θ * h) • basisVec i) - c‖ ≤
            ε / 2 := by
        intro θ hθ
        rw [Set.uIcc_of_le zero_le_one] at hθ
        refine (hδ₀b h hh (by linarith) _ ?_).le
        have hn : ‖(θ * h) • basisVec i‖ ≤ |h| := by
          rw [norm_smul, Real.norm_eq_abs, abs_mul, abs_of_nonneg hθ.1]
          have hb : ‖(basisVec i : Vec 2)‖ ≤ 1 := by
            rw [pi_norm_le_iff_of_nonneg zero_le_one]
            intro k
            by_cases hk : k = i <;> simp [basisVec, hk]
          calc θ * |h| * ‖(basisVec i : Vec 2)‖ ≤ 1 * |h| * 1 := by
                gcongr
                · exact hθ.2
            _ = |h| := by ring
        calc dist (y + (θ * h) • basisVec i) z ≤ dist y z + ‖(θ * h) • basisVec i‖ := by
              rw [dist_eq_norm, dist_eq_norm]
              calc ‖y + (θ * h) • basisVec i - z‖ = ‖(y - z) + (θ * h) • basisVec i‖ := by
                    congr 1; abel
                _ ≤ ‖y - z‖ + ‖(θ * h) • basisVec i‖ := norm_add_le _ _
          _ < δ₀ / 2 + δ₀ / 2 := by linarith
          _ = δ₀ := by ring
      rw [fastDiffs_append, fastDerivs_reverse_append]
      change ‖sdiff i h (fastDiffs m h g) y - c‖ < ε
      rw [hrep]
      simp_rw [hcomm]
      have hint : IntervalIntegrable (fun θ : ℝ =>
          fastDiffs m h (fun z => fderiv ℝ g z (basisVec i)) (y + (θ * h) • basisVec i)) volume
          0 1 := by
        refine Continuous.intervalIntegrable ?_ _ _
        have := (contDiff_fastDiffs hg' m h).continuous
        exact this.comp (continuous_const.add ((continuous_id.mul continuous_const).smul
          continuous_const))
      have hc1 : (∫ θ in (0 : ℝ)..1, c) = c := by simp
      calc ‖(∫ θ in (0 : ℝ)..1, fastDiffs m h (fun z => fderiv ℝ g z (basisVec i))
              (y + (θ * h) • basisVec i)) - c‖
          = ‖∫ θ in (0 : ℝ)..1, (fastDiffs m h (fun z => fderiv ℝ g z (basisVec i))
              (y + (θ * h) • basisVec i) - c)‖ := by
            rw [intervalIntegral.integral_sub hint intervalIntegrable_const, hc1]
        _ ≤ (ε / 2) * |(1 : ℝ) - 0| :=
            intervalIntegral.norm_integral_le_of_norm_le_const fun θ hθ =>
              hpt θ (Set.uIoc_subset_uIcc hθ)
        _ < ε := by norm_num; linarith

/-- Pointwise convergence of iterated fast difference quotients. -/
theorem fastDiffs_tendsto_sharp (m : List (Fin 2)) (g : Vec 2 → E)
    (hg : ContDiff ℝ (m.length : WithTop ℕ∞) g) (z : Vec 2) :
    Tendsto (fun h => fastDiffs m h g z) (𝓝[≠] 0) (𝓝 (fastDerivs m.reverse g z)) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  obtain ⟨δ, hδ, hb⟩ := fastDiffs_locUnif_sharp m g hg z ε hε
  have h1 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), h ≠ 0 := self_mem_nhdsWithin
  have h2 : ∀ᶠ h in 𝓝[≠] (0 : ℝ), |h| < δ := by
    refine nhdsWithin_le_nhds ?_
    filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδ] with h hh
    simpa [Real.dist_eq] using hh
  filter_upwards [h1, h2] with h hh0 hhδ
  rw [dist_eq_norm]
  exact hb h hh0 hhδ z (by simpa using hδ)

/-- The `L²` bound of iterated fast differences of a `C^{|m|}` periodic field. -/
theorem lintegral_fastDiffs_le_sharp {h : ℝ} (hh : h ≠ 0) :
    ∀ (m : List (Fin 2)) (g : Vec 2 → E), AVenhance.IsZ2Periodic g →
      ContDiff ℝ (m.length : WithTop ℕ∞) g →
      ∫⁻ z in AVenhance.unitCube, ‖fastDiffs m h g z‖ₑ ^ 2 ≤
        ∫⁻ z in AVenhance.unitCube, ‖fastDerivs m.reverse g z‖ₑ ^ 2 := by
  intro m
  induction m using List.reverseRecOn with
  | nil => intro g _ _; exact le_rfl
  | append_singleton m i ih =>
      intro g hp hg
      have hlen : (((m ++ [i]).length : ℕ) : WithTop ℕ∞) = (m.length : WithTop ℕ∞) + 1 := by
        simp
      rw [hlen] at hg
      have h1 : (1 : WithTop ℕ∞) ≤ (m.length : WithTop ℕ∞) + 1 := by
        norm_cast; omega
      have hd := contDiff_fastDiffs (hg.of_le h1) m h
      have hpd := isZ2Periodic_fastDiffs hp m h
      rw [fastDiffs_append, fastDerivs_reverse_append]
      refine (lintegral_fast_sdiff_le i hh (hd.differentiable (by simp)) ?_ hpd).trans ?_
      · exact (hd.continuous_fderiv (by simp)).clm_apply continuous_const
      · have e := fderiv_fastDiffs_apply (n := m.length) hg m h i
        rw [show (∫⁻ z in AVenhance.unitCube, ‖fderiv ℝ (fastDiffs m h g) z (basisVec i)‖ₑ ^ 2) =
          ∫⁻ z in AVenhance.unitCube,
            ‖fastDiffs m h (fun z => fderiv ℝ g z (basisVec i)) z‖ₑ ^ 2 from
          lintegral_congr fun z => by rw [← congrFun e z]]
        exact ih _ (isZ2Periodic_fderiv_apply hp i) (contDiff_fderiv_apply hg i)

end AVRegularity.QuietDecay
end
end
end

section
@[expose] public noncomputable section
section
open MeasureTheory Set Homogenization AVRegularity.Sobolev
open AVRegularity.CycleEvolution
namespace AVRegularity.QuietDecay

/-! Fast difference quotients of a family of cell solutions: the translation in the fast variable
of a cell solution with space-independent coefficients is again a cell solution, so the fast
difference quotient of a family with periodic sources and fluxes is again a cell family. -/

/-- The fast difference quotient of a family. -/
def fastStep (i : Fin 2) (h : ℝ) (Φ : CellFam) : CellFam where
  D X t := h⁻¹ • ((fun a z => Φ.D X t a (z + h • basisVec i)) - Φ.D X t)
  src X t z := (h⁻¹ : ℂ) * (Φ.src X t (z + h • basisVec i) - Φ.src X t z)
  F X t z := h⁻¹ • (Φ.F X t (z + h • basisVec i) - Φ.F X t z)

theorem isCellFam_fastStep {J : Set ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam}
    (hΦ : IsCellFam J G (fun _ _ => 0) Φ)
    (hsrc : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.src X t))
    (hF : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.F X t)) (i : Fin 2) (h : ℝ) :
    IsCellFam J G (fun _ _ => 0) (fastStep i h Φ) := by
  intro X
  set w := h • basisVec i
  have h1 : IsCellSolution J (slowCoeffs G (fun _ _ => 0) X) (fun t z => Φ.src X t (z + w))
      (fun t z => Φ.F X t (z + w)) (fun t a z => Φ.D X t a (z + w)) :=
    cellSolution_translate (fun t => G t X) (fun _ => 0) (fun _ => 0) (hsrc X) (hF X) (hΦ X) w
  have h2 := cellSolution_smul (hΦ X) (-1)
  have h3 := cellSolution_smul (cellSolution_add h1 h2) h⁻¹
  have hD : (fastStep i h Φ).D X = h⁻¹ • ((fun t a z => Φ.D X t a (z + w)) +
      (-1 : ℝ) • Φ.D X) := by
    funext t
    simp only [fastStep, Pi.smul_apply, Pi.add_apply, neg_one_smul, sub_eq_add_neg, w]
    rfl
  rw [hD]
  refine cellSolution_source_congr_sections J _ _ _ _ _ _
    (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun z => ?_)
    (Filter.Eventually.of_forall fun r => Filter.Eventually.of_forall fun z => ?_) h3
  · simp only [Pi.smul_apply, Pi.add_apply, fastStep, w]
    rw [Complex.real_smul, Complex.real_smul, Complex.ofReal_inv, Complex.ofReal_neg,
      Complex.ofReal_one]
    ring
  · simp only [Pi.smul_apply, Pi.add_apply, fastStep, w]
    rw [neg_one_smul, ← sub_eq_add_neg]

theorem fastStep_src_periodic {J : Set ℝ} {Φ : CellFam}
    (hsrc : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.src X t)) (i : Fin 2) (h : ℝ) :
    ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic ((fastStep i h Φ).src X t) := by
  intro X t ht n z
  simp only [fastStep]
  rw [add_right_comm, hsrc X t ht n (z + h • basisVec i), hsrc X t ht n z]

theorem fastStep_F_periodic {J : Set ℝ} {Φ : CellFam}
    (hF : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.F X t)) (i : Fin 2) (h : ℝ) :
    ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic ((fastStep i h Φ).F X t) := by
  intro X t ht n z
  simp only [fastStep]
  rw [add_right_comm, hF X t ht n (z + h • basisVec i), hF X t ht n z]

theorem fastStep_F_zero {Φ : CellFam} (hF : Φ.F = fun _ _ _ => 0) (i : Fin 2) (h : ℝ) :
    (fastStep i h Φ).F = fun _ _ _ => 0 := by
  funext X t z
  simp [fastStep, hF]

theorem isFiniteMeasure_cube_fast : IsFiniteMeasure (volume.restrict AVenhance.unitCube) := by
  refine ⟨?_⟩
  rw [Measure.restrict_apply_univ]
  have hsub : AVenhance.unitCube ⊆ Set.Icc (0 : Vec 2) 1 := fun x hx =>
    ⟨fun i => (hx i (Set.mem_univ i)).1.le, fun i => (hx i (Set.mem_univ i)).2.le⟩
  exact (measure_mono hsub).trans_lt measure_Icc_lt_top

/-- The values of the fast difference quotient are the difference quotients of the values. -/
theorem cellValue_fastStep (i : Fin 2) (h : ℝ) (Φ : CellFam) (X : Vec 2) (t : ℝ) (z : Vec 2) :
    cellValue ((fastStep i h Φ).D X) t z = sdiff i h (cellValue (Φ.D X) t) z := rfl

/-- The fast difference quotient of a periodic mean value is mean zero (no hypothesis on the mean
of the original is needed). -/
theorem fastStep_cellMean {J : Set ℝ} {Φ : CellFam}
    (hv : ∀ X, ∀ t ∈ J, MemLp (cellValue (Φ.D X) t) 2 (volume.restrict AVenhance.unitCube) ∧
      AVenhance.IsZ2Periodic (cellValue (Φ.D X) t))
    (i : Fin 2) (h : ℝ) :
    ∀ X, ∀ t ∈ J, cellMean (cellValue ((fastStep i h Φ).D X) t) = 0 := by
  intro X t ht
  obtain ⟨hL, hp⟩ := hv X t ht
  have := isFiniteMeasure_cube_fast
  have hint : Integrable (cellValue (Φ.D X) t) (volume.restrict AVenhance.unitCube) :=
    hL.integrable one_le_two
  have hsh := integral_shift hp hint.aestronglyMeasurable (h • basisVec i)
  unfold cellMean
  have e : cellValue ((fastStep i h Φ).D X) t = fun z => h⁻¹ •
      (cellValue (Φ.D X) t (z + h • basisVec i) - cellValue (Φ.D X) t z) := rfl
  rw [e, integral_smul, integral_sub (integrable_shift hp hint _) hint, hsh, sub_self, smul_zero]

theorem fastStep_src_aestronglyMeasurable {J : Set ℝ} (hJ : MeasurableSet J) {Φ : CellFam}
    (hsrc : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.src X t))
    (hm : ∀ X, AEStronglyMeasurable (Function.uncurry (Φ.src X))
      ((volume.restrict J).prod (volume.restrict AVenhance.unitCube))) (i : Fin 2) (h : ℝ) :
    ∀ X, AEStronglyMeasurable (Function.uncurry ((fastStep i h Φ).src X))
      ((volume.restrict J).prod (volume.restrict AVenhance.unitCube)) := by
  intro X
  have hper : ∀ᵐ t ∂(volume.restrict J), AVenhance.IsZ2Periodic (Φ.src X t) :=
    (ae_restrict_iff' hJ).2 (Filter.Eventually.of_forall fun t ht => hsrc X t ht)
  have hs := aestronglyMeasurable_joint_shift (f := Φ.src X) (hm X) hper (h • basisVec i)
  exact (aestronglyMeasurable_const.mul (hs.sub (hm X)) : AEStronglyMeasurable _ _)

/-! Iterated fast steps of a family of cell solutions, and the identification of the values of
iterated fast and slow difference quotients of a family with iterated difference quotients of the
values. -/

/-- The family after the fast steps of the word `m` (first letter first). -/
def fastWord (m : List (Fin 2)) (h : ℝ) (Φ : CellFam) : CellFam :=
  m.foldl (fun Ψ i => fastStep i h Ψ) Φ

theorem fastWord_append (m : List (Fin 2)) (i : Fin 2) (h : ℝ) (Φ : CellFam) :
    fastWord (m ++ [i]) h Φ = fastStep i h (fastWord m h Φ) := by
  simp [fastWord, List.foldl_append]

theorem fastWord_src_periodic {J : Set ℝ} {Φ : CellFam}
    (hsrc : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.src X t)) (m : List (Fin 2)) (h : ℝ) :
    ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic ((fastWord m h Φ).src X t) := by
  induction m using List.reverseRecOn with
  | nil => exact hsrc
  | append_singleton m i ih => rw [fastWord_append]; exact fastStep_src_periodic ih i h

theorem fastWord_F_periodic {J : Set ℝ} {Φ : CellFam}
    (hF : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.F X t)) (m : List (Fin 2)) (h : ℝ) :
    ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic ((fastWord m h Φ).F X t) := by
  induction m using List.reverseRecOn with
  | nil => exact hF
  | append_singleton m i ih => rw [fastWord_append]; exact fastStep_F_periodic ih i h

theorem fastWord_F_zero {Φ : CellFam} (hF : Φ.F = fun _ _ _ => 0) (m : List (Fin 2)) (h : ℝ) :
    (fastWord m h Φ).F = fun _ _ _ => 0 := by
  induction m using List.reverseRecOn with
  | nil => exact hF
  | append_singleton m i ih => rw [fastWord_append]; exact fastStep_F_zero ih i h

theorem isCellFam_fastWord {J : Set ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam}
    (hΦ : IsCellFam J G (fun _ _ => 0) Φ)
    (hsrc : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.src X t))
    (hF : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.F X t)) (m : List (Fin 2)) (h : ℝ) :
    IsCellFam J G (fun _ _ => 0) (fastWord m h Φ) := by
  induction m using List.reverseRecOn with
  | nil => exact hΦ
  | append_singleton m i ih =>
      rw [fastWord_append]
      exact isCellFam_fastStep ih (fastWord_src_periodic hsrc m h) (fastWord_F_periodic hF m h) i h

/-- Mean zero of the values on `J` is preserved (and created by any nonempty word). -/
theorem fastWord_cellMean {J : Set ℝ} {G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ} {Φ : CellFam}
    (hΦ : IsCellFam J G (fun _ _ => 0) Φ)
    (hsrc : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.src X t))
    (hF : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.F X t))
    (hm : ∀ X, ∀ t ∈ J, cellMean (cellValue (Φ.D X) t) = 0) (m : List (Fin 2)) (h : ℝ) :
    ∀ X, ∀ t ∈ J, cellMean (cellValue ((fastWord m h Φ).D X) t) = 0 := by
  induction m using List.reverseRecOn with
  | nil => exact hm
  | append_singleton m i ih =>
      rw [fastWord_append]
      exact fastStep_cellMean (fun X t ht => (isCellFam_fastWord hΦ hsrc hF m h X).2.2.1 t ht) i h

theorem fastWord_src_aestronglyMeasurable {J : Set ℝ} (hJ : MeasurableSet J) {Φ : CellFam}
    (hsrc : ∀ X, ∀ t ∈ J, AVenhance.IsZ2Periodic (Φ.src X t))
    (hm : ∀ X, AEStronglyMeasurable (Function.uncurry (Φ.src X))
      ((volume.restrict J).prod (volume.restrict AVenhance.unitCube))) (m : List (Fin 2)) (h : ℝ) :
    ∀ X, AEStronglyMeasurable (Function.uncurry ((fastWord m h Φ).src X))
      ((volume.restrict J).prod (volume.restrict AVenhance.unitCube)) := by
  induction m using List.reverseRecOn with
  | nil => exact hm
  | append_singleton m i ih =>
      rw [fastWord_append]
      exact fastStep_src_aestronglyMeasurable hJ (fastWord_src_periodic hsrc m h) ih i h

/-- The values of the fast word are the iterated fast difference quotients of the values. -/
theorem cellValue_fastWord (m : List (Fin 2)) (h : ℝ) (Φ : CellFam) (X : Vec 2) (t : ℝ) :
    cellValue ((fastWord m h Φ).D X) t = fastDiffs m h (cellValue (Φ.D X) t) := by
  induction m using List.reverseRecOn with
  | nil => rfl
  | append_singleton m i ih =>
      rw [fastWord_append, fastDiffs_append, ← ih]
      funext z
      exact cellValue_fastStep i h _ X t z

/-- The values of the slow word are the iterated slow difference quotients of the values. -/
theorem cellValue_famWord (G : ℝ → Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Φ : CellFam)
    (l : List (Fin 2)) (h : ℝ) (t : ℝ) (X z : Vec 2) :
    cellValue ((famWord G Φ l h).D X) t z =
      slowDiffs l h (fun X' z' => cellValue (Φ.D X') t z') X z := by
  induction l using List.reverseRecOn generalizing X with
  | nil => rfl
  | append_singleton l i ih =>
      rw [slowDiffs_append]
      unfold cellValue
      rw [famWord_D_append]
      simp only [Pi.smul_apply, Pi.sub_apply, sdiff]
      have e1 := ih (X + h • basisVec i)
      have e2 := ih X
      simp only [cellValue] at e1 e2
      rw [e1, e2]

end AVRegularity.QuietDecay
end
end
end
