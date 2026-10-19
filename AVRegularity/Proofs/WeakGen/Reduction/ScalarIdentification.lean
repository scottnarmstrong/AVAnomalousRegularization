-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Reduction.ScalarForced
import AVRegularity.Applications.HeatReplacement.Main
import AVRegularity.Applications.LocalEnergy.Caccioppoli
import AVRegularity.Proofs.Transverse.ClassicalCell.Spatial
import AVRegularity.Proofs.WeakGen.Reduction.CoeffAllOrder

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The scalar identification**: the `L²` curve of a forced torus solution.

* `forced_l2_curve`: a forced torus solution has a continuous curve of `L²(cube)` classes equal
  to its slices at every time of the window. The continuous cutoff trace `W` of `forced_W` is
  identified with the cutoff slices at every time (`trace_rep`). The slices of a difference of two
  times have the norm of the difference of the traces (`trace_norm_sq` for the shifted family),
  so the `L²` curve is as continuous as `W`.
* `weakScalarL2AsH0_continuous`, `weakScalarL2AsH0_value_ae`: the order-zero torus class of an
  `L²` class is continuous in it and has it as value.

The `H¹` lift (the real form of `CycleEvolution.cellH1Slice`):
* `realSlice`: the spatial `L²` class at every time of a product-`L²` field, through a strongly
  measurable modification (`bochnerL2TotalSlice`); Bochner `L²` in time, and the literal slice
  class at almost every time.
* `realH1Slice`: the orthogonal projection onto the periodic `H¹` graph of the raw jet slices.
  It is Bochner `L²`, and it is the torus class of the raw jet at almost every time where that
  jet is a periodic weak jet.
* For a weak solution, the `H¹` lift of its first jet `(θ, Dθ)`. -/

open Applications

/-- **The continuous `L²` curve of a forced torus solution.** -/
theorem forced_l2_curve {w : ℝ → Vec 2 → ℝ} {Dw P : ℝ → Vec 2 → Vec 2} {g : ℝ → Vec 2 → ℝ}
    {t₁ t₂ : ℝ} (h12 : t₁ < t₂) (h : IsTorusForced w Dw P g t₁ t₂) :
    ∃ U : ℝ → Lp ℝ 2 (volume.restrict unitCube), ContinuousOn U (Set.Icc t₁ t₂) ∧
      ∀ τ ∈ Set.Icc t₁ t₂, (U τ : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] w τ := by
  classical
  obtain ⟨W, hWc, hWae, -⟩ := forced_W h12 h
  let U : ℝ → Lp ℝ 2 (volume.restrict unitCube) := fun τ =>
    if hτ : τ ∈ Set.Icc t₁ t₂ then (h.slice τ hτ).2.toLp (w τ) else 0
  have hU : ∀ τ (hτ : τ ∈ Set.Icc t₁ t₂), U τ = (h.slice τ hτ).2.toLp (w τ) :=
    fun τ hτ => dite_eq_left hτ
  have hUae : ∀ τ ∈ Set.Icc t₁ t₂, (U τ : Vec 2 → ℝ) =ᵐ[volume.restrict unitCube] w τ :=
    fun τ hτ => by rw [hU τ hτ]; exact (h.slice τ hτ).2.coeFn_toLp
  refine ⟨U, ?_, hUae⟩
  have hnorm : ∀ σ ∈ Set.Icc t₁ t₂, ∀ τ ∈ Set.Icc t₁ t₂, ‖U τ - U σ‖ = ‖W τ - W σ‖ := by
    intro σ hσ τ hτ
    have hrepσ := trace_rep h12 h.slice h.cont hWc hWae hσ
    let w' : ℝ → Vec 2 → ℝ := fun s x => w s x - w σ x
    have hslice' : ∀ s ∈ Set.Icc t₁ t₂, IsZ2Periodic (w' s) ∧ MemL2On unitCube (w' s) :=
      fun s hs => ⟨fun n x => by
        simp only [w', (h.slice s hs).1 n x, (h.slice σ hσ).1 n x], (h.slice s hs).2.sub
          (h.slice σ hσ).2⟩
    have hcont' : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
        ContinuousOn (fun s => ∫ x in unitCube, w' s x * ψ x) (Set.Icc t₁ t₂) := by
      intro ψ hψ hψp
      refine ((h.cont ψ hψ hψp).sub (continuousOn_const (c := ∫ x in unitCube, w σ x * ψ x))).congr
        fun s hs => ?_
      have i1 := integrable_mul_memL2 (h.slice s hs).2 (memL2_continuous hψ.continuous)
      have i2 := integrable_mul_memL2 (h.slice σ hσ).2 (memL2_continuous hψ.continuous)
      change ∫ x in unitCube, (w s x - w σ x) * ψ x =
        (∫ x in unitCube, w s x * ψ x) - ∫ x in unitCube, w σ x * ψ x
      rw [← integral_sub i1 i2]
      exact integral_congr_ae (Eventually.of_forall fun x => by ring)
    have hWc' : ContinuousOn (fun s => W s - W σ) (Set.Icc t₁ t₂) := hWc.sub continuousOn_const
    have hWae' : ∀ᵐ s ∂(volume.restrict (Set.Ioo t₁ t₂)),
        ((W s - W σ : Lp ℝ 2 (volume.restrict cutBall)) : Vec 2 → ℝ) =ᵐ[volume.restrict cutBall]
          fun y => cutoffZ y * w' s y := by
      filter_upwards [hWae] with s hs
      filter_upwards [hs, hrepσ, Lp.coeFn_sub (W s) (W σ)] with y h1 h2 h3
      rw [h3, Pi.sub_apply, h1, h2]
      simp only [w']
      ring
    have h1 := trace_norm_sq h12 hslice' hcont' hWc' hWae' hτ
    have h2 : ‖U τ - U σ‖ ^ 2 = l2NormSq (w' τ) := by
      rw [← LocalEnergy.integral_sq_lp]
      unfold l2NormSq
      refine integral_congr_ae ?_
      filter_upwards [Lp.coeFn_sub (U τ) (U σ), hUae τ hτ, hUae σ hσ] with x hx hxτ hxσ
      rw [hx, Pi.sub_apply, hxτ, hxσ]
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h2.trans h1.symm)
  intro σ hσ
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  obtain ⟨δ, hδ, hW⟩ := Metric.continuousWithinAt_iff.1 (hWc σ hσ) ε hε
  refine ⟨δ, hδ, fun τ hτ hd => ?_⟩
  rw [dist_eq_norm, hnorm σ hσ τ hτ, ← dist_eq_norm]
  exact hW hτ hd

/-- The order-zero torus class of an `L²` class depends continuously on it. -/
theorem weakScalarL2AsH0_continuous :
    Continuous (WeakEntryProofs.weakScalarL2AsH0 (E := ℝ)) := by
  apply Continuous.subtype_mk
  exact (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : JetIndex2 0 => Lp ℝ 2 (volume.restrict unitCube))).symm.continuous.comp
      (continuous_pi fun _ => continuous_id)

/-- The value of the order-zero torus class of an `L²` class is that class. -/
theorem weakScalarL2AsH0_value_ae (u : Lp ℝ 2 (volume.restrict unitCube)) :
    (WeakEntryProofs.weakScalarL2AsH0 u).toFunction.jet (valueIndex2 0)
      =ᵐ[volume.restrict unitCube] u :=
  periodicJetRepresentative_ae (WeakEntryProofs.weakScalarL2AsH0 u).val (valueIndex2 0)

/-! ### Step 3: the `H¹` lift -/

/-- Inject one spatial `L²` class into the first-order jet product (real scalars). -/
def realJetEntryCLM (a : JetIndex2 1) :
    Lp ℝ 2 (volume.restrict unitCube) →L[ℝ] JetL2 (volume.restrict unitCube) 1 ℝ :=
  let L : Lp ℝ 2 (volume.restrict unitCube) →ₗ[ℝ] JetL2 (volume.restrict unitCube) 1 ℝ :=
    { toFun := PiLp.single (β := fun _ : JetIndex2 1 => Lp ℝ 2 (volume.restrict unitCube)) 2 a
      map_add' := by
        intro x y
        exact PiLp.single_add (β := fun _ : JetIndex2 1 => Lp ℝ 2 (volume.restrict unitCube)) 2 a
      map_smul' := by
        intro r x
        apply PiLp.ext
        intro b
        by_cases h : b = a
        · subst b; simp
        · simp [h] }
  L.mkContinuous 1 (by
    intro x
    change ‖PiLp.single (β := fun _ : JetIndex2 1 =>
      Lp ℝ 2 (volume.restrict unitCube)) 2 a x‖ ≤ 1 * ‖x‖
    rw [PiLp.norm_single, one_mul])

open Classical in
/-- The spatial `L²` class at every time of a product-`L²` field, through a strongly measurable
modification; zero if the field is not product measurable. -/
def realSlice (I : Set ℝ) (f : ℝ → Vec 2 → ℝ) : ℝ → Lp ℝ 2 (volume.restrict unitCube) :=
  if hf : AEStronglyMeasurable (Function.uncurry f)
      ((volume.restrict I).prod (volume.restrict unitCube)) then
    CycleWords.bochnerL2TotalSlice (volume.restrict unitCube) (Function.curry (hf.mk _))
  else fun _ => 0

theorem realSlice_memLp (I : Set ℝ) (f : ℝ → Vec 2 → ℝ)
    (hf : MemLp (Function.uncurry f) 2 ((volume.restrict I).prod (volume.restrict unitCube))) :
    MemLp (realSlice I f) 2 (volume.restrict I) := by
  let : SecondCountableTopology (Lp ℝ 2 (volume.restrict unitCube)) := by
    let : Fact ((2 : ENNReal) ≠ ⊤) := ⟨by norm_num⟩
    exact Lp.SecondCountableTopology
  unfold realSlice
  rw [dite_eq_left hf.aestronglyMeasurable]
  exact CycleWords.bochnerL2TotalSlice_memLp _ _ _ hf.aestronglyMeasurable.stronglyMeasurable_mk
    (hf.ae_eq hf.aestronglyMeasurable.ae_eq_mk)

theorem realSlice_ae (I : Set ℝ) (f : ℝ → Vec 2 → ℝ)
    (hf : MemLp (Function.uncurry f) 2 ((volume.restrict I).prod (volume.restrict unitCube))) :
    ∀ᵐ t ∂(volume.restrict I), ∀ h : MemLp (f t) 2 (volume.restrict unitCube),
      realSlice I f t = h.toLp (f t) := by
  have hae := Measure.ae_ae_of_ae_prod hf.aestronglyMeasurable.ae_eq_mk
  filter_upwards [hae] with t ht h
  have hm : MemLp (Function.curry (hf.aestronglyMeasurable.mk _) t) 2 (volume.restrict unitCube) := h.ae_eq ht
  unfold realSlice
  rw [dite_eq_left hf.aestronglyMeasurable]
  have ht' : Function.curry (hf.aestronglyMeasurable.mk _) t =ᵐ[volume.restrict unitCube] f t :=
    ht.mono fun y hy => hy.symm
  exact Lp.ext ((CycleWords.bochnerL2TotalSlice_ae _ _ t hm).trans
    (ht'.trans h.coeFn_toLp.symm))

/-- The raw first-order jet slices. -/
def realRawJetSlices (I : Set ℝ) (D : ℝ → RawJet2 1 ℝ) (t : ℝ) :
    JetL2 (volume.restrict unitCube) 1 ℝ :=
  ∑ a : JetIndex2 1, realJetEntryCLM a (realSlice I (fun s x => D s a x) t)

/-- **The `H¹` lift**: the projection of the raw jet slices onto the periodic `H¹` graph. -/
def realH1Slice (I : Set ℝ) (D : ℝ → RawJet2 1 ℝ) (t : ℝ) : TorusHk 1 ℝ :=
  (torusHkGraph (E := ℝ) 1).toSubmodule.orthogonalProjectionOnto (realRawJetSlices I D t)

theorem realH1Slice_memLp (I : Set ℝ) (D : ℝ → RawJet2 1 ℝ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict unitCube))) :
    MemLp (realH1Slice I D) 2 (volume.restrict I) := by
  refine (torusHkGraph (E := ℝ) 1).toSubmodule.orthogonalProjectionOnto.comp_memLp' ?_
  apply memLp_finsetSum Finset.univ
  intro a _
  exact (realJetEntryCLM a).comp_memLp' (realSlice_memLp I (fun t x => D t a x) (hD a))

theorem realH1Slice_eq_toHk (I : Set ℝ) (D : ℝ → RawJet2 1 ℝ)
    (hD : ∀ a, MemLp (fun p : ℝ × Vec 2 => D p.1 a p.2) 2
      ((volume.restrict I).prod (volume.restrict unitCube))) :
    ∀ᵐ t ∂(volume.restrict I), ∀ ht : HasPeriodicOrderedWeakJet (D t),
      realH1Slice I D t = (TorusHkFunction.mk (D t) ht).toHk := by
  filter_upwards [ae_all_iff.2 fun a => realSlice_ae I (fun s x => D s a x) (hD a)] with t hts ht
  have hraw : realRawJetSlices I D t = torusJetToL2 (D t) ht.2.1 := by
    apply PiLp.ext
    intro a
    simp [realRawJetSlices, realJetEntryCLM, hts a (ht.2.1 a), torusJetToL2]
  unfold realH1Slice
  rw [hraw]
  exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self
    ((TorusHkFunction.mk (D t) ht).toHk)

/-- The jets of a promoted raw torus jet are the raw jets almost everywhere. -/
theorem toHk_jet_ae {K : ℕ} (F : TorusHkFunction K ℝ) (a : JetIndex2 K) :
    F.toHk.toFunction.jet a =ᵐ[volume.restrict unitCube] F.jet a :=
  (periodicJetRepresentative_ae F.toHk.val a).trans
    (torusJetToL2_ae F.jet F.hasPeriodicWeakJet.2.1 a)

/-- A product-window `L²` field is product `L²` for the product of the restricted measures. -/
theorem memLp_prod_of_window {g : ℝ × Vec 2 → ℝ} {s : Set ℝ}
    (h : MemLp g 2 (volume.restrict (s ×ˢ unitCube))) :
    MemLp g 2 ((volume.restrict s).prod (volume.restrict unitCube)) := by
  rwa [Measure.prod_restrict, ← Measure.volume_eq_prod]

/-- The first jets `(θ, Dθ)` of a weak solution are product `L²` on its window. -/
theorem weak_firstJet_memLp {b : ℝ → Vec 2 → Vec 2} {κ a T : ℝ} {f : Vec 2 → ℝ}
    {θ : ℝ → Vec 2 → ℝ} {Dθ : ℝ → Vec 2 → Vec 2} (h : IsWeakSolutionOnWith b κ a T f θ Dθ)
    (a' : JetIndex2 1) :
    MemLp (fun p : ℝ × Vec 2 => firstJet (θ p.1) (Dθ p.1) a' p.2) 2
      ((volume.restrict (Set.Ioo a T)).prod (volume.restrict unitCube)) := by
  by_cases h0 : a'.1 = (0 : Fin 2)
  · have e : (fun p : ℝ × Vec 2 => firstJet (θ p.1) (Dθ p.1) a' p.2) =
        fun p => θ p.1 p.2 := by
      funext p
      simp [firstJet, h0]
    rw [e]
    exact memLp_prod_of_window h.2.2.1
  · have e : (fun p : ℝ × Vec 2 => firstJet (θ p.1) (Dθ p.1) a' p.2) =
        fun p => Dθ p.1 p.2 (a'.2 ⟨0, Nat.pos_of_ne_zero (fun hv => h0 (Fin.ext hv))⟩) := by
      funext p
      simp [firstJet, h0]
    rw [e]
    exact memLp_prod_of_window (h.2.2.2.1 _)

end AVRegularity.Providers.WeakGen.Reduction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance Filter Topology
namespace AVRegularity.Providers.WeakGen.Reduction

/-! **The scalar identification, step 4**: the per-time identity for every `H¹` test,
and the identification.

* `window_pairing_bound`: product Cauchy–Schwarz for a window pairing against a time-independent
  test.
* `rawRHS` and its continuity (`rawRHS_sub_bound`): the time-integrated transport and diffusion
  terms of a weak solution, tested against `(φ, dφ)`. They are Lipschitz in the `L²` norms of the
  test.
* `raw_identity_extend`: the identity for every `H¹` test, from the identity for smooth periodic
  tests. The Galerkin projections of the test have smooth periodic jets
  (`galerkinProj_jet_ae_smooth`) and converge in `TorusHk 1` (`galerkinProj_tendsto`).
* `weak_smooth_identity`: the smooth-test identity of a weak solution on `[t₁, t]`
  (`weak_pairing_divergence`), with the endpoint `t = T` by continuity of both sides.
* `cwi_of_raw`: the coupled weak identity of a scalar torus trajectory from the raw identity, with
  gradient lifts equal to `Dθ` at almost every time.
* `weak_identification_core`, `weak_scalar_torus_identification`: the identification. Its pieces
  are the continuous `L²` curve (step 2), the `H¹` lift `realH1Slice` (step 3), and the identity for every
  test.
* `weak_scalar_smoothing` and `weak_entry_reduction plan (hcommon : WeakEntryCommonOK plan) :
  WeakEntryReductionStatement plan`. -/

open Applications WeakEntryProofs WeakEntryProofs.Assembly

/-- The product measure of a window and the cube. -/
abbrev winMeasure (t₁ t : ℝ) : Measure (ℝ × Vec 2) :=
  (volume.restrict (Set.Ioc t₁ t)).prod (volume.restrict unitCube)

instance (t₁ t : ℝ) : IsFiniteMeasure (volume.restrict (Set.Ioc t₁ t) : Measure ℝ) :=
  isFiniteMeasure_restrict.2 (by simp [Real.volume_Ioc])

/-- **Product Cauchy–Schwarz** for a window pairing against a time-independent test. -/
theorem window_pairing_bound {t₁ t : ℝ} (ht : t₁ ≤ t) {g : ℝ × Vec 2 → ℝ}
    (hg : MemLp g 2 (winMeasure t₁ t)) {φ : Vec 2 → ℝ} (hφ : MemL2On unitCube φ) :
    |∫ p, g p * φ p.2 ∂(winMeasure t₁ t)| ≤
      Real.sqrt ((∫ p, g p ^ 2 ∂(winMeasure t₁ t)) * ((t - t₁) * ∫ x in unitCube, φ x ^ 2)) := by
  have hφ2 : MemLp (fun p : ℝ × Vec 2 => φ p.2) 2 (winMeasure t₁ t) :=
    hφ.comp_snd (volume.restrict (Set.Ioc t₁ t))
  have h := HeatReplacement.abs_integral_mul_le hg hφ2
  have e : ∫ p, (φ p.2) ^ 2 ∂(winMeasure t₁ t) = (t - t₁) * ∫ x in unitCube, φ x ^ 2 := by
    rw [integral_prod (fun p : ℝ × Vec 2 => φ p.2 ^ 2) hφ2.integrable_sq]
    dsimp only
    rw [setIntegral_const, Real.volume_real_Ioc_of_le ht, smul_eq_mul]
  rwa [e] at h

variable {b : ℝ → Vec 2 → Vec 2} {Dθ : ℝ → Vec 2 → Vec 2} {κ t₁ t : ℝ}

/-- The time-integrated transport and diffusion terms of a weak solution, tested against a
time-independent `(φ, dφ)`. -/
def rawRHS (b : ℝ → Vec 2 → Vec 2) (Dθ : ℝ → Vec 2 → Vec 2) (κ t₁ t : ℝ) (φ : Vec 2 → ℝ)
    (dφ : Fin 2 → Vec 2 → ℝ) : ℝ :=
  ∫ s in Set.Ioc t₁ t, ∫ x in unitCube,
    (-(vecDot (b s x) (Dθ s x) * φ x) - κ * ∑ k : Fin 2, Dθ s x k * dφ k x)

/-- The transport density `−b·Dθ` is product `L²` for a bounded measurable drift. -/
theorem drift_density_memLp {B : ℝ} (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hB : ∀ s x, ‖b s x‖ ≤ B)
    (hD : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ t)) :
    MemLp (fun p : ℝ × Vec 2 => -vecDot (b p.1 p.2) (Dθ p.1 p.2)) 2 (winMeasure t₁ t) := by
  have hi : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => b p.1 p.2 k * Dθ p.1 p.2 k) 2
      (winMeasure t₁ t) := fun k => by
    have hm : MemLp (fun p : ℝ × Vec 2 => b p.1 p.2 k) ⊤ (winMeasure t₁ t) :=
      MemLp.of_bound ((measurable_pi_apply k).comp hbm).aestronglyMeasurable B
        (Eventually.of_forall fun p => (norm_le_pi_norm (b p.1 p.2) k).trans (hB p.1 p.2))
    exact hm.mul (hD k)
  have e : (fun p : ℝ × Vec 2 => -vecDot (b p.1 p.2) (Dθ p.1 p.2)) =
      fun p => -(b p.1 p.2 0 * Dθ p.1 p.2 0 + b p.1 p.2 1 * Dθ p.1 p.2 1) := by
    funext p
    simp [vecDot, Fin.sum_univ_two]
  rw [e]
  exact ((hi 0).add (hi 1)).neg

/-- The integrand of `rawRHS` on the product measure. -/
def rawDensity (b : ℝ → Vec 2 → Vec 2) (Dθ : ℝ → Vec 2 → Vec 2) (κ : ℝ) (φ : Vec 2 → ℝ)
    (dφ : Fin 2 → Vec 2 → ℝ) (p : ℝ × Vec 2) : ℝ :=
  -vecDot (b p.1 p.2) (Dθ p.1 p.2) * φ p.2 + ∑ k : Fin 2, (-κ * Dθ p.1 p.2 k) * dφ k p.2

theorem rawDensity_integrable {B : ℝ} (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hB : ∀ s x, ‖b s x‖ ≤ B)
    (hD : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ t))
    {φ : Vec 2 → ℝ} {dφ : Fin 2 → Vec 2 → ℝ} (hφ : MemL2On unitCube φ)
    (hdφ : ∀ k, MemL2On unitCube (dφ k)) :
    Integrable (rawDensity b Dθ κ φ dφ) (winMeasure t₁ t) := by
  have h0 := (drift_density_memLp (t₁ := t₁) (t := t) hbm hB hD).integrable_mul
    (hφ.comp_snd (volume.restrict (Set.Ioc t₁ t)))
  have hk : ∀ k : Fin 2, Integrable (fun p : ℝ × Vec 2 => (-κ * Dθ p.1 p.2 k) * dφ k p.2)
      (winMeasure t₁ t) := fun k =>
    ((hD k).const_mul (-κ)).integrable_mul ((hdφ k).comp_snd (volume.restrict (Set.Ioc t₁ t)))
  exact h0.add (integrable_finsetSum _ fun k _ => hk k)

/-- `rawRHS` is the product integral of `rawDensity`. -/
theorem rawRHS_eq_prod {B : ℝ} (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hB : ∀ s x, ‖b s x‖ ≤ B)
    (hD : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ t))
    {φ : Vec 2 → ℝ} {dφ : Fin 2 → Vec 2 → ℝ} (hφ : MemL2On unitCube φ)
    (hdφ : ∀ k, MemL2On unitCube (dφ k)) :
    rawRHS b Dθ κ t₁ t φ dφ = ∫ p, rawDensity b Dθ κ φ dφ p ∂(winMeasure t₁ t) := by
  rw [integral_prod _ (rawDensity_integrable hbm hB hD hφ hdφ)]
  unfold rawRHS rawDensity
  refine integral_congr_ae (Eventually.of_forall fun s => integral_congr_ae
    (Eventually.of_forall fun x => ?_))
  simp only [Finset.mul_sum]
  have e : ∀ k : Fin 2, -κ * Dθ s x k * dφ k x = -(κ * (Dθ s x k * dφ k x)) := fun k => by ring
  simp only [e, Finset.sum_neg_distrib]
  ring

/-- **`rawRHS` is Lipschitz in the test**: the difference at two tests is bounded by the `L²`
norms of the differences of the tests. -/
theorem rawRHS_sub_bound (ht : t₁ ≤ t) {B : ℝ}
    (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2)) (hB : ∀ s x, ‖b s x‖ ≤ B)
    (hD : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ t))
    {φ φ' : Vec 2 → ℝ} {dφ dφ' : Fin 2 → Vec 2 → ℝ} (hφ : MemL2On unitCube φ)
    (hφ' : MemL2On unitCube φ') (hdφ : ∀ k, MemL2On unitCube (dφ k))
    (hdφ' : ∀ k, MemL2On unitCube (dφ' k)) :
    |rawRHS b Dθ κ t₁ t φ dφ - rawRHS b Dθ κ t₁ t φ' dφ'| ≤
      Real.sqrt ((∫ p, (-vecDot (b p.1 p.2) (Dθ p.1 p.2)) ^ 2 ∂(winMeasure t₁ t)) *
          ((t - t₁) * ∫ x in unitCube, (φ x - φ' x) ^ 2)) +
        ∑ k : Fin 2, Real.sqrt ((∫ p, (-κ * Dθ p.1 p.2 k) ^ 2 ∂(winMeasure t₁ t)) *
          ((t - t₁) * ∫ x in unitCube, (dφ k x - dφ' k x) ^ 2)) := by
  have hφd : MemL2On unitCube (fun x => φ x - φ' x) := hφ.sub hφ'
  have hdφd : ∀ k, MemL2On unitCube (fun x => dφ k x - dφ' k x) := fun k => (hdφ k).sub (hdφ' k)
  have hdiff : rawRHS b Dθ κ t₁ t φ dφ - rawRHS b Dθ κ t₁ t φ' dφ' =
      ∫ p, rawDensity b Dθ κ (fun x => φ x - φ' x) (fun k x => dφ k x - dφ' k x) p
        ∂(winMeasure t₁ t) := by
    rw [rawRHS_eq_prod hbm hB hD hφ hdφ, rawRHS_eq_prod hbm hB hD hφ' hdφ',
      ← integral_sub (rawDensity_integrable hbm hB hD hφ hdφ)
        (rawDensity_integrable hbm hB hD hφ' hdφ')]
    refine integral_congr_ae (Eventually.of_forall fun p => ?_)
    simp only [rawDensity, Fin.sum_univ_two]
    ring
  have h0 : Integrable (fun p : ℝ × Vec 2 => -vecDot (b p.1 p.2) (Dθ p.1 p.2) * (φ p.2 - φ' p.2))
      (winMeasure t₁ t) := (drift_density_memLp (t₁ := t₁) (t := t) hbm hB hD).integrable_mul
    (hφd.comp_snd (volume.restrict (Set.Ioc t₁ t)))
  have hk : ∀ k : Fin 2, Integrable (fun p : ℝ × Vec 2 => (-κ * Dθ p.1 p.2 k) * (dφ k p.2 - dφ' k p.2))
      (winMeasure t₁ t) := fun k =>
    ((hD k).const_mul (-κ)).integrable_mul ((hdφd k).comp_snd (volume.restrict (Set.Ioc t₁ t)))
  have hsplit : ∫ p, rawDensity b Dθ κ (fun x => φ x - φ' x) (fun k x => dφ k x - dφ' k x) p
      ∂(winMeasure t₁ t) = (∫ p, -vecDot (b p.1 p.2) (Dθ p.1 p.2) * (φ p.2 - φ' p.2)
        ∂(winMeasure t₁ t)) + ∑ k : Fin 2, ∫ p, (-κ * Dθ p.1 p.2 k) * (dφ k p.2 - dφ' k p.2)
          ∂(winMeasure t₁ t) := by
    rw [← integral_finsetSum _ (fun k _ => hk k),
      ← integral_add h0 (integrable_finsetSum _ fun k _ => hk k)]
    rfl
  rw [hdiff, hsplit]
  refine (abs_add_le _ _).trans (add_le_add (window_pairing_bound ht
    (drift_density_memLp hbm hB hD) hφd) ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun k _ => ?_)
  exact window_pairing_bound ht ((hD k).const_mul (-κ)) (hdφd k)

/-- The `L²` distance of a torus jet to its Galerkin projections tends to zero. -/
theorem galerkin_jet_sq_tendsto (φ : TorusHk 1 ℝ) (a : JetIndex2 1) :
    Tendsto (fun N : ℕ => ∫ x in unitCube,
      (CoupledEnergy.Galerkin.smoothFourierJet (L := 1) N φ a x - φ.toFunction.jet a x) ^ 2)
      atTop (𝓝 0) := by
  have hc : Tendsto (fun N : ℕ => (CoupledEnergy.Galerkin.galerkinProj N φ).val.ofLp a) atTop
      (𝓝 (φ.val.ofLp a)) :=
    (((continuous_apply a).comp (PiLp.continuous_ofLp 2 _)).comp continuous_subtype_val).tendsto
      φ |>.comp (CoupledEnergy.Galerkin.galerkinProj_tendsto φ)
  have hn : Tendsto (fun N : ℕ => ‖(CoupledEnergy.Galerkin.galerkinProj N φ).val.ofLp a -
      φ.val.ofLp a‖ ^ 2) atTop (𝓝 0) := by
    have := (tendsto_iff_norm_sub_tendsto_zero.1 hc).pow 2
    simpa using this
  refine hn.congr fun N => ?_
  rw [← LocalEnergy.integral_sq_lp]
  refine integral_congr_ae ?_
  filter_upwards [Lp.coeFn_sub ((CoupledEnergy.Galerkin.galerkinProj N φ).val.ofLp a)
      (φ.val.ofLp a), CoupledEnergy.Galerkin.galerkinProj_jet_ae_smooth N φ a,
    periodicJetRepresentative_ae φ.val a] with x h1 h2 h3
  rw [h1, Pi.sub_apply, h2]
  change _ = (_ - periodicJetRepresentative φ.val a x) ^ 2
  rw [h3]

/-- **The raw identity for every `H¹` test**, from the identity for smooth periodic tests: the
Galerkin projections of the test are smooth periodic tests converging in `L²` with their first
derivatives, and both sides are Lipschitz in the test. -/
theorem raw_identity_extend (ht : t₁ ≤ t) {B : ℝ}
    (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2)) (hB : ∀ s x, ‖b s x‖ ≤ B)
    (hD : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ t))
    {u₀ u₁ : Vec 2 → ℝ} (hu₀ : MemL2On unitCube u₀) (hu₁ : MemL2On unitCube u₁)
    (hsmooth : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
      (∫ x in unitCube, u₀ x * ψ x) - ∫ x in unitCube, u₁ x * ψ x =
        rawRHS b Dθ κ t₁ t ψ (fun k x => spaceGrad ψ x k))
    (φ : TorusHk 1 ℝ) :
    (∫ x in unitCube, u₀ x * φ.toFunction.jet (valueIndex2 1) x) -
        ∫ x in unitCube, u₁ x * φ.toFunction.jet (valueIndex2 1) x =
      rawRHS b Dθ κ t₁ t (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) := by
  set φv := φ.toFunction.jet (valueIndex2 1) with hφv
  set φd : Fin 2 → Vec 2 → ℝ := fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
    with hφd
  let ψ : ℕ → Vec 2 → ℝ := fun N => CoupledEnergy.Galerkin.smoothFourierJet (L := 1) N φ
    (valueIndex2 1)
  let dψ : ℕ → Fin 2 → Vec 2 → ℝ := fun N k =>
    CoupledEnergy.Galerkin.smoothFourierJet (L := 1) N φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
  have hψs : ∀ N, ContDiff ℝ (⊤ : ℕ∞) (ψ N) := fun N =>
    CoupledEnergy.Galerkin.smoothFourierJet_contDiff N φ _
  have hdψs : ∀ N k, ContDiff ℝ (⊤ : ℕ∞) (dψ N k) := fun N k =>
    CoupledEnergy.Galerkin.smoothFourierJet_contDiff N φ _
  have hgrad : ∀ N, (fun k x => spaceGrad (ψ N) x k) = dψ N := fun N => by
    funext k x
    exact CoupledEnergy.Galerkin.smoothFourierJet_fderiv N φ (0 : Fin 1) Fin.elim0 k x
  have hidN : ∀ N, (∫ x in unitCube, u₀ x * ψ N x) - ∫ x in unitCube, u₁ x * ψ N x =
      rawRHS b Dθ κ t₁ t (ψ N) (dψ N) := fun N => by
    rw [← hgrad N]
    exact hsmooth (ψ N) (hψs N) (CoupledEnergy.Galerkin.smoothFourierJet_periodic N φ _)
  have hφvL : MemL2On unitCube φv := φ.toFunction.hasPeriodicWeakJet.2.1 _
  have hφdL : ∀ k, MemL2On unitCube (φd k) := fun k => φ.toFunction.hasPeriodicWeakJet.2.1 _
  have hψL : ∀ N, MemL2On unitCube (ψ N) := fun N => memL2_continuous (hψs N).continuous
  have hdψL : ∀ N k, MemL2On unitCube (dψ N k) := fun N k => memL2_continuous (hdψs N k).continuous
  have cv := galerkin_jet_sq_tendsto φ (valueIndex2 1)
  have cd : ∀ k : Fin 2, Tendsto (fun N : ℕ => ∫ x in unitCube, (dψ N k x - φd k x) ^ 2) atTop
      (𝓝 0) := fun k => galerkin_jet_sq_tendsto φ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩
  -- the left side converges
  have hL : Tendsto (fun N : ℕ => ((∫ x in unitCube, u₀ x * ψ N x) - ∫ x in unitCube, u₁ x * ψ N x)
      - ((∫ x in unitCube, u₀ x * φv x) - ∫ x in unitCube, u₁ x * φv x)) atTop (𝓝 0) := by
    have hb : ∀ N : ℕ, |((∫ x in unitCube, u₀ x * ψ N x) - ∫ x in unitCube, u₁ x * ψ N x)
        - ((∫ x in unitCube, u₀ x * φv x) - ∫ x in unitCube, u₁ x * φv x)| ≤
        (Real.sqrt (l2NormSq u₀) + Real.sqrt (l2NormSq u₁)) *
          Real.sqrt (∫ x in unitCube, (ψ N x - φv x) ^ 2) := fun N => by
      have hd := (hψL N).sub hφvL
      have e0 : (∫ x in unitCube, u₀ x * ψ N x) - ∫ x in unitCube, u₀ x * φv x =
          ∫ x in unitCube, u₀ x * (ψ N x - φv x) := by
        rw [← integral_sub (integrable_mul_memL2 hu₀ (hψL N)) (integrable_mul_memL2 hu₀ hφvL)]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      have e1 : (∫ x in unitCube, u₁ x * ψ N x) - ∫ x in unitCube, u₁ x * φv x =
          ∫ x in unitCube, u₁ x * (ψ N x - φv x) := by
        rw [← integral_sub (integrable_mul_memL2 hu₁ (hψL N)) (integrable_mul_memL2 hu₁ hφvL)]
        exact integral_congr_ae (Eventually.of_forall fun x => by ring)
      have h0 := abs_integral_mul_le_norms hu₀ hd
      have h1 := abs_integral_mul_le_norms hu₁ hd
      have e : ((∫ x in unitCube, u₀ x * ψ N x) - ∫ x in unitCube, u₁ x * ψ N x)
          - ((∫ x in unitCube, u₀ x * φv x) - ∫ x in unitCube, u₁ x * φv x) =
          (∫ x in unitCube, u₀ x * (ψ N x - φv x)) - ∫ x in unitCube, u₁ x * (ψ N x - φv x) := by
        rw [← e0, ← e1]; ring
      rw [e]
      calc _ ≤ |∫ x in unitCube, u₀ x * (ψ N x - φv x)| +
            |∫ x in unitCube, u₁ x * (ψ N x - φv x)| := abs_sub _ _
        _ ≤ Real.sqrt (l2NormSq u₀) * Real.sqrt (l2NormSq fun x => ψ N x - φv x) +
            Real.sqrt (l2NormSq u₁) * Real.sqrt (l2NormSq fun x => ψ N x - φv x) :=
          add_le_add h0 h1
        _ = _ := by unfold l2NormSq; ring
    have hlim : Tendsto (fun N : ℕ => (Real.sqrt (l2NormSq u₀) + Real.sqrt (l2NormSq u₁)) *
        Real.sqrt (∫ x in unitCube, (ψ N x - φv x) ^ 2)) atTop (𝓝 0) := by
      have := (Real.continuous_sqrt.tendsto 0).comp cv
      simpa using this.const_mul (Real.sqrt (l2NormSq u₀) + Real.sqrt (l2NormSq u₁))
    exact squeeze_zero_norm (fun N => by rw [Real.norm_eq_abs]; exact hb N) hlim
  -- the right side converges
  have hR : Tendsto (fun N : ℕ => rawRHS b Dθ κ t₁ t (ψ N) (dψ N) - rawRHS b Dθ κ t₁ t φv φd)
      atTop (𝓝 0) := by
    refine squeeze_zero_norm (fun N => (Real.norm_eq_abs _).trans_le
      (rawRHS_sub_bound ht hbm hB hD (hψL N) hφvL (hdψL N) hφdL)) ?_
    have hsq : ∀ (A : ℝ) (c : ℕ → ℝ), Tendsto c atTop (𝓝 0) →
        Tendsto (fun N => Real.sqrt (A * ((t - t₁) * c N))) atTop (𝓝 0) := by
      intro A c hc
      have h1 : Tendsto (fun N => A * ((t - t₁) * c N)) atTop (𝓝 0) := by
        simpa using (hc.const_mul (t - t₁)).const_mul A
      have h2 := (Real.continuous_sqrt.tendsto 0).comp h1
      rw [Real.sqrt_zero] at h2
      exact h2
    have := (hsq (∫ p, (-vecDot (b p.1 p.2) (Dθ p.1 p.2)) ^ 2 ∂(winMeasure t₁ t)) _ cv).add
      (tendsto_finsetSum Finset.univ fun k _ =>
        hsq (∫ p, (-κ * Dθ p.1 p.2 k) ^ 2 ∂(winMeasure t₁ t)) _ (cd k))
    simpa using this
  have hconst : Tendsto (fun N : ℕ => (rawRHS b Dθ κ t₁ t (ψ N) (dψ N) - rawRHS b Dθ κ t₁ t φv φd)
      - (((∫ x in unitCube, u₀ x * ψ N x) - ∫ x in unitCube, u₁ x * ψ N x)
        - ((∫ x in unitCube, u₀ x * φv x) - ∫ x in unitCube, u₁ x * φv x))) atTop (𝓝 0) := by
    simpa using hR.sub hL
  have heq : ∀ N : ℕ, (rawRHS b Dθ κ t₁ t (ψ N) (dψ N) - rawRHS b Dθ κ t₁ t φv φd)
      - (((∫ x in unitCube, u₀ x * ψ N x) - ∫ x in unitCube, u₁ x * ψ N x)
        - ((∫ x in unitCube, u₀ x * φv x) - ∫ x in unitCube, u₁ x * φv x)) =
      ((∫ x in unitCube, u₀ x * φv x) - ∫ x in unitCube, u₁ x * φv x) - rawRHS b Dθ κ t₁ t φv φd :=
    fun N => by rw [hidN N]; ring
  simp only [heq] at hconst
  exact sub_eq_zero.1 (tendsto_nhds_unique tendsto_const_nhds hconst)

/-- **The smooth-test identity on `[t₁, t]`**, including the endpoint `t = T`: the pairing
increment of a weak solution against a smooth periodic test is `rawRHS`. -/
theorem weak_smooth_identity {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {a T : ℝ}
    (hb : IsContDrift b) (h : IsWeakSolutionOnWith b κ a T f θ Dθ) (ht₁ : a ≤ t₁) (ht : t₁ ≤ t)
    (htT : t ≤ T) {ψ : Vec 2 → ℝ} (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψp : IsZ2Periodic ψ) :
    pairing θ ψ t - pairing θ ψ t₁ = rawRHS b Dθ κ t₁ t ψ (fun k x => spaceGrad ψ x k) := by
  let F : ℝ → ℝ := fun s => ∫ x in unitCube,
    (-(vecDot (b s x) (Dθ s x) * ψ x) - κ * vecDot (Dθ s x) (spaceGrad ψ x))
  have hraw : rawRHS b Dθ κ t₁ t ψ (fun k x => spaceGrad ψ x k) = ∫ s in t₁..t, F s := by
    rw [intervalIntegral.integral_of_le ht]
    rfl
  rw [hraw]
  have hlt : ∀ τ, t₁ ≤ τ → τ < T → pairing θ ψ τ - pairing θ ψ t₁ = ∫ s in t₁..τ, F s :=
    fun τ h1 h2 => weak_pairing_divergence hb h hψ hψp ht₁ h1 h2
  rcases lt_or_eq_of_le htT with htT' | rfl
  · exact hlt t ht htT'
  rcases lt_or_eq_of_le ht with ht' | rfl
  · obtain ⟨B, hB0, hBb⟩ := hb.bounded
    have hFi : IntegrableOn F (Set.Ioo a t) := by
      refine (incK_integrable hb h hψ hψp).congr_fun_ae ?_
      have hH1 := (ae_restrict_iff' measurableSet_Ioo).1 h.2.2.2.2.1
      rw [EventuallyEq, ae_restrict_iff' measurableSet_Ioo]
      filter_upwards [hH1] with s hs hsI
      exact incK_eq_divergence (hb.slice_continuous s) ⟨B, hB0, fun x => hBb s x⟩ (hb.periodic s)
        (hb.divFree s) κ (hs hsI) hψ hψp
    have hFi' : IntegrableOn F (Set.uIcc t₁ t) := by
      rw [Set.uIcc_of_le ht, integrableOn_Icc_iff_integrableOn_Ioo]
      exact hFi.mono_set (Set.Ioo_subset_Ioo_left ht₁)
    have hcL : ContinuousOn (fun τ => pairing θ ψ τ - pairing θ ψ t₁) (Set.Icc t₁ t) :=
      ((h.2.2.2.2.2.2.1 ψ hψ hψp).mono (Set.Icc_subset_Icc_left ht₁)).sub continuousOn_const
    have hcR : ContinuousOn (fun τ => ∫ s in t₁..τ, F s) (Set.Icc t₁ t) := by
      have := intervalIntegral.continuousOn_primitive_interval hFi'
      rwa [Set.uIcc_of_le ht] at this
    have heq : Set.EqOn (fun τ => pairing θ ψ τ - pairing θ ψ t₁) (fun τ => ∫ s in t₁..τ, F s)
        (Set.Ico t₁ t) := fun τ hτ => hlt τ hτ.1 hτ.2
    exact heq.of_subset_closure hcL hcR Set.Ico_subset_Icc_self
      (by rw [closure_Ico ht'.ne]) ⟨ht, le_rfl⟩
  · simp

/-- The inner integral of `rawRHS` at one time. -/
def rawSlice (b : ℝ → Vec 2 → Vec 2) (Dθ : ℝ → Vec 2 → Vec 2) (κ : ℝ) (φ : Vec 2 → ℝ)
    (dφ : Fin 2 → Vec 2 → ℝ) (s : ℝ) : ℝ :=
  ∫ x in unitCube, (-(vecDot (b s x) (Dθ s x) * φ x) - κ * ∑ k : Fin 2, Dθ s x k * dφ k x)

theorem rawSlice_integrableOn {B : ℝ} (hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2))
    (hB : ∀ s x, ‖b s x‖ ≤ B)
    (hD : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ t))
    {φ : Vec 2 → ℝ} {dφ : Fin 2 → Vec 2 → ℝ} (hφ : MemL2On unitCube φ)
    (hdφ : ∀ k, MemL2On unitCube (dφ k)) :
    IntegrableOn (rawSlice b Dθ κ φ dφ) (Set.Ioc t₁ t) := by
  refine (rawDensity_integrable (κ := κ) hbm hB hD hφ hdφ).integral_prod_left.congr
    (Eventually.of_forall fun s => integral_congr_ae (Eventually.of_forall fun x => ?_))
  simp only [rawDensity, Finset.mul_sum]
  have e : ∀ k : Fin 2, -κ * Dθ s x k * dφ k x = -(κ * (Dθ s x k * dφ k x)) := fun k => by ring
  simp only [e, Finset.sum_neg_distrib]
  ring

/-- **The coupled weak identity of a scalar torus trajectory from the raw identity**: gradient
lifts equal to `Dθ` at almost every time, a zero flux, and forcings vanishing almost
everywhere. -/
theorem cwi_of_raw (κ : ℝ) (hbc : Continuous (fun p : ℝ × Vec 2 => b p.1 p.2)) {B : ℝ}
    (hB : ∀ s x, ‖b s x‖ ≤ B)
    (hD : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ t))
    {u₀ u₁ φv : Vec 2 → ℝ} {φd : Fin 2 → Vec 2 → ℝ} (hu₀ : MemL2On unitCube u₀)
    (hu₁ : MemL2On unitCube u₁) (hφv : MemL2On unitCube φv) (hφd : ∀ k, MemL2On unitCube (φd k))
    {du : ℝ → Fin 2 → Vec 2 → ℝ} (hdu : ∀ s k, MemL2On unitCube (du s k))
    (hdu_ae : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₁ t)), ∀ k,
      du s k =ᵐ[volume.restrict unitCube] fun x => Dθ s x k)
    {flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => ℝ)} {g : ℝ → Vec 2 → ℝ}
    (hflux : ∀ s x, flux s x = 0) (hF0 : ∀ s, F s =ᵐ[volume.restrict unitCube] 0)
    (hg0 : ∀ s, g s =ᵐ[volume.restrict unitCube] 0)
    (hraw : (∫ x in unitCube, u₀ x * φv x) - ∫ x in unitCube, u₁ x * φv x =
      rawRHS b Dθ κ t₁ t φv φd) :
    CoupledWeakIdentity (volume.restrict unitCube) κ t₁ t b u₀ u₁ φv φd du flux F g := by
  have hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2) := hbc.measurable
  -- the right side at one time, almost everywhere in space
  let R : ℝ → Vec 2 → ℝ := fun s x =>
    -(∑ k : Fin 2, b s x k * inner ℝ (du s k x) (φv x))
      - κ * ∑ k : Fin 2, inner ℝ (du s k x) (φd k x)
      - ∑ k : Fin 2, inner ℝ (flux s x k + F s x k) (φd k x) + inner ℝ (g s x) (φv x)
  let R' : ℝ → Vec 2 → ℝ := fun s x =>
    -(∑ k : Fin 2, b s x k * (du s k x * φv x)) - κ * ∑ k : Fin 2, du s k x * φd k x
  have hRR' : ∀ s, R s =ᵐ[volume.restrict unitCube] R' s := fun s => by
    filter_upwards [hF0 s, hg0 s] with x hFx hgx
    simp only [R, R', Real.inner_apply, hflux s x, hFx, hgx, Pi.zero_apply,
      PiLp.zero_apply, zero_mul, Finset.sum_const_zero, sub_zero, add_zero]
  have hR'i : ∀ s, Integrable (R' s) (volume.restrict unitCube) := fun s => by
    have hbk : ∀ k : Fin 2, Integrable (fun x => b s x k * (du s k x * φv x))
        (volume.restrict unitCube) := fun k =>
      (integrable_mul_memL2 (hdu s k) hφv).bdd_mul
        ((continuous_apply k).comp (hbc.comp (continuous_const.prodMk continuous_id))).aestronglyMeasurable
        (Eventually.of_forall fun x => (norm_le_pi_norm (b s x) k).trans (hB s x))
    have hdk : ∀ k : Fin 2, Integrable (fun x => du s k x * φd k x) (volume.restrict unitCube) :=
      fun k => integrable_mul_memL2 (hdu s k) (hφd k)
    exact (integrable_finsetSum _ fun k _ => hbk k).neg.sub
      ((integrable_finsetSum _ fun k _ => hdk k).const_mul κ)
  have hslice : ∀ᵐ s ∂(volume.restrict (Set.Ioc t₁ t)),
      ∫ x in unitCube, R s x = rawSlice b Dθ κ φv φd s := by
    filter_upwards [hdu_ae] with s hs
    rw [integral_congr_ae (hRR' s)]
    unfold rawSlice
    refine integral_congr_ae ?_
    filter_upwards [ae_all_iff.2 hs] with x hx
    simp only [R', vecDot, Finset.sum_mul, hx]
    congr 2
    exact Finset.sum_congr rfl fun k _ => by ring
  have hint := rawSlice_integrableOn (κ := κ) hbm hB hD hφv hφd
  refine ⟨?_, ?_, fun s _ => (hR'i s).congr (hRR' s).symm, ?_, ?_⟩
  · simp only [Real.inner_apply]
    exact integrable_mul_memL2 hu₀ hφv
  · simp only [Real.inner_apply]
    exact integrable_mul_memL2 hu₁ hφv
  · exact hint.congr_fun_ae (hslice.mono fun s hs => hs.symm)
  · have e0 : ∫ x in unitCube, inner ℝ (u₀ x) (φv x) = ∫ x in unitCube, u₀ x * φv x := by
      simp only [Real.inner_apply]
    have e1 : ∫ x in unitCube, inner ℝ (u₁ x) (φv x) = ∫ x in unitCube, u₁ x * φv x := by
      simp only [Real.inner_apply]
    rw [e0, e1, hraw]
    exact (integral_congr_ae hslice).symm

/-- Two order-zero torus classes with the same value are equal. -/
theorem torusHk0_eq_of_value {x y : TorusHk 0 ℝ}
    (h : x.val.ofLp (valueIndex2 0) = y.val.ofLp (valueIndex2 0)) : x = y := by
  apply Subtype.ext
  apply PiLp.ext
  intro a
  obtain ⟨⟨j, hj⟩, w⟩ := a
  obtain rfl : j = 0 := by omega
  obtain rfl : w = Fin.elim0 := funext fun i => i.elim0
  exact h

/-- Periodic `H¹` data give a periodic ordered first jet. -/
theorem firstJet_hasPeriodicWeakJet {f : Vec 2 → ℝ} {Df : Vec 2 → Vec 2}
    (h : IsPeriodicH1With f Df) : HasPeriodicOrderedWeakJet (firstJet f Df) := by
  rcases h with ⟨hper, hDper, hf, hDf, hweak⟩
  exact ⟨firstJet_periodic f Df hper hDper, firstJet_memL2 f Df hf hDf,
    firstJet_hasWeakJet f Df hweak⟩

theorem restrict_Icc_le_Ioo {a t₁ T : ℝ} (h : a ≤ t₁) :
    (volume.restrict (Set.Icc t₁ T) : Measure ℝ) ≤ volume.restrict (Set.Ioo a T) := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Icc]
  exact Measure.restrict_mono (Set.Ioo_subset_Ioo_left h) le_rfl

theorem restrict_Ioc_le_Ioo {a t₁ t T : ℝ} (h : a ≤ t₁) (ht : t ≤ T) :
    (volume.restrict (Set.Ioc t₁ t) : Measure ℝ) ≤ volume.restrict (Set.Ioo a T) := by
  rw [← Measure.restrict_congr_set Ioo_ae_eq_Ioc]
  exact Measure.restrict_mono (Set.Ioo_subset_Ioo h ht) le_rfl

/-- **The identification for a continuous drift**: on `[t₁, T]`, `a < t₁ ≤ T`, a weak solution is
an order-zero solution of the scalar torus class from `θ(t₁)`, with values `θ(t)` at every time. -/
theorem weak_identification_core {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {a T : ℝ}
    (hb : IsContDrift b) (h : IsWeakSolutionOnWith b κ a T f θ Dθ) (ht₁ : a < t₁)
    (ht₁T : t₁ ≤ T) :
    ∃ (u : ℝ → TorusHk 0 ℝ) (w : ℝ → TorusHk 1 ℝ),
      WeakScalarTorusSolution κ t₁ T b 0 (u t₁) u w ∧
      ∀ t ∈ Set.Icc t₁ T,
        (u t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] θ t := by
  have haT : a < T := ht₁.trans_le ht₁T
  have hbc := hb.continuous
  have hbm : Measurable (fun p : ℝ × Vec 2 => b p.1 p.2) := hbc.measurable
  obtain ⟨B, -, hB⟩ := hb.bounded
  have hforced := isTorusForced_of_weakSolutionOnWith hbm ⟨B, fun t _ x => hB t x⟩
    (fun t _ => hb.periodic t) h
  obtain ⟨U, hUc, hUae⟩ := forced_l2_curve haT hforced
  let u : ℝ → TorusHk 0 ℝ := fun τ => WeakEntryProofs.weakScalarL2AsH0 (U τ)
  have huv : ∀ τ ∈ Set.Icc a T,
      (u τ).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube] θ τ :=
    fun τ hτ => (weakScalarL2AsH0_value_ae (U τ)).trans (hUae τ hτ)
  let D : ℝ → RawJet2 1 ℝ := fun τ => firstJet (θ τ) (Dθ τ)
  have hD := weak_firstJet_memLp h
  let w : ℝ → TorusHk 1 ℝ := realH1Slice (Set.Ioo a T) D
  have hle := restrict_Icc_le_Ioo (T := T) ht₁.le
  have hgood : ∀ᵐ s ∂(volume.restrict (Set.Ioo a T)), ∃ hs : IsPeriodicH1With (θ s) (Dθ s),
      w s = (TorusHkFunction.mk (D s) (firstJet_hasPeriodicWeakJet hs)).toHk := by
    filter_upwards [h.2.2.2.2.1, realH1Slice_eq_toHk (Set.Ioo a T) D hD] with s hs hw
    exact ⟨hs, hw _⟩
  have hwjet : ∀ s, (∃ hs : IsPeriodicH1With (θ s) (Dθ s),
      w s = (TorusHkFunction.mk (D s) (firstJet_hasPeriodicWeakJet hs)).toHk) →
      ∀ a', (w s).toFunction.jet a' =ᵐ[volume.restrict unitCube] firstJet (θ s) (Dθ s) a' := by
    rintro s ⟨hs, hws⟩ a'
    rw [hws]
    exact toHk_jet_ae _ a'
  refine ⟨u, w, ⟨fun _ => ?_, fun _ => ?_, fun _ => ?_, fun _ => rfl, fun _ τ hτ φ => ?_⟩,
    fun t ht => huv t ⟨ht₁.le.trans ht.1, ht.2⟩⟩
  · exact weakScalarL2AsH0_continuous.comp_continuousOn
      (hUc.mono (Set.Icc_subset_Icc_left ht₁.le))
  · exact (realH1Slice_memLp (Set.Ioo a T) D hD).mono_measure hle
  · filter_upwards [ae_mono hle hgood, ae_restrict_mem measurableSet_Icc] with s hsg hsI
    obtain ⟨hs, hws⟩ := hsg
    apply torusHk0_eq_of_value
    rw [truncateTorusHk_apply]
    apply Lp.ext
    have h1 : ((w s).val.ofLp (truncateJetIndex (Nat.le_succ 0) (valueIndex2 0)) : Vec 2 → ℝ)
        =ᵐ[volume.restrict unitCube] θ s := by
      rw [hws]
      exact (torusJetToL2_ae (D s) _ _).trans (Eventually.of_forall fun x => by
        simp [D, firstJet, truncateJetIndex, valueIndex2, valueIndex])
    exact h1.trans (hUae s ⟨ht₁.le.trans hsI.1, hsI.2⟩).symm
  · have hIoc := restrict_Ioc_le_Ioo (a := a) ht₁.le hτ.2
    have hD' : ∀ k : Fin 2, MemLp (fun p : ℝ × Vec 2 => Dθ p.1 p.2 k) 2 (winMeasure t₁ τ) :=
      fun k => (memLp_prod_of_window (h.2.2.2.1 k)).mono_measure (Measure.prod_mono hIoc le_rfl)
    have hu₀ : MemL2On unitCube ((u τ).toFunction.jet (valueIndex2 0)) :=
      (u τ).toFunction.hasPeriodicWeakJet.2.1 _
    have hu₁ : MemL2On unitCube ((u t₁).toFunction.jet (valueIndex2 0)) :=
      (u t₁).toFunction.hasPeriodicWeakJet.2.1 _
    have hsmooth : ∀ ψ : Vec 2 → ℝ, ContDiff ℝ (⊤ : ℕ∞) ψ → IsZ2Periodic ψ →
        (∫ x in unitCube, (u τ).toFunction.jet (valueIndex2 0) x * ψ x) -
          ∫ x in unitCube, (u t₁).toFunction.jet (valueIndex2 0) x * ψ x =
        rawRHS b Dθ κ t₁ τ ψ (fun k x => spaceGrad ψ x k) := by
      intro ψ hψ hψp
      rw [← weak_smooth_identity hb h ht₁.le hτ.1 hτ.2 hψ hψp]
      unfold pairing
      congr 1
      · exact integral_congr_ae ((huv τ ⟨ht₁.le.trans hτ.1, hτ.2⟩).mono fun x hx =>
          congrArg (· * ψ x) hx)
      · exact integral_congr_ae ((huv t₁ ⟨ht₁.le, ht₁T⟩).mono fun x hx =>
          congrArg (· * ψ x) hx)
    refine cwi_of_raw κ hbc hB hD' hu₀ hu₁ (φ.toFunction.hasPeriodicWeakJet.2.1 _)
      (fun k => φ.toFunction.hasPeriodicWeakJet.2.1 _)
      (fun s k => (w s).toFunction.hasPeriodicWeakJet.2.1 _) ?_ (fun s x => ?_)
      (fun s => torusHk_zero_jet_ae _ _) (fun s => torusHk_zero_jet_ae _ _)
      (raw_identity_extend hτ.1 hbm hB hD' hu₀ hu₁ hsmooth φ)
    · filter_upwards [ae_mono hIoc hgood] with s hs k
      exact (hwjet s hs _).trans (Eventually.of_forall fun x => by simp [firstJet])
    · simp

/-- **The single identification of scalar smoothing** (`WeakScalarTorusIdentificationStatement`). -/
theorem weak_scalar_torus_identification : WeakScalarTorusIdentificationStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ Λ hΛ Φ hΦ m hm κ hκ a T f θ hθ t₁ ht₁ ht₁T
  obtain ⟨Dθ, h⟩ := hθ
  exact weak_identification_core (streamSeq_isContDrift hζ hΛ hΦ m) h ht₁ ht₁T

/-- **Scalar smoothing** (`WeakScalarSmoothingStatement`). -/
theorem weak_scalar_smoothing : WeakScalarSmoothingStatement :=
  weak_scalar_smoothing_of_identification weak_scalar_torus_identification

/-- **The weak reduction** (`WeakEntryReductionStatement`) for every glue plan dominating the
common coefficient plan. -/
theorem weak_entry_reduction (plan : WeakEntryGluePlan) (hcommon : WeakEntryCommonOK plan) :
    WeakEntryReductionStatement plan :=
  weak_entry_reduction_of_identification plan hcommon weak_scalar_torus_identification

end AVRegularity.Providers.WeakGen.Reduction
end
