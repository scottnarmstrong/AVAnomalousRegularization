-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.PrimWeak
public import AVRegularity.CycleComparison.Reconstruction.CoarseDefectApprox
public import AVRegularity.Statements.Intermediate.CycleOutput.IsMeanPresentation
import AVRegularity.EntryWeak.WeakCarrierAppend
import AVRegularity.CycleComparison.Coarse.Defect.DFBound
import AVRegularity.CycleComparison.Coarse.Defect.Final
import Mathlib.Combinatorics.SimpleGraph.Basic

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev Filter Topology
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time continuity in `L²` from the weak identity.** A trajectory `U : ℝ → H¹(𝕋²)` that is
bounded in `H¹` on `[t_A, t_Z]` and satisfies the integrated weak identity from `t_A` to every
time of the interval, against every first-order test, with gradient, flux, forcing and source
bounded in `L²` of the cell by an integrable function of time, is continuous in time into `L²` of
the cell (`tendsto_cellL2_sub_of_weakIdentity`): test the difference of the identities at two
times with the difference of the values. With `continuousOn_periodicHk_of_L2` this gives the
clause `û ∈ C(I; H^K)` of the solution class for the physical lift. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H]
  [BorelSpace H] [CompleteSpace H]

omit [NormedAddCommGroup H] [InnerProductSpace ℝ H] [MeasurableSpace H] [BorelSpace H]
  [CompleteSpace H] in
/-- An interval integral is bounded by the interval integral of a pointwise bound, in absolute
value and for either order of the end points. -/
theorem abs_intervalIntegral_le_of_abs_le {f g : ℝ → ℝ} {a b : ℝ}
    (hg : IntervalIntegrable g volume a b) (h : ∀ σ ∈ Set.uIoc a b, |f σ| ≤ g σ) :
    |∫ σ in a..b, f σ| ≤ |∫ σ in a..b, g σ| := by
  have h1 := intervalIntegral.norm_integral_le_abs_of_norm_le (μ := volume) (f := f)
    ((ae_restrict_iff' measurableSet_uIoc).2 (Eventually.of_forall fun σ hσ =>
      (Real.norm_eq_abs _).trans_le (h σ hσ))) hg
  rwa [Real.norm_eq_abs] at h1

/-- **Time continuity in `L²` from the weak identity.** -/
theorem tendsto_cellL2_sub_of_weakIdentity {ν tA tZ : ℝ} (htAZ : tA ≤ tZ)
    (v : ℝ → Vec 2 → Vec 2) (Vb : ℝ)
    (hvm : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      AEStronglyMeasurable (fun x => v s x k) (volume.restrict AVenhance.unitCube))
    (hv : ∀ s ∈ Set.Ioc tA tZ, ∀ x k, |v s x k| ≤ Vb)
    (U : ℝ → TorusHk 1 H) {C₁ : ℝ} (hU : ∀ t ∈ Set.Icc tA tZ, ‖U t‖ ≤ C₁)
    (du : ℝ → Fin 2 → Vec 2 → H) (flux F : ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => H))
    (g : ℝ → Vec 2 → H) (C : ℝ → ℝ) (hC : IntegrableOn C (Set.Ioc tA tZ))
    (hdu : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (du s k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (du s k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hflux : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => flux s x k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hF : ∀ s ∈ Set.Ioc tA tZ, ∀ k,
      MemLp (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube) ∧
        (eLpNorm (fun x => F s x k) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hg : ∀ s ∈ Set.Ioc tA tZ, MemLp (g s) 2 (volume.restrict AVenhance.unitCube) ∧
      (eLpNorm (g s) 2 (volume.restrict AVenhance.unitCube)).toReal ≤ C s)
    (hid : ∀ t ∈ Set.Icc tA tZ, ∀ φ : TorusHk 1 H,
      CoupledWeakIdentity (volume.restrict AVenhance.unitCube) ν tA t v
        ((U t).toFunction.jet (valueIndex2 1)) ((U tA).toFunction.jet (valueIndex2 1))
        (φ.toFunction.jet (valueIndex2 1))
        (fun k => φ.toFunction.jet ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩) du flux F g) :
    ∀ t ∈ Set.Icc tA tZ, Tendsto (fun s => cellL2 (fun x =>
        (U s).toFunction.jet (valueIndex2 1) x - (U t).toFunction.jet (valueIndex2 1) x))
      (𝓝[Set.Icc tA tZ] t) (𝓝 0) := by
  intro t ht
  set Kc : ℝ := 2 * Vb + 2 * |ν| + 5 with hKc
  have hC₁ : 0 ≤ C₁ := (norm_nonneg _).trans (hU t ht)
  -- the tested time integrand and its bound
  have hB : ∀ σ ∈ Set.Ioc tA tZ, ∀ ψ : TorusHk 1 H,
      |∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x| ≤ Kc * C σ * ‖ψ‖ :=
    fun σ hσ ψ => (weakRhs_integrable_and_bound (hvm σ hσ) (hv σ hσ) (hdu σ hσ) (hflux σ hσ)
      (hF σ hσ) (hg σ hσ) (Coarse.memLp_jet ψ (valueIndex2 1))
      (Coarse.eLpNorm_jet_le ψ (valueIndex2 1))
      (fun k => Coarse.memLp_jet ψ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)
      (fun k => Coarse.eLpNorm_jet_le ψ ⟨⟨1, Nat.one_lt_two⟩, fun _ => k⟩)).2
  have hCi : IntervalIntegrable C volume tA tZ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le htAZ).2 hC
  have hRi : ∀ ψ : TorusHk 1 H, IntervalIntegrable
      (fun σ => ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x) volume tA tZ :=
    fun ψ => (intervalIntegrable_iff_integrableOn_Ioc_of_le htAZ).2
      (coupledWeakIdentity_iff.1 (hid tZ ⟨htAZ, le_rfl⟩ ψ)).2.2.2.1
  -- the pairing at a time of the interval as a primitive
  have hprim : ∀ s ∈ Set.Icc tA tZ, ∀ ψ : TorusHk 1 H,
      (∫ x in AVenhance.unitCube, inner ℝ ((U s).toFunction.jet (valueIndex2 1) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) =
      (∫ x in AVenhance.unitCube, inner ℝ ((U tA).toFunction.jet (valueIndex2 1) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) +
        ∫ σ in tA..s, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x := by
    intro s hs ψ
    have h := (coupledWeakIdentity_iff.1 (hid s hs ψ)).2.2.2.2
    rw [intervalIntegral.integral_of_le hs.1]
    have h' : (∫ x in AVenhance.unitCube, inner ℝ ((U s).toFunction.jet (valueIndex2 1) x)
        (ψ.toFunction.jet (valueIndex2 1) x)) -
        ∫ x in AVenhance.unitCube, inner ℝ ((U tA).toFunction.jet (valueIndex2 1) x)
          (ψ.toFunction.jet (valueIndex2 1) x) =
        ∫ σ in Set.Ioc tA s, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x := h
    linarith
  -- the primitive of the bound is continuous
  have hQ : ContinuousOn (fun x => ∫ σ in tA..x, C σ) (Set.Icc tA tZ) := by
    have h := intervalIntegral.continuousOn_primitive_interval (μ := volume) (f := C)
      (a := tA) (b := tZ) (by
        rw [Set.uIcc_of_le htAZ]
        exact hC.congr_set_ae Ioc_ae_eq_Icc.symm)
    rwa [Set.uIcc_of_le htAZ] at h
  have hGlim : Tendsto (fun s => Real.sqrt (|Kc| * (2 * C₁) *
      |(∫ σ in tA..s, C σ) - ∫ σ in tA..t, C σ|)) (𝓝[Set.Icc tA tZ] t) (𝓝 0) := by
    have h1 : Tendsto (fun s => (∫ σ in tA..s, C σ) - ∫ σ in tA..t, C σ)
        (𝓝[Set.Icc tA tZ] t) (𝓝 0) := by
      have := (hQ t ht).tendsto.sub_const (∫ σ in tA..t, C σ)
      simpa using this
    have h2 := (h1.abs.const_mul (|Kc| * (2 * C₁))).sqrt
    simpa using h2
  refine squeeze_zero' (Eventually.of_forall fun s => cellL2_nonneg _) ?_ hGlim
  filter_upwards [self_mem_nhdsWithin] with s hs
  -- test with the difference of the values
  set ψ : TorusHk 1 H := U s - U t with hψ
  have hψn : ‖ψ‖ ≤ 2 * C₁ := by
    refine (norm_sub_le _ _).trans ?_
    have h1 := hU s hs
    have h2 := hU t ht
    linarith
  have hd : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ψ.toFunction.jet (valueIndex2 1) x =
      (U s).toFunction.jet (valueIndex2 1) x - (U t).toFunction.jet (valueIndex2 1) x := by
    filter_upwards [Coarse.jet_sub_ae (U s) (U t)] with x hx
    exact hx (valueIndex2 1)
  have Ms := Coarse.memLp_jet (U s) (valueIndex2 1)
  have Mt := Coarse.memLp_jet (U t) (valueIndex2 1)
  have Mψ := Coarse.memLp_jet ψ (valueIndex2 1)
  have Md : MemLp (fun x => (U s).toFunction.jet (valueIndex2 1) x -
      (U t).toFunction.jet (valueIndex2 1) x) 2 (volume.restrict AVenhance.unitCube) :=
    Ms.sub Mt
  have hsq : cellL2 (fun x => (U s).toFunction.jet (valueIndex2 1) x -
      (U t).toFunction.jet (valueIndex2 1) x) ^ 2 =
      (∫ σ in tA..s, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x) -
        ∫ σ in tA..t, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x := by
    rw [← integral_inner_self_cell Md]
    have e1 : ∫ x in AVenhance.unitCube, inner ℝ ((U s).toFunction.jet (valueIndex2 1) x -
        (U t).toFunction.jet (valueIndex2 1) x) ((U s).toFunction.jet (valueIndex2 1) x -
        (U t).toFunction.jet (valueIndex2 1) x) =
        (∫ x in AVenhance.unitCube, inner ℝ ((U s).toFunction.jet (valueIndex2 1) x)
          (ψ.toFunction.jet (valueIndex2 1) x)) -
        ∫ x in AVenhance.unitCube, inner ℝ ((U t).toFunction.jet (valueIndex2 1) x)
          (ψ.toFunction.jet (valueIndex2 1) x) := by
      rw [← integral_sub (Coarse.integrable_inner_memLp Ms Mψ)
        (Coarse.integrable_inner_memLp Mt Mψ)]
      refine integral_congr_ae ?_
      filter_upwards [hd] with x hx
      rw [hx, inner_sub_left]
    rw [e1, hprim s hs ψ, hprim t ht ψ]
    ring
  have hint : (∫ σ in tA..s, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x) -
      (∫ σ in tA..t, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x) =
      ∫ σ in t..s, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x := by
    have hsub : ∀ {a b : ℝ}, a ∈ Set.Icc tA tZ → b ∈ Set.Icc tA tZ → IntervalIntegrable
        (fun σ => ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x) volume a b :=
      fun {a b} ha hb => (hRi ψ).mono_set (by
        rw [Set.uIcc_of_le htAZ]
        exact Set.uIcc_subset_Icc ha hb)
    exact intervalIntegral.integral_interval_sub_left (hsub ⟨le_rfl, htAZ⟩ hs)
      (hsub ⟨le_rfl, htAZ⟩ ht)
  have hCsub : IntervalIntegrable C volume t s := hCi.mono_set (by
    rw [Set.uIcc_of_le htAZ]
    exact Set.uIcc_subset_Icc ht hs)
  have hbound : |∫ σ in t..s, ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x| ≤
      |Kc| * (2 * C₁) * |(∫ σ in tA..s, C σ) - ∫ σ in tA..t, C σ| := by
    have h1 := abs_intervalIntegral_le_of_abs_le
      (f := fun σ => ∫ x in AVenhance.unitCube, testRhs ν v du flux F g ψ σ x)
      (g := fun σ => Kc * C σ * ‖ψ‖) ((hCsub.const_mul Kc).mul_const ‖ψ‖)
      (fun σ hσ => by
        refine hB σ ?_ ψ
        have hsub : Set.uIoc t s ⊆ Set.Ioc tA tZ := by
          intro y hy
          rcases le_total t s with hts | hst
          · rw [Set.uIoc_of_le hts] at hy
            exact ⟨lt_of_le_of_lt ht.1 hy.1, hy.2.trans hs.2⟩
          · rw [Set.uIoc_of_ge hst] at hy
            exact ⟨lt_of_le_of_lt hs.1 hy.1, hy.2.trans ht.2⟩
        exact hsub hσ)
    refine h1.trans ?_
    have e : (∫ σ in t..s, Kc * C σ * ‖ψ‖) = Kc * ‖ψ‖ * ∫ σ in t..s, C σ := by
      rw [← intervalIntegral.integral_const_mul]
      exact intervalIntegral.integral_congr fun σ _ => by ring
    have e2 : (∫ σ in t..s, C σ) = (∫ σ in tA..s, C σ) - ∫ σ in tA..t, C σ := by
      have hsub : ∀ {a b : ℝ}, a ∈ Set.Icc tA tZ → b ∈ Set.Icc tA tZ →
          IntervalIntegrable C volume a b := fun {a b} ha hb => hCi.mono_set (by
        rw [Set.uIcc_of_le htAZ]
        exact Set.uIcc_subset_Icc ha hb)
      exact (intervalIntegral.integral_interval_sub_left (hsub ⟨le_rfl, htAZ⟩ hs)
        (hsub ⟨le_rfl, htAZ⟩ ht)).symm
    rw [e, e2, abs_mul, abs_mul, abs_of_nonneg (norm_nonneg ψ)]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hψn (abs_nonneg _)) (abs_nonneg _)
  have hle : cellL2 (fun x => (U s).toFunction.jet (valueIndex2 1) x -
      (U t).toFunction.jet (valueIndex2 1) x) ^ 2 ≤
      |Kc| * (2 * C₁) * |(∫ σ in tA..s, C σ) - ∫ σ in tA..t, C σ| := by
    rw [hsq, hint]
    exact (le_abs_self _).trans hbound
  calc cellL2 (fun x => (U s).toFunction.jet (valueIndex2 1) x -
        (U t).toFunction.jet (valueIndex2 1) x)
      = Real.sqrt (cellL2 (fun x => (U s).toFunction.jet (valueIndex2 1) x -
          (U t).toFunction.jet (valueIndex2 1) x) ^ 2) :=
        (Real.sqrt_sq (cellL2_nonneg _)).symm
    _ ≤ _ := Real.sqrt_le_sqrt hle

end AVRegularity.CycleComparison.Reconstruction
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The time density of the finite-rank coarse approximants.** Let `aRep(s, ·)` be a classical
representative of the retained coarse field `W(s)` at an order `r₀ ≥ D` (`IsClassicalRep`). The
weak jets of `W(s)` entering the tested coarse defect identity (`coarseTestedRhs`) are then a.e.
the classical derivatives of `aRep(s, ·)`, so the tested right side is the pairing of the classical
field `g₁ = -𝐛·∇a + div Ξ` (`classicalDefectField`, with the classical total flux
`Ξ = ∑_{r ≤ H} F^{[r]} a`, `classicalTotalFlux`) with the test, minus the flux pairing of the
forcing `F_coarse`:

* (C4a) `coarseDefectFlux_ae_eq`: `B ∇W + flux(W) = Ξ` a.e. on the cell;
* (C4b) `coarseTestedRhs_integral_eq`: `∫ coarseTestedRhs ψ = ∫ ⟪g₁, ψ⟫ - ∫ ∑_j ⟪F_j, ∂_j ψ⟫`
  (periodic integration by parts of the `Ξ` term, `cell_ibp_div`);
* (C4c) `coarseCoeffDot_eq`: the same for the coefficient densities `ċ_r`;
* (C5) `coarseCoeffDot_synthesis`: `∑_r ċ_r e_r = a_n[g₁] + ∑_j ∂_j (S_n F_coarse)_j`, with the
  approximant of the classical field (`coarseProj_classical_eq`) and the divergence of the flux
  approximant (`coarseProj_div_eq`).

This is the finite-rank form of `(∂_t + 𝐛·∇ - 𝖩:D² - div F_A) a - E a = div F_coarse`.
-/

/-! ### The classical flux and the classical defect field -/

/-- The classical total flux `Ξ_v(x)_j = ∑_{r=0}^{H} (F^{[r]} a)_v(s, x)_j` of the coarse mean
equation applied to the classical coarse field `aRep`. -/
def classicalTotalFlux {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (aRep : ℝ → Vec 2 → ∀ i, h i) (s : ℝ) (v : ι)
    (x : Vec 2) (j : Fin 2) : h v :=
  ∑ r ∈ Finset.range (H + 1), classicalGradeFlux D r AD CE Jm aRep v s x j

/-- The classical field `g₁ = -∑_j b_j ∂_j a_v + ∑_j ∂_j Ξ_{v,j}`. -/
def classicalDefectField {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (b : ℝ → Vec 2 → Vec 2)
    (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (aRep : ℝ → Vec 2 → ∀ i, h i) (s : ℝ) (v : ι)
    (x : Vec 2) : h v :=
  -(∑ j : Fin 2, b s x j • fderiv ℝ (fun y => aRep s y v) x (basisVec j)) +
    ∑ j : Fin 2, fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j) x (basisVec j)

theorem classicalGradeFlux_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {v : ι} {t : ℝ}
    {x : Vec 2} {k : Fin 2} :
    classicalGradeFlux D 0 AD CE Jm a v t x k =
      (∑ l : Fin 2, Jm t k l • fderiv ℝ (fun y => a t y v) x (basisVec l)) +
        ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
          (AD d t x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) k) •
            orderedDerivative α (fun y => a t y v) x := by
  unfold classicalGradeFlux
  exact ite_eq_left rfl

theorem classicalGradeFlux_ne_zero {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D r : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {v : ι} {t : ℝ}
    {x : Vec 2} {k : Fin 2} (hr : r ≠ 0) :
    classicalGradeFlux D r AD CE Jm a v t x k =
      ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (CE r v u d t x (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a t y u) x)) k := by
  unfold classicalGradeFlux
  exact ite_eq_right hr

theorem sum_range_succ_eq_add_Icc {M : Type*} [AddCommMonoid M] (H : ℕ) (f : ℕ → M) :
    ∑ r ∈ Finset.range (H + 1), f r = f 0 + ∑ r ∈ Finset.Icc 1 H, f r := by
  have hs : Finset.range (H + 1) = insert 0 (Finset.Icc 1 H) := by
    ext r
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    constructor <;> intro hr <;> omega
  rw [hs, Finset.sum_insert (by rw [Finset.mem_Icc]; omega)]

/-- The classical total flux, grade `0` and grades `1, …, H` written out. -/
theorem classicalTotalFlux_eq {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {D H : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {a : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} {v : ι}
    {x : Vec 2} {j : Fin 2} :
    classicalTotalFlux D H AD CE Jm a s v x j =
      ((∑ l : Fin 2, Jm s j l • fderiv ℝ (fun y => a s y v) x (basisVec l)) +
        ∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
          (AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) •
            orderedDerivative α (fun y => a s y v) x) +
      ∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
        (CE r v u d s x (WithLp.toLp 2 fun α => orderedDerivative α (fun y => a s y u) x)) j := by
  unfold classicalTotalFlux
  rw [sum_range_succ_eq_add_Icc, classicalGradeFlux_zero]
  congr 1
  refine Finset.sum_congr rfl fun r hr => ?_
  exact classicalGradeFlux_ne_zero (by have := Finset.mem_Icc.1 hr; omega)

/-- The component `j` of the coarse defect flux, written out. -/
theorem coarseDefectFlux_apply {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {B : ℝ} {D H : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {K : ℕ} {W : ∀ v, ℝ → TorusHk K (h v)} {v : ι}
    {s : ℝ} {x : Vec 2} {j : Fin 2} :
    coarseDefectFlux B D H AD CE Jm W v s x j =
      (∑ l : Fin 2, (Jm s j l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) j l) •
          torusJetOrder (W v s) 1 (fun _ => l) x)
      + (∑ d : Finset.Icc 2 D, ∑ α : DerivativeWord2 (d.1 - 1),
          (AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ))) j) •
            torusJetOrder (W v s) (d.1 - 1) α x)
      + (∑ r ∈ Finset.Icc 1 H, ∑ u : ι, ∑ d : Finset.Icc 2 D,
          (CE r v u d s x (WithLp.toLp 2 fun α => torusJetOrder (W u s) (d.1 - 1) α x)) j) :=
  rfl

/-- `B ∂_j a + ∑_l (𝖩_{jl} - B δ_{jl}) ∂_l a = ∑_l 𝖩_{jl} ∂_l a`, with the remaining fluxes. -/
theorem coarseFlux_algebra {E : Type*} [AddCommGroup E] [Module ℝ E]
    (J : Matrix (Fin 2) (Fin 2) ℝ) (B : ℝ) (j : Fin 2) (X : Fin 2 → E) (S₂ S₃ : E) :
    B • X j + ((∑ l : Fin 2, (J j l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) j l) • X l) + S₂ + S₃) =
      ((∑ l : Fin 2, J j l • X l) + S₂) + S₃ := by
  have hδ : ∑ l : Fin 2, (B * (1 : Matrix (Fin 2) (Fin 2) ℝ) j l) • X l = B • X j := by
    rw [Finset.sum_eq_single j]
    · rw [Matrix.one_apply_eq, mul_one]
    · intro l _ hl
      rw [Matrix.one_apply_ne (Ne.symm hl), mul_zero, zero_smul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hsub : ∑ l : Fin 2, (J j l - B * (1 : Matrix (Fin 2) (Fin 2) ℝ) j l) • X l =
      ∑ l : Fin 2, J j l • X l - B • X j := by
    rw [← hδ, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun l _ => sub_smul _ _ _
  rw [hsub]
  abel

/-! ### Classical representatives: regularity and the a.e. jets -/

/-- A classical representative is `C^m` for `m ≤ r`. -/
theorem isClassicalRep_contDiff_of_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K r m : ℕ} {V : TorusHk K E}
    {a : Vec 2 → E} (ha : IsClassicalRep V a r) (hm : m ≤ r) : ContDiff ℝ (m : ℕ∞) a := by
  have hr : ContDiff ℝ (r : ℕ∞) a := ha.2.1
  exact hr.of_le (by exact_mod_cast hm)

/-- The coordinate derivatives of a classical representative at order `≥ 2` are `C¹`. -/
theorem classicalRep_partial_contDiff {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K r : ℕ}
    {V : TorusHk K E} {a : Vec 2 → E} (ha : IsClassicalRep V a r) (hr : 2 ≤ r) (l : Fin 2) :
    ContDiff ℝ 1 (fun x => fderiv ℝ a x (basisVec l)) := by
  have h := AVRegularity.ChartTransport.contDiff_orderedDerivative (p := 1) (fun _ : Fin 1 => l)
    (isClassicalRep_contDiff_of_le (m := 1 + 1) ha (by omega))
  rw [orderedDerivative_one_eq_fderiv] at h
  exact h

/-- The ordered derivatives of order `q` of a classical representative at order `≥ q + 1` are
`C¹`. -/
theorem classicalRep_word_contDiff {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] {K r q : ℕ} {V : TorusHk K E}
    {a : Vec 2 → E} (ha : IsClassicalRep V a r) (hq : q + 1 ≤ r) (α : DerivativeWord2 q) :
    ContDiff ℝ 1 (orderedDerivative α a) :=
  AVRegularity.ChartTransport.contDiff_orderedDerivative (p := 1) α
    (isClassicalRep_contDiff_of_le ha (by omega))

/-- A.e. on the cell, every jet of order `≤ r₀` of `W(s)` is the classical derivative of the
representative `aRep(s, ·)`. -/
theorem classicalRep_jets_ae {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {K r₀ : ℕ} {W : ∀ v, ℝ → TorusHk K (h v)} {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ}
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ u : ι, ∀ m : ℕ, m ≤ r₀ →
      ∀ w : DerivativeWord2 m,
        torusJetOrder (W u s) m w x = orderedDerivative w (fun y => aRep s y u) x := by
  rw [ae_all_iff]
  intro u
  rw [ae_all_iff]
  intro m
  by_cases hm : m ≤ r₀
  · filter_upwards [ae_all_iff.2 fun w => (ha u).2.2.2 m hm w] with x hx _ w
    exact hx w
  · exact ae_of_all _ fun x hm' => absurd hm' hm

/-- **(C4a)** A.e. on the cell, `B ∂_j W_v + flux_j(W)_v = Ξ_{v,j}`: the jets of `W(s)` are the
classical derivatives of `aRep(s, ·)` and `(𝖩 - B I)∇ + B∇ = 𝖩∇`. -/
theorem coarseDefectFlux_ae_eq {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {B : ℝ} {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (hD : 2 ≤ D) (hDr : D ≤ r₀)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀) (v : ι) :
    ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ j : Fin 2,
      B • torusJetOrder (W v s) 1 (fun _ => j) x + coarseDefectFlux B D H AD CE Jm W v s x j =
        classicalTotalFlux D H AD CE Jm aRep s v x j := by
  filter_upwards [classicalRep_jets_ae ha] with x hx j
  have h1 : ∀ (u : ι) (l : Fin 2), torusJetOrder (W u s) 1 (fun _ => l) x =
      fderiv ℝ (fun y => aRep s y u) x (basisVec l) := fun u l => by
    rw [hx u 1 (by omega) (fun _ => l), orderedDerivative_one_eq_fderiv]
  have hd : ∀ (u : ι) (d : Finset.Icc 2 D) (α : DerivativeWord2 (d.1 - 1)),
      torusJetOrder (W u s) (d.1 - 1) α x = orderedDerivative α (fun y => aRep s y u) x :=
    fun u d α => hx u (d.1 - 1) (by have := Finset.mem_Icc.1 d.2; omega) α
  rw [coarseDefectFlux_apply, classicalTotalFlux_eq]
  simp only [h1, hd]
  exact coarseFlux_algebra (Jm s) B j (fun l => fderiv ℝ (fun y => aRep s y v) x (basisVec l))
    _ _

/-! ### Regularity and periodicity of the classical flux -/

theorem classicalGradeFlux_contDiff {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (hD : 2 ≤ D) (hDr : D ≤ r₀)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s)) (v : ι) {r : ℕ}
    (hr : r ∈ Finset.range (H + 1)) (j : Fin 2) :
    ContDiff ℝ 1 (fun x => classicalGradeFlux D r AD CE Jm aRep v s x j) := by
  have hq : ∀ d : Finset.Icc 2 D, d.1 - 1 + 1 ≤ r₀ := fun d => by
    have := Finset.mem_Icc.1 d.2
    omega
  by_cases hr0 : r = 0
  · subst hr0
    simp only [classicalGradeFlux_zero]
    refine ContDiff.add (ContDiff.sum fun l _ => ?_)
      (ContDiff.sum fun d _ => ContDiff.sum fun α _ => ?_)
    · exact (classicalRep_partial_contDiff (ha v) (by omega) l).const_smul (Jm s j l)
    · have h1 : ContDiff ℝ 1 (fun x => AD d s x (WithLp.toLp 2 (Pi.single α (1 : ℝ)))) :=
        (hAD d).clm_apply contDiff_const
      exact ((contDiff_piLp 2).1 h1 j).fun_smul (classicalRep_word_contDiff (ha v) (hq d) α)
  · have hrI : r ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.2 ⟨by omega, by have := Finset.mem_range.1 hr; omega⟩
    simp only [classicalGradeFlux_ne_zero hr0]
    refine ContDiff.sum fun u _ => ContDiff.sum fun d _ => ?_
    have hw : ContDiff ℝ 1 (fun x => (WithLp.toLp 2
        (fun α : DerivativeWord2 (d.1 - 1) => orderedDerivative α (fun y => aRep s y u) x) :
        PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u))) :=
      (contDiff_piLp 2).2 fun α => classicalRep_word_contDiff (ha u) (hq d) α
    have hc : ContDiff ℝ 1 (fun x => CE r v u d s x (WithLp.toLp 2
        (fun α : DerivativeWord2 (d.1 - 1) => orderedDerivative α (fun y => aRep s y u) x))) :=
      (hCE r hrI v u d).clm_apply hw
    exact (contDiff_piLp 2).1 hc j

theorem classicalGradeFlux_periodic {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ}
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s)) (v : ι)
    {r : ℕ} (hr : r ∈ Finset.range (H + 1)) (j : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => classicalGradeFlux D r AD CE Jm aRep v s x j) := by
  intro z x
  have hX : ∀ (u : ι) (l : Fin 2),
      fderiv ℝ (fun y => aRep s y u) (x + AVenhance.latticeShift z) (basisVec l) =
        fderiv ℝ (fun y => aRep s y u) x (basisVec l) := fun u l =>
    AVRegularity.CycleComparison.Coarse.periodic_partial (ha u).2.2.1 l z x
  have hO : ∀ (u : ι) (m : ℕ) (α : DerivativeWord2 m),
      orderedDerivative α (fun y => aRep s y u) (x + AVenhance.latticeShift z) =
        orderedDerivative α (fun y => aRep s y u) x := fun u _ α =>
    AVRegularity.ChartTransport.isZ2Periodic_orderedDerivative α (ha u).2.2.1 z x
  by_cases hr0 : r = 0
  · subst hr0
    have hA : ∀ d, AD d s (x + AVenhance.latticeShift z) = AD d s x := fun d => hADp d z x
    simp only [classicalGradeFlux_zero, hX, hO, hA]
  · have hrI : r ∈ Finset.Icc 1 H :=
      Finset.mem_Icc.2 ⟨by omega, by have := Finset.mem_range.1 hr; omega⟩
    have hC : ∀ u d, CE r v u d s (x + AVenhance.latticeShift z) = CE r v u d s x :=
      fun u d => hCEp r hrI v u d z x
    simp only [classicalGradeFlux_ne_zero hr0, hO, hC]

theorem classicalTotalFlux_contDiff {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (hD : 2 ≤ D) (hDr : D ≤ r₀)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s)) (v : ι) (j : Fin 2) :
    ContDiff ℝ 1 (fun x => classicalTotalFlux D H AD CE Jm aRep s v x j) := by
  show ContDiff ℝ 1
    (fun x => ∑ r ∈ Finset.range (H + 1), classicalGradeFlux D r AD CE Jm aRep v s x j)
  exact ContDiff.sum fun r hr => classicalGradeFlux_contDiff hD hDr ha hAD hCE v hr j

theorem classicalTotalFlux_periodic {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ}
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s)) (v : ι)
    (j : Fin 2) :
    AVenhance.IsZ2Periodic (fun x => classicalTotalFlux D H AD CE Jm aRep s v x j) :=
  fun z x => by
    show ∑ r ∈ Finset.range (H + 1),
        classicalGradeFlux D r AD CE Jm aRep v s (x + AVenhance.latticeShift z) j =
      ∑ r ∈ Finset.range (H + 1), classicalGradeFlux D r AD CE Jm aRep v s x j
    exact Finset.sum_congr rfl fun r hr => classicalGradeFlux_periodic ha hADp hCEp v hr j z x

theorem classicalDefectField_continuous {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {b : ℝ → Vec 2 → Vec 2} {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (hD : 2 ≤ D) (hDr : D ≤ r₀)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hb : Continuous (b s)) (v : ι) :
    Continuous (classicalDefectField b D H AD CE Jm aRep s v) := by
  have hbj : ∀ j : Fin 2, Continuous (fun x => b s x j) := fun j => (continuous_apply j).comp hb
  have h1 : Continuous (fun x =>
      ∑ j : Fin 2, b s x j • fderiv ℝ (fun y => aRep s y v) x (basisVec j)) :=
    continuous_finsetSum _ fun j _ =>
      (hbj j).fun_smul (classicalRep_partial_contDiff (ha v) (by omega) j).continuous
  have h2 : Continuous (fun x => ∑ j : Fin 2,
      fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j) x (basisVec j)) :=
    continuous_finsetSum _ fun j _ =>
      cell_continuous_partial (classicalTotalFlux_contDiff hD hDr ha hAD hCE v j) j
  exact h1.fun_neg.fun_add h2

theorem classicalDefectField_periodic {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]
    {b : ℝ → Vec 2 → Vec 2} {D H K r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ}
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s))
    (hbp : AVenhance.IsZ2Periodic (b s)) (v : ι) :
    AVenhance.IsZ2Periodic (classicalDefectField b D H AD CE Jm aRep s v) := fun z x => by
  have hX : ∀ j : Fin 2,
      fderiv ℝ (fun y => aRep s y v) (x + AVenhance.latticeShift z) (basisVec j) =
        fderiv ℝ (fun y => aRep s y v) x (basisVec j) := fun j =>
    AVRegularity.CycleComparison.Coarse.periodic_partial (ha v).2.2.1 j z x
  have hΞ : ∀ j : Fin 2,
      fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j)
          (x + AVenhance.latticeShift z) (basisVec j) =
        fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j) x (basisVec j) :=
    fun j => AVRegularity.CycleComparison.Coarse.periodic_partial
      (classicalTotalFlux_periodic ha hADp hCEp v j) j z x
  simp only [classicalDefectField, hbp z x, hX, hΞ]

/-! ### (C4b), (C4c): the tested right side through the classical representative -/

theorem coarseTested_algebra {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (B : ℝ) (β : Fin 2 → ℝ) (T X Fl G Ξ P : Fin 2 → E) (ψ : E) (hT : ∀ j, T j = X j)
    (hΞ : ∀ j, B • T j + Fl j = Ξ j) :
    -(∑ j : Fin 2, β j * inner ℝ (T j) ψ) - B * ∑ j : Fin 2, inner ℝ (T j) (P j)
        - ∑ j : Fin 2, inner ℝ (Fl j + G j) (P j) =
      -(∑ j : Fin 2, β j * inner ℝ (X j) ψ) - ∑ j : Fin 2, inner ℝ (Ξ j) (P j)
        - ∑ j : Fin 2, inner ℝ (G j) (P j) := by
  have h1 : ∀ j, inner ℝ (Ξ j) (P j) = B * inner ℝ (X j) (P j) + inner ℝ (Fl j) (P j) :=
    fun j => by rw [← hΞ j, hT j, inner_add_left, real_inner_smul_left]
  simp only [hT, h1, inner_add_left, Finset.sum_add_distrib, Finset.mul_sum]
  ring

/-- **(C4b) The tested right side through the classical representative.** For a `C¹` periodic
test `ψ`: `∫ coarseTestedRhs ψ = ∫ ⟪g₁, ψ⟫ - ∫ ∑_j ⟪(F_coarse)_j, ∂_j ψ⟫`. -/
theorem coarseTestedRhs_integral_eq {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H K k r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (hD : 2 ≤ D) (hDr : D ≤ r₀)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s)) (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s))
    (hb : Continuous (b s)) (v : ι) (ψ : Vec 2 → h v) (hψ : ContDiff ℝ 1 ψ)
    (hψp : AVenhance.IsZ2Periodic ψ) :
    ∫ x in AVenhance.unitCube, coarseTestedRhs B b D H AD CE Jm W Fc v ψ s x =
      (∫ x in AVenhance.unitCube, inner ℝ (classicalDefectField b D H AD CE Jm aRep s v x) (ψ x)) -
        ∫ x in AVenhance.unitCube, ∑ j : Fin 2,
          inner ℝ ((Fc v s).toFunction.jet (valueIndex2 k) x j) (fderiv ℝ ψ x (basisVec j)) := by
  have hX : ∀ j : Fin 2, ContDiff ℝ 1 (fun x => fderiv ℝ (fun y => aRep s y v) x (basisVec j)) :=
    fun j => classicalRep_partial_contDiff (ha v) (by omega) j
  have hΞ : ∀ j : Fin 2, ContDiff ℝ 1 (fun x => classicalTotalFlux D H AD CE Jm aRep s v x j) :=
    fun j => classicalTotalFlux_contDiff hD hDr ha hAD hCE v j
  have hΞp : ∀ j : Fin 2,
      AVenhance.IsZ2Periodic (fun x => classicalTotalFlux D H AD CE Jm aRep s v x j) :=
    fun j => classicalTotalFlux_periodic ha hADp hCEp v j
  have hP : ∀ j : Fin 2, Continuous (fun x => fderiv ℝ ψ x (basisVec j)) :=
    fun j => cell_continuous_partial hψ j
  have hbj : ∀ j : Fin 2, Continuous (fun x => b s x j) := fun j => (continuous_apply j).comp hb
  have hF := (Fc v s).toFunction.hasPeriodicWeakJet.2.1 (valueIndex2 k)
  have hA : Integrable (fun x => -(∑ j : Fin 2,
      b s x j * inner ℝ (fderiv ℝ (fun y => aRep s y v) x (basisVec j)) (ψ x)))
      (volume.restrict AVenhance.unitCube) :=
    continuous_cell_integrable _ (Continuous.fun_neg (continuous_finsetSum _ fun j _ =>
      Continuous.fun_mul (hbj j) (Continuous.inner (hX j).continuous hψ.continuous)))
  have hS : Integrable (fun x => ∑ j : Fin 2,
      inner ℝ (classicalTotalFlux D H AD CE Jm aRep s v x j) (fderiv ℝ ψ x (basisVec j)))
      (volume.restrict AVenhance.unitCube) :=
    continuous_cell_integrable _ (continuous_finsetSum _ fun j _ =>
      Continuous.inner (hΞ j).continuous (hP j))
  have hG : Integrable (fun x => ∑ j : Fin 2,
      inner ℝ ((Fc v s).toFunction.jet (valueIndex2 k) x j) (fderiv ℝ ψ x (basisVec j)))
      (volume.restrict AVenhance.unitCube) :=
    integrable_finsetSum _ fun j _ => integrable_component_inner hF j (hP j)
  have hDψ : Integrable (fun x => inner ℝ (∑ j : Fin 2,
      fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j) x (basisVec j)) (ψ x))
      (volume.restrict AVenhance.unitCube) :=
    continuous_cell_integrable _ (Continuous.inner (continuous_finsetSum _ fun j _ =>
      cell_continuous_partial (hΞ j) j) hψ.continuous)
  have hibp : (∫ x in AVenhance.unitCube, inner ℝ (∑ j : Fin 2,
      fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j) x (basisVec j)) (ψ x)) =
      -∫ x in AVenhance.unitCube, ∑ j : Fin 2,
        inner ℝ (classicalTotalFlux D H AD CE Jm aRep s v x j) (fderiv ℝ ψ x (basisVec j)) :=
    cell_ibp_div hΞ hΞp hψ hψp
  have hg₁ : ∀ x, inner ℝ (classicalDefectField b D H AD CE Jm aRep s v x) (ψ x) =
      -(∑ j : Fin 2, b s x j * inner ℝ (fderiv ℝ (fun y => aRep s y v) x (basisVec j)) (ψ x)) +
        inner ℝ (∑ j : Fin 2, fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j)
          x (basisVec j)) (ψ x) := fun x => by
    rw [classicalDefectField, inner_add_left, inner_neg_left, sum_inner]
    simp only [real_inner_smul_left]
  have hae : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube),
      coarseTestedRhs B b D H AD CE Jm W Fc v ψ s x =
        -(∑ j : Fin 2, b s x j * inner ℝ (fderiv ℝ (fun y => aRep s y v) x (basisVec j)) (ψ x))
          - ∑ j : Fin 2, inner ℝ (classicalTotalFlux D H AD CE Jm aRep s v x j)
              (fderiv ℝ ψ x (basisVec j))
          - ∑ j : Fin 2, inner ℝ ((Fc v s).toFunction.jet (valueIndex2 k) x j)
              (fderiv ℝ ψ x (basisVec j)) := by
    filter_upwards [coarseDefectFlux_ae_eq (B := B) (H := H) (AD := AD) (CE := CE) (Jm := Jm)
      hD hDr ha v, classicalRep_jets_ae ha] with x hx hj
    have hT : ∀ j : Fin 2, torusJetOrder (W v s) 1 (fun _ => j) x =
        fderiv ℝ (fun y => aRep s y v) x (basisVec j) := fun j => by
      rw [hj v 1 (by omega) (fun _ => j), orderedDerivative_one_eq_fderiv]
    exact coarseTested_algebra B (fun j => b s x j) _ _ _ _ _ _ (ψ x) hT hx
  calc (∫ x in AVenhance.unitCube, coarseTestedRhs B b D H AD CE Jm W Fc v ψ s x)
      = ∫ x in AVenhance.unitCube,
          (-(∑ j : Fin 2,
            b s x j * inner ℝ (fderiv ℝ (fun y => aRep s y v) x (basisVec j)) (ψ x))
          - ∑ j : Fin 2, inner ℝ (classicalTotalFlux D H AD CE Jm aRep s v x j)
              (fderiv ℝ ψ x (basisVec j))
          - ∑ j : Fin 2, inner ℝ ((Fc v s).toFunction.jet (valueIndex2 k) x j)
              (fderiv ℝ ψ x (basisVec j))) := integral_congr_ae hae
    _ = (∫ x in AVenhance.unitCube, -(∑ j : Fin 2,
            b s x j * inner ℝ (fderiv ℝ (fun y => aRep s y v) x (basisVec j)) (ψ x)))
          - (∫ x in AVenhance.unitCube, ∑ j : Fin 2,
              inner ℝ (classicalTotalFlux D H AD CE Jm aRep s v x j) (fderiv ℝ ψ x (basisVec j)))
          - ∫ x in AVenhance.unitCube, ∑ j : Fin 2,
              inner ℝ ((Fc v s).toFunction.jet (valueIndex2 k) x j)
                (fderiv ℝ ψ x (basisVec j)) := by
        rw [integral_sub (hA.sub' hS) hG, integral_sub hA hS]
    _ = ((∫ x in AVenhance.unitCube, -(∑ j : Fin 2,
            b s x j * inner ℝ (fderiv ℝ (fun y => aRep s y v) x (basisVec j)) (ψ x)))
          + ∫ x in AVenhance.unitCube, inner ℝ (∑ j : Fin 2,
              fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm aRep s v y j) x (basisVec j))
              (ψ x))
          - ∫ x in AVenhance.unitCube, ∑ j : Fin 2,
              inner ℝ ((Fc v s).toFunction.jet (valueIndex2 k) x j)
                (fderiv ℝ ψ x (basisVec j)) := by
        rw [hibp]
        ring
    _ = (∫ x in AVenhance.unitCube,
            inner ℝ (classicalDefectField b D H AD CE Jm aRep s v x) (ψ x))
          - ∫ x in AVenhance.unitCube, ∑ j : Fin 2,
              inner ℝ ((Fc v s).toFunction.jet (valueIndex2 k) x j)
                (fderiv ℝ ψ x (basisVec j)) := by
        rw [← integral_add hA hDψ]
        exact congrArg (· - _) (integral_congr_ae (ae_of_all _ fun x => (hg₁ x).symm))

/-- **(C4c)** The coefficient density `ċ_r` of a coarse defect, through the classical
representative. -/
theorem coarseCoeffDot_eq {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H K k r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (hD : 2 ≤ D) (hDr : D ≤ r₀)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s)) (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s))
    (hb : Continuous (b s)) (n : ℕ) (r : CoupledFourierModeIndex (h := h) n) :
    coarseCoeffDot n B b D H AD CE Jm W Fc r s =
      (∫ x in AVenhance.unitCube, inner ℝ (classicalDefectField b D H AD CE Jm aRep s r.1 x)
          (coupledModeJet n r r.1 0 Fin.elim0 x)) -
        ∫ x in AVenhance.unitCube, ∑ j : Fin 2,
          inner ℝ ((Fc r.1 s).toFunction.jet (valueIndex2 k) x j)
            (fderiv ℝ (coupledModeJet n r r.1 0 Fin.elim0) x (basisVec j)) :=
  coarseTestedRhs_integral_eq hD hDr ha hAD hADp hCE hCEp hb r.1
    (coupledModeJet n r r.1 0 Fin.elim0)
    ((coupledModeJet_contDiff n r r.1 0 Fin.elim0).of_le (by exact_mod_cast le_top))
    (coupledModeJet_periodic n r r.1 0 Fin.elim0)

/-! ### (C5) The synthesis -/

/-- **(C5) The time density of the finite-rank approximant.** With `g₁ = -𝐛·∇a + div Ξ`
(`classicalDefectField`):
`∑_r ċ_r(s) e_r(x) = a_n[g₁](x) + ∑_j ∂_j (S_n F_coarse(s))_j(x)`. -/
theorem coarseCoeffDot_synthesis {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)] {B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H K k r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {s : ℝ} (hD : 2 ≤ D) (hDr : D ≤ r₀)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s)) (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s))
    (hb : Continuous (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (n : ℕ) (x : Vec 2) :
    ∑ r : CoupledFourierModeIndex (h := h) n,
        coarseCoeffDot n B b D H AD CE Jm W Fc r s • coarseMode n r x =
      coarseApprox n (fun v => periodicHk 0 (classicalDefectField b D H AD CE Jm aRep s v)
          (contDiff_zero_natCast (classicalDefectField_continuous hD hDr ha hAD hCE hb v))
          (classicalDefectField_periodic ha hADp hCEp hbp v)) x
        + fun v => ∑ j : Fin 2,
          fderiv ℝ (fun y => fluxApprox n (fun v => Fc v s) y j v) x (basisVec j) := by
  have hsplit : ∀ r : CoupledFourierModeIndex (h := h) n,
      coarseCoeffDot n B b D H AD CE Jm W Fc r s • coarseMode n r x =
        (∫ y in AVenhance.unitCube, inner ℝ (classicalDefectField b D H AD CE Jm aRep s r.1 y)
          (coupledModeJet n r r.1 0 Fin.elim0 y)) • coarseMode n r x +
        (-(∫ y in AVenhance.unitCube, ∑ j : Fin 2,
          inner ℝ ((Fc r.1 s).toFunction.jet (valueIndex2 k) y j)
            (fderiv ℝ (coupledModeJet n r r.1 0 Fin.elim0) y (basisVec j)))) •
          coarseMode n r x := fun r => by
    rw [coarseCoeffDot_eq hD hDr ha hAD hADp hCE hCEp hb n r, sub_eq_add_neg, add_smul]
  rw [Finset.sum_congr rfl fun r _ => hsplit r, Finset.sum_add_distrib,
    coarseProj_classical_eq n (classicalDefectField b D H AD CE Jm aRep s)
      (classicalDefectField_continuous hD hDr ha hAD hCE hb)
      (classicalDefectField_periodic ha hADp hCEp hbp) x,
    coarseProj_div_eq n (fun v => Fc v s) x]

/-! **The coarse defect field of a Galerkin approximant**. The finite-rank identity of the glued
lift (`glued_finiteRank_identity_closed`) lifts the coarse defect field of the approximant
`a_n = ∑_r c_r e_r`, `∑_r ċ_r e_r + 𝐛·∇a_n + ∑_{r ≤ H} 𝓜_r a_n`. With the mean presentation
`𝓜_r a = -div F^{[r]} a` (`IsMeanPresentation`) and the synthesis of the Galerkin coefficients
(`coarseCoeffDot_synthesis`: `∑_r ċ_r e_r = S_n g₁(aRep) + div S_n F_coarse`,
`g₁ = -𝐛·∇a + div Ξ`), it is the commutator remainder `e_n = S_n g₁(aRep) - g₁(a_n)` plus the
divergence of the flux approximant (`coarse_defect_split`). -/

section
variable {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)]

/-- The Galerkin projection `S_n g` of a family of continuous fields, as a field. -/
def coarseProjField (n : ℕ) (g : ∀ v, Vec 2 → h v) (x : Vec 2) : ∀ i, h i :=
  ∑ r : CoupledFourierModeIndex (h := h) n,
    (∫ y in AVenhance.unitCube, inner ℝ (g r.1 y) (coupledModeJet n r r.1 0 Fin.elim0 y)) •
      coarseMode n r x

/-- The finite-rank approximant `a_n(t) = ∑_r c_r(t) e_r` as a function of time. -/
def coarseTraj (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) (x : Vec 2) :
    ∀ i, h i :=
  ∑ r : CoupledFourierModeIndex (h := h) n, coarseCoeff n W r t • coarseMode n r x

/-- The divergence of the flux approximant `div S_n F_coarse(t)`. -/
def fluxApproxDiv (n : ℕ) {k : ℕ} (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v)))
    (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  fun v => ∑ j : Fin 2, fderiv ℝ (fun y => fluxApprox n (fun v => Fc v t) y j v) x (basisVec j)

theorem fluxApprox_component_contDiff (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (j : Fin 2) (v : ι) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => fluxApprox n Fc x j v) :=
  contDiff_pi.1 (fluxApprox_contDiff n Fc j) v

theorem fluxApprox_component_periodic (n : ℕ) {k : ℕ}
    (Fc : ∀ v, TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (j : Fin 2) (v : ι) :
    AVenhance.IsZ2Periodic (fun x => fluxApprox n Fc x j v) := fun z x =>
  congrFun (fluxApprox_periodic n Fc j z x) v

theorem fluxApproxDiv_contDiff (n : ℕ) {k : ℕ}
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (fluxApproxDiv n Fc t) :=
  contDiff_pi.2 fun v => ContDiff.sum fun j _ =>
    ((fluxApprox_component_contDiff n (fun v => Fc v t) j v).fderiv_right
      (m := (⊤ : ℕ∞)) (by simp)).clm_apply contDiff_const

theorem fluxApproxDiv_periodic (n : ℕ) {k : ℕ}
    (Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))) (t : ℝ) :
    AVenhance.IsZ2Periodic (fluxApproxDiv n Fc t) := fun z x => funext fun v => by
  simp only [fluxApproxDiv,
    fderiv_periodic (fluxApprox_component_periodic n (fun v => Fc v t) _ v) z x]

/-- The commutator remainder `e_n = S_n g₁(aRep) - g₁(a_n)`. -/
def defectRemainder (n : ℕ) (b : ℝ → Vec 2 → Vec 2) (D H : ℕ)
    (AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ))
    (CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v)))
    (Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v))
    (aRep : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (x : Vec 2) : ∀ i, h i :=
  coarseProjField n (classicalDefectField b D H AD CE Jm aRep t) x -
    fun v => classicalDefectField b D H AD CE Jm (coarseTraj n W) t v x

/-- The approximant is the Galerkin approximant of the trajectory. -/
theorem coarseTraj_eq (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) :
    coarseTraj n W t = coarseApprox n (fun v => W v t) :=
  funext fun x => (coarseApprox_eq_sum n W t x).symm

theorem coarseTraj_contDiff (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (coarseTraj n W t) :=
  ContDiff.sum fun r _ => (coarseMode_contDiff n r).const_smul _

theorem coarseTraj_periodic (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v)) (t : ℝ) :
    AVenhance.IsZ2Periodic (coarseTraj n W t) := fun z x => by
  simp only [coarseTraj, coarseMode_periodic n _ z x]

/-- The drift term of the approximant. -/
theorem coarseTraj_drift (n : ℕ) {K : ℕ} (W : ∀ v, ℝ → TorusHk K (h v)) (s : ℝ) (w x : Vec 2) :
    ∑ r : CoupledFourierModeIndex (h := h) n, coarseCoeff n W r s • fderiv ℝ (coarseMode n r) x w
      = fun v => ∑ j : Fin 2, w j • fderiv ℝ (fun y => coarseTraj n W s y v) x (basisVec j) := by
  funext v
  have hd : ∀ r : CoupledFourierModeIndex (h := h) n,
      DifferentiableAt ℝ (fun y => coarseCoeff n W r s • coarseMode n r y) x := fun r =>
    (((coarseMode_contDiff n r).differentiable (by simp)) x).fun_const_smul _
  have hcomp : ∀ (g : Vec 2 → ∀ i, h i), DifferentiableAt ℝ g x → ∀ u : Vec 2,
      fderiv ℝ (fun y => g y v) x u = fderiv ℝ g x u v := fun g hg u => by
    have := (ContinuousLinearMap.proj (R := ℝ) (φ := h) v).hasFDerivAt.comp x hg.hasFDerivAt
    show fderiv ℝ ((ContinuousLinearMap.proj (R := ℝ) (φ := h) v) ∘ g) x u = _
    rw [this.fderiv]
    rfl
  have hT : DifferentiableAt ℝ (coarseTraj n W s) x :=
    ((coarseTraj_contDiff n W s).differentiable (by simp)) x
  simp only [fun j => hcomp _ hT (basisVec j)]
  rw [Finset.sum_apply]
  have hsum : fderiv ℝ (coarseTraj n W s) x = ∑ r : CoupledFourierModeIndex (h := h) n,
      fderiv ℝ (fun y => coarseCoeff n W r s • coarseMode n r y) x := by
    have he : coarseTraj n W s = fun y => ∑ r : CoupledFourierModeIndex (h := h) n,
        coarseCoeff n W r s • coarseMode n r y := rfl
    rw [he, fderiv_fun_sum fun r _ => hd r]
  have hsm : ∀ r : CoupledFourierModeIndex (h := h) n,
      fderiv ℝ (fun y => coarseCoeff n W r s • coarseMode n r y) x =
        coarseCoeff n W r s • fderiv ℝ (coarseMode n r) x := fun r =>
    fderiv_fun_const_smul ((coarseMode_contDiff n r).differentiable (by simp) x) _
  have hw : w = ∑ j : Fin 2, w j • basisVec j := EntryWeakProofs.finite_vec_eq_sum_basis w
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, hsum, hsm,
    FunLike.coe_sum, FunLike.coe_smul, Finset.smul_sum]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun r _ =>
    smul_comm (coarseCoeff n W r s) (w j) (fderiv ℝ (coarseMode n r) x (basisVec j) v)

/-- **The coarse defect field of the approximant** is the commutator remainder plus the
divergence of the flux approximant. -/
theorem coarse_defect_split {B : ℝ} {b : ℝ → Vec 2 → Vec 2} {D H K k r₀ : ℕ}
    {AD : ∀ d : Finset.Icc 2 D, ℝ → Vec 2 →
      PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)}
    {CE : ℕ → ∀ (v u : ι) (d : Finset.Icc 2 D), ℝ → Vec 2 →
      (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h u)) →L[ℝ]
        (PiLp 2 (fun _ : Fin 2 => h v))}
    {Jm : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {W : ∀ v, ℝ → TorusHk K (h v)}
    {Fc : ∀ v, ℝ → TorusHk k (PiLp 2 (fun _ : Fin 2 => h v))}
    {aRep : ℝ → Vec 2 → ∀ i, h i} {I : Set ℝ}
    (M : ℕ → (ℝ → Vec 2 → ∀ i, h i) → ℝ → Vec 2 → ∀ i, h i)
    (hM : ∀ r ∈ Finset.range (H + 1), IsMeanPresentation I D r AD CE Jm (M r))
    {s : ℝ} (hs : s ∈ I) (hD : 2 ≤ D) (hDr : D ≤ r₀) (hrK : r₀ ≤ K)
    (ha : ∀ v, IsClassicalRep (W v s) (fun x => aRep s x v) r₀)
    (hAD : ∀ d, ContDiff ℝ 1 (AD d s)) (hADp : ∀ d, AVenhance.IsZ2Periodic (AD d s))
    (hCE : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, ContDiff ℝ 1 (CE r v u d s))
    (hCEp : ∀ r ∈ Finset.Icc 1 H, ∀ v u d, AVenhance.IsZ2Periodic (CE r v u d s))
    (hb : Continuous (b s)) (hbp : AVenhance.IsZ2Periodic (b s)) (n : ℕ) (x : Vec 2) :
    (∑ r : CoupledFourierModeIndex (h := h) n,
        coarseCoeffDot n B b D H AD CE Jm W Fc r s • coarseMode n r x +
      ∑ r : CoupledFourierModeIndex (h := h) n,
        coarseCoeff n W r s • fderiv ℝ (coarseMode n r) x (b s x)) +
      ∑ r ∈ Finset.range (H + 1), M r (coarseTraj n W) s x =
    defectRemainder n b D H AD CE Jm W aRep s x + fluxApproxDiv n Fc s x := by
  -- the synthesis of the Galerkin coefficients
  have h5 := coarseCoeffDot_synthesis (B := B) (Jm := Jm) (Fc := Fc) hD hDr ha hAD hADp hCE hCEp
    hb hbp n x
  rw [← coarseProj_classical_eq n (classicalDefectField b D H AD CE Jm aRep s)
    (classicalDefectField_continuous hD hDr ha hAD hCE hb)
    (classicalDefectField_periodic ha hADp hCEp hbp) x] at h5
  -- the classical representative of the approximant
  have haN : ∀ v, IsClassicalRep (galerkinProj n (W v s)) (fun x => coarseTraj n W s x v) r₀ :=
    fun v => by
      rw [coarseTraj_eq]
      exact coarseApprox_isClassicalRep n (fun v => W v s) v hrK
  -- the mean presentation
  have hmean : ∑ r ∈ Finset.range (H + 1), M r (coarseTraj n W) s x = fun v =>
      -∑ j : Fin 2, fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm (coarseTraj n W) s v y j) x
        (basisVec j) := by
    funext v
    rw [Finset.sum_apply]
    have hr : ∀ r ∈ Finset.range (H + 1), M r (coarseTraj n W) s x v =
        -∑ j : Fin 2, fderiv ℝ (fun y => classicalGradeFlux D r AD CE Jm (coarseTraj n W) v s y j)
          x (basisVec j) := fun r hr =>
      hM r hr (coarseTraj n W) (coarseTraj_contDiff n W) (coarseTraj_periodic n W) s hs x v
    rw [Finset.sum_congr rfl hr, Finset.sum_neg_distrib]
    congr 1
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hdj : ∀ r ∈ Finset.range (H + 1), DifferentiableAt ℝ
        (fun y => classicalGradeFlux D r AD CE Jm (coarseTraj n W) v s y j) x := fun r hr =>
      ((classicalGradeFlux_contDiff (W := fun v s => galerkinProj n (W v s)) hD hDr haN hAD hCE
        v hr j).differentiable one_ne_zero) x
    show _ = fderiv ℝ (fun y => ∑ r ∈ Finset.range (H + 1),
      classicalGradeFlux D r AD CE Jm (coarseTraj n W) v s y j) x (basisVec j)
    rw [fderiv_fun_sum hdj, sum_apply]
  have hcp : (∑ r : CoupledFourierModeIndex (h := h) n,
      (∫ y in AVenhance.unitCube, inner ℝ (classicalDefectField b D H AD CE Jm aRep s r.1 y)
        (coupledModeJet n r r.1 0 Fin.elim0 y)) • coarseMode n r x) =
      coarseProjField n (classicalDefectField b D H AD CE Jm aRep s) x := rfl
  rw [hcp] at h5
  rw [h5, coarseTraj_drift n W s (b s x) x, hmean]
  funext v
  have hg : classicalDefectField b D H AD CE Jm (coarseTraj n W) s v x =
      -(∑ j : Fin 2, b s x j • fderiv ℝ (fun y => coarseTraj n W s y v) x (basisVec j)) +
        ∑ j : Fin 2, fderiv ℝ (fun y => classicalTotalFlux D H AD CE Jm (coarseTraj n W) s v y j)
          x (basisVec j) := rfl
  simp only [defectRemainder, fluxApproxDiv, Pi.add_apply, Pi.sub_apply]
  rw [hg]
  abel
end

end AVRegularity.CycleComparison.Reconstruction
end
