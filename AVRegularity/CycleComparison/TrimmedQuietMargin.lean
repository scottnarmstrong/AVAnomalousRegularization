-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleComparison.IsLiftSequence
import AVRegularity.CycleJoint.ActivePieceDimensionalSmooth
public import AVRegularity.Statements.Intermediate.Families.ChartedFamilyIsFastIndependentOn
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleJoint.OcTrimmedQuietTimes
import AVRegularity.Construction.Stream.NextAdmissible

@[expose] public section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity

/-! The coefficientwise cell mean of a classical finite-past cell inverse is zero. -/

theorem fieldCellMean_eq_zero_of_IsCellFieldInverse
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (G : ℝ → Matrix (Fin 2) (Fin 2) ℝ) (v : ℝ → Vec 2 → Vec 2)
    (sZ : ℕ) (t₀ t₁ : ℝ) (g c : ℝ → Vec 2 → E)
    (hc : IsCellFieldInverse (fun t => G t) v sZ t₀ t₁ (fun _ => 0) g c)
    {t : ℝ} (ht : t ∈ Set.Icc t₀ t₁) :
    fieldCellMean (c t) = 0 := by
  have hcont : Continuous (c t) := (hc.1 t ht).continuous
  have hint : IntegrableOn (c t) (AVenhance.Infra.Torus.unitCell 2) :=
    AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell hcont
  let m : E := ∫ z in AVenhance.Infra.Torus.unitCell 2, c t z
  have hdual : ∀ ℓ : E →L[ℝ] ℝ, ℓ m = 0 := by
    intro ℓ
    have hmean := (hc.2 ℓ).2.1 t ht
    have hmeanCube :
        (∫ z in AVenhance.unitCube, ((ℓ (c t z) : ℝ) : ℂ)) = 0 := by
      simpa [cellMean, cellValue, cellJetOfField, valueIndex2, valueIndex] using hmean
    have hmeanCell :
        (∫ z in AVenhance.Infra.Torus.unitCell 2,
          ((ℓ (c t z) : ℝ) : ℂ)) = 0 := by
      rw [AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
      exact hmeanCube
    have hreal : (∫ z in AVenhance.Infra.Torus.unitCell 2, ℓ (c t z)) = 0 := by
      apply Complex.ofReal_injective
      calc
        ((∫ z in AVenhance.Infra.Torus.unitCell 2, ℓ (c t z) : ℝ) : ℂ) =
            ∫ z in AVenhance.Infra.Torus.unitCell 2, ((ℓ (c t z) : ℝ) : ℂ) := by
          simp only [integral_complex_ofReal]
        _ = 0 := hmeanCell
    have hmap := ℓ.integral_comp_comm hint
    change ℓ (∫ z in AVenhance.Infra.Torus.unitCell 2, c t z) = 0
    rw [← hmap]
    exact hreal
  have hm : m = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero hdual
  change (∫ z in AVenhance.unitCube, c t z) = 0
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  exact hm

theorem fieldCellMean_fastPartial_eq_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
    (f : Vec 2 → E) (hf : ContDiff ℝ 1 f)
    (hper : AVenhance.IsZ2Periodic f) (k : Fin 2) :
    fieldCellMean (fun z => fderiv ℝ f z (basisVec k)) = 0 := by
  let g : Vec 2 → E := fun z => fderiv ℝ f z (basisVec k)
  have hgcont : Continuous g := by
    dsimp [g]
    exact (hf.continuous_fderiv (by norm_num)).clm_apply continuous_const
  have hgint : IntegrableOn g (AVenhance.Infra.Torus.unitCell 2) :=
    AVenhance.Infra.Torus.Calculus.continuous_integrableOn_unitCell hgcont
  let m : E := ∫ z in AVenhance.Infra.Torus.unitCell 2, g z
  have hdual : ∀ ℓ : E →L[ℝ] ℝ, ℓ m = 0 := by
    intro ℓ
    let q : Vec 2 → ℂ := fun z => (ℓ (f z) : ℂ)
    have hscalar : ContDiff ℝ 1 (fun z => ℓ (f z)) := ℓ.contDiff.comp hf
    have hq : ContDiff ℝ 1 q := by
      exact Complex.ofRealCLM.contDiff.comp hscalar
    have hqper : AVenhance.Infra.Torus.IsZdPeriodic q := by
      apply (AVenhance.Infra.Torus.isZdPeriodic_iff_frozen q).2
      intro n z
      simp [q, hper n z]
    have hqderiv (z : Vec 2) :
        AVenhance.Infra.Torus.coordDeriv k q z = ((ℓ (g z) : ℝ) : ℂ) := by
      have hsecond := fderiv_comp z ℓ.differentiableAt
        (hf.differentiable (by norm_num) z)
      have hsecond' :
          fderiv ℝ (fun y => ℓ (f y)) z =
            fderiv ℝ (⇑ℓ) (f z) ∘SL fderiv ℝ f z := by
        change fderiv ℝ (⇑ℓ ∘ f) z = _
        exact hsecond
      change fderiv ℝ (Complex.ofRealCLM ∘ (fun y => ℓ (f y))) z (basisVec k) = _
      rw [fderiv_comp z Complex.ofRealCLM.differentiableAt
        (hscalar.differentiable (by norm_num) z)]
      rw [hsecond']
      simp [g, Complex.ofRealCLM.fderiv, ℓ.fderiv]
    have hcomplex :
        (∫ z in AVenhance.Infra.Torus.unitCell 2, ((ℓ (g z) : ℝ) : ℂ)) = 0 := by
      calc
        _ = ∫ z in AVenhance.Infra.Torus.unitCell 2,
              AVenhance.Infra.Torus.coordDeriv k q z := by
            apply integral_congr_ae
            filter_upwards with z
            exact (hqderiv z).symm
        _ = 0 :=
          AVenhance.Infra.Torus.integral_unitCell_coord_deriv_eq_zero k hq hqper
    have hreal : (∫ z in AVenhance.Infra.Torus.unitCell 2, ℓ (g z)) = 0 := by
      apply Complex.ofReal_injective
      have hcast :
          ((∫ z in AVenhance.Infra.Torus.unitCell 2, ℓ (g z) : ℝ) : ℂ) = 0 := by
        simpa only [integral_complex_ofReal] using hcomplex
      exact hcast
    have hmap := ℓ.integral_comp_comm hgint
    change ℓ (∫ z in AVenhance.Infra.Torus.unitCell 2, g z) = 0
    rw [← hmap]
    exact hreal
  have hm : m = 0 := SeparatingDual.eq_zero_of_forall_dual_eq_zero hdual
  change (∫ z in AVenhance.unitCube, g z) = 0
  rw [← AVenhance.Infra.Torus.integral_unitCell_eq_unitCube]
  exact hm

theorem liftApply_fieldCellMean_eq_zero
    {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, CompleteSpace (h i)]
    {D : ℕ} (Q : LiftOperatorData ι h D) (sX sZ : ℕ)
    (t₀ t₁ : ℝ) (N H : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n) (hN : n ≤ N)
    (a₀ : Vec 2 → ∀ i, h i) (ha : ContDiff ℝ (⊤ : ℕ∞) a₀)
    (t : ℝ) (ht : t ∈ Set.Icc t₀ t₁) (X : Vec 2) :
    fieldCellMean (fun z => liftApply n (Cc hh n) (fun _ => a₀) t X z) = 0 := by
  rcases hseq with ⟨_, _, _, _, _, _, hinv⟩
  have hfield := hinv hh hhh n hn hN a₀ ha X
  exact fieldCellMean_eq_zero_of_IsCellFieldInverse
    (fun s => Matrix.of (Q.G s X)) Q.v sZ t₀ t₁
    (fun s z => liftCellSource Q Cc (fun _ => a₀) hh n s X z)
    (fun s z => liftApply n (Cc hh n) (fun _ => a₀) s X z) hfield ht

end AVRegularity
end

section
namespace AVRegularity.CycleComparison

/-! # The trimmed quiet margins

The fast independence of the premise `hquiet` of `cycle_comparison` holds on the trimmed quiet
times `T_m = {t : [t - τ/24, t + τ/24] ⊆ quiet times}` (`ocTrimmedQuietTimes`). Around every
even `j` the quiet margin `[(j - 1/3)τ, (j + 1/3)τ]` (`even_fast_center_quiet_margin`) gives the
trimmed quiet margin `[(j - 7/24)τ, (j + 7/24)τ]` (`even_trimmed_quiet_margin`). After an odd pulse `k` this is
`[(k + 17/24)τ, (k + 31/24)τ] = [(k + 34/48)τ, (k + 62/48)τ]` (`odd_trimmed_gap`), before it
`[(k - 31/24)τ, (k - 17/24)τ]` (`odd_trimmed_gap_left`). It contains the margins of the pulse
windows, the falling and rising gaps of the partition bound after the entrance `(k + 17/24)τ`, and
the overlaps of two pulse windows. -/

/-- The unfolding of the trimmed quiet times. -/
theorem mem_ocTrimmedQuietTimes_iff {α q : ℝ} {Λ : ℕ} {ζ : ℝ → ℝ} {m : ℕ} {t : ℝ} :
    t ∈ ocTrimmedQuietTimes α q Λ ζ m ↔
      Set.Icc (t - ocTau α q Λ m / 24) (t + ocTau α q Λ m / 24) ⊆ ocQuietTimes α q Λ ζ m :=
  Iff.rfl

/-- The trimmed quiet times are quiet. -/
theorem ocTrimmedQuietTimes_subset_quiet {α q : ℝ} {Λ : ℕ} (hΛ : 1 ≤ Λ) (ζ : ℝ → ℝ) (m : ℕ) :
    ocTrimmedQuietTimes α q Λ ζ m ⊆ ocQuietTimes α q Λ ζ m := by
  intro t ht
  have hτ := Construction.Stream.ocTau_pos (α := α) (q := q) hΛ (m := m)
  apply mem_ocTrimmedQuietTimes_iff.mp ht
  constructor <;> linarith only [hτ]

/-- **The trimmed quiet margin of an even center.** -/
theorem even_trimmed_quiet_margin {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (j : ℤ) (hj : Even j) :
    Set.Icc (((j : ℝ) - 7 / 24) * ocTau α q Λ m) (((j : ℝ) + 7 / 24) * ocTau α q Λ m) ⊆
      ocTrimmedQuietTimes α q Λ ζ m := by
  intro t ht
  refine mem_ocTrimmedQuietTimes_iff.mpr fun s hs => ?_
  apply CycleJointProofs.even_fast_center_quiet_margin hΛ hζ j hj
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hs1, hs2⟩ := hs
  constructor <;> linarith

/-- **The trimmed gap after an odd pulse.** -/
theorem odd_trimmed_gap {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    {k : ℤ} (hk : Odd k) {t : ℝ} (h1 : ((k : ℝ) + 17 / 24) * ocTau α q Λ m ≤ t)
    (h2 : t ≤ ((k : ℝ) + 31 / 24) * ocTau α q Λ m) : t ∈ ocTrimmedQuietTimes α q Λ ζ m := by
  have hj : Even (k + 1) := hk.add_one
  refine even_trimmed_quiet_margin hΛ hζ (k + 1) hj ⟨?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

/-- **The trimmed gap before an odd pulse.** -/
theorem odd_trimmed_gap_left {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} (hΛ : 1 ≤ Λ)
    (hζ : IsFastProfile ζ) {k : ℤ} (hk : Odd k) {t : ℝ}
    (h1 : ((k : ℝ) - 31 / 24) * ocTau α q Λ m ≤ t)
    (h2 : t ≤ ((k : ℝ) - 17 / 24) * ocTau α q Λ m) : t ∈ ocTrimmedQuietTimes α q Λ ζ m := by
  have hj : Even (k - 1) := hk.sub_odd odd_one
  refine even_trimmed_quiet_margin hΛ hζ (k - 1) hj ⟨?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- Fast independence on a set gives fast independence on every subset. -/
theorem isFastIndependentOn_mono (F : ChartedFamily ι h D P Ctx) {S S' : Set ℝ} (hS : S ⊆ S')
    (h' : F.IsFastIndependentOn S') : F.IsFastIndependentOn S :=
  fun p c v u γ d I t ht => h' p c v u γ d I t ⟨hS ht.1, ht.2⟩

end AVRegularity.CycleComparison
end
