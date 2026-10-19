-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Residual.CoarseEnergy.ReadoutNamed
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FluxJets

section
@[expose] public noncomputable section
open Homogenization
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **Linearity of the ordered derivative** on finite weighted sums of smooth real functions
(for the frontier flux bound). -/

/-- One step of the ordered derivative. -/
abbrev odStep (g' : Vec 2 → ℝ) (i : Fin 2) : Vec 2 → ℝ := fun x => fderiv ℝ g' x (basisVec i)

theorem odFoldl_sum {ι : Type*} (s : Finset ι) (c : ι → ℝ) (L : List (Fin 2)) :
    ∀ (n : ℕ) (g : ι → Vec 2 → ℝ), L.length ≤ n → (∀ i, ContDiff ℝ n (g i)) →
      L.foldl odStep (fun x => ∑ i ∈ s, c i * g i x) =
        fun x => ∑ i ∈ s, c i * L.foldl odStep (g i) x := by
  induction L with
  | nil => intro n g _ _; rfl
  | cons a L ih =>
    intro n g hL hg
    have hn : n ≠ 0 := by simp at hL; omega
    have hdiff : ∀ i x, DifferentiableAt ℝ (g i) x := fun i x =>
      (hg i).differentiable (by exact_mod_cast hn) x
    have hstep : odStep (fun x => ∑ i ∈ s, c i * g i x) a =
        fun x => ∑ i ∈ s, c i * odStep (g i) a x := by
      funext x
      have hd : ∀ i ∈ s, DifferentiableAt ℝ (fun x => c i * g i x) x := fun i _ =>
        (hdiff i x).const_mul _
      simp only [odStep]
      rw [fderiv_fun_sum hd, sum_apply]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [fderiv_const_mul (hdiff i x)]
      rfl
    simp only [List.foldl_cons]
    rw [hstep]
    simp only [List.length_cons] at hL
    exact ih (n - 1) (fun i => odStep (g i) a) (by omega) (fun i => by
      have := (hg i).fderiv_right (m := ((n - 1 : ℕ) : WithTop ℕ∞))
        (by exact_mod_cast (by omega : n - 1 + 1 ≤ n))
      exact (this.clm_apply contDiff_const))

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **Change of the length of the mass norm** (shared by the frontier flux and the readout energy).

For `s ≥ 0`, the factorial norm at the length `s ρ` of an order-`K` jet is at most
`(max 1 s)^{2K}` times the norm at `ρ` (the weights are `ρ^{2j}/(j!)²`, `j ≤ K`), hence the same for
`massNormSq` (nonnegative masses) and, with integrability of the time integrand at `ρ`, for
`FluxMassLe`: the bound `Y` at `ρ` gives the bound `(max 1 s)^k · Y` at `s ρ`. -/

/-- The factor of the change of length `ρ ↦ s ρ` at the order `k` (for the norm, not squared). -/
def radiusChangeFactor (s : ℝ) (k : ℕ) : ℝ := max 1 s ^ k

theorem radiusChangeFactor_nonneg (s : ℝ) (k : ℕ) : 0 ≤ radiusChangeFactor s k :=
  pow_nonneg (zero_le_one.trans (le_max_left _ _)) _

theorem factorialNormSq_scale_le {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
    {μ : Measure (Vec 2)} {K : ℕ} (ρ s : ℝ) (hs : 0 ≤ s) (D : JetL2 μ K E) :
    factorialNormSq (s * ρ) D ≤ radiusChangeFactor s K ^ 2 * factorialNormSq ρ D := by
  unfold factorialNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  have hw : factorialWeight (s * ρ) j.val = s ^ (2 * j.val) * factorialWeight ρ j.val := by
    unfold factorialWeight; rw [mul_pow, mul_div_assoc]
  have hs1 : s ^ (2 * j.val) ≤ radiusChangeFactor s K ^ 2 := by
    unfold radiusChangeFactor
    rw [← pow_mul, mul_comm K 2]
    calc s ^ (2 * j.val) ≤ max 1 s ^ (2 * j.val) := pow_le_pow_left₀ hs (le_max_right _ _) _
      _ ≤ max 1 s ^ (2 * K) :=
        pow_le_pow_right₀ (le_max_left _ _) (by have := j.2; omega)
  rw [hw, mul_assoc]
  exact mul_le_mul_of_nonneg_right hs1
    (mul_nonneg (factorialWeight_nonneg ρ _) (derivativeNormSq_nonneg D j))

/-- The change of length for the mass norm (nonnegative masses). -/
theorem massNormSq_scale_le {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
    {μ : Measure (Vec 2)} {K : ι → ℕ} (ρ s : ℝ) (hs : 0 ≤ s) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (k : ℕ) (hK : ∀ i, K i ≤ k) (D : ∀ i, JetL2 μ (K i) (E i)) :
    massNormSq (E := E) (K := K) (μ := μ) (s * ρ) π D ≤
      radiusChangeFactor s k ^ 2 * massNormSq (E := E) (K := K) (μ := μ) ρ π D := by
  unfold massNormSq
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun i _ => ?_
  have h1 := factorialNormSq_scale_le ρ s hs (D i)
  have h2 : radiusChangeFactor s (K i) ^ 2 ≤ radiusChangeFactor s k ^ 2 := by
    unfold radiusChangeFactor
    exact pow_le_pow_left₀ (pow_nonneg (zero_le_one.trans (le_max_left _ _)) _)
      (pow_le_pow_right₀ (le_max_left _ _) (hK i)) 2
  have hp : 0 < (π i)⁻¹ := inv_pos.2 (hπ i)
  calc (π i)⁻¹ * factorialNormSq (s * ρ) (D i)
      ≤ (π i)⁻¹ * (radiusChangeFactor s k ^ 2 * factorialNormSq ρ (D i)) :=
        mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right h2
          (Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg ρ _)
            (derivativeNormSq_nonneg (D i) j)))) hp.le
    _ = _ := by ring

theorem massNormSq_nonneg' {ι : Type*} [Fintype ι] {E : ι → Type*} [∀ i, NormedAddCommGroup (E i)]
    [∀ i, InnerProductSpace ℝ (E i)] [∀ i, FiniteDimensional ℝ (E i)]
    [∀ i, MeasurableSpace (E i)] [∀ i, BorelSpace (E i)] [∀ i, CompleteSpace (E i)]
    {μ : Measure (Vec 2)} {K : ι → ℕ} (ρ : ℝ) (π : ι → ℝ) (hπ : ∀ i, 0 < π i)
    (D : ∀ i, JetL2 μ (K i) (E i)) : 0 ≤ massNormSq (E := E) (K := K) (μ := μ) ρ π D :=
  Finset.sum_nonneg fun i _ => mul_nonneg (inv_nonneg.2 (hπ i).le)
    (Finset.sum_nonneg fun j _ => mul_nonneg (factorialWeight_nonneg ρ _)
      (derivativeNormSq_nonneg (D i) j))

open AVRegularity.Construction.Residual.Presentation in
/-- **The change of length for `FluxMassLe`**: with `s ≥ 0`, positive masses, orders `K i ≤ k` and
integrability of the time integrand at the length `ρ`, the bound `Y` at `ρ` gives
`radiusChangeFactor s k * Y` at `s ρ`. -/
theorem fluxMassLe_scale {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)]
    [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)] {K : ι → ℕ} {ν ρ : ℝ} (s : ℝ)
    {π : ι → ℝ} {I : Set ℝ} {F : ∀ v, ℝ → TorusHk (K v) (PiLp 2 (fun _ : Fin 2 => h v))} {Y : ℝ}
    (hν : 0 < ν) (hs : 0 ≤ s) (hπ : ∀ i, 0 < π i) (k : ℕ) (hK : ∀ i, K i ≤ k)
    (hint : IntegrableOn (fun u => massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
      (K := K) ρ π (fun v => (F v u).val)) I)
    (hF : FluxMassLe (h := h) (K := K) ν ρ π I F Y) :
    FluxMassLe (h := h) (K := K) ν (s * ρ) π I F (radiusChangeFactor s k * Y) := by
  refine ⟨hF.1, ?_⟩
  have hmono : ∫ u in I, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v)) (K := K)
        (s * ρ) π (fun v => (F v u).val) ≤
      radiusChangeFactor s k ^ 2 * ∫ u in I, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
        (K := K) ρ π (fun v => (F v u).val) := by
    rw [← integral_const_mul]
    exact integral_mono_of_nonneg (Filter.Eventually.of_forall fun u =>
      massNormSq_nonneg' _ _ hπ _) (hint.const_mul _)
      (Filter.Eventually.of_forall fun u => massNormSq_scale_le ρ s hs π hπ k hK _)
  have hc := radiusChangeFactor_nonneg s k
  calc Real.sqrt (ν⁻¹ * ∫ u in I, massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
          (K := K) (s * ρ) π (fun v => (F v u).val))
      ≤ Real.sqrt (radiusChangeFactor s k ^ 2 * (ν⁻¹ * ∫ u in I,
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
            (K := K) ρ π (fun v => (F v u).val))) :=
        Real.sqrt_le_sqrt (by
          calc _ ≤ ν⁻¹ * (radiusChangeFactor s k ^ 2 * _) :=
                mul_le_mul_of_nonneg_left hmono (inv_nonneg.2 hν.le)
            _ = _ := by ring)
    _ = radiusChangeFactor s k * Real.sqrt (ν⁻¹ * ∫ u in I,
          massNormSq (E := fun v => PiLp 2 (fun _ : Fin 2 => h v))
            (K := K) ρ π (fun v => (F v u).val)) := by
        rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hc]
    _ ≤ _ := mul_le_mul_of_nonneg_left hF.2 hc

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
section
/-! **The flux bound of the response frontier** (statement).

With the coarse-defect data, the coarse flux `Fc` of the passage `i`
(`CdFcRealizes`: minus the `AD`-flux of the frontier readout `H = cdFrontier`) satisfies, in the
form the reconstruction window asks of its flux (`FluxMassLe`, i.e. the square root of
`κ_M⁻¹ ∫_{[t_i, a + T₀]} massNormSq ρ π (Fc s)`),

    κ_M^{-1/2} ‖Fc‖_{L²([t_i, T]; H^k_ρ); π} ≤ C_fl · ε_M^{2a_*(R_w+1)} · Φ,

at the LENGTH `ρ = plan.radius R · ε_{i-1}` (the window of the free-length structure is
instantiated at this `ρ`), the mass `π v = weakMass c.D N_w J_w η₀ v`, the order `k` of `Fc`.

* `weakFluxScaleConst B`: the constant `C_w` of `EntryScales.weak_scales_core`
  (`Pe_i ≤ C_w ε_{i-1}^{a_*}`).
* `weakFrontierFluxConst ρ R` (`C_fl`): a named function of the normalized radius and the request:
  the readout constant `weakCoarseReadoutConst ρ R` of the frontier energy times the letter
  constant `N_w · C_edge(ρ) · C_w²` of the flux of the letters (`weakRawEdgeConst`).

Hypotheses beyond the data: the plan conditions of the readout energy; the two menu inequalities of
`WeakCoarseFrontierEnergyAt`; `m ≤ weakEntryMmax R`; the orders `k + D - 1 ≤ kOf R` (a derivative of
order `d - 1 ≤ D - 1` of `H` at the order `k`); `kOf R + 3 ≤ K_w + m` (as `weakCoarseFamilyRep`);
and the truncation clause of the high-reserve energy statement (`WeakCoarseHighEnergyAt`), from which the frontier readout of
`Uhi` is a classical representative of `weakFrontierField` of `h.aU` (`weakCoarseFamilyRep`).

The degenerate cases are included: `R_w = 0` makes `AD = 0`, so `Fc = 0`; `Φ = 0` gives zero. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

/-- The constant `C_w` of `Pe_i ≤ C_w ε_{i-1}^{a_*}` (`EntryScales.weak_scales_core`). -/
def weakFluxScaleConst (B : WeakCoefficientBase) : ℝ :=
  Classical.choose (EntryScales.weak_scales_core B.hα₀ B.hα₁ B.hs₀ B.hs₁ B.hq)

/-- The letter constant: `N_w · C_edge(ρ) · C_w²` (`ρ` the normalized radius). Adjustable here. -/
def weakFluxLetterConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (ρ : ℝ)
    (R : WeakPassageRequest A) : ℝ :=
  (A.Nw : ℝ) * weakRawEdgeConst ρ R * weakFluxScaleConst B ^ 2

/-- **`C_fl`** of the frontier flux bound: a named function of the normalized radius `ρ = plan.radius R` and the
request. -/
def weakFrontierFluxConst {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (ρ : ℝ)
    (R : WeakPassageRequest A) : ℝ :=
  weakCoarseReadoutConst ρ R * weakFluxLetterConst ρ R

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}

/-- **The flux bound of the response frontier.** -/
def WeakFrontierFluxStatement (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc) (_hm : m ≤ weakEntryMmax R)
    (hk : k + 1 + Dc ≤ R.Kw + m) (_hkOf : k + Dc - 1 ≤ kOf R)
    (_hkOf3 : kOf R + 3 ≤ R.Kw + m),
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
    ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
      (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j),
    (∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j) →
    ∀ (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
      (v₀ : CompIn (c.stage i).comps)
      (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
    -- the truncation clause exported by `WeakCoarseHighEnergyAt`
    (∀ v : CompIn (c.stage (i - 1)).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
        r.Ur (i - 1) v t) →
    CdFcRealizes c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi
      (cdAD c Dc i v₀) Fc →
    AVRegularity.Construction.Residual.Presentation.FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => k) (c.D.κ c.M) (plan.radius R * c.D.eps (i - 1))
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.a + A.T₀)) Fc
      (weakFrontierFluxConst (plan.radius R) R *
        c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1)) * h.Φ)

/-- **The frontier flux bound at the length `ε_{i-1}` of the window** (the lift length; the hypothesis `hY` of the
reconstruction window): the statement above with the radius changed by the factor
`(max 1 (plan.radius R)⁻¹)^k` (`radiusChangeFactor`). -/
def WeakFrontierFluxFinalStatement (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc) (_hm : m ≤ weakEntryMmax R)
    (hk : k + 1 + Dc ≤ R.Kw + m) (_hkOf : k + Dc - 1 ≤ kOf R)
    (_hkOf3 : kOf R + 3 ≤ R.Kw + m),
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
    ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
      (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
      (Whi : ∀ j, WeakStageLift (weakPassageRawSetting c) m j),
    (∀ j, c.M < j → j ≤ c.M + A.Jw →
      WeakStagePassage (weakPassageRawSetting c) (weakPassageRawClock r) m Uhi Whi j) →
    ∀ (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i)
      (v₀ : CompIn (c.stage i).comps)
      (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
        TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
    -- the truncation clause exported by `WeakCoarseHighEnergyAt`
    (∀ v : CompIn (c.stage (i - 1)).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
        r.Ur (i - 1) v t) →
    CdFcRealizes c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi
      (cdAD c Dc i v₀) Fc →
    AVRegularity.Construction.Residual.Presentation.FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => k) (c.D.κ c.M) (c.D.eps (i - 1))
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.a + A.T₀)) Fc
      (max 1 (plan.radius R)⁻¹ ^ k * (weakFrontierFluxConst (plan.radius R) R *
        c.D.eps c.M ^ (2 * weakAStar B.α B.q * (A.Rw + 1)) * h.Φ))

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The frontier flux: its named step statements and the assembly.**

* `FrontierJetsStep`: the jets of `cdFrontier` of orders `≤ D_c` are the classical derivatives
  of `weakFrontierField` of `h.aU` (from `weakCoarseFamilyRep`, the truncation clause of the high-reserve energy statement).
* `FrontierLetterStep`: the letter coefficient `cdAD` is regular and its normalized seminorm,
  with the reserve factors, is at most `κ_M · C_L · ε_M^{2a_*}`.
* `FrontierFluxEnergyStep`: the flux of the letters against the classical frontier field:
  `∫ ‖Fc‖² ≤ Λ² · ∑_v π_v⁻¹ ∫ |∇H_v|²`.
* The frontier energy is the proved `weakCoarseFrontierEnergyAt_named`.
* `weakFrontierFlux_of_steps`: the assembly. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}

/-- The seminorm total of the letter coefficient at the order `k` and length `ρ`. -/
def frontierLetterTotal {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Dc k i : ℕ) (v₀ : CompIn (c.stage i).comps) (ρ : ℝ) : ℝ :=
  ∑ d : Finset.Icc 2 Dc,
    (coefficientSeminorm ρ k (r.tq i) (r.a + A.T₀) (cdAD c Dc i v₀ d)).toReal *
      derivativeReserveFactor ρ k (d.1 - 2)

/-- Regularity of the letter coefficient: finite seminorm, smooth and periodic on the window. -/
def FrontierLetterReg {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Dc k i : ℕ) (v₀ : CompIn (c.stage i).comps) (ρ : ℝ) : Prop :=
  ∀ d : Finset.Icc 2 Dc, coefficientSeminorm ρ k (r.tq i) (r.a + A.T₀) (cdAD c Dc i v₀ d) ≠ ⊤ ∧
    ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ContDiff ℝ (k : ℕ) (cdAD c Dc i v₀ d t) ∧ IsZ2Periodic (cdAD c Dc i v₀ d t)

/-- **Jets**: the jets of the frontier readout are the classical derivatives of the classical
frontier field. -/
def FrontierJetsStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k : ℕ) (_hm : m ≤ weakEntryMmax R)
    (hk : k + 1 + Dc ≤ R.Kw + m) (_hkOf : k + Dc - 1 ≤ kOf R) (_hkOf3 : kOf R + 3 ≤ R.Kw + m)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw) (h : WeakComparisonInput r i),
    (∀ v : CompIn (c.stage (i - 1)).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      truncateTorusHk (weakReductionReserve_kw_le R m v.1) (Uhi (i - 1) v t) =
        r.Ur (i - 1) v t) →
    ∀ v : CompIn (c.stage i).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ∀ j ≤ Dc, ∀ w : DerivativeWord2 j,
        torusJetOrder (cdFrontier c m (k + 1 + Dc)
            (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi v t) j w
          =ᵐ[volume.restrict unitCube] fun x => orderedDerivative w
            (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v) x

/-- **The letter step**: the size of the letter coefficient. -/
def FrontierLetterStep (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc k : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc) (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ) (_hi : c.M < i) (_hit : i ≤ c.M + A.Jw)
    (v₀ : CompIn (c.stage i).comps),
    FrontierLetterReg c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) ∧
    frontierLetterTotal c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) ≤
      c.D.κ c.M * (weakFluxLetterConst (plan.radius R) R *
        c.D.eps c.M ^ (2 * weakAStar B.α B.q))

/-- The classical dissipation of the frontier field. -/
def frontierDissipation {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i kk : ℕ) (h : WeakComparisonInput r i) (ρ : ℝ) : ℝ≥0∞ :=
  ∑ v : CompIn (c.stage i).comps, ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
    ∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀), classicalGradFactorialSq ρ kk
      (fun x => weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v x)

/-- **The flux step**: the flux of the letters on the classical frontier field. -/
def FrontierFluxEnergyStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (Dc m k : ℕ) (_hDc : 1 + A.Jw * A.Nw ≤ Dc)
    (hk : k + 1 + Dc ≤ R.Kw + m) (_hkOf : k + Dc - 1 ≤ kOf R)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (Uhi : ∀ j, WeakStageFamily (weakPassageRawSetting c) m j)
    (i : ℕ) (h : WeakComparisonInput r i) (v₀ : CompIn (c.stage i).comps)
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))),
    FrontierLetterReg c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) →
    (∀ v : CompIn (c.stage i).comps, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
      ∀ j ≤ Dc, ∀ w : DerivativeWord2 j,
        torusJetOrder (cdFrontier c m (k + 1 + Dc)
            (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi v t) j w
          =ᵐ[volume.restrict unitCube] fun x => orderedDerivative w
            (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v) x) →
    CdFcRealizes c r Dc m k (fun w => hk.trans (weakReductionReserve_kw R m w)) i Uhi
      (cdAD c Dc i v₀) Fc →
    (∀ v, MemLp (Fc v) 2 (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
    IntegrableOn (fun s => massNormSq (E := fun v : CompIn (c.stage i).comps => PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
          (K := fun _ => k) (plan.radius R * c.D.eps (i - 1))
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Fc v s).val)) (Set.Icc (r.tq i) (r.a + A.T₀)) ∧
    ENNReal.ofReal (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        massNormSq (E := fun v : CompIn (c.stage i).comps => PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
          (K := fun _ => k) (plan.radius R * c.D.eps (i - 1))
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Fc v s).val)) ≤
      ENNReal.ofReal (frontierLetterTotal c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) ^ 2) *
        frontierDissipation c r i (kOf R) h (plan.radius R * c.D.eps (i - 1))

/-- The dissipative part of the strong energy: `κ · dissipation ≤ energy²`. -/
theorem frontierDissipation_le_energy {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c)
    (i kk : ℕ) (h : WeakComparisonInput r i) (ρ : ℝ) :
    ENNReal.ofReal (c.D.κ c.M) * frontierDissipation c r i kk h ρ ≤
      classicalStrongEnergy ρ (c.D.κ c.M)
        (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
        (Set.Icc (r.tq i) (r.a + A.T₀)) kk
        (fun t x v => weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v x) ^ 2 := by
  unfold classicalStrongEnergy frontierDissipation
  rw [← ENNReal.rpow_natCast, ← ENNReal.rpow_mul]
  norm_num
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  rw [mul_left_comm]
  exact mul_le_mul' le_rfl le_add_self

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The assembly** of `WeakFrontierFluxStatement` from the letter step, the factorial flux estimate and the
temporal control, and the proved frontier energy. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan}
  {kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ}

/-- The real inequality of the assembly. -/
theorem frontierFlux_real_step {κ I Λ Y0 X Y : ℝ} (hκ : 0 < κ) (hΛ : 0 ≤ Λ) (hY0 : 0 ≤ Y0)
    (hI : κ * I ≤ Λ ^ 2 * Y0 ^ 2) (hΛX : Λ ≤ κ * X) (hY : Y = X * Y0) :
    Real.sqrt (κ⁻¹ * I) ≤ Y := by
  have hX : 0 ≤ X := by
    by_contra hneg
    have hneg' := not_le.1 hneg
    nlinarith [mul_neg_of_pos_of_neg hκ hneg']
  have hY' : 0 ≤ Y := hY ▸ mul_nonneg hX hY0
  rw [Real.sqrt_le_iff]
  refine ⟨hY', ?_⟩
  have h1 : κ⁻¹ * I = κ⁻¹ ^ 2 * (κ * I) := by field_simp
  have h2 : Λ * Y0 ≤ κ * (X * Y0) := by nlinarith [mul_le_mul_of_nonneg_right hΛX hY0]
  rw [h1]
  calc κ⁻¹ ^ 2 * (κ * I) ≤ κ⁻¹ ^ 2 * (Λ ^ 2 * Y0 ^ 2) :=
        mul_le_mul_of_nonneg_left hI (sq_nonneg _)
    _ = (κ⁻¹ * (Λ * Y0)) ^ 2 := by ring
    _ ≤ Y ^ 2 := by
        apply pow_le_pow_left₀ (mul_nonneg (inv_nonneg.2 hκ.le) (mul_nonneg hΛ hY0))
        rw [hY]
        calc κ⁻¹ * (Λ * Y0) ≤ κ⁻¹ * (κ * (X * Y0)) :=
              mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hκ.le)
          _ = X * Y0 := by field_simp

/-- **The frontier flux bound from its steps.** -/
theorem weakFrontierFlux_of_steps (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) (hF0 : FrontierJetsStep plan kOf)
    (hS2 : FrontierLetterStep plan) (hS3 : FrontierFluxEnergyStep plan kOf) :
    WeakFrontierFluxStatement plan kOf := by
  intro B A R Dc m k hDc hm hk hkOf hkOf3 menu1 menu2 c r Uhi Whi hpass i hi hit h v₀ Fc htrunc hreal
  obtain ⟨hreg, hLt⟩ := hS2 R Dc k hDc c r i hi hit v₀
  have hjets := hF0 R Dc m k hm hk hkOf hkOf3 c r Uhi i hi hit h htrunc
  obtain ⟨hmem, _, hI⟩ := hS3 R Dc m k hDc hk hkOf c r Uhi i h v₀ Fc hreg hjets hreal
  have hEn := weakCoarseFrontierEnergyAt_named hcommon hok menu1 menu2 c r i hi hit h
  have hκ : 0 < c.D.κ c.M := (weakPassageRawSetting c).kappa_pos
  have hε : 0 < c.D.eps c.M := frontier_eps_pos c c.M
  have hwin := weak_quiet_window c r i hi hit
  have hΦ0 : 0 ≤ h.Φ :=
    (by unfold weightedNorm; positivity : (0 : ℝ) ≤ _).trans
      (h.mass_bound (r.tq (i + 1)) ⟨le_rfl, hwin.2.2.1.le.trans hwin.2.1⟩)
  have hρ : 0 < plan.radius R * c.D.eps (i - 1) :=
    mul_pos (plan.radius_pos R) (frontier_eps_pos c (i - 1))
  have hΛ0 : 0 ≤ frontierLetterTotal c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1)) := by
    unfold frontierLetterTotal derivativeReserveFactor
    exact Finset.sum_nonneg fun d _ => mul_nonneg ENNReal.toReal_nonneg (by positivity)
  have hCen : 0 ≤ weakCoarseReadoutConst (plan.radius R) R := weakCoarseReadoutConst_nonneg _ _
  set Y0 := weakCoarseReadoutConst (plan.radius R) R *
    c.D.eps c.M ^ (2 * weakAStar B.α B.q * A.Rw) * h.Φ with hY0def
  have hY0 : 0 ≤ Y0 := by positivity
  set Λ := frontierLetterTotal c r Dc k i v₀ (plan.radius R * c.D.eps (i - 1))
  have h1 : ENNReal.ofReal (c.D.κ c.M) * ENNReal.ofReal (∫ s in Set.Icc (r.tq i) (r.a + A.T₀),
        massNormSq (E := fun v : CompIn (c.stage i).comps => PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
          (K := fun _ => k) (plan.radius R * c.D.eps (i - 1))
          (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
          (fun v => (Fc v s).val)) ≤ ENNReal.ofReal (Λ ^ 2) * ENNReal.ofReal (Y0 ^ 2) := by
    calc _ ≤ ENNReal.ofReal (c.D.κ c.M) * (ENNReal.ofReal (Λ ^ 2) *
          frontierDissipation c r i (kOf R) h (plan.radius R * c.D.eps (i - 1))) :=
          mul_le_mul' le_rfl hI
      _ = ENNReal.ofReal (Λ ^ 2) * (ENNReal.ofReal (c.D.κ c.M) *
          frontierDissipation c r i (kOf R) h (plan.radius R * c.D.eps (i - 1))) := by
          rw [mul_left_comm]
      _ ≤ _ := by
          refine mul_le_mul' le_rfl ?_
          refine (frontierDissipation_le_energy c r i (kOf R) h _).trans ?_
          rw [ENNReal.ofReal_pow hY0]
          exact pow_le_pow_left' hEn 2
  rw [← ENNReal.ofReal_mul hκ.le, ← ENNReal.ofReal_mul (sq_nonneg _),
    ENNReal.ofReal_le_ofReal_iff (mul_nonneg (sq_nonneg _) (sq_nonneg _))] at h1
  refine ⟨hmem, frontierFlux_real_step hκ hΛ0 hY0 h1 hLt ?_⟩
  rw [hY0def, weakFrontierFluxConst, mul_add, mul_one, Real.rpow_add hε]
  ring

open AVRegularity.Construction.Residual.Presentation in
/-- The radius change at the window length, for the data of the passage. -/
theorem frontierFlux_radius_change {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i k : ℕ)
    (Fc : ∀ v : CompIn (c.stage i).comps, ℝ →
      TorusHk k (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))) (Y : ℝ)
    (hint : IntegrableOn (fun s => massNormSq
      (E := fun v : CompIn (c.stage i).comps => PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root))
      (K := fun _ => k) (plan.radius R * c.D.eps (i - 1))
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (fun v => (Fc v s).val)) (Set.Icc (r.tq i) (r.a + A.T₀)))
    (hbase : FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => k) (c.D.κ c.M) (plan.radius R * c.D.eps (i - 1))
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.a + A.T₀)) Fc Y) :
    FluxMassLe (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
      (K := fun _ => k) (c.D.κ c.M) (c.D.eps (i - 1))
      (fun v : CompIn (c.stage i).comps => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (Set.Icc (r.tq i) (r.a + A.T₀)) Fc (radiusChangeFactor (plan.radius R)⁻¹ k * Y) := by
  have hκ : 0 < c.D.κ c.M := (weakPassageRawSetting c).kappa_pos
  have hs : 0 < (plan.radius R)⁻¹ := inv_pos.2 (plan.radius_pos R)
  have hmain := fluxMassLe_scale (ι := CompIn (c.stage i).comps)
    (h := fun v => ScalarH v.1.root) (K := fun _ => k) (plan.radius R)⁻¹ hκ hs.le
    (fun v => (weakPassageRawSetting c).mass_pos v.1) k (fun _ => le_rfl) hint hbase
  have hrad : (plan.radius R)⁻¹ * (plan.radius R * c.D.eps (i - 1)) = c.D.eps (i - 1) := by
    have := (plan.radius_pos R).ne'
    field_simp
  rw [hrad] at hmain
  exact hmain

/-- **The frontier flux bound at the length `ε_{i-1}` of the window, from its steps.** -/
theorem weakFrontierFluxFinal_of_steps (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarseReadoutPlanOK plan kOf) (hF0 : FrontierJetsStep plan kOf)
    (hS2 : FrontierLetterStep plan) (hS3 : FrontierFluxEnergyStep plan kOf) :
    WeakFrontierFluxFinalStatement plan kOf := by
  intro B A R Dc m k hDc hm hk hkOf hkOf3 menu1 menu2 c r Uhi Whi hpass i hi hit h v₀ Fc htrunc hreal
  have hbase := weakFrontierFlux_of_steps hcommon hok hF0 hS2 hS3 R Dc m k hDc hm hk hkOf hkOf3
    menu1 menu2 c r Uhi Whi hpass i hi hit h v₀ Fc htrunc hreal
  obtain ⟨hreg, _⟩ := hS2 R Dc k hDc c r i hi hit v₀
  have hjets := hF0 R Dc m k hm hk hkOf hkOf3 c r Uhi i hi hit h htrunc
  obtain ⟨_, hint, _⟩ := hS3 R Dc m k hDc hk hkOf c r Uhi i h v₀ Fc hreg hjets hreal
  exact frontierFlux_radius_change c r i k Fc _ hint hbase

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end

section
/-! **The jets of the frontier readout.** `frontierJetsStep` proves
`FrontierJetsStep`: from the classical representatives of the family
(`weakCoarseFamilyRep`) the jets of `cdFrontier` of order `j ≤ D_c` are the classical derivatives
of `weakFrontierField`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance

namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  AVRegularity.Providers.WeakGen.Residual

/-- The jet of a finite weighted sum of elements of `TorusHk K ℝ`. -/
theorem torusJetOrder_wsum_ae {ι : Type*} {K : ℕ} (s : Finset ι) (c : ι → ℝ)
    (U : ι → TorusHk K ℝ) {j : ℕ} (hj : j ≤ K) (w : DerivativeWord2 j) :
    torusJetOrder (∑ i ∈ s, c i • U i) j w =ᵐ[volume.restrict unitCube]
      fun x => ∑ i ∈ s, c i * torusJetOrder (U i) j w x := by
  classical
  have hdef : ∀ W : TorusHk K ℝ, torusJetOrder W j w = fun x => W.toFunction.jet ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩ x := by
    intro W; funext x; simp [torusJetOrder, hj]
  simp only [hdef]
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    have := AVRegularity.CycleComparison.Coarse.jet_smul_ae (0 : ℝ) (0 : TorusHk K ℝ)
    filter_upwards [this] with x hx
    simpa using hx ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    filter_upwards [AVRegularity.CycleComparison.Coarse.jet_add_ae (c a • U a) (∑ i ∈ s, c i • U i),
      AVRegularity.CycleComparison.Coarse.jet_smul_ae (c a) (U a), ih] with x h1 h2 h3
    rw [Finset.sum_insert ha, h1 ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩, h2 ⟨⟨j, Nat.lt_succ_of_le hj⟩, w⟩, h3]
    rfl

/-- **F0, proved.** -/
theorem frontierJetsStep (plan : WeakPassagePlan)
    (kOf : ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B},
      WeakPassageRequest A → ℕ) : FrontierJetsStep plan kOf := by
  classical
  intro B A R Dc m k hm hk hkOf hkOf3 c r Uhi i hi hit h htrunc v t ht j hj w
  have hkOf' : k + Dc - 1 ≤ kOf R := hkOf
  have hkOf3' : kOf R + 3 ≤ R.Kw + m := hkOf3
  have hrep := weakCoarseFamilyRep plan kOf R m hm hkOf3' c r Uhi i hi hit h htrunc
  have hDc : Dc ≤ kOf R + 1 := by omega
  let cw : CompIn (c.stage (i - 1)).comps → ℝ := fun v' =>
    if compParent i v'.1 = v.1 ∧ (compWord i v'.1).length = A.Rw
    then (c.D.eps (i - 1) ^ A.η₀) ^ A.Rw else 0
  have hH : cdFrontier c m (k + 1 + Dc) (fun w => hk.trans (weakReductionReserve_kw R m w)) i
      Uhi v t = ∑ v' : CompIn (c.stage (i - 1)).comps, cw v' •
        truncateTorusHk ((fun w => hk.trans (weakReductionReserve_kw R m w)) v'.1)
          (Uhi (i - 1) v' t) := by
    unfold cdFrontier cdReadout
    refine Finset.sum_congr rfl fun v' _ => ?_
    by_cases h1 : compParent i v'.1 = v.1 ∧ (compWord i v'.1).length = A.Rw
    · simp only [cw, h1, and_self, ite_true, cdWeight]
    · simp only [cw, h1, ite_false, zero_smul]
  rw [hH]
  have step1 := torusJetOrder_wsum_ae Finset.univ cw
    (fun v' => truncateTorusHk ((fun w => hk.trans (weakReductionReserve_kw R m w)) v'.1)
      (Uhi (i - 1) v' t)) (hj.trans (by omega)) w
  have step2 : ∀ v' : CompIn (c.stage (i - 1)).comps,
      torusJetOrder (truncateTorusHk ((fun w => hk.trans (weakReductionReserve_kw R m w)) v'.1)
        (Uhi (i - 1) v' t)) j w =ᵐ[volume.restrict unitCube]
        orderedDerivative w (h.aU t v') := by
    intro v'
    have hr := hrep v' t ht
    have hKv : k + 1 + Dc ≤ weakReductionReserve R m v'.1 := hk.trans (weakReductionReserve_kw R m v'.1)
    have hr' : IsClassicalRep (Uhi (i - 1) v' t) (h.aU t v') Dc :=
      ⟨by omega, hr.2.1.of_le (by exact_mod_cast hDc), hr.2.2.1,
        fun m' hm' w' => hr.2.2.2 m' (hm'.trans hDc) w'⟩
    exact (AVRegularity.Construction.Preservation.FullLift.classicalRep_truncate _ (by omega) _ _
      hr').2.2.2 j hj w
  have hae := ae_all_iff.2 step2
  have hdiff : ∀ v' : CompIn (c.stage (i - 1)).comps, ContDiff ℝ (Dc : ℕ) (h.aU t v') := fun v' =>
    (hrep v' t ht).2.1.of_le (by exact_mod_cast hDc)
  have step3 : orderedDerivative w
      (weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v) =
      fun x => ∑ v' : CompIn (c.stage (i - 1)).comps, cw v' * orderedDerivative w (h.aU t v') x := by
    have hf : weakFrontierField i A.Rw A.η₀ (c.stage i) (c.stage (i - 1)) (h.aU t) v =
        fun x => ∑ v' : CompIn (c.stage (i - 1)).comps, cw v' * h.aU t v' x := by
      funext x
      unfold weakFrontierField
      refine Finset.sum_congr rfl fun v' _ => ?_
      by_cases h1 : compParent i v'.1 = v.1 ∧ (compWord i v'.1).length = A.Rw
      · simp only [cw, h1, and_self, ite_true]
      · simp only [cw, h1, ite_false, zero_mul]
    rw [hf]
    exact odFoldl_sum Finset.univ cw (List.ofFn w) Dc (fun v' => h.aU t v') (by simpa using hj) hdiff
  filter_upwards [step1, hae] with x h1 h2
  rw [h1, step3]
  exact Finset.sum_congr rfl fun v' _ => by rw [h2 v']

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end
end
