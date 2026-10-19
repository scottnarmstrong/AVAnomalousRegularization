-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.CycleComparison.Reconstruction.PulseTail
import AVRegularity.CycleComparison.Residual.LiftStatements
import AVRegularity.CycleComparison.Residual.TailJets
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
import AVRegularity.CycleComparison.Residual.TailDiff.Main
import AVRegularity.CycleComparison.TailConstructed.RawFluxOrderZero
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import AVRegularity.CycleComparison.Reconstruction.CoarseDefectApprox
import AVRegularity.CycleComparison.Lift.SettingConstructedLiftSequence
import AVRegularity.CycleComparison.Lift.SettingAmbientEnergyGrading
import AVRegularity.CycleComparison.Lift.SettingLiftPolyTimeIntegral
import AVRegularity.CycleComparison.Lift.SettingTailFluxCoefficientCellBound
import AVRegularity.CycleComparison.Lift.NormalizedSourceArrayZeroMatrixBound
import AVRegularity.CycleComparison.Reconstruction.PulseTailPeriodic

@[expose] public noncomputable section

section
open Homogenization MeasureTheory AVRegularity.Sobolev AVenhance
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lift of a smooth field in cleanup form** (for the lifted coarse flux, the same cleanup
is applied to `g_n = C_n^{(h)} div_X (F_c)_ρ`, and `(F_c, 0)` is added at grade zero).

The label lift of a chart-frame field `A` is `∑_{hh ≤ H} ∑_{n ≤ N} ε^n C_n^{(hh)} A`. Its degree
zero is the field itself (`IsLiftSequence.liftApply_zero`). For a positive degree `n + 1 ≤ N` and
a cleanup chain `Vn hh n` of the data `(C_{n+1}^{(hh)} A, 0)`, the cleanup identity
(`cleanup_identity`) writes the sampled lift as the label divergence of the sampled cleanup flux
plus the sampled cleanup remainder. Hence, with the fluxes and forces of the module
`Reconstruction.PulseTail` (`tailFluxLabel`, `tailFluxPhys`, `tailForcePhys`, at the degree `n` and
with the chains `fun hh => Vn hh n`):

* `labelLift_cleanup`: the label lift at the label `y` is `A(y/ρ)` plus `c` times the label
  divergences of the label fluxes plus the forces of the degrees `n < N`;
* `labelLift_cleanup_phys`: at `y = ψ x`, for a chart `χ` with inverse `ψ` and `det Dχ = 1`, the
  label divergences are the physical divergences of the Piola transports;
* `setting_labelLift_cleanup_tested`: tested against a `C¹` periodic field on the cell, the
  divergences are integrated by parts (the physical fluxes are `C¹` and `ℤ²`-periodic: the chains
  are slow invariant for `ρ⁻¹ℤ²` by uniqueness, and fast periodic).

This is the presentation of the lift of the coarse flux divergence; the identity term is the
field itself, which is a physical divergence when the field is. -/

section
section Defs

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- **The physical cleanup flux of a lift**: the sum over the degrees `n < N` of `c` times the
physical tail flux of the chains `fun hh => Vn hh n` (which carries `c⁻¹ ε^{n+1}`). -/
def liftFluxPhys (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2) (a₀ : Fin 2) : E :=
  ∑ n ∈ Finset.range N, c • tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x a₀

/-- **The physical cleanup force of a lift**: the sum over the degrees `n < N` of `c` times the
physical tail force of the chains `fun hh => Vn hh n`. -/
def liftForcePhys (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2) : E :=
  ∑ n ∈ Finset.range N, c • tailForcePhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x

end Defs

section Label

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]

/-- The chains of the data `(g, 0)` are box smooth. -/
theorem cleanupChain_zeroFlux_box {sXc sZc Acl : ℕ} {g : Vec 2 → Vec 2 → ∀ i, h i}
    {W : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i}
    (hW : IsCleanupChain sXc sZc Acl g (fun _ _ _ => 0) W) :
    ∀ j, j < Acl → IsBoxSmooth sXc sZc (W j) :=
  IsCleanupChain.isBoxSmooth (F₀ := fun _ _ _ => 0) (isBoxSmooth_zero sXc sZc) hW

/-- **One positive degree in cleanup form** at the label `y`. -/
theorem sample_eq_cleanup_zeroFlux {sXc sZc Acl : ℕ} (hAcl : 1 ≤ Acl) (hXc : 1 ≤ sXc)
    (hZc : 1 ≤ sZc) {c ρs es : ℝ} (hρ : ρs ≠ 0) (he : es ≠ 0)
    {g : ℝ → Vec 2 → Vec 2 → ∀ i, h i} (W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) (t : ℝ)
    (hW : IsCleanupChain sXc sZc Acl (g (c * t)) (fun _ _ _ => 0) (fun j => W j (c * t)))
    (y : Vec 2) :
    g (c * t) (ρs⁻¹ • y) (es⁻¹ • y) =
      ∑ kk : Fin 2, fderiv ℝ (fun y' => cleanupFlux c ρs es Acl W t y' kk) y (basisVec kk)
        + cleanupRemainder c ρs es Acl W t y := by
  have hcl := cleanup_identity (F₀ := fun _ _ _ => (0 : ∀ i, h i)) hAcl hXc hZc hρ he
    (isBoxSmooth_zero sXc sZc) hW y
  have hz : ∑ kk : Fin 2, fastPartial kk (fun (_ _ : Vec 2) => (0 : ∀ i, h i)) (ρs⁻¹ • y)
      (es⁻¹ • y) = 0 := by
    simp [fastPartial]
  rw [hz, add_zero] at hcl
  exact hcl

variable [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ} {Q : LiftOperatorData ι h D} {a b : ℝ}
  {N H : ℕ}

/-- **The label lift in cleanup form.** -/
theorem labelLift_cleanup {sX sZ : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) {sXc sZc Acl : ℕ} (hAcl : 1 ≤ Acl)
    (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc) (ε : ℝ) {c ρs es : ℝ} (hc : c ≠ 0) (hρ : ρs ≠ 0)
    (he : es ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ n, n < N → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (liftApply (n + 1) (Cc hh (n + 1)) A τ) (fun _ _ _ => 0) (fun j => Vn hh n j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) (y : Vec 2) :
    labelLift Cc N H ε A ρs es c t y = A (c⁻¹ * t) (ρs⁻¹ • y) +
      ∑ n ∈ Finset.range N, c • (∑ i₀ : Fin 2,
          fderiv ℝ (fun y' => tailFluxLabel H n Acl ε c ρs es (fun hh => Vn hh n) t y' i₀) y
            (basisVec i₀)
        + ∑ hh ∈ Finset.range (H + 1),
          c⁻¹ • ε ^ (n + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vn hh n) t y) := by
  -- one degree and one grade
  have hterm : ∀ n ∈ Finset.range N, ∀ hh ∈ Finset.range (H + 1),
      liftApply (n + 1) (Cc hh (n + 1)) A (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) =
        ∑ kk : Fin 2, fderiv ℝ (fun y' => cleanupFlux c⁻¹ ρs es Acl (Vn hh n) t y' kk) y
            (basisVec kk)
          + cleanupRemainder c⁻¹ ρs es Acl (Vn hh n) t y := fun n hn hh hhm =>
    sample_eq_cleanup_zeroFlux (g := fun τ => liftApply (n + 1) (Cc hh (n + 1)) A τ) hAcl hXc
      hZc hρ he (Vn hh n) t (hV hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) n
        (Finset.mem_range.1 hn) _ ht) y
  -- one degree, summed over the grades
  have hdeg : ∀ n ∈ Finset.range N, ∑ hh ∈ Finset.range (H + 1), ε ^ (n + 1) •
        liftApply (n + 1) (Cc hh (n + 1)) A (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) =
      c • (∑ i₀ : Fin 2,
          fderiv ℝ (fun y' => tailFluxLabel H n Acl ε c ρs es (fun hh => Vn hh n) t y' i₀) y
            (basisVec i₀)
        + ∑ hh ∈ Finset.range (H + 1),
          c⁻¹ • ε ^ (n + 1) • cleanupRemainder c⁻¹ ρs es Acl (Vn hh n) t y) := by
    intro n hn
    have hd : ∀ hh ∈ Finset.range (H + 1), ∀ i₀ : Fin 2, DifferentiableAt ℝ
        (fun y' => cleanupFlux c⁻¹ ρs es Acl (Vn hh n) t y' i₀) y := fun hh hhm i₀ =>
      (contDiff_cleanupFlux_sample hXc hZc c⁻¹ ρs es t (cleanupChain_zeroFlux_box
        (hV hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) n (Finset.mem_range.1 hn) _ ht))
        i₀).differentiable one_ne_zero y
    have hd' : ∀ hh ∈ Finset.range (H + 1), ∀ i₀ : Fin 2, DifferentiableAt ℝ
        (fun y' => c⁻¹ • ε ^ (n + 1) • cleanupFlux c⁻¹ ρs es Acl (Vn hh n) t y' i₀) y :=
      fun hh hhm i₀ => ((hd hh hhm i₀).const_smul (ε ^ (n + 1))).const_smul c⁻¹
    have hfl : ∑ i₀ : Fin 2,
        fderiv ℝ (fun y' => tailFluxLabel H n Acl ε c ρs es (fun hh => Vn hh n) t y' i₀) y
          (basisVec i₀) =
        ∑ hh ∈ Finset.range (H + 1), ∑ i₀ : Fin 2, c⁻¹ • ε ^ (n + 1) •
          fderiv ℝ (fun y' => cleanupFlux c⁻¹ ρs es Acl (Vn hh n) t y' i₀) y (basisVec i₀) := by
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun i₀ _ => ?_
      show fderiv ℝ (fun y' => ∑ hh ∈ Finset.range (H + 1),
        c⁻¹ • ε ^ (n + 1) • cleanupFlux c⁻¹ ρs es Acl (Vn hh n) t y' i₀) y (basisVec i₀) = _
      rw [fderiv_fun_sum fun hh hhm => hd' hh hhm i₀]
      simp only [FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun hh hhm => ?_
      have hde : DifferentiableAt ℝ
          (fun y' => ε ^ (n + 1) • cleanupFlux c⁻¹ ρs es Acl (Vn hh n) t y' i₀) y :=
        (hd hh hhm i₀).const_smul (ε ^ (n + 1))
      rw [fderiv_fun_const_smul hde c⁻¹, fderiv_fun_const_smul (hd hh hhm i₀) (ε ^ (n + 1))]
      rfl
    rw [hfl, ← Finset.sum_add_distrib, Finset.smul_sum]
    refine Finset.sum_congr rfl fun hh hhm => ?_
    rw [hterm n hn hh hhm]
    simp only [← Finset.smul_sum, ← smul_add]
    rw [smul_smul c c⁻¹, mul_inv_cancel₀ hc, one_smul]
  -- the degree zero is the field
  have hzero : ∑ hh ∈ Finset.range (H + 1), ε ^ 0 •
      liftApply 0 (Cc hh 0) A (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) = A (c⁻¹ * t) (ρs⁻¹ • y) := by
    have h1 : ∀ hh ∈ Finset.range (H + 1), ε ^ 0 •
        liftApply 0 (Cc hh 0) A (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) =
        if hh = 0 then A (c⁻¹ * t) (ρs⁻¹ • y) else 0 := fun hh hhm => by
      rw [pow_zero, one_smul]
      exact hseq.liftApply_zero (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) A ht _ _
    rw [Finset.sum_congr rfl h1, Finset.sum_ite_eq' (Finset.range (H + 1)) 0,
      ite_eq_left (Finset.mem_range.2 (Nat.succ_pos H))]
  have hsplit : labelLift Cc N H ε A ρs es c t y =
      ∑ n ∈ Finset.range (N + 1), ∑ hh ∈ Finset.range (H + 1), ε ^ n •
        liftApply n (Cc hh n) A (c⁻¹ * t) (ρs⁻¹ • y) (es⁻¹ • y) := by
    simp only [labelLift, liftPolyField]
    exact Finset.sum_comm
  rw [hsplit, Finset.sum_range_succ', hzero, add_comm, Finset.sum_congr rfl hdeg]

/-- **The label lift in physical cleanup form**, at the label `ψ x` of a chart with `det Dχ = 1`
and inverse `ψ`. -/
theorem labelLift_cleanup_phys {sX sZ : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h}
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) {sXc sZc Acl : ℕ} (hAcl : 1 ≤ Acl)
    (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc) (ε : ℝ) {c ρs es : ℝ} (hc : c ≠ 0) (hρ : ρs ≠ 0)
    (he : es ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ n, n < N → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (liftApply (n + 1) (Cc hh (n + 1)) A τ) (fun _ _ _ => 0) (fun j => Vn hh n j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) {χ ψ : Vec 2 → Vec 2}
    (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) (hψχ : ∀ y, ψ (χ y) = y)
    (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1) (x : Vec 2) :
    labelLift Cc N H ε A ρs es c t (ψ x) = A (c⁻¹ * t) (ρs⁻¹ • ψ x) +
      (∑ a₀ : Fin 2, fderiv ℝ (fun x' => liftFluxPhys ψ H N Acl ε c ρs es Vn t x' a₀) x
          (basisVec a₀)
        + liftForcePhys ψ H N Acl ε c ρs es Vn t x) := by
  have hbox : ∀ n, n < N → ∀ hh, hh ≤ H → ∀ j, j < Acl →
      IsBoxSmooth sXc sZc (Vn hh n j (c⁻¹ * t)) := fun n hn hh hhh =>
    cleanupChain_zeroFlux_box (hV hh hhh n hn _ ht)
  have hLc : ∀ n, n < N → ∀ i₀, ContDiff ℝ 1
      (fun y => tailFluxLabel H n Acl ε c ρs es (fun hh => Vn hh n) t y i₀) := fun n hn =>
    contDiff_tailFluxLabel hXc hZc H n Acl ε c ρs es (fun hh => Vn hh n) t (hbox n hn)
  have hPd : ∀ n ∈ Finset.range N, ∀ a₀ : Fin 2, DifferentiableAt ℝ
      (fun x' => c • tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x' a₀) x :=
    fun n hn a₀ => ((contDiff_tailFluxPhys hχ hψ hψχ hχψ H n Acl ε c ρs es (fun hh => Vn hh n)
      t (hLc n (Finset.mem_range.1 hn)) a₀).differentiable one_ne_zero x).const_smul c
  have hdiv : ∑ a₀ : Fin 2, fderiv ℝ (fun x' => liftFluxPhys ψ H N Acl ε c ρs es Vn t x' a₀) x
      (basisVec a₀) =
      ∑ n ∈ Finset.range N, c • ∑ i₀ : Fin 2,
        fderiv ℝ (fun y' => tailFluxLabel H n Acl ε c ρs es (fun hh => Vn hh n) t y' i₀) (ψ x)
          (basisVec i₀) := by
    have h1 : ∀ a₀ : Fin 2, fderiv ℝ (fun x' => liftFluxPhys ψ H N Acl ε c ρs es Vn t x' a₀) x
        (basisVec a₀) = ∑ n ∈ Finset.range N, c • fderiv ℝ (fun x' =>
          tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x' a₀) x (basisVec a₀) := by
      intro a₀
      show fderiv ℝ (fun x' => ∑ n ∈ Finset.range N,
        c • tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x' a₀) x (basisVec a₀) = _
      rw [fderiv_fun_sum fun n hn => hPd n hn a₀]
      simp only [FunLike.coe_sum, Finset.sum_apply]
      refine Finset.sum_congr rfl fun n hn => ?_
      have hdp : DifferentiableAt ℝ (fun x' =>
          tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x' a₀) x :=
        (contDiff_tailFluxPhys hχ hψ hψχ hχψ H n Acl ε c ρs es (fun hh => Vn hh n) t
          (hLc n (Finset.mem_range.1 hn)) a₀).differentiable one_ne_zero x
      rw [fderiv_fun_const_smul hdp c]
      rfl
    rw [Finset.sum_congr rfl fun a₀ _ => h1 a₀, Finset.sum_comm]
    refine Finset.sum_congr rfl fun n hn => ?_
    rw [← Finset.smul_sum, div_tailFluxPhys hχ hψ hψχ hχψ hd H n Acl ε c ρs es
      (fun hh => Vn hh n) t (fun i₀ => (hLc n (Finset.mem_range.1 hn) i₀).differentiable
        one_ne_zero) x]
  rw [labelLift_cleanup hseq hAcl hXc hZc ε hc hρ he A Vn hV ht (ψ x), hdiv, liftForcePhys,
    ← Finset.sum_add_distrib]
  refine congrArg (fun z => A (c⁻¹ * t) (ρs⁻¹ • ψ x) + z) (Finset.sum_congr rfl fun n _ => ?_)
  rw [smul_add]
  rfl

end Label

section Setting

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The tested lift in cleanup form.** In the setting of `labelLift_cleanup_phys`, let the
chart inverse `ψ` be lattice equivariant, `e⁻¹ = M ∈ ℕ`, and let the slow translations by
`ρ⁻¹ℤ²` leave the metric, the source coefficients and the coarse field at the cell time
invariant. Then for a `C¹` periodic test `φt` the tested lift on the cell is the tested field
minus the tested cleanup flux plus the tested cleanup force; the flux, the force and the lift
are continuous. -/
theorem setting_labelLift_cleanup_tested (sX sZ : ℕ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (sXc sZc Acl : ℕ) (hAcl : 1 ≤ Acl)
    (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc) (ε : ℝ) {c ρs es : ℝ} (hc : c ≠ 0) (hρ : ρs ≠ 0)
    (he : es ≠ 0) (A : ℝ → Vec 2 → ∀ i, h i)
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ hh, hh ≤ H → ∀ n, n < N → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
      (liftApply (n + 1) (Cc hh (n + 1)) A τ) (fun _ _ _ => 0) (fun j => Vn hh n j τ))
    {t : ℝ} (ht : c⁻¹ * t ∈ Set.Icc a b) (hA : Continuous (A (c⁻¹ * t)))
    {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ) (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ)
    (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x) (hd : ∀ y, (jacMatrix χ y).det = 1)
    (hψl : ∀ (n : Fin 2 → ℤ) (x : Vec 2), ψ (x + latticeShift n) = ψ x + latticeShift n)
    (M : ℕ) (hM : es⁻¹ = M)
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρs⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρs⁻¹ • latticeShift n) z = γ.coeff α t X z)
    (hAp : ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      A (c⁻¹ * t) (X + ρs⁻¹ • latticeShift n) = A (c⁻¹ * t) X)
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    (∫ x in AVenhance.unitCube, inner ℝ (labelLift Cc N H ε A ρs es c t (ψ x) v) (φt x) =
      (∫ x in AVenhance.unitCube, inner ℝ (A (c⁻¹ * t) (ρs⁻¹ • ψ x) v) (φt x))
        - (∫ x in AVenhance.unitCube, ∑ a₀ : Fin 2,
          inner ℝ (liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ v) (fderiv ℝ φt x (basisVec a₀)))
        + ∫ x in AVenhance.unitCube,
          inner ℝ (liftForcePhys ψ H N Acl ε c ρs es Vn t x v) (φt x)) ∧
      (∀ a₀ : Fin 2, Continuous (fun x => liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ v)) ∧
      Continuous (fun x => liftForcePhys ψ H N Acl ε c ρs es Vn t x v) ∧
      Continuous (fun x => labelLift Cc N H ε A ρs es c t (ψ x) v) := by
  have hbox : ∀ n, n < N → ∀ hh, hh ≤ H → ∀ j, j < Acl →
      IsBoxSmooth sXc sZc (Vn hh n j (c⁻¹ * t)) := fun n hn hh hhh =>
    cleanupChain_zeroFlux_box (hV hh hhh n hn _ ht)
  -- the chains at the cell time are slow invariant for `ρ⁻¹ℤ²` and fast periodic
  have hslow : ∀ n, n < N → ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ (m : Fin 2 → ℤ) (X : Vec 2),
      Vn hh n j (c⁻¹ * t) (X + ρs⁻¹ • latticeShift m) = Vn hh n j (c⁻¹ * t) X := by
    intro n hn hh hhh j hj m X
    refine isCleanupChain_slow_invariant hZc (ρs⁻¹ • latticeShift m) (fun X' => ?_)
      (fun _ => rfl) (hV hh hhh n hn _ ht) j hj X
    funext z
    exact liftApply_slow_invariant (n + 1) (Cc hh (n + 1)) A (c⁻¹ * t) (ρs⁻¹ • latticeShift m)
      (fun m' α X'' z' v' u' =>
        LiftMeanEntrywise.setting_liftSequence_slowShift_invariant P sX sZ Cc hseq
          (ρs⁻¹ • latticeShift m) (hGs m) (hcs m) hh hhh (n + 1) m' α (c⁻¹ * t) ht X'' z' v' u')
      (hAp m) X' z
  have hfast : ∀ n, n < N → ∀ hh, hh ≤ H → ∀ j, j < Acl → ∀ X,
      IsZ2Periodic (Vn hh n j (c⁻¹ * t) X) := fun n hn hh hhh =>
    (hV hh hhh n hn _ ht).periodic (F₀ := fun _ _ _ => 0) (fun _ _ _ => rfl)
  -- the physical fluxes of the degrees are `C¹` and periodic, the forces continuous
  have hLc : ∀ n, n < N → ∀ i₀, ContDiff ℝ 1
      (fun y => tailFluxLabel H n Acl ε c ρs es (fun hh => Vn hh n) t y i₀) := fun n hn =>
    contDiff_tailFluxLabel hXc hZc H n Acl ε c ρs es (fun hh => Vn hh n) t (hbox n hn)
  have hF : ∀ n, n < N → ∀ a₀, ContDiff ℝ 1
      (fun x => tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x a₀) := fun n hn =>
    contDiff_tailFluxPhys hχ hψ hψχ hχψ H n Acl ε c ρs es (fun hh => Vn hh n) t (hLc n hn)
  have hFp : ∀ n, n < N → ∀ a₀, IsZ2Periodic
      (fun x => tailFluxPhys ψ H n Acl ε c ρs es (fun hh => Vn hh n) t x a₀) := fun n hn =>
    tailFluxPhys_isZ2Periodic hψl H n Acl ε c ρs es (fun hh => Vn hh n) t
      (tailFluxLabel_isZ2Periodic H n Acl ε c ρs es (fun hh => Vn hh n) t M hM (hslow n hn)
        (hfast n hn))
  have hGc : ∀ a₀ : Fin 2, ContDiff ℝ 1 (fun x => liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀) :=
    fun a₀ => ContDiff.sum fun n hn => (hF n (Finset.mem_range.1 hn) a₀).const_smul c
  have hGv : ∀ a₀ : Fin 2, ContDiff ℝ 1
      (fun x => liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ v) := fun a₀ =>
    contDiff_pi.1 (hGc a₀) v
  have hGvp : ∀ a₀ : Fin 2,
      IsZ2Periodic (fun x => liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ v) := by
    intro a₀ m x
    show liftFluxPhys ψ H N Acl ε c ρs es Vn t (x + latticeShift m) a₀ v =
      liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ v
    simp only [liftFluxPhys]
    exact congrFun (Finset.sum_congr rfl fun n hn => congrArg (fun z => c • z)
      (hFp n (Finset.mem_range.1 hn) a₀ m x)) v
  have hR : Continuous (fun x => liftForcePhys ψ H N Acl ε c ρs es Vn t x v) :=
    (continuous_apply v).comp (continuous_finsetSum _ fun n hn =>
      (continuous_tailForcePhys hψ.continuous H n Acl ε c ρs es (fun hh => Vn hh n) t
        fun hh hhh => continuous_cleanupRemainder_sample hAcl hXc c⁻¹ ρs es t
          (hbox n (Finset.mem_range.1 hn) hh hhh)).const_smul c)
  have hAc : Continuous (fun x => A (c⁻¹ * t) (ρs⁻¹ • ψ x) v) :=
    (continuous_apply v).comp (hA.comp (hψ.continuous.const_smul ρs⁻¹))
  -- the pointwise identity, componentwise
  have hpt : ∀ x, labelLift Cc N H ε A ρs es c t (ψ x) v = A (c⁻¹ * t) (ρs⁻¹ • ψ x) v +
      (∑ a₀ : Fin 2, fderiv ℝ (fun x' => liftFluxPhys ψ H N Acl ε c ρs es Vn t x' a₀ v) x
          (basisVec a₀)
        + liftForcePhys ψ H N Acl ε c ρs es Vn t x v) := by
    intro x
    rw [labelLift_cleanup_phys hseq hAcl hXc hZc ε hc hρ he A Vn hV ht hχ hψ hψχ hχψ hd x]
    simp only [Pi.add_apply, Finset.sum_apply]
    refine congrArg (fun z => A (c⁻¹ * t) (ρs⁻¹ • ψ x) v + (z + _)) ?_
    exact Finset.sum_congr rfl fun a₀ _ =>
      tail_fderiv_pi_coord ((hGc a₀).differentiable one_ne_zero x) (basisVec a₀) v
  refine ⟨?_, fun a₀ => (hGv a₀).continuous, hR,
    (hAc.add ((continuous_finsetSum _ fun a₀ _ => cell_continuous_partial (hGv a₀) a₀).add
      hR)).congr fun x => (hpt x).symm⟩
  have hi0 : Integrable (fun x => inner ℝ (A (c⁻¹ * t) (ρs⁻¹ • ψ x) v) (φt x))
      (volume.restrict AVenhance.unitCube) :=
    cell_integrable_inner_continuous hAc hφt.continuous
  have hi1 : Integrable (fun x => inner ℝ (∑ a₀ : Fin 2,
      fderiv ℝ (fun x' => liftFluxPhys ψ H N Acl ε c ρs es Vn t x' a₀ v) x (basisVec a₀))
      (φt x)) (volume.restrict AVenhance.unitCube) :=
    cell_integrable_inner_continuous
      (continuous_finsetSum _ fun a₀ _ => cell_continuous_partial (hGv a₀) a₀) hφt.continuous
  have hi2 : Integrable (fun x => inner ℝ (liftForcePhys ψ H N Acl ε c ρs es Vn t x v) (φt x))
      (volume.restrict AVenhance.unitCube) :=
    cell_integrable_inner_continuous hR hφt.continuous
  simp only [hpt, inner_add_left]
  rw [integral_add hi0 (hi1.fun_add hi2), integral_add hi1 hi2, cell_ibp_div hGv hGvp hφt hφtp]
  ring

end Setting
end

/-! **Cleanup chains of the positive degrees of a lift exist** (the same cleanup is applied to
`g_n = C_n^{(h)} div_X (F_c)_ρ`). For a lift sequence in a lift setting and a chart-frame field
that is smooth at every cell time of the window, the data `(C_{n+1}^{(hh)} A, 0)` of every grade
`hh ≤ H` and degree `n + 1 ≤ N` are box smooth (the coefficients are, with the reserves of the
setting), periodic in the fast variable and of zero cell mean (the positive lifts are centered),
so their cleanup chains exist (`exists_isCleanupChain_pi`); `setting_exists_lift_cleanupChain`
chooses them for all grades, degrees and window times at once. -/

section
variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, CompleteSpace (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

include P in
/-- **Cleanup chains of the positive degrees of the lift of a smooth field exist.** -/
theorem setting_exists_lift_cleanupChain (sX sZ : ℕ) (hsZ : 1 ≤ sZ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ a b N H Cc)
    (sXc sZc Acl : ℕ) (hXc : 1 ≤ sXc) (hZc : 1 ≤ sZc)
    (hX : sXc + Acl ≤ K + N + 2 * D + 2) (hZ : sZc + 1 ≤ max k (L + 2) + 2 * D)
    (A : ℝ → Vec 2 → ∀ i, h i) (hA : ∀ τ ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (A τ)) :
    ∃ Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i,
      ∀ hh, hh ≤ H → ∀ n, n < N → ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl
        (liftApply (n + 1) (Cc hh (n + 1)) A τ) (fun _ _ _ => 0) (fun j => Vn hh n j τ) := by
  classical
  have hex : ∀ hh n τ, hh ≤ H → n < N → τ ∈ Set.Icc a b →
      ∃ W : ℕ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i, IsCleanupChain sXc sZc Acl
        (liftApply (n + 1) (Cc hh (n + 1)) A τ) (fun _ _ _ => 0) W := by
    intro hh n τ hhh hn hτ
    have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq
      (sXc + Acl) (sZc + 1) hX hZ hh hhh (n + 1)
    have hcbox : ∀ m (α : DerivativeWord2 m) v u, IsBoxSmooth (sXc + Acl) (sZc + 1)
        (fun X y => Cc hh (n + 1) m α τ X y v u) := by
      intro m α v u
      by_cases hm : m ≤ n + 1
      · exact data.box m hm α v u τ hτ
      · have hz : (fun X y => Cc hh (n + 1) m α τ X y v u) = fun _ _ => 0 := by
          funext X y
          exact hseq.2.2.2.1 hh hhh (n + 1) m (by omega) α τ X y v u
        rw [hz]
        exact isBoxSmooth_zero _ _
    have hf : IsBoxSmooth (sXc + Acl) (sZc + 1) (liftApply (n + 1) (Cc hh (n + 1)) A τ) :=
      TailDiff.isBoxSmooth_pi fun v =>
        QuietDecay.Partition.isBoxSmooth_liftApply (n + 1) _ _ (Cc hh (n + 1)) A τ hcbox
          ((hA τ hτ).of_le (by exact_mod_cast le_top)) v
    have hfp : ∀ X, IsZ2Periodic (liftApply (n + 1) (Cc hh (n + 1)) A τ X) := fun X =>
      liftApply_isZ2Periodic (n + 1) (Cc hh (n + 1)) A τ X
        (fun m α v u => (hseq.2.2.2.2.2.1 hh hhh (n + 1) m α v u τ hτ).2 X)
    have hfm : ∀ X, fieldCellMean (liftApply (n + 1) (Cc hh (n + 1)) A τ X) = 0 := fun X =>
      liftSequence_tested_mean_zero Q sX sZ a b N H Cc hseq hh (n + 1) hhh (Nat.succ_pos n)
        (Nat.succ_le_of_lt hn) A τ hτ X
    exact exists_isCleanupChain_pi sXc sZc Acl hXc hZc _ _ hf hfp hfm (isBoxSmooth_zero _ _)
      (fun _ _ _ => rfl) (fun _ _ => fieldCellMean_const 0)
  refine ⟨fun hh n j τ => if hc : hh ≤ H ∧ n < N ∧ τ ∈ Set.Icc a b then
    Classical.choose (hex hh n τ hc.1 hc.2.1 hc.2.2) j else 0, fun hh hhh n hn τ hτ => ?_⟩
  have he : (fun j => (if hc : hh ≤ H ∧ n < N ∧ τ ∈ Set.Icc a b then
      Classical.choose (hex hh n τ hc.1 hc.2.1 hc.2.2) j else 0)) =
      Classical.choose (hex hh n τ hhh hn hτ) :=
    funext fun j => dite_eq_left ⟨hhh, hn, hτ⟩
  rw [he]
  exact Classical.choose_spec (hex hh n τ hhh hn hτ)
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Linearity of the residual pieces**. The residual of the glued lift of a
difference of two coarse fields is the difference of the residuals: the lift is linear in a
sufficiently smooth input (`liftApply_sub_input`, hence the tail fields `tailScalarField_sub_input`,
`tailFluxField_sub_input`), and the sampled cleanup flux and remainder, and the physical tail and
lifted coarse fluxes and forces built from them, are linear in the cleanup chains
(`cleanupFlux_sub_chain`, `cleanupRemainder_sub_chain`, `tailFluxPhys_sub_chain`,
`tailForcePhys_sub_chain`, `liftFluxPhys_sub_chain`, `liftForcePhys_sub_chain`). With
`IsCleanupChain.sub` this bounds the difference of the residuals of two Galerkin approximants by
the slice estimates applied to the difference of the approximants. -/

section Chains

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The sampled cleanup flux of a difference of chains. -/
theorem cleanupFlux_sub_chain (c ρ e : ℝ) (A : ℕ) (W W' : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (t : ℝ) (x : Vec 2) (k : Fin 2) :
    cleanupFlux c ρ e A (fun j τ X z k' => W j τ X z k' - W' j τ X z k') t x k =
      cleanupFlux c ρ e A W t x k - cleanupFlux c ρ e A W' t x k := by
  simp only [cleanupFlux, diagSample, smul_sub, Finset.sum_sub_distrib]

/-- The sampled cleanup remainder of a difference of chains whose last members are slowly
differentiable. -/
theorem cleanupRemainder_sub_chain (c ρ e : ℝ) (A : ℕ)
    (W W' : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hW : ∀ z k, Differentiable ℝ (fun X => W (A - 1) (c * t) X z k))
    (hW' : ∀ z k, Differentiable ℝ (fun X => W' (A - 1) (c * t) X z k)) (x : Vec 2) :
    cleanupRemainder c ρ e A (fun j τ X z k' => W j τ X z k' - W' j τ X z k') t x =
      cleanupRemainder c ρ e A W t x - cleanupRemainder c ρ e A W' t x := by
  have hfd : ∀ z k X, fderiv ℝ (fun X' => W (A - 1) (c * t) X' z k -
      W' (A - 1) (c * t) X' z k) X = fderiv ℝ (fun X' => W (A - 1) (c * t) X' z k) X -
        fderiv ℝ (fun X' => W' (A - 1) (c * t) X' z k) X :=
    fun z k X => fderiv_fun_sub (hW z k X) (hW' z k X)
  simp only [cleanupRemainder, diagSample, cleanupSource, slowPartial, hfd,
    sub_apply, Finset.sum_sub_distrib, neg_sub, smul_sub, smul_neg]
  abel

end Chains

section Fields

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **The lift of a difference of inputs.** -/
theorem liftApply_sub_input (n : ℕ) (c : LiftCoeff ι h) (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ)
    (ha : ContDiff ℝ (n : ℕ∞) (a t)) (hb : ContDiff ℝ (n : ℕ∞) (b t)) (X z : Vec 2) :
    liftApply n c (fun s Y => a s Y - b s Y) t X z =
      liftApply n c a t X z - liftApply n c b t X z := by
  funext v
  simp only [liftApply, Pi.sub_apply, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m hm => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have hmn : ((m : ℕ∞) : WithTop ℕ∞) ≤ ((n : ℕ∞) : WithTop ℕ∞) := by
    exact_mod_cast Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  rw [orderedDerivative_sub α (ha.of_le hmn) (hb.of_le hmn)]
  simp only [Pi.sub_apply, map_sub]

/-- The scalar tail field of a difference of inputs. -/
theorem tailScalarField_sub_input (f : ℕ → LiftCoeff ι h) (N D : ℕ) (ε : ℝ)
    (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ha : ContDiff ℝ ((2 * N + D : ℕ) : ℕ∞) (a t))
    (hb : ContDiff ℝ ((2 * N + D : ℕ) : ℕ∞) (b t)) (X z : Vec 2) :
    tailScalarField f N D ε (fun s Y => a s Y - b s Y) t X z =
      tailScalarField f N D ε a t X z - tailScalarField f N D ε b t X z := by
  simp only [tailScalarField]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [liftApply_sub_input _ _ a b t ha hb, smul_sub]

/-- The flux tail field of a difference of inputs. -/
theorem tailFluxField_sub_input (F : ℕ → Fin 2 → LiftCoeff ι h) (N D : ℕ) (ε : ℝ)
    (a b : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (ha : ContDiff ℝ ((2 * N + D : ℕ) : ℕ∞) (a t))
    (hb : ContDiff ℝ ((2 * N + D : ℕ) : ℕ∞) (b t)) (X z : Vec 2) (k : Fin 2) :
    tailFluxField F N D ε (fun s Y => a s Y - b s Y) t X z k =
      tailFluxField F N D ε a t X z k - tailFluxField F N D ε b t X z k := by
  simp only [tailFluxField]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [liftApply_sub_input _ _ a b t ha hb, smul_sub]

end Fields

section Physical

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The physical tail flux of a difference of chains. -/
theorem tailFluxPhys_sub_chain (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc Vc' : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2) (a₀ : Fin 2) :
    tailFluxPhys ψ H N Acl ε c ρs es (fun hh j τ X z k => Vc hh j τ X z k - Vc' hh j τ X z k)
        t x a₀ =
      tailFluxPhys ψ H N Acl ε c ρs es Vc t x a₀ - tailFluxPhys ψ H N Acl ε c ρs es Vc' t x a₀ := by
  simp only [tailFluxPhys, tailFluxLabel, cleanupFlux_sub_chain, smul_sub,
    Finset.sum_sub_distrib]

/-- The physical tail force of a difference of chains whose last members are slowly
differentiable. -/
theorem tailForcePhys_sub_chain (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vc Vc' : ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hVc : ∀ hh, hh ≤ H → ∀ z k, Differentiable ℝ (fun X => Vc hh (Acl - 1) (c⁻¹ * t) X z k))
    (hVc' : ∀ hh, hh ≤ H → ∀ z k, Differentiable ℝ (fun X => Vc' hh (Acl - 1) (c⁻¹ * t) X z k))
    (x : Vec 2) :
    tailForcePhys ψ H N Acl ε c ρs es (fun hh j τ X z k => Vc hh j τ X z k - Vc' hh j τ X z k)
        t x =
      tailForcePhys ψ H N Acl ε c ρs es Vc t x - tailForcePhys ψ H N Acl ε c ρs es Vc' t x := by
  simp only [tailForcePhys]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun hh hhm => ?_
  have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
  rw [cleanupRemainder_sub_chain c⁻¹ ρs es Acl (Vc hh) (Vc' hh) t (hVc hh hhh) (hVc' hh hhh),
    smul_sub, smul_sub]

/-- The physical lifted coarse flux of a difference of chains. -/
theorem liftFluxPhys_sub_chain (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vn Vn' : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ) (x : Vec 2) (a₀ : Fin 2) :
    liftFluxPhys ψ H N Acl ε c ρs es
        (fun hh n j τ X z k => Vn hh n j τ X z k - Vn' hh n j τ X z k) t x a₀ =
      liftFluxPhys ψ H N Acl ε c ρs es Vn t x a₀ - liftFluxPhys ψ H N Acl ε c ρs es Vn' t x a₀ := by
  simp only [liftFluxPhys]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [← smul_sub]
  congr 1
  exact tailFluxPhys_sub_chain ψ H n Acl ε c ρs es (fun hh => Vn hh n) (fun hh => Vn' hh n) t x a₀

/-- The physical lifted coarse force of a difference of chains whose last members are slowly
differentiable. -/
theorem liftForcePhys_sub_chain (ψ : Vec 2 → Vec 2) (H N Acl : ℕ) (ε c ρs es : ℝ)
    (Vn Vn' : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (t : ℝ)
    (hVn : ∀ hh, hh ≤ H → ∀ n, n < N → ∀ z k,
      Differentiable ℝ (fun X => Vn hh n (Acl - 1) (c⁻¹ * t) X z k))
    (hVn' : ∀ hh, hh ≤ H → ∀ n, n < N → ∀ z k,
      Differentiable ℝ (fun X => Vn' hh n (Acl - 1) (c⁻¹ * t) X z k)) (x : Vec 2) :
    liftForcePhys ψ H N Acl ε c ρs es
        (fun hh n j τ X z k => Vn hh n j τ X z k - Vn' hh n j τ X z k) t x =
      liftForcePhys ψ H N Acl ε c ρs es Vn t x - liftForcePhys ψ H N Acl ε c ρs es Vn' t x := by
  simp only [liftForcePhys]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [← smul_sub]
  congr 1
  exact tailForcePhys_sub_chain ψ H n Acl ε c ρs es (fun hh => Vn hh n) (fun hh => Vn' hh n) t
    (fun hh hhh => hVn hh hhh n (Finset.mem_range.1 hn))
    (fun hh hhh => hVn' hh hhh n (Finset.mem_range.1 hn)) x

end Physical

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory AVRegularity.Sobolev
open AVRegularity.CycleComparison.Lift
namespace AVRegularity.CycleComparison.Reconstruction

/-! **Time measurability of the lift coefficients and of the cleanup chains of a lift setting**.
In a lift setting with a lift sequence `Cc` on the window `[a, b]`, measurability
is measured in the clamped time `t ↦ Set.projIcc a b t`, so that nothing is assumed outside the
window.

* `setting_tailLeftCoefficient_dual_measurable`: the literal tail left coefficients are
  measurable in time. Their normalized actions on exponential tests are the normalized tails
  `liftTail_normalized_component_expansion`, measurable by the uncentered data of the setting
  (`setting_tail_uncentered_data`) and the ordered mean corrections
  (`ambient_ordered_mean_clamped_dual_measurable`); the coefficients are recovered from finitely
  many tests (`liftCoefficient_dual_measurable_of_finite_tests`).
* `setting_tailFluxCoefficient_clamped_measurable`: the tail flux coefficients, the centered
  transverse primitives of the positive tail left coefficients, are measurable in time
  (`measurable_centeredIntervalPrimitive_param`, Carathéodory in the fast variable).
* `setting_tailFluxField_clamped_measurable`: the divided tail flux field of a coarse field
  measurable in time is measurable in time.
* `setting_tail_chain_measurable`, `setting_lift_chain_measurable`: every cleanup chain of the
  divided tail of a coarse field, and of a positive degree of the lift of a coarse field, and its
  last source, are measurable in clamped time (`isCleanupChain_time_measurable_pi`), under the
  orders `(sX + A, sZ + 1)` of the existence of the chains.
* `cleanupChain_joint_measurable`, `cleanupSource_joint_measurable`,
  `setting_liftApply_joint_measurable`: the same, jointly in the clamped time and `(X, z)`
  (Carathéodory: the members are box smooth). -/

/-! ### Generic tools -/

/-- A point of the window is fixed by the clamp. -/
theorem projIcc_val_of_mem {a b : ℝ} (hab : a ≤ b) {x : ℝ} (hx : x ∈ Set.Icc a b) :
    (Set.projIcc a b hab x : ℝ) = x :=
  congrArg Subtype.val (Set.projIcc_of_mem hab hx)

/-- Every finite order of smoothness is below the smooth order. -/
theorem order_natCast_le_top (r : ℕ) : ((r : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

/-- A box-smooth field is jointly continuous. -/
theorem isBoxSmooth_continuous_uncurry {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {sX sZ : ℕ} {f : Vec 2 → Vec 2 → E} (hf : IsBoxSmooth sX sZ f) :
    Continuous fun q : Vec 2 × Vec 2 => f q.1 q.2 :=
  (hf.contDiff_uncurry (Nat.zero_le _) (Nat.zero_le _)).continuous

/-- **Carathéodory in clamped time.** A family that is continuous in `(X, z)` at the times of
the window and measurable in clamped time at every `(X, z)` is jointly measurable. -/
theorem measurable_clamped_of_continuous {E : Type*} [TopologicalSpace E]
    [TopologicalSpace.PseudoMetrizableSpace E] [MeasurableSpace E] [BorelSpace E] {a b : ℝ}
    (hab : a ≤ b)
    (f : ℝ → Vec 2 → Vec 2 → E)
    (hc : ∀ τ ∈ Set.Icc a b, Continuous fun q : Vec 2 × Vec 2 => f τ q.1 q.2)
    (hm : ∀ X z, Measurable fun τ => f (Set.projIcc a b hab τ) X z) :
    Measurable fun q : ℝ × Vec 2 × Vec 2 => f (Set.projIcc a b hab q.1) q.2.1 q.2.2 :=
  (measurable_uncurry_of_continuous_of_measurable
    (u := fun (y : Vec 2 × Vec 2) (τ : ℝ) => f (Set.projIcc a b hab τ) y.1 y.2)
    (fun τ => hc _ (Set.projIcc a b hab τ).2) (fun y => hm y.1 y.2)).comp measurable_swap

/-- **Carathéodory on `ℝ × ℝ`**: a function continuous in the second variable and measurable in
the first is jointly measurable. -/
theorem measurable_prod_of_continuous_right {β : Type*} [TopologicalSpace β]
    [TopologicalSpace.PseudoMetrizableSpace β] [MeasurableSpace β] [BorelSpace β]
    (Fn : ℝ → ℝ → β) (hc : ∀ t, Continuous (Fn t)) (hm : ∀ r, Measurable fun t => Fn t r) :
    Measurable fun p : ℝ × ℝ => Fn p.1 p.2 :=
  (measurable_uncurry_of_continuous_of_measurable (u := fun r t => Fn t r) hc hm).comp
    measurable_swap

/-- An interval primitive of a jointly measurable family is measurable in the parameter. -/
theorem measurable_intervalIntegral_param {T F : Type*} [MeasurableSpace T]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [MeasurableSpace F] [BorelSpace F]
    [SecondCountableTopology F] (g : T → ℝ → F)
    (hg : Measurable fun p : T × ℝ => g p.1 p.2) (r : ℝ) :
    Measurable fun t => ∫ y in (0 : ℝ)..r, g t y := by
  have hs : StronglyMeasurable (Function.uncurry g) := hg.stronglyMeasurable
  have h1 : Measurable fun t => ∫ y in Set.Ioc (0 : ℝ) r, g t y :=
    (hs.integral_prod_right (ν := volume.restrict (Set.Ioc (0 : ℝ) r))).measurable
  have h2 : Measurable fun t => ∫ y in Set.Ioc r (0 : ℝ), g t y :=
    (hs.integral_prod_right (ν := volume.restrict (Set.Ioc r (0 : ℝ)))).measurable
  exact h1.fun_sub h2

/-- The centered periodic primitive of a jointly measurable family of continuous functions is
measurable in the parameter. -/
theorem measurable_centeredIntervalPrimitive_param {T F : Type*} [MeasurableSpace T]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F] [MeasurableSpace F]
    [BorelSpace F] [SecondCountableTopology F] (g : T → ℝ → F)
    (hg : Measurable fun p : T × ℝ => g p.1 p.2) (hc : ∀ t, Continuous (g t)) (r : ℝ) :
    Measurable fun t => centeredIntervalPrimitive (g t) r := by
  have hP : ∀ s : ℝ, Measurable fun t => ∫ y in (0 : ℝ)..s, g t y :=
    measurable_intervalIntegral_param g hg
  have hPc : ∀ t, Continuous fun s : ℝ => ∫ y in (0 : ℝ)..s, g t y := fun t =>
    intervalIntegral.continuous_primitive (fun a b => (hc t).intervalIntegrable a b) 0
  have hPj : Measurable fun p : T × ℝ => ∫ y in (0 : ℝ)..p.2, g p.1 y :=
    (measurable_uncurry_of_continuous_of_measurable
      (u := fun (s : ℝ) (t : T) => ∫ y in (0 : ℝ)..s, g t y) hPc hP).comp measurable_swap
  exact (hP r).fun_sub
    (measurable_intervalIntegral_param (fun t s => ∫ y in (0 : ℝ)..s, g t y) hPj 1)

/-- A lift action is measurable in clamped time when its coefficients are and the field is
measurable in clamped time and smooth on the window. -/
theorem liftApply_clamped_measurable_of_coeff {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    {a b : ℝ} (hab : a ≤ b) (R : ℕ) (c : LiftCoeff ι h)
    (hc : ∀ m, m ≤ R → ∀ (α : DerivativeWord2 m) (v u : ι) (X z : Vec 2),
      Measurable fun t => c m α (Set.projIcc a b hab t) X z v u)
    (g : ℝ → Vec 2 → ∀ i, h i) (hg : ∀ t ∈ Set.Icc a b, ContDiff ℝ (R : ℕ∞) (g t))
    (hgm : ∀ X, Measurable fun t => g (Set.projIcc a b hab t) X) (v : ι) (X z : Vec 2) :
    Measurable fun t => liftApply R c g (Set.projIcc a b hab t) X z v := by
  unfold liftApply
  apply Finset.measurable_sum
  intro m hm
  have hmR : m ≤ R := Nat.lt_succ_iff.1 (Finset.mem_range.1 hm)
  apply Finset.measurable_sum
  intro α _
  apply Finset.measurable_sum
  intro u _
  have hword := orderedDerivative_parameter_measurable
    (fun t => g (Set.projIcc a b hab t)) R hgm
    (fun t => hg _ (Set.projIcc a b hab t).2) m hmR α X
  have heval : Continuous (fun pair : (h u →L[ℝ] h v) × h u => pair.1 pair.2) :=
    continuous_fst.clm_apply continuous_snd
  exact heval.measurable.comp ((hc m hmR α v u X z).prodMk ((measurable_pi_apply u).comp hword))

/-- The divided tail scalar field of the zero arrays vanishes. -/
theorem tailScalarField_zero_coeff {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] (N D : ℕ) (ε : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (X z : Vec 2) :
    tailScalarField (fun _ => (0 : LiftCoeff ι h)) N D ε A t X z = 0 := by
  have h0 : liftApply (2 * N + D) (0 : LiftCoeff ι h) A = 0 :=
    liftApply_of_coeff_zero (2 * N + D) 0 (fun _ _ _ _ _ _ _ => rfl) A
  simp only [tailScalarField, h0, Pi.zero_apply, smul_zero, Finset.sum_const_zero]

/-! ### The tail coefficients of a lift setting -/

/-- **The normalized tail on exponential tests is measurable in clamped time.** -/
theorem setting_liftTail_normalized_clamped_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (A : Vec 2 →L[ℝ] ℝ) (u v : ι) (ξ : h u) (X z : Vec 2) :
    Measurable fun t => (Real.exp ((lam • A) X))⁻¹ • liftTailCoeff Q Cc N
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n
        (Set.projIcc a b P.window t) X z v := by
  have hlam : 0 ≤ lam := by rw [P.lam_eq]; exact (div_pos P.ρ_pos P.E_pos).le
  have hunc := setting_tail_uncentered_data P sX sZ hsZ Cc hseq 0 0 (Nat.zero_le _)
    (Nat.zero_le _) hh hhh n hn
  have h1 : Measurable fun t => (Real.exp ((lam • A) X))⁻¹ • liftA Q Cc
      (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) hh n
        (Set.projIcc a b P.window t) X z v :=
    measurable_of_all_real_duals _ fun l => hunc.measurable A u v ξ l X z
  have h2 : ∀ r ∈ Finset.range (N + 1), r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D →
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal hh, Measurable fun t =>
        (Real.exp ((lam • A) X))⁻¹ • liftApply r (Cc p.1 r)
          (liftMean Q Cc (fun _ Y => Real.exp ((lam • A) Y) • Pi.single u ξ) p.2 (n - r))
          (Set.projIcc a b P.window t) X z v := by
    intro r hr hg p hp
    obtain ⟨-, hg2, -⟩ := hg
    have hpq := Finset.HasAntidiagonal.mem_antidiagonal.mp hp
    have hrN : r ≤ N := Nat.lt_succ_iff.1 (Finset.mem_range.1 hr)
    have coef := TailConstructed.setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq 0 0
      (Nat.zero_le _) (Nat.zero_le _) p.1 (by omega) r
    have mean := setting_tail_uncentered_data P sX sZ hsZ Cc hseq r 0 (by omega)
      (Nat.zero_le _) p.2 (by omega) (n - r) (by omega)
    exact measurable_of_all_real_duals _ fun l =>
      ambient_ordered_mean_clamped_dual_measurable par a b P.window lam hlam r (n - r) 0 0 r 0
        p.2 le_rfl Q Cc (Cc p.1 r) _ _ _ coef mean A u v ξ l X z
  simp only [liftTail_normalized_component_expansion]
  refine h1.fun_sub (Finset.measurable_sum _ fun r hr => ?_)
  by_cases hg : r ≤ n ∧ 2 ≤ n - r ∧ n - r ≤ N + D
  · simp only [ite_eq_left hg]
    exact Finset.measurable_sum _ fun p hp => h2 r hr hg p hp
  · simp only [ite_eq_right hg]
    exact measurable_const

/-- **The tail left coefficients of a lift setting are measurable in clamped time.** -/
theorem setting_tailLeftCoefficient_dual_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (hm : m ≤ n) (α : DerivativeWord2 m) (X z : Vec 2) (v u : ι)
    (l : (h u →L[ℝ] h v) →L[ℝ] ℝ) :
    Measurable fun t =>
      l (tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X z v u) := by
  have hlam : 0 < lam := by rw [P.lam_eq]; exact div_pos P.ρ_pos P.E_pos
  refine liftCoefficient_dual_measurable_of_finite_tests n m hm (tailLeftCoefficient Q Cc N hh n)
    lam hlam.ne' (fun β σ => tailLeftCoefficient_perm Q Cc N hh n m β σ) α a b P.window X z v u
    l fun ξ l' j s => ?_
  have hmeas := setting_liftTail_normalized_clamped_measurable P sX sZ (by omega) Cc hseq hh hhh
    n hn ((s : ℝ) • coordinateSymbolDirection (j : ℝ)) u v ξ X z
  have e : (fun t => (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
      liftApply n (tailLeftCoefficient Q Cc N hh n)
        (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
          Pi.single u ξ) (Set.projIcc a b P.window t) X z v) =
      fun t => (Real.exp ((lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
        liftTailCoeff Q Cc N
          (fun _ Y => Real.exp ((lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) Y) •
            Pi.single u ξ) hh n (Set.projIcc a b P.window t) X z v := by
    funext t
    rw [smul_comm (s : ℝ) lam (coordinateSymbolDirection (j : ℝ))]
    exact setting_tail_coefficient_normalized_test_eq P sX sZ hsX hsZ Cc hseq hh hhh n hn
      (lam • ((s : ℝ) • coordinateSymbolDirection (j : ℝ))) u v ξ (Set.projIcc a b P.window t)
      (Set.projIcc a b P.window t).2 X z
  have hm2 : Measurable fun t =>
      (Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) X))⁻¹ •
        liftApply n (tailLeftCoefficient Q Cc N hh n)
          (fun _ Y => Real.exp (((s : ℝ) • (lam • coordinateSymbolDirection (j : ℝ))) Y) •
            Pi.single u ξ) (Set.projIcc a b P.window t) X z v := by
    rw [e]
    exact hmeas
  exact l'.continuous.measurable.comp hm2

/-- The tail left coefficients along a fast line are jointly measurable in clamped time and the
line parameter, and continuous in the line parameter. -/
theorem setting_tailLeftCoefficient_joint
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (m : ℕ) (α : DerivativeWord2 m) (X w : Vec 2) (v u : ι) :
    Measurable (fun p : ℝ × ℝ =>
        tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window p.1) X (p.2 • w) v u) ∧
      ∀ t, Continuous fun r : ℝ =>
        tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X (r • w) v u := by
  by_cases hmn : m ≤ n
  · have hcont : ∀ t, Continuous fun r : ℝ =>
        tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X (r • w) v u := by
      intro t
      have hbox := (setting_tail_coefficient_box_and_bound P sX sZ hsX hsZ Cc hseq 0 0
        (Nat.zero_le _) (Nat.zero_le _) hh hhh n hn m hmn α u v _
        (Set.projIcc a b P.window t).2).1
      exact (hbox.1 X).continuous.comp (continuous_id.smul continuous_const)
    have hm : ∀ r : ℝ, Measurable fun t =>
        tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X (r • w) v u :=
      fun r => measurable_of_all_real_duals _ fun l =>
        setting_tailLeftCoefficient_dual_measurable P sX sZ hsX hsZ Cc hseq hh hhh n hn m hmn α
          X (r • w) v u l
    exact ⟨measurable_prod_of_continuous_right (fun t r =>
      tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X (r • w) v u)
      hcont hm, hcont⟩
  · have hz : ∀ t r : ℝ,
        tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X (r • w) v u = 0 :=
      fun t r => tailLeftCoefficient_above_order Q Cc N hh n hn m (by omega) α _ X _ v u
    refine ⟨?_, fun t => ?_⟩
    · have e : (fun p : ℝ × ℝ => tailLeftCoefficient Q Cc N hh n m α
          (Set.projIcc a b P.window p.1) X (p.2 • w) v u) = fun _ => 0 :=
        funext fun p => hz p.1 p.2
      rw [e]
      exact measurable_const
    · have e : (fun r : ℝ => tailLeftCoefficient Q Cc N hh n m α
          (Set.projIcc a b P.window t) X (r • w) v u) = fun _ => 0 :=
        funext fun r => hz t r
      rw [e]
      exact continuous_const

/-- **The tail flux coefficients of a lift setting are measurable in clamped time.** -/
theorem setting_tailFluxCoefficient_clamped_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ) (hn : 1 ≤ n)
    (dir : Fin 2) (m : ℕ) (α : DerivativeWord2 m) (X z : Vec 2) (v u : ι) :
    Measurable fun t =>
      tailFluxCoefficient par Q Cc N hh n dir m α (Set.projIcc a b P.window t) X z v u := by
  by_cases hm : 1 ≤ m ∧ m ≤ 2 * N + D
  · by_cases hd : dir = par.rev
    · have e : (fun t => tailFluxCoefficient par Q Cc N hh n dir m α
          (Set.projIcc a b P.window t) X z v u) = fun t => centeredIntervalPrimitive
            (fun r => tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X
              (r • basisVec par.rev) v u) (z par.rev) := by
        funext t
        simp only [tailFluxCoefficient, positiveFluxLiftCoefficient,
          centeredFluxLiftCoefficient, positiveLiftCoefficient, transverseCenteredFlux,
          ite_eq_left hm, ite_eq_left hd]
      rw [e]
      obtain ⟨hj, hc⟩ := setting_tailLeftCoefficient_joint P sX sZ hsX hsZ Cc hseq hh hhh n hn
        m α X (basisVec par.rev) v u
      exact measurable_centeredIntervalPrimitive_param
        (fun t r => tailLeftCoefficient Q Cc N hh n m α (Set.projIcc a b P.window t) X
          (r • basisVec par.rev) v u) hj hc (z par.rev)
    · have e : (fun t => tailFluxCoefficient par Q Cc N hh n dir m α
          (Set.projIcc a b P.window t) X z v u) = fun _ => 0 := by
        funext t
        simp only [tailFluxCoefficient, positiveFluxLiftCoefficient,
          centeredFluxLiftCoefficient, transverseCenteredFlux, ite_eq_right hd]
      rw [e]
      exact measurable_const
  · have e : (fun t => tailFluxCoefficient par Q Cc N hh n dir m α
        (Set.projIcc a b P.window t) X z v u) = fun _ => 0 :=
      funext fun t => tailFluxCoefficient_outside par dir Q Cc N hh n m α _ X z v u (by omega)
    rw [e]
    exact measurable_const

/-- **The divided tail flux field of a coarse field measurable in time is measurable in
time.** -/
theorem setting_tailFluxField_clamped_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (ε : ℝ)
    (A : ℝ → Vec 2 → ∀ i, h i) (hA : ∀ τ ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (A τ))
    (hAm : ∀ X, Measurable fun τ => A (Set.projIcc a b P.window τ) X)
    (X z : Vec 2) (kk : Fin 2) (v : ι) :
    Measurable fun τ => tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A
      (Set.projIcc a b P.window τ) X z kk v := by
  have e : (fun τ => tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A
      (Set.projIcc a b P.window τ) X z kk v) = fun τ =>
        ∑ n ∈ Finset.Icc (N + 1) (2 * N + D), ε ^ (n - N - 1) •
          liftApply (2 * N + D) (tailFluxCoefficient par Q Cc N hh n kk) A
            (Set.projIcc a b P.window τ) X z v := by
    funext τ
    simp only [tailFluxField, Finset.sum_apply, Pi.smul_apply]
  rw [e]
  refine Finset.measurable_sum _ fun n hn => ?_
  have hn1 : 1 ≤ n := by have := (Finset.mem_Icc.1 hn).1; omega
  exact (liftApply_clamped_measurable_of_coeff P.window (2 * N + D) _
    (fun m _ α v' u X' z' => setting_tailFluxCoefficient_clamped_measurable P sX sZ hsX hsZ Cc
      hseq hh hhh n hn1 kk m α X' z' v' u) A
    (fun τ hτ => (hA τ hτ).of_le (order_natCast_le_top _)) hAm v X z).fun_const_smul
      (ε ^ (n - N - 1))

/-! ### Cleanup chains of a lift setting -/

/-- **The cleanup chains of the divided tail of a coarse field measurable in time are
measurable in clamped time**, and so are their last sources. -/
theorem setting_tail_chain_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) {sXc sZc Acl : ℕ} (hXc : 1 ≤ sXc)
    (hZc : 1 ≤ sZc) (hXA : sXc + Acl ≤ K + D + 2) (hZ1 : sZc + 1 ≤ max (k + 1) (L + 2))
    (ε : ℝ) (A : ℝ → Vec 2 → ∀ i, h i) (hA : ∀ τ ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (A τ))
    (hAm : ∀ X, Measurable fun τ => A (Set.projIcc a b P.window τ) X) (hh : ℕ) (hhh : hh ≤ H)
    (Vc : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hV : ∀ τ ∈ Set.Icc a b, IsCleanupChain sXc sZc Acl (tailScalarField (fun _ => 0) N D ε A τ)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ)
      (fun j => Vc j τ)) :
    (∀ j, j < Acl → ∀ X z kk i,
        Measurable fun τ => Vc j (Set.projIcc a b P.window τ) X z kk i) ∧
      (1 ≤ Acl → ∀ X z i, Measurable fun τ =>
        cleanupSource (fun j => Vc j (Set.projIcc a b P.window τ)) Acl X z i) := by
  have hpres := fun (n : ℕ) (hn1 : N + 1 ≤ n) (hn2 : n ≤ 2 * N + D) =>
    setting_tail_presentation P sX sZ hsX hsZ Cc hseq hh hhh n (by omega) hn2
  have hf : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sXc + Acl) (sZc + 1)
      (tailScalarField (fun _ => 0) N D ε A τ) := fun τ hτ =>
    (isBoxSmooth_tailScalarField_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) hpres ε A hτ (hA τ hτ)).mono hXA hZ1
  have hfp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic
      (tailScalarField (fun _ => 0) N D ε A τ X) := fun τ hτ X =>
    tailScalarField_isZ2Periodic_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) hpres ε A hτ X
  have hfm : ∀ τ ∈ Set.Icc a b, ∀ X,
      fieldCellMean (tailScalarField (fun _ => 0) N D ε A τ X) = 0 := fun τ hτ X =>
    fieldCellMean_tailScalarField_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) hpres ε A hτ (hA τ hτ) X
  have hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sXc + Acl) (sZc + 1)
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ) := fun τ hτ =>
    (isBoxSmooth_tailFluxField_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) hpres ε A hτ (hA τ hτ)).mono hXA hZ1
  have hFp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic
      (tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ X) :=
    fun τ hτ X => tailFluxField_isZ2Periodic_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) hpres ε A hτ X
  have hFm : ∀ τ ∈ Set.Icc a b, ∀ X (kk : Fin 2), fieldCellMean (fun z =>
      tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A τ X z kk) = 0 :=
    fun τ hτ X kk => fieldCellMean_tailFluxField_of_presentation (f := fun _ => 0)
      (F := fun n => tailFluxCoefficient par Q Cc N hh n) hpres ε A hτ (hA τ hτ) X kk
  have hfmeas : ∀ X z i, Measurable fun τ =>
      tailScalarField (fun _ => (0 : LiftCoeff ι h)) N D ε A (Set.projIcc a b P.window τ) X z i :=
    fun X z i => by
      simp only [tailScalarField_zero_coeff, Pi.zero_apply]
      exact measurable_const
  have hFmeas : ∀ X z kk i, Measurable fun τ =>
      tailFluxField (fun n => tailFluxCoefficient par Q Cc N hh n) N D ε A
        (Set.projIcc a b P.window τ) X z kk i := fun X z kk i =>
    setting_tailFluxField_clamped_measurable P sX sZ hsX hsZ Cc hseq hh hhh ε A hA hAm X z kk i
  exact ⟨isCleanupChain_time_measurable_pi hXc hZc P.window _ _ Vc hf hfp hfm hF hFp hFm hfmeas
    hFmeas hV, fun hA1 => cleanupSource_time_measurable_pi hXc hZc hA1 P.window _ _ Vc hf hfp hfm
    hF hFp hFm hfmeas hFmeas hV⟩

/-- **The cleanup chains of a positive degree of the lift of a coarse field measurable in time
are measurable in clamped time**, and so are their last sources. -/
theorem setting_lift_chain_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) {sXl sZl Acl : ℕ} (hXl : 1 ≤ sXl)
    (hZl : 1 ≤ sZl) (hXA : sXl + Acl ≤ K + N + 2 * D + 2)
    (hZ1 : sZl + 1 ≤ max k (L + 2) + 2 * D) (g : ℝ → Vec 2 → ∀ i, h i)
    (hg : ∀ τ ∈ Set.Icc a b, ContDiff ℝ (⊤ : ℕ∞) (g τ))
    (hgm : ∀ X, Measurable fun τ => g (Set.projIcc a b P.window τ) X) (hh : ℕ) (hhh : hh ≤ H)
    (n : ℕ) (hn : n < N) (W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i)
    (hW : ∀ τ ∈ Set.Icc a b, IsCleanupChain sXl sZl Acl (liftApply (n + 1) (Cc hh (n + 1)) g τ)
      (fun _ _ _ => 0) (fun j => W j τ)) :
    (∀ j, j < Acl → ∀ X z kk i,
        Measurable fun τ => W j (Set.projIcc a b P.window τ) X z kk i) ∧
      (1 ≤ Acl → ∀ X z i, Measurable fun τ =>
        cleanupSource (fun j => W j (Set.projIcc a b P.window τ)) Acl X z i) := by
  have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq (sXl + Acl)
    (sZl + 1) hXA hZ1 hh hhh (n + 1)
  have hf : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sXl + Acl) (sZl + 1)
      (liftApply (n + 1) (Cc hh (n + 1)) g τ) := fun τ hτ =>
    TailDiff.isBoxSmooth_pi fun v => QuietDecay.Partition.isBoxSmooth_liftApply (n + 1) _ _
      (Cc hh (n + 1)) g τ (fun m α v' u => TailConstructed.setting_tailRaw_coefficient_box P sX sZ
        hsZ Cc hseq _ _ hXA hZ1 hh hhh (n + 1) m α v' u τ hτ)
      ((hg τ hτ).of_le (order_natCast_le_top _)) v
  have hfp : ∀ τ ∈ Set.Icc a b, ∀ X, AVenhance.IsZ2Periodic
      (liftApply (n + 1) (Cc hh (n + 1)) g τ X) := fun τ hτ X =>
    liftApply_isZ2Periodic (n + 1) (Cc hh (n + 1)) g τ X
      (fun m α v u => (hseq.2.2.2.2.2.1 hh hhh (n + 1) m α v u τ hτ).2 X)
  have hfm : ∀ τ ∈ Set.Icc a b, ∀ X,
      fieldCellMean (liftApply (n + 1) (Cc hh (n + 1)) g τ X) = 0 := fun τ hτ X =>
    liftSequence_tested_mean_zero Q sX sZ a b N H Cc hseq hh (n + 1) hhh (Nat.succ_pos n)
      (Nat.succ_le_of_lt hn) g τ hτ X
  have hfmeas : ∀ X z i, Measurable fun τ =>
      liftApply (n + 1) (Cc hh (n + 1)) g (Set.projIcc a b P.window τ) X z i := fun X z i =>
    data.liftApply_clamped_measurable g (fun τ hτ => (hg τ hτ).of_le (order_natCast_le_top _))
      hgm i X z
  have hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth (sXl + Acl) (sZl + 1)
      ((fun (_ : ℝ) (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) τ) := fun _ _ =>
    isBoxSmooth_zero _ _
  exact ⟨isCleanupChain_time_measurable_pi hXl hZl P.window _
    (fun (_ : ℝ) (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) W hf hfp hfm hF
    (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => fieldCellMean_const 0) hfmeas
    (fun _ _ _ _ => measurable_const) hW,
    fun hA1 => cleanupSource_time_measurable_pi hXl hZl hA1 P.window _
      (fun (_ : ℝ) (_ _ : Vec 2) (_ : Fin 2) => (0 : ∀ i, h i)) W hf hfp hfm hF
      (fun _ _ _ _ _ => rfl) (fun _ _ _ _ => fieldCellMean_const 0) hfmeas
      (fun _ _ _ _ => measurable_const) hW⟩

/-! ### Joint measurability in clamped time and `(X, z)` -/

/-- **A member of a cleanup chain measurable in clamped time is jointly measurable.** -/
theorem cleanupChain_joint_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E] {sX sZ A : ℕ} {a b : ℝ}
    (hab : a ≤ b) {f₀ : ℝ → Vec 2 → Vec 2 → E} {F₀ : ℝ → Vec 2 → Vec 2 → Fin 2 → E}
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth sX sZ (F₀ τ))
    (hV : ∀ τ ∈ Set.Icc a b, IsCleanupChain sX sZ A (f₀ τ) (F₀ τ) (fun j => V j τ))
    (j : ℕ) (hj : j < A) (hm : ∀ X z, Measurable fun τ => V j (Set.projIcc a b hab τ) X z) :
    Measurable fun q : ℝ × Vec 2 × Vec 2 => V j (Set.projIcc a b hab q.1) q.2.1 q.2.2 :=
  measurable_clamped_of_continuous hab (V j) (fun τ hτ => isBoxSmooth_continuous_uncurry
    (IsCleanupChain.isBoxSmooth (hF τ hτ) (hV τ hτ) j hj)) hm

/-- **The last source of a cleanup chain measurable in clamped time is jointly measurable.** -/
theorem cleanupSource_joint_measurable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] {sX sZ A : ℕ} (hsX : 1 ≤ sX) (hA : 1 ≤ A) {a b : ℝ}
    (hab : a ≤ b) {f₀ : ℝ → Vec 2 → Vec 2 → E} {F₀ : ℝ → Vec 2 → Vec 2 → Fin 2 → E}
    (V : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E)
    (hF : ∀ τ ∈ Set.Icc a b, IsBoxSmooth sX sZ (F₀ τ))
    (hV : ∀ τ ∈ Set.Icc a b, IsCleanupChain sX sZ A (f₀ τ) (F₀ τ) (fun j => V j τ))
    (hm : ∀ X z, Measurable fun τ =>
      cleanupSource (fun j => V j (Set.projIcc a b hab τ)) A X z) :
    Measurable fun q : ℝ × Vec 2 × Vec 2 =>
      cleanupSource (fun j => V j (Set.projIcc a b hab q.1)) A q.2.1 q.2.2 := by
  refine measurable_clamped_of_continuous hab
    (fun τ X z => cleanupSource (fun j => V j τ) A X z) (fun τ hτ => ?_) hm
  have hb := IsCleanupChain.isBoxSmooth (hF τ hτ) (hV τ hτ) (A - 1) (by omega)
  have h1 : ∀ kk : Fin 2, IsBoxSmooth 0 0 (slowPartial kk (fun X z => V (A - 1) τ X z kk)) :=
    fun kk => ((hb.mono (by omega : 0 + 1 ≤ sX) (Nat.zero_le sZ)).clm_comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 2 => E) kk)).slowPartial kk
  have hS : IsBoxSmooth 0 0 (cleanupSource (fun j => V j τ) A) :=
    (IsBoxSmooth.sum Finset.univ fun kk _ => h1 kk).neg
  exact isBoxSmooth_continuous_uncurry hS

/-- **A lift action of a lift setting on a coarse field measurable in time is jointly
measurable** in clamped time and `(X, z)`. -/
theorem setting_liftApply_joint_measurable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
    {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)
    (sX sZ : ℕ) (hsZ : 1 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q sX sZ a b N H Cc) (hh : ℕ) (hhh : hh ≤ H) (n : ℕ)
    (g : ℝ → Vec 2 → ∀ i, h i) (hg : ∀ τ ∈ Set.Icc a b, ContDiff ℝ (n : ℕ∞) (g τ))
    (hgm : ∀ X, Measurable fun τ => g (Set.projIcc a b P.window τ) X) (v : ι) :
    Measurable fun q : ℝ × Vec 2 × Vec 2 =>
      liftApply n (Cc hh n) g (Set.projIcc a b P.window q.1) q.2.1 q.2.2 v := by
  have data := TailConstructed.setting_tailRaw_coefficient_data P sX sZ hsZ Cc hseq 0 0
    (Nat.zero_le _) (Nat.zero_le _) hh hhh n
  refine measurable_clamped_of_continuous P.window
    (fun τ X z => liftApply n (Cc hh n) g τ X z v) (fun τ hτ => ?_)
    (fun X z => data.liftApply_clamped_measurable g hg hgm v X z)
  have hbox := QuietDecay.Partition.isBoxSmooth_liftApply n 0 0 (Cc hh n) g τ
    (fun m α v' u => TailConstructed.setting_tailRaw_coefficient_box P sX sZ hsZ Cc hseq 0 0
      (Nat.zero_le _) (Nat.zero_le _) hh hhh n m α v' u τ hτ) (by simpa using hg τ hτ) v
  exact isBoxSmooth_continuous_uncurry hbox

end AVRegularity.CycleComparison.Reconstruction
end
