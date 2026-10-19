-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.CovCommTime
public import AVRegularity.KernelEnergy.PlaneFluxTerm
import AVRegularity.CycleComparison.Coarse.Energy.Zero
import AVRegularity.Construction.Preservation.FullLift.KernelRegularizerScalarTransfer
public import AVRegularity.CoupledEnergy.Variational.GradientTensorCLM
import AVRegularity.CoupledEnergy.Variational.TorusRawSpatialForm
import AVRegularity.CoupledEnergy.Galerkin.TorusProjectedMassLimit
import AVRegularity.CycleComparison.Reconstruction.CoarseModesTested
import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.FluxBoundBasic
import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.EntryTerminal.Ingredients.ResidualFlux.LiftEnergyStatement
import AVRegularity.Finite.TerminalLift.CovarianceIdentification

section
section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp AVRegularity.EntryTerminal.CovGrad
namespace AVRegularity.EntryTerminal.CovComm

/-! **The factorial-norm price of the vector commutator adjoint** (statement (D)).

Each term `𝒞^{l-1-a}(𝔑_j 𝒞^a ·)` has the price `c^{l-1-a} (m c^a)` with `c = fbCovConst ≤ Kc² ω`
(`covOp_fbCovConst_le`) and `m = fbMulConst ≤ 32 (Kc+1)² 4^Kc (M a B₀)` (`gfbComm_le`), and
`M a B₀ = ω ρ² a B₀ ≤ ω κ / 8`; summing over `l, a, j` gives `κ · commPriceConst` (`commPrice`).

Special cases:
- `ω = 0`: the price is `0` (and indeed `commVec` has `covBound = 0` factors).
- `p = 0`: empty sum. -/

/-- The bound of one inner term by its share of the price. -/
theorem commStep_const_le {ρ ω a B₀ lam κ : ℝ} {H : Matrix (Fin 2) (Fin 2) ℝ} (Kc n c : ℕ)
    (hρ : 0 < ρ) (hω : 0 ≤ ω) (ha : 0 ≤ a) (hB₀ : 1 ≤ B₀) (hlam : 0 < lam)
    (hu : B₀ * ρ / lam ≤ 1 / 2) (hst : a * B₀ * ρ ^ 2 ≤ κ / 8) (hH : covBound H ≤ ω * ρ ^ 2) :
    fbCovConst ρ H Kc ^ n * (fbMulConst ρ (commBound (ω * ρ ^ 2) (driftB a B₀ lam)) Kc *
      fbCovConst ρ H Kc ^ c) ≤
      κ * (((Kc : ℝ) ^ 2 * ω) ^ n * ((4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) *
        ((Kc : ℝ) ^ 2 * ω) ^ c)) := by
  have hX := covOp_fbCovConst_le hρ H Kc hH
  have hX0 := fbCovConst_nonneg hρ H Kc
  have hM0 : 0 ≤ ω * ρ ^ 2 := by positivity
  have hm := gfbComm_le (Bb := driftB a B₀ lam) hρ hM0 ha hB₀ hlam hu (fun l => rfl) Kc
  have hm0 : 0 ≤ fbMulConst ρ (commBound (ω * ρ ^ 2) (driftB a B₀ lam)) Kc := by
    refine fbMulConst_nonneg hρ.le fun l _ => ?_
    unfold commBound driftB
    have : 0 ≤ lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ)) := (zpow_pos hlam _).le
    have : 0 ≤ B₀ := by linarith
    positivity
  have hm2 : fbMulConst ρ (commBound (ω * ρ ^ 2) (driftB a B₀ lam)) Kc ≤
      κ * (4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) := by
    refine hm.trans ?_
    have hc : 0 ≤ 32 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc := by positivity
    have : ω * ρ ^ 2 * a * B₀ ≤ ω * (κ / 8) := by
      calc ω * ρ ^ 2 * a * B₀ = ω * (a * B₀ * ρ ^ 2) := by ring
        _ ≤ ω * (κ / 8) := mul_le_mul_of_nonneg_left hst hω
    calc 32 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * (ω * ρ ^ 2 * a * B₀)
        ≤ 32 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * (ω * (κ / 8)) :=
          mul_le_mul_of_nonneg_left this hc
      _ = κ * (4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) := by ring
  have hpn := pow_le_pow_left₀ hX0 hX n
  have hpc := pow_le_pow_left₀ hX0 hX c
  have hX' : 0 ≤ (Kc : ℝ) ^ 2 * ω := by positivity
  calc fbCovConst ρ H Kc ^ n * (fbMulConst ρ (commBound (ω * ρ ^ 2) (driftB a B₀ lam)) Kc *
        fbCovConst ρ H Kc ^ c)
      ≤ ((Kc : ℝ) ^ 2 * ω) ^ n * ((κ * (4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω)) *
        ((Kc : ℝ) ^ 2 * ω) ^ c) :=
        mul_le_mul hpn (mul_le_mul hm2 hpc (pow_nonneg hX0 _) (hm0.trans hm2)) (by positivity)
          (pow_nonneg hX' _)
    _ = κ * (((Kc : ℝ) ^ 2 * ω) ^ n * ((4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) *
        ((Kc : ℝ) ^ 2 * ω) ^ c)) := by ring

theorem commFbMul_nonneg {ρ ω a B₀ lam : ℝ} (Kc : ℕ) (hρ : 0 < ρ) (hω : 0 ≤ ω) (ha : 0 ≤ a)
    (hB₀ : 1 ≤ B₀) (hlam : 0 < lam) :
    0 ≤ fbMulConst ρ (commBound (ω * ρ ^ 2) (driftB a B₀ lam)) Kc := by
  refine fbMulConst_nonneg hρ.le fun l _ => ?_
  unfold commBound driftB
  have : 0 ≤ lam ^ ((1 : ℤ) - ((l + 1 : ℕ) : ℤ)) := (zpow_pos hlam _).le
  have : 0 ≤ B₀ := by linarith
  positivity

section Fb

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {I : Set ℝ} {k p : ℕ} {M : ℝ}
  {Bb : ℕ → ℝ}

theorem commStep_fb (h : CommHyp b Hc I k p M Bb) {ρ : ℝ} (hρ : 0 < ρ) (s : ↥I) (j : Fin 2)
    (l a' : ℕ) (hal : a' < l) (hlp : l ≤ p) :
    ((TorusAdj.commStep (E := E) (Hc s.1) (h.cov s.1 s.2) b s.1 j k (k + 2 * p) (k + 2 * p + 3)
      p 1 l a' hal hlp (by omega) (by omega) (h.smooth s.1 s.2) (h.periodic s.1 s.2) Bb
      (h.drift s.1 s.2)).ofOrder (by omega : 2 * p + 1 - 1 = 2 * p)).FBound ρ
      (fbCovConst ρ (Hc s.1) (k + 2 * p) ^ (l - 1 - a') *
        (fbMulConst ρ (commBound M Bb) (k + 2 * p) * fbCovConst ρ (Hc s.1) (k + 2 * p) ^ a')) :=
  TorusAdj.FBound.ofOrder _ (TorusAdj.FBound.commStep hρ (Hc s.1) (h.cov s.1 s.2) b s.1 j k
    (k + 2 * p) (k + 2 * p + 3) p 1 l a' hal hlp (by omega) (by omega) (h.smooth s.1 s.2)
    (h.periodic s.1 s.2) Bb (h.drift s.1 s.2))

theorem commComp_fb (h : CommHyp b Hc I k p M Bb) {ρ : ℝ} (hρ : 0 < ρ) (s : ↥I) (j : Fin 2) :
    (commComp (E := E) h s j).FBound ρ
      (∑ l ∈ Finset.Icc 1 p, |((l.factorial : ℝ)⁻¹)| * ∑ a' ∈ Finset.range l,
        fbCovConst ρ (Hc s.1) (k + 2 * p) ^ (l - 1 - a') *
          (fbMulConst ρ (commBound M Bb) (k + 2 * p) *
            fbCovConst ρ (Hc s.1) (k + 2 * p) ^ a')) := by
  unfold commComp
  refine TorusAdj.FBound.ofOp _ ?_
  refine TorusAdj.FBound.mono ?_ le_rfl le_rfl _
  refine TorusAdj.FBound.sumMem _ fun l hl => TorusAdj.FBound.smul _ ?_
  exact TorusAdj.FBound.sumMem _ fun a' ha' =>
    commStep_fb h hρ s j l a' (Finset.mem_range.mp ha') (Finset.mem_Icc.mp hl).2

end Fb

/-- **(D)** -/
theorem commPrice : CommPriceStatement := by
  intro E _ _ _ _ _ _ b Hc I k p ρ ω a B₀ lam κ h hρ hω ha hB₀ hlam hu hst hκ s
  set Kc := k + 2 * p with hKc
  set Cc : ℝ := ∑ l ∈ Finset.Icc 1 p, |((l.factorial : ℝ)⁻¹)| * ∑ a' ∈ Finset.range l,
    fbCovConst ρ (Hc s.1) Kc ^ (l - 1 - a') *
      (fbMulConst ρ (commBound (ω * ρ ^ 2) (driftB a B₀ lam)) Kc *
        fbCovConst ρ (Hc s.1) Kc ^ a') with hCc
  have hcomp : ∀ j, (commComp (E := E) h s j).FBound ρ Cc := fun j => commComp_fb h hρ s j
  have hCc0 : 0 ≤ Cc := by
    have hm := commFbMul_nonneg (ρ := ρ) (ω := ω) (a := a) (B₀ := B₀) (lam := lam) Kc hρ hω ha hB₀
      hlam
    have hc := fbCovConst_nonneg hρ (Hc s.1) Kc
    exact Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (Finset.sum_nonneg fun a' _ =>
      mul_nonneg (pow_nonneg hc _) (mul_nonneg hm (pow_nonneg hc _)))
  have hvec : (commVec (E := E) h s).FBound ρ (∑ _j : Fin 2, 1 * Cc) := by
    unfold commVec
    exact TorusAdj.FBound.ofOp _ (TorusAdj.FBound.sum _ fun j => TorusAdj.FBound.ofOrder _
      (TorusAdj.FBound.comp (fbound_singleOp ρ hρ.le j k Kc)
        (TorusAdj.FBound.neg (hcomp j)) hCc0 le_rfl (by omega)))
  refine TorusAdj.FBound.mono_const hvec ?_
  have hterm : Cc ≤ κ * ∑ l ∈ Finset.Icc 1 p, (l.factorial : ℝ)⁻¹ * ∑ a' ∈ Finset.range l,
      (((Kc : ℝ) ^ 2 * ω) ^ (l - 1 - a') * ((4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) *
        ((Kc : ℝ) ^ 2 * ω) ^ a')) := by
    rw [Finset.mul_sum, hCc]
    refine Finset.sum_le_sum fun l _ => ?_
    have hf : (0 : ℝ) ≤ ((l.factorial : ℝ))⁻¹ := by positivity
    rw [abs_of_nonneg hf]
    calc (l.factorial : ℝ)⁻¹ * ∑ a' ∈ Finset.range l, fbCovConst ρ (Hc s.1) Kc ^ (l - 1 - a') *
          (fbMulConst ρ (commBound (ω * ρ ^ 2) (driftB a B₀ lam)) Kc *
            fbCovConst ρ (Hc s.1) Kc ^ a')
        ≤ (l.factorial : ℝ)⁻¹ * (κ * ∑ a' ∈ Finset.range l,
            (((Kc : ℝ) ^ 2 * ω) ^ (l - 1 - a') * ((4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) *
              ((Kc : ℝ) ^ 2 * ω) ^ a'))) := by
          refine mul_le_mul_of_nonneg_left ?_ hf
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum fun a' _ =>
            commStep_const_le Kc _ _ hρ hω ha hB₀ hlam hu hst (h.cov s.1 s.2)
      _ = κ * ((l.factorial : ℝ)⁻¹ * ∑ a' ∈ Finset.range l,
            (((Kc : ℝ) ^ 2 * ω) ^ (l - 1 - a') * ((4 * ((Kc : ℝ) + 1) ^ 2 * 4 ^ Kc * ω) *
              ((Kc : ℝ) ^ 2 * ω) ^ a'))) := by ring
  unfold commPriceConst
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_mul, nsmul_eq_mul]
  linarith [hterm]

end AVRegularity.EntryTerminal.CovComm
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev
open AVRegularity.KernelEnergy AVRegularity.CoupledEnergy.Galerkin
namespace AVRegularity.Construction.Residual.Presentation

/-! Physical coefficient data for the exact gradient-carrier operator of the cell-mean operator. A block
of derivative order r is charged its coefficient seminorm times the exact factorial reserve.
The row and column sums are mass-weighted; no count of components enters the price.
The coefficient values need only joint measurability in time and space.

This data is used by the diagonal and positive mean operators after physical chart transfer
and covariance-polynomial expansion. Constants in its terminal producer retain TermResPrefix.
Special cases: order zero is multiplication, zero coefficients give zero price, and one
component gives the usual scalar multiplier bound. -/

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- Actual differential coefficients acting on a finite family of gradient fluxes. -/
structure CovTruncCoefficientData (K R : ℕ) (a b ρ Cb : ℝ) (π : ι → ℝ)
    (input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)) where
  coeff : ∀ v u (r : Fin (R + 1)), ℝ → Vec 2 →
    PiLp 2 (fun _ : DerivativeWord2 r.val => PiLp 2 (fun _ : Fin 2 => h u)) →L[ℝ]
      PiLp 2 (fun _ : Fin 2 => h v)
  smooth : ∀ v u r, ∀ t ∈ Set.Icc a b, ContDiff ℝ (K : ℕ) (coeff v u r t)
  periodic : ∀ v u r, ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (coeff v u r t)
  measurable : ∀ v u r, Measurable fun p : Set.Icc a b × Vec 2 => coeff v u r p.1 p.2
  finite : ∀ v u r, coefficientSeminorm ρ K a b (coeff v u r) ≠ ⊤
  price : ι → ι → ℝ
  price_nonneg : ∀ v u, 0 ≤ price v u
  coefficient_cost : ∀ v u,
    (∑ r : Fin (R + 1), (coefficientSeminorm ρ K a b (coeff v u r)).toReal *
      derivativeReserveFactor ρ K r.val) ≤ price v u
  row : ∀ v, ∑ u, Real.sqrt (π u / π v) * price v u ≤ Cb
  col : ∀ u, ∑ v, Real.sqrt (π u / π v) * price v u ≤ Cb
  input_smooth : ∀ v, ∀ t ∈ Set.Icc a b, ContDiff ℝ ((K + R : ℕ) : ℕ∞) (input v t)
  input_periodic : ∀ v, ∀ t ∈ Set.Icc a b, AVenhance.IsZ2Periodic (input v t)
  action : ∀ v, ∀ t ∈ Set.Icc a b, ∀ x,
    target v t x = ∑ u, ∑ r : Fin (R + 1), coeff v u r t x
      (WithLp.toLp 2 fun α : DerivativeWord2 r.val => orderedDerivative α (input u t) x)

namespace CovTruncCoefficientData
variable {K R : ℕ} {a b ρ Cb : ℝ} {π : ι → ℝ}
  {input target : ∀ v : ι, ℝ → Vec 2 → PiLp 2 (fun _ : Fin 2 => h v)}
  (P : CovTruncCoefficientData K R a b ρ Cb π input target)

/-- The fixed derivative budget of a multiplier block. -/
def jetBound (v u : ι) (r : Fin (R + 1)) (j : Fin (K + 1)) : ℝ :=
  (coefficientOrderSup a b (P.coeff v u r) j.val).toReal

omit [∀ i, FiniteDimensional ℝ (h i)] [∀ i, BorelSpace (h i)]
  [∀ i, CompleteSpace (h i)] [∀ i, MeasurableSpace (h i)] in
/-- The source supremum bounds every multiplier derivative at each window time. -/
theorem jetBound_bounds (hρ : 0 < ρ) (v u : ι) (r : Fin (R + 1))
    (t : ℝ) (ht : t ∈ Set.Icc a b) (j : Fin (K + 1)) (x : Vec 2) :
    ‖coefficientDerivativeArray (P.coeff v u r t) j.val x‖ ≤ P.jetBound v u r j :=
  coefficientOrderSup_derivative_bound ρ hρ K a b (P.coeff v u r) (P.finite v u r)
    j.val (Nat.le_of_lt_succ j.isLt) t ht x

/-- A genuine Sobolev multiplier composed with its ordered derivative tensor. -/
def termCLM (hρ : 0 < ρ) (v u : ι) (r : Fin (R + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc a b) :
    TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h u)) →L[ℝ]
      TorusHk K (PiLp 2 (fun _ : Fin 2 => h v)) :=
  (torusMultiplierCLM (P.coeff v u r t) (P.smooth v u r t ht) (P.periodic v u r t ht)
    (P.jetBound v u r) (P.jetBound_bounds hρ v u r t ht) ρ hρ).comp
      ((torusKernelDerivativeTensorCLM (E := PiLp 2 (fun _ : Fin 2 => h u)) K r.val).comp
        (truncateTorusHk (E := PiLp 2 (fun _ : Fin 2 => h u)) (Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) K)))

/-- The literal carrier action of a multiplier block. -/
theorem termCLM_apply (hρ : 0 < ρ) (v u : ι) (r : Fin (R + 1)) (t : ℝ)
    (ht : t ∈ Set.Icc a b) (U : TorusHk (K + R) (PiLp 2 (fun _ : Fin 2 => h u))) :
    P.termCLM hρ v u r t ht U =
      (AVRegularity.KernelEnergy.torusDerivativeTensor
        (truncateTorusHk (E := PiLp 2 (fun _ : Fin 2 => h u)) (Nat.add_le_add_left (Nat.le_of_lt_succ r.isLt) K) U)).mulCoefficient
        (P.coeff v u r t) (P.smooth v u r t ht) (P.periodic v u r t ht)
        (P.jetBound_bounds hρ v u r t ht) := by
  simp only [termCLM, ContinuousLinearMap.comp_apply, torusKernelDerivativeTensorCLM_apply]
  rfl

end CovTruncCoefficientData

end AVRegularity.Construction.Residual.Presentation
end
end

section
/-! **The gradient flux of a field of bounded strong energy is a realized flux**.

Let `(U, W)` be a pair of trajectories of orders `L`, `L + 1`, with `W` square integrable and
`truncate W = U` for almost every time, and suppose `U(t)` has the classical representative
`a(t)` (class `C^1` at least) for each time of the window. If the strong energy
`(∑_v π_v⁻¹ (sup |U_v|² + ν ∫ |∇ W_v|²))^{1/2}` is at most `E`, then the classical gradient
flux `∇ a` has a realization of order `K' ≤ L - 1` with `(ν⁻¹ ∫ ‖·‖²)^{1/2} ≤ E / ν`
(`covGrad_hasFluxBound_of_strongEnergy`).

Special cases:
- `E = 0`: the gradient flux is realized by `0` with mass `0`.
- `ν` large: the bound `E/ν` is small, the dissipation is paid by `ν`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CoupledEnergy.Variational
open AVRegularity.Construction.Residual.Presentation AVRegularity.Construction.Preservation.FullLift
open scoped ENNReal

namespace AVRegularity.EntryTerminal.CovGrad

section Generic

variable {ι : Type} [Fintype ι] {h : ι → Type} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] [∀ i, CompleteSpace (h i)]

/-- The dissipation part of a strong energy bound, as a real inequality. -/
theorem covGrad_dissipation_le {ρ ν a b E : ℝ} (hν : 0 < ν) (hE : 0 ≤ E) (π : ι → ℝ)
    (hπ : ∀ v, 0 < π v) {K : ℕ} (u : ∀ i, ℝ → TorusHk K (h i))
    (w : ∀ i, ℝ → TorusHk (K + 1) (h i))
    (hw : ∀ i, MemLp (w i) 2 (volume.restrict (Set.Icc a b)))
    (hen : strongEnergy ρ ν π a b u w ≤ ENNReal.ofReal E) :
    ν * ∑ i, (π i)⁻¹ * ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val ≤ E ^ 2 := by
  rw [strongEnergy_component_integral hν.le π u w hw] at hen
  have hnn : ∀ i, 0 ≤ ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val := fun i =>
    integral_nonneg fun s => CycleComparison.Coarse.gradFactorialNormSq_nonneg ρ _
  have h1 := ENNReal.rpow_le_rpow hen (show (0 : ℝ) ≤ 2 by norm_num)
  rw [← ENNReal.rpow_mul, show (1 / 2 : ℝ) * 2 = 1 by norm_num, ENNReal.rpow_one] at h1
  have h2 : ENNReal.ofReal (ν * ∑ i, (π i)⁻¹ * ∫ s in Set.Icc a b,
      gradFactorialNormSq ρ (w i s).val) ≤ ∑ i, ENNReal.ofReal (π i)⁻¹ *
        ((⨆ t ∈ Set.Icc a b, ENNReal.ofReal (factorialNormSq ρ (u i t).val)) +
          ENNReal.ofReal (ν * ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val)) := by
    rw [Finset.mul_sum, ENNReal.ofReal_sum_of_nonneg (fun i _ =>
      mul_nonneg hν.le (mul_nonneg (inv_nonneg.2 (hπ i).le) (hnn i)))]
    refine Finset.sum_le_sum fun i _ => ?_
    rw [show ν * ((π i)⁻¹ * ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val) =
      (π i)⁻¹ * (ν * ∫ s in Set.Icc a b, gradFactorialNormSq ρ (w i s).val) by ring,
      ENNReal.ofReal_mul (inv_nonneg.2 (hπ i).le)]
    exact mul_le_mul' le_rfl le_add_self
  have h3 := h2.trans h1
  rw [ENNReal.ofReal_rpow_of_nonneg hE (by norm_num : (0 : ℝ) ≤ 2), Real.rpow_two,
    ENNReal.ofReal_le_ofReal_iff (sq_nonneg E)] at h3
  exact h3

/-- The classical gradient of a classical representative is the value jet of the gradient
carrier of its truncation. -/
theorem covGrad_realization {L K' : ℕ} (hK : K' + 1 ≤ L) {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [CompleteSpace E]
    [FiniteDimensional ℝ E] (U : TorusHk L E) (a : Vec 2 → E) (ha : IsClassicalRep U a 1) :
    (torusGradientTensor (truncateTorusHk hK U)).toFunction.jet (valueIndex2 K') =ᵐ[
      volume.restrict AVenhance.unitCube] fun x => toFluxL (gradE a x) := by
  have h1 := periodicJetRepresentative_ae (torusGradientTensor (truncateTorusHk hK U)).val
    (valueIndex2 K')
  have h2 := torusGradientTensor_value_ae (truncateTorusHk hK U)
  have h3 : ∀ k : Fin 2, (fun x => (truncateTorusHk hK U).val
      ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K')⟩, fun _ => k⟩ x) =ᵐ[
        volume.restrict AVenhance.unitCube] fun x => fderiv ℝ a x (basisVec k) := by
    intro k
    have hL1 : 1 ≤ L := by omega
    have h4 := ha.2.2.2 1 le_rfl (fun _ => k)
    have h4' : (U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hL1⟩, fun _ => k⟩) =ᵐ[
        volume.restrict AVenhance.unitCube] orderedDerivative (fun _ : Fin 1 => k) a := by
      have e : torusJetOrder U 1 (fun _ => k) =
          U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hL1⟩, fun _ => k⟩ := by
        funext x
        simp [torusJetOrder, hL1]
      rw [e] at h4
      exact h4
    have h5 := periodicJetRepresentative_ae U.val ⟨⟨1, Nat.lt_succ_of_le hL1⟩, fun _ => k⟩
    filter_upwards [h4', h5] with x hx4 hx5
    have e1 : (truncateTorusHk hK U).val ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K')⟩, fun _ => k⟩ x =
        U.val ⟨⟨1, Nat.lt_succ_of_le hL1⟩, fun _ => k⟩ x := rfl
    rw [e1, ← hx5]
    change U.toFunction.jet ⟨⟨1, Nat.lt_succ_of_le hL1⟩, fun _ => k⟩ x = _
    rw [hx4, CycleComparison.Reconstruction.orderedDerivative_one_eq_fderiv]
  have hall : ∀ᵐ x ∂(volume.restrict AVenhance.unitCube), ∀ k : Fin 2,
      (truncateTorusHk hK U).val ⟨⟨1, Nat.succ_lt_succ (Nat.succ_pos K')⟩, fun _ => k⟩ x =
        fderiv ℝ a x (basisVec k) := by
    rw [Filter.eventually_all]
    exact h3
  filter_upwards [h1, h2, hall] with x hx1 hx2 hx3
  change periodicJetRepresentative _ _ x = _
  rw [hx1, hx2]
  ext k
  exact hx3 k

/-- **The gradient flux of a bounded strong energy is a realized flux.** -/
theorem covGrad_hasFluxBound_of_strongEnergy {L K' : ℕ} (hK : K' + 1 ≤ L) {t0 t1 ν ρ E : ℝ}
    (π : ι → ℝ) (hν : 0 < ν) (hE : 0 ≤ E) (hπ : ∀ v, 0 < π v)
    (U : ∀ v, ℝ → TorusHk L (h v)) (W : ∀ v, ℝ → TorusHk (L + 1) (h v))
    (a : ℝ → Vec 2 → ∀ v, h v)
    (hW : ∀ v, MemLp (W v) 2 (volume.restrict (Set.Icc t0 t1)))
    (hae : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)),
      truncateTorusHk (Nat.le_succ L) (W v t) = U v t)
    (hrep : ∀ v, ∀ t ∈ Set.Icc t0 t1, IsClassicalRep (U v t) (fun x => a t x v) 1)
    (hen : strongEnergy ρ ν π t0 t1 U W ≤ ENNReal.ofReal E) :
    HasFluxBound K' (Set.Icc t0 t1) ν ρ π
      (fun v t x => toFluxL (gradE (fun z => a t z v) x)) (E / ν) := by
  have hKL : K' ≤ L := by omega
  let Wt : ∀ v, ℝ → TorusHk (K' + 1) (h v) := fun v t =>
    truncateTorusHk (Nat.succ_le_succ hKL) (W v t)
  let Ut : ∀ v, ℝ → TorusHk K' (h v) := fun v t => truncateTorusHk hKL (U v t)
  have hWt : ∀ v, MemLp (Wt v) 2 (volume.restrict (Set.Icc t0 t1)) := fun v =>
    (truncateTorusHk (E := h v) (Nat.succ_le_succ hKL)).comp_memLp' (hW v)
  let Fk : ∀ v, ℝ → TorusHk K' (PiLp 2 (fun _ : Fin 2 => h v)) := fun v t =>
    torusGradientTensor (truncateTorusHk hK (U v t))
  let Fk' : ∀ v, ℝ → TorusHk K' (PiLp 2 (fun _ : Fin 2 => h v)) := fun v t =>
    torusGradientTensor (Wt v t)
  have hFk' : ∀ v, MemLp (Fk' v) 2 (volume.restrict (Set.Icc t0 t1)) := fun v =>
    torusGradientTensor_carrier_memLp K' t0 t1 (Wt v) (hWt v)
  have hFeq : ∀ v, ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)), Fk v t = Fk' v t := by
    intro v
    filter_upwards [hae v] with t ht
    simp only [Fk, Fk', Wt]
    rw [← ht]
    rfl
  have hFk : ∀ v, MemLp (Fk v) 2 (volume.restrict (Set.Icc t0 t1)) := fun v =>
    (hFk' v).ae_eq (Filter.EventuallyEq.symm (hFeq v))
  refine ⟨Fk, fun v t ht => covGrad_realization hK (U v t) (fun x => a t x v) (hrep v t ht),
    hFk, ?_⟩
  have hdis := covGrad_dissipation_le hν hE π hπ Ut Wt hWt
    ((strongEnergy_truncate_le hKL ρ ν π t0 t1 U W).trans hen)
  have hae2 : ∀ᵐ t ∂(volume.restrict (Set.Icc t0 t1)), ∀ v, Fk v t = Fk' v t :=
    Filter.eventually_all.2 hFeq
  have hint : ∫ s in Set.Icc t0 t1, massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => K') ρ π (fun v => (Fk v s).val) =
      ∑ i, (π i)⁻¹ * ∫ s in Set.Icc t0 t1, gradFactorialNormSq ρ (Wt i s).val := by
    rw [integral_congr_ae (g := fun s => massGradNormSq (E := h) (K := fun _ => K') ρ π
      (fun v => (Wt v s).val)) (by
        filter_upwards [hae2] with s hs
        rw [← CoupledEnergy.Galerkin.torusGradientTensor_massNormSq (fun _ => K') ρ π (fun v => Wt v s)]
        simp only [hs]
        rfl)]
    unfold massGradNormSq
    rw [integral_finsetSum _ (fun i _ => (CycleComparison.Coarse.integrable_gradFactorialNormSq_torus (hWt i)).const_mul _)]
    simp only [integral_const_mul]
  show Real.sqrt (ν⁻¹ * ∫ s in Set.Icc t0 t1, massNormSq (E := fun v : ι => PiLp 2 (fun _ : Fin 2 => h v))
      (K := fun _ => K') ρ π (fun v => (Fk v s).val)) ≤ E / ν
  rw [hint]
  refine Real.sqrt_le_iff.2 ⟨by positivity, ?_⟩
  rw [div_pow, show ν⁻¹ * ∑ i, (π i)⁻¹ * ∫ s in Set.Icc t0 t1, gradFactorialNormSq ρ (Wt i s).val =
    (ν * ∑ i, (π i)⁻¹ * ∫ s in Set.Icc t0 t1, gradFactorialNormSq ρ (Wt i s).val) / ν ^ 2 by
      field_simp]
  exact div_le_div_of_nonneg_right hdis (sq_nonneg ν)

end Generic

end AVRegularity.EntryTerminal.CovGrad
end
end
end

section
section
/-! **The duality of the commutator flux with the vector adjoint** (statement (E)).

With `N(x) = Db(x) H + H Db(x)ᵀ`: `toFluxL (commFluxE b H g x) = -N(x) ∇g(x)` and
`commFluxMap E H j (Db x) w = (N(x)ᵀ w)_j` (`commFluxE_eq`, `commFluxMap_eq`). Pairing
`𝒞^a 𝒥_H 𝒞^n u` with `φ` moves `𝒞^a` to `φ` (self-adjointness), then the matrix to the other side
of the inner product, then `𝒞^n` back to `∇u` (`𝒞` commutes with the gradient), which gives
`⟨∇u, 𝒞^n(N(x)ᵀ 𝒞^a φ)⟩`, the pairing with the `l,a` term of `commVecOp`.

Special cases:
- `H = 0`: `N = 0` and both sides vanish.
- `n = a = 0`: `⟨-N ∇u, φ⟩ = ⟨∇u, -Nᵀ φ⟩`. -/

@[expose] public noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp AVRegularity.EntryTerminal.CovGrad AVRegularity

namespace AVRegularity.EntryTerminal.CovComm

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The matrix `N = Db H + H Dbᵀ`. -/
def Nmat (bv : Vec 2 → Vec 2) (H : Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2) :
    Matrix (Fin 2) (Fin 2) ℝ := jacMatrix bv x * H + H * (jacMatrix bv x).transpose

theorem centry_eq_Nmat (bv : Vec 2 → Vec 2) (H : Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2)
    (k j : Fin 2) : centry H k j (fderiv ℝ bv x) = Nmat bv H x k j := by
  simp [centry, Nmat, jacMatrix, Matrix.mul_apply, Matrix.add_apply, Matrix.transpose_apply,
    Fin.sum_univ_two]
  ring

theorem commFluxE_eq (bv : Vec 2 → Vec 2) (H : Matrix (Fin 2) (Fin 2) ℝ) (g : Vec 2 → E)
    (x : Vec 2) :
    toFluxL (commFluxE bv H g x) = -matAct (Nmat bv H x) (gradFlux g x) := by
  ext j
  simp [toFluxL, commFluxE, matAct, gradFlux, Nmat, Fin.sum_univ_two]

theorem commFluxMap_eq (bv : Vec 2 → Vec 2) (H : Matrix (Fin 2) (Fin 2) ℝ) (x : Vec 2)
    (j : Fin 2) (w : PiLp 2 (fun _ : Fin 2 => E)) :
    commFluxMap E H j (fderiv ℝ bv x) w = (matAct (Nmat bv H x).transpose w) j := by
  simp [commFluxMap, commFluxCLM, commFluxVec, matAct, centry_eq_Nmat, Matrix.transpose_apply]

section Smooth

theorem contDiff_matAct {r : ℕ} {N : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {w : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hN : ∀ i j, ContDiff ℝ (r : WithTop ℕ∞) (fun x => N x i j))
    (hw : ContDiff ℝ (r : WithTop ℕ∞) w) : ContDiff ℝ (r : WithTop ℕ∞) (fun x => matAct (N x) (w x)) := by
  have hwl : ∀ l : Fin 2, ContDiff ℝ (r : WithTop ℕ∞) (fun x => w x l) := fun l =>
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) l).contDiff.comp hw
  have h1 : ContDiff ℝ (r : WithTop ℕ∞) (fun x => fun j : Fin 2 => ∑ l : Fin 2, N x j l • w x l) :=
    contDiff_pi.2 fun j => ContDiff.sum fun l _ => (hN j l).smul (hwl l)
  exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)).symm.contDiff.comp h1

theorem periodic_matAct {N : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ}
    {w : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)} (hN : AVenhance.IsZ2Periodic N)
    (hw : AVenhance.IsZ2Periodic w) : AVenhance.IsZ2Periodic (fun x => matAct (N x) (w x)) :=
  fun n x => by
    change matAct (N (x + AVenhance.latticeShift n)) (w (x + AVenhance.latticeShift n)) = _
    rw [hN n x, hw n x]

theorem contDiff_jac {r : ℕ} {bv : Vec 2 → Vec 2} (hb : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) bv)
    (i j : Fin 2) : ContDiff ℝ (r : WithTop ℕ∞) (fun x => jacMatrix bv x i j) := by
  have h1 : ContDiff ℝ (r : WithTop ℕ∞) (fun x => fderiv ℝ bv x (basisVec j)) :=
    (hb.fderiv_right (by exact_mod_cast le_rfl)).clm_apply contDiff_const
  exact (contDiff_pi.1 h1) i

theorem contDiff_Nmat {r : ℕ} {bv : Vec 2 → Vec 2} (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) bv) (i j : Fin 2) :
    ContDiff ℝ (r : WithTop ℕ∞) (fun x => Nmat bv H x i j) := by
  have e : (fun x => Nmat bv H x i j) = fun x => (jacMatrix bv x i 0 * H 0 j +
      jacMatrix bv x i 1 * H 1 j) + (H i 0 * jacMatrix bv x j 0 + H i 1 * jacMatrix bv x j 1) := by
    funext x
    simp [Nmat, Matrix.mul_apply, Fin.sum_univ_two]
  rw [e]
  exact (((contDiff_jac hb i 0).mul contDiff_const).add ((contDiff_jac hb i 1).mul
    contDiff_const)).add ((contDiff_const.mul (contDiff_jac hb j 0)).add
    (contDiff_const.mul (contDiff_jac hb j 1)))

theorem periodic_Nmat {bv : Vec 2 → Vec 2} (H : Matrix (Fin 2) (Fin 2) ℝ)
    (hb : ContDiff ℝ 1 bv) (hp : AVenhance.IsZ2Periodic bv) :
    AVenhance.IsZ2Periodic (Nmat bv H) := fun n x => by
  have hd := fderiv_isZ2Periodic (hb.differentiable (by norm_num)) hp n x
  simp only [Nmat, jacMatrix, hd]

end Smooth

section Term

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Self-adjointness of a covariance power on periodic fields. -/
theorem cov_iter_adj (H : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ) {V : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℝ V] [MeasurableSpace V] [BorelSpace V] [CompleteSpace V]
    [FiniteDimensional ℝ V] (u q : Vec 2 → V)
    (hu : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) u) (hq : ContDiff ℝ ((2 * p : ℕ) : ℕ∞) q)
    (hpu : AVenhance.IsZ2Periodic u) (hpq : AVenhance.IsZ2Periodic q) :
    cellInner ((covOperator H)^[p] u) q = cellInner u ((covOperator H)^[p] q) := by
  have := covOp_polynomial_adjoint H p (fun l => if l = p then 1 else 0) u q hu hq hpu hpq
  rwa [covGrad_pow_eq_poly, covGrad_pow_eq_poly] at this

open AVRegularity.Construction.Preservation.FullLift AVRegularity.Finite.TerminalLift in
/-- **The duality for one term `(l, a)`.** -/
theorem commTerm_dual (bv : Vec 2 → Vec 2) (H : Matrix (Fin 2) (Fin 2) ℝ) (n a p : ℕ)
    (hnap : n + a + 1 ≤ p) (hb : ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) bv)
    (hbp : AVenhance.IsZ2Periodic bv) (u : Vec 2 → E)
    (hu : ContDiff ℝ ((2 * p + 1 : ℕ) : WithTop ℕ∞) u) (hpu : AVenhance.IsZ2Periodic u)
    (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hpφ : AVenhance.IsZ2Periodic φ) :
    Continuous (fun x => toFluxL ((covOperator H)^[a] (commFluxE bv H ((covOperator H)^[n] u)) x)) ∧
    Continuous (fun x => -(WithLp.toLp 2 (fun j => (covOperator H)^[n]
        (fun y => commFluxMap E H j (fderiv ℝ bv y) (((covOperator H)^[a] φ) y)) x))) ∧
    cellInner (fun x => toFluxL ((covOperator H)^[a] (commFluxE bv H ((covOperator H)^[n] u)) x)) φ =
      cellInner (gradFlux u) (fun x => -(WithLp.toLp 2 (fun j => (covOperator H)^[n]
        (fun y => commFluxMap E H j (fderiv ℝ bv y) (((covOperator H)^[a] φ) y)) x))) := by
  have hφr : ∀ r : ℕ, ContDiff ℝ (r : WithTop ℕ∞) φ := fun r => hφ.of_le (by exact_mod_cast le_top)
  have hψ : ∀ r : ℕ, ContDiff ℝ (r : WithTop ℕ∞) ((covOperator H)^[a] φ) := fun r =>
    covOperator_iterate_contDiff (E := PiLp 2 (fun _ : Fin 2 => E)) H a r φ (by exact_mod_cast hφr _)
  have hψp : AVenhance.IsZ2Periodic ((covOperator H)^[a] φ) :=
    covOperator_iterate_periodic (E := PiLp 2 (fun _ : Fin 2 => E)) H a φ (by exact_mod_cast hφr _) hpφ
  have hg : ContDiff ℝ ((2 * a + 1 : ℕ) : WithTop ℕ∞) ((covOperator H)^[n] u) :=
    covOperator_iterate_contDiff (E := E) H n (2 * a + 1) u
      (by exact_mod_cast hu.of_le (by exact_mod_cast (by omega : 2 * a + 1 + 2 * n ≤ 2 * p + 1)))
  have hgp : AVenhance.IsZ2Periodic ((covOperator H)^[n] u) :=
    covOperator_iterate_periodic (E := E) H n u
      (by exact_mod_cast hu.of_le (by exact_mod_cast (by omega : 2 * n ≤ 2 * p + 1))) hpu
  have hbr : ContDiff ℝ ((2 * a + 1 : ℕ) : WithTop ℕ∞) bv :=
    hb.of_le (by exact_mod_cast (by omega : 2 * a + 1 ≤ 2 * p + 1))
  have hbn : ContDiff ℝ ((2 * n + 1 : ℕ) : WithTop ℕ∞) bv :=
    hb.of_le (by exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * p + 1))
  -- the flux field
  set Jv : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) :=
    fun x => toFluxL (commFluxE bv H ((covOperator H)^[n] u) x) with hJv
  have hJe : Jv = fun x => -matAct (Nmat bv H x) (gradFlux ((covOperator H)^[n] u) x) := by
    funext x; exact commFluxE_eq bv H _ x
  have hJd : ContDiff ℝ ((2 * a : ℕ) : WithTop ℕ∞) Jv := by
    rw [hJe]
    exact (contDiff_matAct (fun i j => contDiff_Nmat H hbr i j) (contDiff_gradFlux hg)).neg
  have hJp : AVenhance.IsZ2Periodic Jv := by
    rw [hJe]
    intro m x
    have := periodic_matAct (periodic_Nmat H (hb.of_le (by exact_mod_cast (by omega : 1 ≤ 2 * p + 1))) hbp)
      (periodic_gradFlux (hg.of_le (by exact_mod_cast (by omega : 1 ≤ 2 * a + 1))) hgp) m x
    simp only [this]
  -- move the covariance power onto the test field
  set w : Vec 2 → PiLp 2 (fun _ : Fin 2 => E) :=
    fun x => matAct (Nmat bv H x).transpose (((covOperator H)^[a] φ) x) with hw
  have hwd : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) w :=
    contDiff_matAct (fun i j => contDiff_Nmat H hbn j i) (hψ _)
  have hwp : AVenhance.IsZ2Periodic w := by
    have hNp := periodic_Nmat H (hb.of_le (by exact_mod_cast (by omega : 1 ≤ 2 * p + 1))) hbp
    refine periodic_matAct (fun m x => ?_) hψp
    simp only [hNp m x]
  have h5 : (fun x => toFluxL ((covOperator H)^[a] (commFluxE bv H ((covOperator H)^[n] u)) x)) =
      (covOperator H)^[a] Jv := by
    funext x
    have hf : ContDiff ℝ ((2 * a : ℕ) : ℕ∞) (commFluxE bv H ((covOperator H)^[n] u)) := by
      have : commFluxE bv H ((covOperator H)^[n] u) =
          fun x => (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)) (Jv x) := rfl
      rw [this]
      exact (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)).contDiff.comp
        (by exact_mod_cast hJd)
    exact terminal_covariance_iterate_clm H
      (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => E)).symm.toContinuousLinearMap a _ hf x
  have hTc : Continuous (fun x => toFluxL ((covOperator H)^[a]
      (commFluxE bv H ((covOperator H)^[n] u)) x)) := by
    rw [h5]
    exact (covOperator_iterate_contDiff (E := PiLp 2 (fun _ : Fin 2 => E)) H a 0 Jv
      (by rw [Nat.zero_add]; exact_mod_cast hJd)).continuous
  have hVc : Continuous (fun x => -(WithLp.toLp 2 (fun j => (covOperator H)^[n]
        (fun y => commFluxMap E H j (fderiv ℝ bv y) (((covOperator H)^[a] φ) y)) x))) := by
    have e2 : (fun x => (WithLp.toLp 2 (fun j => (covOperator H)^[n]
        (fun y => commFluxMap E H j (fderiv ℝ bv y) (((covOperator H)^[a] φ) y)) x) :
        PiLp 2 (fun _ : Fin 2 => E))) = (covOperator H)^[n] w := by
      funext x
      ext j
      have := terminal_covariance_iterate_clm H (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) j) n w
        (by exact_mod_cast hwd) x
      rw [PiLp.proj_apply] at this
      rw [this]
      simp only [hw, PiLp.proj_apply, commFluxMap_eq]
    have hc : Continuous (fun x => (WithLp.toLp 2 (fun j => (covOperator H)^[n]
        (fun y => commFluxMap E H j (fderiv ℝ bv y) (((covOperator H)^[a] φ) y)) x) :
        PiLp 2 (fun _ : Fin 2 => E))) := by
      rw [e2]
      exact (covOperator_iterate_contDiff (E := PiLp 2 (fun _ : Fin 2 => E)) H n 0 w
        (by rw [Nat.zero_add]; exact_mod_cast hwd)).continuous
    exact hc.neg
  refine ⟨hTc, hVc, ?_⟩
  rw [h5, cov_iter_adj H a Jv φ (by exact_mod_cast hJd) (by exact_mod_cast hφr _) hJp hpφ]
  have h7 : cellInner Jv ((covOperator H)^[a] φ) =
      cellInner (gradFlux ((covOperator H)^[n] u)) (fun x => -w x) := by
    unfold cellInner
    congr 1
    funext x
    show inner ℝ (Jv x) _ = inner ℝ _ (-(matAct (Nmat bv H x).transpose _))
    rw [show Jv x = -matAct (Nmat bv H x) (gradFlux ((covOperator H)^[n] u) x) from
      congrFun hJe x, inner_neg_left, inner_neg_right, inner_matAct]
  rw [h7, ← covGrad_commute H n (hu.of_le (by exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * p + 1)))]
  have hup : ContDiff ℝ ((2 * n + 1 : ℕ) : WithTop ℕ∞) u :=
    hu.of_le (by exact_mod_cast (by omega : 2 * n + 1 ≤ 2 * p + 1))
  have hgu : ContDiff ℝ ((2 * n : ℕ) : WithTop ℕ∞) (gradFlux u) := contDiff_gradFlux hup
  have hgup : AVenhance.IsZ2Periodic (gradFlux u) :=
    periodic_gradFlux (hup.of_le (by exact_mod_cast (by omega : 1 ≤ 2 * n + 1))) hpu
  have hwnp : AVenhance.IsZ2Periodic (fun x => -w x) := fun m x => by
    change -w (x + AVenhance.latticeShift m) = -w x
    rw [hwp m x]
  rw [cov_iter_adj H n (gradFlux u) (fun x => -w x) (by exact_mod_cast hgu)
    (by exact_mod_cast hwd.neg) hgup hwnp]
  unfold cellInner
  congr 1
  funext x
  have e1 := terminal_covariance_iterate_clm H (-ContinuousLinearMap.id ℝ
    (PiLp 2 (fun _ : Fin 2 => E))) n w (by exact_mod_cast hwd) x
  have e2 : ((covOperator H)^[n] w x) = WithLp.toLp 2 (fun j => (covOperator H)^[n]
      (fun y => commFluxMap E H j (fderiv ℝ bv y) (((covOperator H)^[a] φ) y)) x) := by
    ext j
    have := terminal_covariance_iterate_clm H (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => E) j) n w
      (by exact_mod_cast hwd) x
    rw [PiLp.proj_apply] at this
    rw [this]
    simp only [hw, PiLp.proj_apply, commFluxMap_eq]
  have e3 : (covOperator H)^[n] (fun x => -w x) x = -(WithLp.toLp 2 (fun j => (covOperator H)^[n]
      (fun y => commFluxMap E H j (fderiv ℝ bv y) (((covOperator H)^[a] φ) y)) x)) := by
    rw [← e2]
    simpa using e1.symm
  show inner ℝ _ ((covOperator H)^[n] (fun x => -w x) x) = _
  rw [e3]

end Term

section Comb

variable {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

theorem cellInner_sum_left (s : Finset ℕ) (F : ℕ → Vec 2 → V) (ψ : Vec 2 → V)
    (hF : ∀ i ∈ s, Continuous (F i)) (hψ : Continuous ψ) :
    cellInner (fun x => ∑ i ∈ s, F i x) ψ = ∑ i ∈ s, cellInner (F i) ψ :=
  cellInner_finsetSum_left s F ψ fun i hi =>
    integrable_inner_continuous (memLp_two_cell_of_continuous (hF i hi)) hψ

theorem cellInner_comb_left (s : Finset ℕ) (t : ℕ → Finset ℕ) (c : ℕ → ℝ)
    (F : ℕ → ℕ → Vec 2 → V) (hF : ∀ i ∈ s, ∀ a ∈ t i, Continuous (F i a)) (ψ : Vec 2 → V)
    (hψ : Continuous ψ) :
    cellInner (fun x => ∑ i ∈ s, c i • ∑ a ∈ t i, F i a x) ψ =
      ∑ i ∈ s, c i * ∑ a ∈ t i, cellInner (F i a) ψ := by
  have hc : ∀ i ∈ s, Continuous (fun x => c i • ∑ a ∈ t i, F i a x) := fun i hi =>
    continuous_const.smul (continuous_finsetSum _ fun a ha => hF i hi a ha)
  rw [cellInner_sum_left s (fun i x => c i • ∑ a ∈ t i, F i a x) ψ hc hψ]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [Construction.Preservation.FullLift.cellInner_smul_left, cellInner_sum_left (t i) (F i) ψ (hF i hi) hψ]

theorem cellInner_sum_right (s : Finset ℕ) (F : ℕ → Vec 2 → V) (g : Vec 2 → V)
    (hg : Continuous g) (hF : ∀ i ∈ s, Continuous (F i)) :
    cellInner g (fun x => ∑ i ∈ s, F i x) = ∑ i ∈ s, cellInner g (F i) :=
  cellInner_finsetSum_right s (memLp_two_cell_of_continuous hg) hF

theorem cellInner_comb_right (s : Finset ℕ) (t : ℕ → Finset ℕ) (c : ℕ → ℝ)
    (F : ℕ → ℕ → Vec 2 → V) (hF : ∀ i ∈ s, ∀ a ∈ t i, Continuous (F i a)) (g : Vec 2 → V)
    (hg : Continuous g) :
    cellInner g (fun x => ∑ i ∈ s, c i • ∑ a ∈ t i, F i a x) =
      ∑ i ∈ s, c i * ∑ a ∈ t i, cellInner g (F i a) := by
  have hc : ∀ i ∈ s, Continuous (fun x => c i • ∑ a ∈ t i, F i a x) := fun i hi =>
    continuous_const.smul (continuous_finsetSum _ fun a ha => hF i hi a ha)
  rw [cellInner_sum_right s (fun i x => c i • ∑ a ∈ t i, F i a x) g hg hc]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [AVRegularity.CycleComparison.Coarse.cellInner_smul_right, cellInner_sum_right (t i) (F i) g hg (hF i hi)]

end Comb

/-- **(E)** -/
theorem commDual : CommDualStatement := by
  intro E _ _ _ _ _ _ b Hc p s u hb hbp hu hpu
  have hterm : ∀ l ∈ Finset.Icc 1 p, ∀ a' ∈ Finset.range l,
      ∀ φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E), ContDiff ℝ (⊤ : ℕ∞) φ →
        AVenhance.IsZ2Periodic φ → _ := fun l hl a' ha' φ hφ hpφ =>
    commTerm_dual (b s) (Hc s) (l - 1 - a') a' p (by
      have := Finset.mem_Icc.mp hl; have := Finset.mem_range.mp ha'; omega) hb hbp u hu hpu φ hφ
      hpφ
  have hz : ContDiff ℝ (⊤ : ℕ∞) (fun _ : Vec 2 => (0 : PiLp 2 (fun _ : Fin 2 => E))) :=
    contDiff_const
  have hzp : AVenhance.IsZ2Periodic (fun _ : Vec 2 => (0 : PiLp 2 (fun _ : Fin 2 => E))) :=
    fun _ _ => rfl
  have htarget : (fun x => toFluxL (commGen b Hc p s u x)) = fun x =>
      ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
        toFluxL ((covOperator (Hc s))^[a'] (commFluxE (b s) (Hc s)
          ((covOperator (Hc s))^[l - 1 - a'] u)) x) := by
    funext x
    simp only [commGen, toFluxL, WithLp.toLp_sum, WithLp.toLp_smul]
  have hvec : commVecOp b Hc p s = fun φ x =>
      ∑ l ∈ Finset.Icc 1 p, ((l.factorial : ℝ)⁻¹) • ∑ a' ∈ Finset.range l,
        (-(WithLp.toLp 2 (fun j => (covOperator (Hc s))^[l - 1 - a']
          (fun y => commFluxMap E (Hc s) j (fderiv ℝ (b s) y)
            (((covOperator (Hc s))^[a'] φ) y)) x))) := by
    funext φ x
    ext j
    simp [commVecOp, commStepOp, Finset.sum_apply, Finset.smul_sum]
  have hgc : Continuous (gradFlux u) :=
    (contDiff_gradFlux (n := 0) (by exact_mod_cast hu.of_le (by exact_mod_cast
      (by omega : 1 ≤ 2 * p + 1)))).continuous
  refine ⟨?_, fun φ hφ hpφ => ?_⟩
  · rw [htarget]
    exact continuous_finsetSum _ fun l hl =>
      (continuous_finsetSum _ fun a' ha' => (hterm l hl a' ha' _ hz hzp).1).const_smul ((l.factorial : ℝ)⁻¹)
  · rw [htarget, hvec, cellInner_comb_left _ (fun l => Finset.range l) _ _
      (fun l hl a' ha' => (hterm l hl a' ha' φ hφ hpφ).1) φ hφ.continuous,
      cellInner_comb_right _ (fun l => Finset.range l) _ _
      (fun l hl a' ha' => (hterm l hl a' ha' φ hφ hpφ).2.1) _ hgc]
    refine Finset.sum_congr rfl fun l hl => ?_
    congr 1
    refine Finset.sum_congr rfl fun a' ha' => ?_
    exact (hterm l hl a' ha' φ hφ hpφ).2.2.symm

end AVRegularity.EntryTerminal.CovComm
end
end

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVRegularity.CycleComparison.Coarse
open AVRegularity.EntryTerminal.CovOp AVRegularity.EntryTerminal.CovGrad
namespace AVRegularity.EntryTerminal.CovComm

/-! **Continuity in time of the commutator adjoint** (statement (C)).

The adjoint maps of `TorusAdj.commInner` (multiplication by the pointwise adjoint coefficient
`N_s(x) = 𝔑_j[H_s](Db_s(x))`) are Lipschitz in the operator norm of the arrays of
`N_s - N_{s₀}` (`MulLipStatement`). Splitting
`N_s - N_{s₀} = (P_s - P_{s₀}) Db_s + P_{s₀} D(b_s - b_{s₀})`, where `P_s = commPrimalMap (H_s)`
is linear in `H_s`, the arrays are bounded by `‖H_s - H_{s₀}‖ Bb` and by the time continuity of the
derivative arrays of `b` (`TimeCont`), so the family is continuous in `s`. The covariance factors
are continuous by `covOp_adjCont_covIter`; `commStep`, `commComp`, `commVec` are built from
`commInner` and the covariance factors by closure operations.

Special cases:
- `Hc` and `b` constant in time: the family is constant.
- `p = 0`: `commVec` is a sum over an empty set. -/

section Arrays

variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [NormedAddCommGroup Y]
  [NormedSpace ℝ Y]

theorem orderedCoeff_add (C C' : Vec 2 → X →L[ℝ] Y) :
    ∀ (j : ℕ), ContDiff ℝ (j : ℕ) C → ContDiff ℝ (j : ℕ) C' → ∀ (w : DerivativeWord2 j) (x : Vec 2),
      orderedCoefficientDerivative (fun y => C y + C' y) j w x =
        orderedCoefficientDerivative C j w x + orderedCoefficientDerivative C' j w x
  | 0, _, _, _, _ => rfl
  | j + 1, hC, hC', w, x => by
    have ih : orderedCoefficientDerivative (fun y => C y + C' y) j (Fin.init w) =
        fun y => orderedCoefficientDerivative C j (Fin.init w) y +
          orderedCoefficientDerivative C' j (Fin.init w) y :=
      funext fun y => orderedCoeff_add C C' j (hC.of_le (by exact_mod_cast Nat.le_succ j))
        (hC'.of_le (by exact_mod_cast Nat.le_succ j)) (Fin.init w) y
    have hd : DifferentiableAt ℝ (orderedCoefficientDerivative C j (Fin.init w)) x :=
      (orderedCoefficientDerivative_contDiff C j 1 (by simpa using hC) (Fin.init w)).differentiable
        (by simp) x
    have hd' : DifferentiableAt ℝ (orderedCoefficientDerivative C' j (Fin.init w)) x :=
      (orderedCoefficientDerivative_contDiff C' j 1 (by simpa using hC') (Fin.init w)).differentiable
        (by simp) x
    change fderiv ℝ (orderedCoefficientDerivative (fun y => C y + C' y) j (Fin.init w)) x
        (basisVec (w (Fin.last j))) =
      fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x (basisVec (w (Fin.last j))) +
      fderiv ℝ (orderedCoefficientDerivative C' j (Fin.init w)) x (basisVec (w (Fin.last j)))
    have hs : HasFDerivAt (fun y => orderedCoefficientDerivative C j (Fin.init w) y +
        orderedCoefficientDerivative C' j (Fin.init w) y)
        (fderiv ℝ (orderedCoefficientDerivative C j (Fin.init w)) x +
          fderiv ℝ (orderedCoefficientDerivative C' j (Fin.init w)) x) x :=
      hd.hasFDerivAt.add hd'.hasFDerivAt
    rw [ih, hs.fderiv]
    rfl

theorem array_add_le (C C' : Vec 2 → X →L[ℝ] Y) (j : ℕ) (hC : ContDiff ℝ (j : ℕ) C)
    (hC' : ContDiff ℝ (j : ℕ) C') (x : Vec 2) :
    ‖coefficientDerivativeArray (fun y => C y + C' y) j x‖ ≤
      ‖coefficientDerivativeArray C j x‖ + ‖coefficientDerivativeArray C' j x‖ := by
  have e : coefficientDerivativeArray (fun y => C y + C' y) j x =
      coefficientDerivativeArray C j x + coefficientDerivativeArray C' j x := by
    ext1 z
    ext1 w
    simp only [coefficientDerivativeArray_apply, add_apply, PiLp.add_apply]
    rw [orderedCoeff_add C C' j hC hC' w x]
    rfl
  rw [e]
  exact norm_add_le _ _

end Arrays

section Prim

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem commPrimalMap_sub (H H' : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) :
    commPrimalMap E H j - commPrimalMap E H' j = commPrimalMap E (H - H') j := by
  ext1 T
  ext1 v
  ext1 k
  simp [commPrimalMap, commPrimalCLM, commPrimalVec, centry, Matrix.sub_apply, sub_mul, mul_sub,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  rw [← sub_smul]
  congr 1
  ring

end Prim

theorem norm_iter_fderiv_diff {f g : Vec 2 → Vec 2} (l : ℕ) (hf : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) g) (x : Vec 2) :
    ‖iteratedFDeriv ℝ l (fderiv ℝ (fun y => f y - g y)) x‖ =
      ‖iteratedFDeriv ℝ (l + 1) f x - iteratedFDeriv ℝ (l + 1) g x‖ := by
  rw [norm_iteratedFDeriv_fderiv]
  have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (i := l + 1) (x := x) hf.contDiffAt hg.contDiffAt
  rw [← this]
  rfl

theorem mulConstK_lin (K : ℕ) (f g : Fin (K + 1) → ℝ) (a c : ℝ) :
    mulConstK K (fun l => a * f l + c * g l) = a * mulConstK K f + c * mulConstK K g := by
  unfold mulConstK
  simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun l _ => ?_
    ring
  · refine Finset.sum_congr rfl fun l _ => ?_
    ring

section Inner

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The pointwise estimate of the array of `N_s - N_{s₀}`. -/
theorem commInner_diff_bound (H H0 : Matrix (Fin 2) (Fin 2) ℝ) (j : Fin 2) {f g : Vec 2 → Vec 2}
    (l : ℕ) (hf : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) f)
    (hg : ContDiff ℝ ((l + 1 : ℕ) : WithTop ℕ∞) g) (x : Vec 2) {Bf ε' : ℝ}
    (hBf : ‖iteratedFDeriv ℝ (l + 1) f x‖ ≤ Bf)
    (hε' : ‖iteratedFDeriv ℝ (l + 1) f x - iteratedFDeriv ℝ (l + 1) g x‖ ≤ ε') :
    ‖coefficientDerivativeArray (fun y => commPrimalMap E H j (fderiv ℝ f y) -
        commPrimalMap E H0 j (fderiv ℝ g y)) l x‖ ≤
      4 ^ l * ((4 * covBound (H - H0)) * Bf + (4 * covBound H0) * ε') := by
  set Φ1 : (Vec 2 →L[ℝ] Vec 2) →L[ℝ] (E →L[ℝ] PiLp 2 (fun _ : Fin 2 => E)) :=
    commPrimalMap E H j - commPrimalMap E H0 j with hΦ1
  have hΦ1n : ‖Φ1‖ ≤ 4 * covBound (H - H0) := by
    rw [hΦ1, commPrimalMap_sub]
    exact norm_commPrimalMap_le _ _
  have hDf : ContDiff ℝ (l : ℕ) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hD : ContDiff ℝ (l : ℕ) (fderiv ℝ (fun y => f y - g y)) :=
    (hf.sub hg).fderiv_right (by simp)
  have e : (fun y => commPrimalMap E H j (fderiv ℝ f y) - commPrimalMap E H0 j (fderiv ℝ g y)) =
      fun y => Φ1 (fderiv ℝ f y) + commPrimalMap E H0 j (fderiv ℝ (fun z => f z - g z) y) := by
    funext y
    have hdf : DifferentiableAt ℝ f y := (hf.differentiable (by simp)) y
    have hdg : DifferentiableAt ℝ g y := (hg.differentiable (by simp)) y
    have hs : HasFDerivAt (fun z => f z - g z) (fderiv ℝ f y - fderiv ℝ g y) y :=
      hdf.hasFDerivAt.sub hdg.hasFDerivAt
    rw [hs.fderiv, hΦ1]
    simp only [sub_apply, map_sub]
    abel
  have hC1 : ContDiff ℝ (l : ℕ) (fun y => Φ1 (fderiv ℝ f y)) := Φ1.contDiff.comp hDf
  have hC2 : ContDiff ℝ (l : ℕ) (fun y => commPrimalMap E H0 j (fderiv ℝ (fun z => f z - g z) y)) :=
    (commPrimalMap E H0 j).contDiff.comp hD
  rw [e]
  refine (array_add_le _ _ l hC1 hC2 x).trans ?_
  have b1 := norm_array_clm_comp_le Φ1 (fderiv ℝ f) l hDf x
  have b2 := norm_array_clm_comp_le (commPrimalMap E H0 j) (fderiv ℝ (fun z => f z - g z)) l hD x
  have a1 := norm_array_le_iteratedFDeriv (fderiv ℝ f) l hDf x
  have a2 := norm_array_le_iteratedFDeriv (fderiv ℝ (fun z => f z - g z)) l hD x
  rw [norm_iteratedFDeriv_fderiv] at a1
  rw [norm_iter_fderiv_diff l hf hg x] at a2
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans hBf
  have h2l : (0 : ℝ) ≤ 2 ^ l := by positivity
  have hP0n : ‖commPrimalMap E H0 j‖ ≤ 4 * covBound H0 := norm_commPrimalMap_le _ _
  have hP0 : 0 ≤ ‖commPrimalMap E H0 j‖ := ContinuousLinearMap.opNorm_nonneg _
  have hP00 : 0 ≤ 4 * covBound H0 := hP0.trans hP0n
  have hε'0 : 0 ≤ ε' := (norm_nonneg _).trans hε'
  have c1 : ‖coefficientDerivativeArray (fun y => Φ1 (fderiv ℝ f y)) l x‖ ≤
      4 ^ l * ((4 * covBound (H - H0)) * Bf) := by
    refine b1.trans ?_
    have : ‖coefficientDerivativeArray (fderiv ℝ f) l x‖ ≤ 2 ^ l * Bf :=
      a1.trans (mul_le_mul_of_nonneg_left hBf h2l)
    calc 2 ^ l * (‖Φ1‖ * ‖coefficientDerivativeArray (fderiv ℝ f) l x‖)
        ≤ 2 ^ l * ((4 * covBound (H - H0)) * (2 ^ l * Bf)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hΦ1n this (norm_nonneg _)
            ((ContinuousLinearMap.opNorm_nonneg _).trans hΦ1n)) h2l
      _ = 4 ^ l * ((4 * covBound (H - H0)) * Bf) := by
          rw [show (4 : ℝ) ^ l = 2 ^ l * 2 ^ l by rw [← mul_pow]; norm_num]
          ring
  have c2 : ‖coefficientDerivativeArray
      (fun y => commPrimalMap E H0 j (fderiv ℝ (fun z => f z - g z) y)) l x‖ ≤
      4 ^ l * ((4 * covBound H0) * ε') := by
    refine b2.trans ?_
    have : ‖coefficientDerivativeArray (fderiv ℝ (fun z => f z - g z)) l x‖ ≤ 2 ^ l * ε' :=
      a2.trans (mul_le_mul_of_nonneg_left hε' h2l)
    calc 2 ^ l * (‖commPrimalMap E H0 j‖ *
          ‖coefficientDerivativeArray (fderiv ℝ (fun z => f z - g z)) l x‖)
        ≤ 2 ^ l * ((4 * covBound H0) * (2 ^ l * ε')) :=
          mul_le_mul_of_nonneg_left (mul_le_mul hP0n this (norm_nonneg _) hP00) h2l
      _ = 4 ^ l * ((4 * covBound H0) * ε') := by
          rw [show (4 : ℝ) ^ l = 2 ^ l * 2 ^ l by rw [← mul_pow]; norm_num]
          ring
  linarith

end Inner

section InnerCont

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

theorem covBound_sub_continuous {I : Set ℝ} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    (hHc : ContinuousOn Hc I) (s0 : ↥I) :
    Continuous (fun s : ↥I => 4 * covBound (Hc s.1 - Hc s0.1)) := by
  unfold covBound
  refine continuous_const.mul (continuous_finsetSum _ fun i _ =>
    continuous_finsetSum _ fun j _ => ?_)
  exact continuous_abs.comp (((hHc.domRestrict.sub continuous_const)).matrix_elem i j)

theorem commInner_adj_sub_le {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {I : Set ℝ} {M : ℝ} {Bb : ℕ → ℝ} (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 1 ≤ Q)
    (hQK : Kc + 1 ≤ Q) (hM : ∀ s ∈ I, covBound (Hc s) ≤ M)
    (hb : ∀ s ∈ I, ContDiff ℝ (Q : ℕ) (b s)) (hp : ∀ s ∈ I, AVenhance.IsZ2Periodic (b s))
    (hBb : ∀ s ∈ I, ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (K : ℕ) (hK : K + 0 ≤ Kc) (s s0 : ↥I) (Δ : Fin (K + 1) → ℝ)
    (hΔ : ∀ l : Fin (K + 1), ∀ x, ‖coefficientDerivativeArray
      (fun y => commPrimalMap E (Hc s.1) j (fderiv ℝ (b s.1) y) -
        commPrimalMap E (Hc s0.1) j (fderiv ℝ (b s0.1) y)) l.val x‖ ≤ Δ l) :
    ‖(TorusAdj.commInner (E := E) b (Hc s.1) (hM s.1 s.2) s.1 j R Kc Q hQR hQK (hb s.1 s.2)
        (hp s.1 s.2) Bb (hBb s.1 s.2)).adj K hK -
      (TorusAdj.commInner (E := E) b (Hc s0.1) (hM s0.1 s0.2) s0.1 j R Kc Q hQR hQK
        (hb s0.1 s0.2) (hp s0.1 s0.2) Bb (hBb s0.1 s0.2)).adj K hK‖ ≤ mulConstK K Δ :=
  mulLip (fun y => commPrimalMap E (Hc s.1) j (fderiv ℝ (b s.1) y))
    (fun y => commPrimalMap E (Hc s0.1) j (fderiv ℝ (b s0.1) y)) _ _ _ _ _ _ Δ hΔ

/-- **Continuity of the inner commutator coefficient family.** -/
theorem commInner_adjCont {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {I : Set ℝ}
    {M : ℝ} {Bb : ℕ → ℝ} (j : Fin 2) (R Kc Q : ℕ) (hQR : R + 1 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hM : ∀ s ∈ I, covBound (Hc s) ≤ M) (hb : ∀ s ∈ I, ContDiff ℝ (Q : ℕ) (b s))
    (hp : ∀ s ∈ I, AVenhance.IsZ2Periodic (b s))
    (hBb : ∀ s ∈ I, ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hHc : ContinuousOn Hc I) (hT : TimeCont b I Kc) :
    AdjCont2 (T := fun s : ↥I => fun (φ : Vec 2 → PiLp 2 (fun _ : Fin 2 => E)) (x : Vec 2) =>
        commFluxMap E (Hc s.1) j (fderiv ℝ (b s.1) x) (φ x)) (m := 0) (R := R) (Kc := Kc)
      (C := fun _ => mulConst (commBound M Bb) Kc)
      (fun s : ↥I => TorusAdj.commInner (E := E) b (Hc s.1) (hM s.1 s.2) s.1 j R Kc Q hQR
        hQK (hb s.1 s.2) (hp s.1 s.2) Bb (hBb s.1 s.2)) := by
  intro K hK
  apply (Metric.continuous_iff (α := ↥I)
    (β := TorusHk (K + 0) E →L[ℝ] TorusHk K (PiLp 2 fun _ : Fin 2 => E))).2
  intro s0 ε hε
  have hKc : K ≤ Kc := by omega
  set c1 : ℝ := mulConstK K (fun l : Fin (K + 1) => 4 ^ l.val * Bb l.val) with hc1
  set p0 : ℝ := 4 * covBound (Hc s0.1) with hp0
  set c2 : ℝ := mulConstK K (fun l : Fin (K + 1) => 4 ^ l.val * p0) with hc2
  have hη : 0 < ε / (2 * (|c1| + 1)) := by positivity
  have hε' : 0 < ε / (2 * (|c2| + 1)) := by positivity
  obtain ⟨δ1, hδ1, h1⟩ := Metric.continuous_iff.mp (covBound_sub_continuous hHc s0) s0 _ hη
  obtain ⟨δ2, hδ2, h2⟩ := hT s0.1 s0.2 _ hε'
  refine ⟨min δ1 δ2, lt_min hδ1 hδ2, fun s hs => ?_⟩
  have hs1 : dist s s0 < δ1 := lt_of_lt_of_le hs (min_le_left _ _)
  have hs2 : |s.1 - s0.1| < δ2 := by
    have := lt_of_lt_of_le hs (min_le_right _ _)
    rwa [Subtype.dist_eq, Real.dist_eq] at this
  have hη0 : 0 ≤ 4 * covBound (Hc s.1 - Hc s0.1) := by
    have := covBound_nonneg (Hc s.1 - Hc s0.1)
    positivity
  have hηlt : 4 * covBound (Hc s.1 - Hc s0.1) < ε / (2 * (|c1| + 1)) := by
    have := h1 s hs1
    have h0 : 4 * covBound (Hc s0.1 - Hc s0.1) = 0 := by simp [covBound]
    rwa [h0, Real.dist_eq, sub_zero, abs_of_nonneg hη0] at this
  set η0 : ℝ := 4 * covBound (Hc s.1 - Hc s0.1) with hη0def
  set ε' : ℝ := ε / (2 * (|c2| + 1)) with hε'def
  let Δ : Fin (K + 1) → ℝ := fun l => η0 * (4 ^ l.val * Bb l.val) + ε' * (4 ^ l.val * p0)
  have hΔ : ∀ l : Fin (K + 1), ∀ x, ‖coefficientDerivativeArray
      (fun y => commPrimalMap E (Hc s.1) j (fderiv ℝ (b s.1) y) -
        commPrimalMap E (Hc s0.1) j (fderiv ℝ (b s0.1) y)) l.val x‖ ≤ Δ l := by
    intro l x
    have hl : l.val ≤ Kc := by have := l.isLt; omega
    have hlQ : l.val + 1 ≤ Q := by omega
    have hf : ContDiff ℝ ((l.val + 1 : ℕ) : WithTop ℕ∞) (b s.1) :=
      (hb s.1 s.2).of_le (by exact_mod_cast hlQ)
    have hg : ContDiff ℝ ((l.val + 1 : ℕ) : WithTop ℕ∞) (b s0.1) :=
      (hb s0.1 s0.2).of_le (by exact_mod_cast hlQ)
    refine (commInner_diff_bound (E := E) (Hc s.1) (Hc s0.1) j l.val hf hg x
      (hBb s.1 s.2 l.val hl x) (h2 s.1 s.2 hs2 l.val hl x)).trans (le_of_eq ?_)
    simp only [Δ, hη0def]
    ring
  rw [show ∀ x y : TorusHk (K + 0) E →L[ℝ] TorusHk K (PiLp 2 fun _ : Fin 2 => E), dist x y = ‖x - y‖ from fun x y => dist_eq_norm x y]
  refine lt_of_le_of_lt (commInner_adj_sub_le j R Kc Q hQR hQK hM hb hp hBb K hK s s0 Δ hΔ) ?_
  rw [show mulConstK K Δ = η0 * c1 + ε' * c2 from mulConstK_lin K _ _ η0 ε']
  have e1 : η0 * c1 ≤ η0 * |c1| := mul_le_mul_of_nonneg_left (le_abs_self _) hη0
  have e2 : ε' * c2 ≤ ε' * |c2| := mul_le_mul_of_nonneg_left (le_abs_self _) hε'.le
  have e3 : η0 * (|c1| + 1) < ε / 2 := by
    have := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2 * (|c1| + 1))).1 hηlt
    linarith
  have e4 : ε' * (|c2| + 1) = ε / 2 := by
    simp only [hε'def]
    field_simp
  nlinarith [abs_nonneg c1, abs_nonneg c2]

/-- **Continuity of one inner commutator term.** -/
theorem commStep_adjCont {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ}
    {I : Set ℝ} {M : ℝ} {Bb : ℕ → ℝ} (j : Fin 2) (R Kc Q p D l a : ℕ) (hal : a < l) (hlp : l ≤ p)
    (hQR : R + 2 * p + D + 2 ≤ Q) (hQK : Kc + 1 ≤ Q)
    (hM : ∀ s ∈ I, covBound (Hc s) ≤ M) (hb : ∀ s ∈ I, ContDiff ℝ (Q : ℕ) (b s))
    (hp : ∀ s ∈ I, AVenhance.IsZ2Periodic (b s))
    (hBb : ∀ s ∈ I, ∀ l ≤ Kc, ∀ x, ‖iteratedFDeriv ℝ (l + 1) (b s) x‖ ≤ Bb l)
    (hHc : ContinuousOn Hc I) (hT : TimeCont b I Kc) :
    AdjCont2 (T := fun s : ↥I => commStepOp (E := E) b s.1 (Hc s.1) j (l - 1 - a) a)
      (m := 2 * p + D - 1) (R := R) (Kc := Kc)
      (C := fun _ => M ^ (l - 1 - a) * (mulConst (commBound M Bb) Kc * M ^ a))
      (fun s : ↥I => TorusAdj.commStep (E := E) (Hc s.1) (hM s.1 s.2) b s.1 j R Kc Q p D l a hal
        hlp hQR hQK (hb s.1 s.2) (hp s.1 s.2) Bb (hBb s.1 s.2)) := by
  have hHs : Continuous (fun s : ↥I => Hc s.1) := hHc.domRestrict
  unfold TorusAdj.commStep
  exact AdjCont2.ofOp _ (AdjCont2.liftOrder _ (AdjCont2.comp
    (covOp_adjCont_covIter (E := E) (H := fun s : ↥I => Hc s.1) hHs (fun s => hM s.1 s.2) _ _ _)
    (AdjCont2.comp (commInner_adjCont (E := E) j _ Kc Q (by omega) hQK hM hb hp hBb hHc hT)
      (covOp_adjCont_covIter (E := PiLp 2 (fun _ : Fin 2 => E)) (H := fun s : ↥I => Hc s.1) hHs
        (fun s => hM s.1 s.2) _ _ _) le_rfl le_rfl) le_rfl le_rfl))

end InnerCont

section Vec

variable {E : Type} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]
  {b : ℝ → Vec 2 → Vec 2} {Hc : ℝ → Matrix (Fin 2) (Fin 2) ℝ} {I : Set ℝ} {k p : ℕ} {M : ℝ}
  {Bb : ℕ → ℝ}

theorem commComp_adjCont (h : CommHyp b Hc I k p M Bb) (hHc : ContinuousOn Hc I)
    (hT : TimeCont b I (k + 2 * p)) (j : Fin 2) :
    AdjCont2 (fun s : ↥I => commComp (E := E) h s j) := by
  unfold commComp
  refine AdjCont2.ofOp _ (AdjCont2.mono _ _ _ (AdjCont2.sumMem _ fun l hl =>
    AdjCont2.smul (fun _ => _) continuous_const (AdjCont2.sumMem _ fun a ha =>
      AdjCont2.ofOrder _ ?_)))
  exact commStep_adjCont (E := E) j k (k + 2 * p) (k + 2 * p + 3) p 1 l a
    (Finset.mem_range.mp ha) (Finset.mem_Icc.mp hl).2 (by omega) (by omega) h.cov h.smooth
    h.periodic h.drift hHc hT

theorem commVec_adjCont (h : CommHyp b Hc I k p M Bb) (hHc : ContinuousOn Hc I)
    (hT : TimeCont b I (k + 2 * p)) :
    AdjCont (fun s : ↥I => commVec (E := E) h s) := by
  unfold commVec
  refine AdjCont2.ofOp _ (AdjCont2.sum _ fun j => AdjCont2.ofOrder _
    (AdjCont2.comp (AdjCont2.constAny _) (AdjCont2.neg (commComp_adjCont h hHc hT j)) _ _))

/-- **(C)** -/
theorem commAdjCont : CommAdjContStatement := fun h hHc hT => commVec_adjCont h hHc hT

end Vec

end AVRegularity.EntryTerminal.CovComm
end
end
end
