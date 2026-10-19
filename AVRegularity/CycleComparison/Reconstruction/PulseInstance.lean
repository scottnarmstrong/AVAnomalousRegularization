-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Reconstruction.ObsEdgesTested
import AVRegularity.CycleComparison.Reconstruction.TailForceSlice
import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.Main
import AVRegularity.CycleComparison.QuietDecay.Partition.Main
public import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.FluxTime
import AVRegularity.CycleComparison.Reconstruction.PulseIdentity
public import AVRegularity.CycleComparison.Reconstruction.PulseTailPeriodic
import AVRegularity.CycleComparison.Reconstruction.LiftSource
import AVRegularity.CycleComparison.Diagonal.Main
public import AVRegularity.CycleComparison.Reconstruction.ApproxMeasurableTail
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVenhance.Infra.Construction.StreamAdmissible
import Mathlib.Algebra.Ring.IsFormallyReal

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open AVRegularity.CycleComparison.Lift
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The lifted coarse force of one charted pulse at one time**. The scalar
companion of `setting_liftFluxPhys_word_slice`: every weighted word derivative of the physical
lifted coarse force (`liftForcePhys`, the sum over the grades and the positive degrees of the
sampled cleanup remainders read at the label `ψ x`) has mass-weighted cell norm at most a constant
times `(ρ⁻¹ (e/ρ)^{A} ε_c θ)²` times the coarse flux density of the physical flux
(`setting_liftForcePhys_word_slice`; `CoarseFluxDiff.rem_time_bound` for every grade,
`scalInt_sum_le`, `ChartTransport.scalar_slice`, `fluxDensity_invPiola_le`). -/

/-- The sampled cleanup remainder of a multiple of a chain. -/
theorem cleanupRemainder_smul_chain {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (c ρ e : ℝ) (A : ℕ) (W : ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → E) (κ : ℝ) (t : ℝ) (x : Vec 2) :
    cleanupRemainder c ρ e A (fun j τ X z k' => κ • W j τ X z k') t x =
      κ • cleanupRemainder c ρ e A W t x := by
  have hfd : ∀ (g : Vec 2 → E) (X : Vec 2), fderiv ℝ (fun X' => κ • g X') X = κ • fderiv ℝ g X :=
    fun g X => congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) κ) X
  simp only [cleanupRemainder, diagSample, cleanupSource, slowPartial, hfd,
    FunLike.coe_smul, Pi.smul_apply, ← Finset.smul_sum, smul_neg]
  rw [smul_comm]

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {D H N K k L qs qf : ℕ} {Q : LiftOperatorData ι h D} {π : ι → ℝ}
  {a b e ν B ρ E ℓ dstar εc lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
  {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edge : ι → ι → ℝ} {Θ : ℝ}
  (P : IsLiftSetting Q π a b e ν B ρ E ℓ dstar εc lam par V H N K k L qs qf CG Cw Cj edge Θ)

/-- The constant of the physical lifted coarse-force slice bound. -/
def liftForceConst (H N Acl r kres Nχ : ℕ) (Dχ : ℝ) : ℝ :=
  ChartTransport.scalarConst Dχ r *
    (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i * (((H + 1 : ℕ) : ℝ) ^ 2 *
      (N * ∑ n ∈ Finset.Icc 1 N, CoarseFluxDiff.remWordConst n Acl r i))) *
    (2 * ChartTransport.densConst kres 0 2 (2 ^ Nχ * Dχ * compConst Dχ Nχ))

omit [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι] [∀ i, MeasurableSpace (h i)]
  [∀ i, BorelSpace (h i)] in
theorem liftForceConst_nonneg (H N Acl r kres Nχ : ℕ) (Dχ : ℝ) :
    0 ≤ liftForceConst H N Acl r kres Nχ Dχ := by
  unfold liftForceConst
  refine mul_nonneg (mul_nonneg (scalarConst_nonneg r)
    (Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (mul_nonneg (by positivity)
      (mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ =>
        CoarseFluxDiff.remWordConst_nonneg n Acl r i))))) ?_
  exact mul_nonneg (by norm_num) (ChartTransport.densConst_nonneg kres 0 2 _)

omit [DecidableEq ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
include P in
/-- **The weighted word derivatives of the physical lifted coarse force of one pulse at one
time.** -/
theorem setting_liftForcePhys_word_slice (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence Q (K + D + 2) (max (k + 1) (L + 2)) a b N H Cc)
    (Acl r kres : ℕ) (hAcl : 1 ≤ Acl) (hX : Acl + 2 + r ≤ K + D + 2) (hr : r ≤ k)
    (hZ : r + 1 ≤ max (k + 1) (L + 2)) (hk : Acl + 2 + r + N + 1 ≤ kres)
    (Cg : ℝ) (hCg : 0 ≤ Cg) (hΘ : 0 ≤ Θ)
    (hgr : ∀ hh, hh ≤ H → ∀ n, 1 ≤ n → n ≤ N → ∀ m, 1 ≤ m → m ≤ n → ∀ j, j ≤ Acl + 2 + r →
      schurEnergyJet π (Set.Icc a b) k j (Cc hh n m) ≤
        ENNReal.ofReal (Cg * Θ ^ hh * lam ^ (n - m + j)))
    (hst : ∀ hh, hh ≤ H → ∀ c0 : ∀ i, h i, ∀ t ∈ Set.Icc a b, ∀ X z, ∀ n, 1 ≤ n → n ≤ N →
      liftApply n (Cc hh n) (fun _ _ => c0) t X z = 0)
    (θ : ℝ) (hθ0 : 0 ≤ θ) (hθ : ∀ hh, hh ≤ H → 2 ^ (Acl + 2 + r) * Cg * Θ ^ hh ≤ θ)
    (F : ℝ → Vec 2 → Fin 2 → ∀ i, h i) (χ ψ : ℝ → Vec 2 → Vec 2)
    (hχ : ∀ s, ContDiff ℝ (⊤ : ℕ∞) (χ s)) (hψ : ∀ s, Differentiable ℝ (ψ s))
    (hψχ : ∀ s y, ψ s (χ s y) = y) (hχψ : ∀ s x, χ s (ψ s x) = x)
    (hd : ∀ s y, (jacMatrix (χ s) y).det = 1)
    (hF : ∀ s k', ContDiff ℝ ((kres + 2 : ℕ) : ℕ∞) (fun x => F s x k'))
    (Vn : ℕ → ℕ → ℕ → ℝ → Vec 2 → Vec 2 → Fin 2 → ∀ i, h i) {t : ℝ}
    (ht : (ℓ ^ 2)⁻¹ * t ∈ Set.Icc a b)
    (hFp : ∀ k', IsZ2Periodic (fun x => F t x k'))
    (hV : ∀ hh, hh ≤ H → ∀ n', n' < N → IsCleanupChain (Acl + 2 + r) (max (k + 1) (L + 2)) Acl
      (liftApply (n' + 1) (Cc hh (n' + 1)) (fun s X => ∑ k' : Fin 2,
        fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k') (χ (ℓ ^ 2 * s) (ρ • X)) (basisVec k'))
          ((ℓ ^ 2)⁻¹ * t))
      (fun _ _ _ => 0) (fun j => Vn hh n' j ((ℓ ^ 2)⁻¹ * t)))
    (hslow : ∀ hh, hh ≤ H → ∀ n', n' < N → ∀ j, j < Acl → ∀ (n : Fin 2 → ℤ) (X : Vec 2),
      Vn hh n' j ((ℓ ^ 2)⁻¹ * t) (X + ρ⁻¹ • latticeShift n) = Vn hh n' j ((ℓ ^ 2)⁻¹ * t) X)
    (hC : IsChart (χ t) (ψ t)) {Dχ Rχ : ℝ} {Nχ : ℕ} (hDχ : 1 ≤ Dχ) (hNχ : kres + 1 ≤ Nχ)
    (hJχN : JetBound (χ t) Nχ Dχ Rχ) (hJψ : JetBound (ψ t) r Dχ Rχ)
    (hψr : ContDiff ℝ (r : ℕ∞) (ψ t)) (hρR : ρ ≤ Rχ)
    {rs : ℝ} (hrs : 0 < rs) (hrse : rs ≤ e) (hsR : rs ≤ Rχ) (heρ : e ≤ ρ) {M : ℕ}
    (hM : e⁻¹ = (M : ℝ)) {j : ℕ} (hj : j ≤ r) (β : DerivativeWord2 j) :
    scalInt π (fun x => rs ^ j • orderedDerivative β
        (fun x' => liftForcePhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vn t x') x) ≤
      ENNReal.ofReal (liftForceConst H N Acl r kres Nχ Dχ) *
        ENNReal.ofReal ((ρ⁻¹ * (e / ρ) ^ Acl) ^ 2 * εc ^ 2 * θ ^ 2) *
          CoarseFluxDiff.fluxDensity ρ kres π F t := by
  have hℓ : 0 < ℓ := by rw [P.ℓ_eq]; exact div_pos P.e_pos (Real.sqrt_pos.2 P.ν_pos)
  have hc : ℓ ^ 2 ≠ 0 := by positivity
  set τ : ℝ := (ℓ ^ 2)⁻¹ * t with hτdef
  have hℓτ : ℓ ^ 2 * τ = t := by rw [hτdef, ← mul_assoc, mul_inv_cancel₀ hc, one_mul]
  -- the data of the lifted coarse flux, grade by grade
  have hT := fun (hh : ℕ) (hhh : hh ≤ H) => setting_liftDiffTime P Cc hseq Acl r kres hAcl hX
    hr hZ hk Cg hCg hΘ hh hhh (hgr hh hhh) (hst hh hhh) θ (hθ hh hhh) F χ ψ hχ hψ hψχ hχψ hd hF
    Vn ht (hV hh hhh) hrs hrse heρ ⟨M, hM⟩
  -- the label force, by grade
  set Qh : ℕ → Vec 2 → ∀ i, h i := fun hh y => ∑ n ∈ Finset.range N,
    εc ^ (n + 1) • cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n) t y with hQh
  set q : Vec 2 → ∀ i, h i := fun y => ∑ hh ∈ Finset.range (H + 1), Qh hh y with hq
  have hfv : ∀ hh, (fun x' => CoarseFluxDiff.remVec ℓ ρ e εc Acl N
      (fun n j τ' X z k' => ρ • Vn hh (n - 1) j τ' X z k') t x') = Qh hh := by
    intro hh
    funext x'
    simp only [CoarseFluxDiff.remVec, cleanupRemainder_smul_chain, smul_smul, Finset.smul_sum]
    rw [sum_Icc_one_eq_sum_range]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [show ρ⁻¹ * (εc ^ (n + 1) * ρ) = εc ^ (n + 1) by field_simp [P.ρ_pos.ne'],
      Nat.add_sub_cancel]
  have hQc : ∀ hh ∈ Finset.range (H + 1), ∀ i, i ≤ r → ContDiff ℝ (i : ℕ∞) (Qh hh) := by
    intro hh hhm i hi
    rw [← hfv hh]
    exact CoarseFluxDiff.contDiff_remVec
      (Vn := fun n j τ' X z k' => ρ • Vn hh (n - 1) j τ' X z k')
      (hT hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm))) t rfl hi
  have hqc : ContDiff ℝ (r : ℕ∞) q := ContDiff.sum fun hh hhm => hQc hh hhm r le_rfl
  have hfast : ∀ hh, hh ≤ H → ∀ n', n' < N → ∀ j', j' < Acl → ∀ X,
      IsZ2Periodic (Vn hh n' j' τ X) := fun hh hhh n' hn' =>
    (hV hh hhh n' hn').periodic (F₀ := fun _ _ _ => 0) (fun _ _ _ => rfl)
  have hqp : IsZ2Periodic q := by
    intro n y
    show ∑ hh ∈ Finset.range (H + 1), ∑ n' ∈ Finset.range N, εc ^ (n' + 1) •
        cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t (y + latticeShift n) = _
    refine Finset.sum_congr rfl fun hh hhm => Finset.sum_congr rfl fun n' hn' => ?_
    have hhh : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
    have hp : cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t (y + latticeShift n) =
        cleanupRemainder (ℓ ^ 2)⁻¹ ρ e Acl (Vn hh n') t y :=
      cleanupRemainder_isZ2Periodic (ℓ ^ 2)⁻¹ ρ e hAcl (Vn hh n') t M hM
        (hslow hh hhh n' (Finset.mem_range.1 hn')) (hfast hh hhh n' (Finset.mem_range.1 hn'))
        n y
    rw [hp]
  -- the physical force is the label force read at the label
  have hforce : (fun x => rs ^ j • orderedDerivative β
      (fun x' => liftForcePhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vn t x') x) =
      fun x => rs ^ j • orderedDerivative β (fun x' => q (ψ t x')) x := by
    have he : (fun x' => liftForcePhys (ψ t) H N Acl εc (ℓ ^ 2) ρ e Vn t x') =
        fun x' => q (ψ t x') := by
      funext x'
      simp only [liftForcePhys, tailForcePhys, hq, hQh, Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun hh _ => Finset.sum_congr rfl fun n _ => ?_
      rw [mul_inv_cancel_left₀ hc]
    rw [he]
  rw [hforce]
  refine (scalar_slice hC hj hψr hqc hqp hDχ hrs hsR hJψ π β).trans ?_
  -- the bound of one grade, by the scalar residual of the straight lifted coarse flux
  set X0 : ℝ≥0∞ := CoarseFluxDiff.fluxDensity ρ kres π
    (fun s y k' => invPiola (χ s) (F s) y k') t with hX0
  set Y0 : ℝ≥0∞ := ENNReal.ofReal ((ρ⁻¹ * (e / ρ) ^ Acl) ^ 2 * εc ^ 2 * θ ^ 2) * X0 with hY0
  have hgrade : ∀ hh, hh ≤ H → ∀ i, i ≤ r → ∀ w : DerivativeWord2 i,
      scalInt π (fun x => rs ^ i • orderedDerivative w (Qh hh) x) ≤
        ENNReal.ofReal (N * ∑ n ∈ Finset.Icc 1 N, CoarseFluxDiff.remWordConst n Acl r i) *
          Y0 := by
    intro hh hhh i hi w
    have hb := CoarseFluxDiff.rem_time_bound
      (Vn := fun n j τ' X z k' => ρ • Vn hh (n - 1) j τ' X z k') (hT hh hhh) t rfl hℓτ θ rfl hθ0
      hi w
    rw [hfv hh] at hb
    unfold scalInt
    refine hb.trans (le_of_eq ?_)
    rw [hY0, ← mul_assoc, ← ENNReal.ofReal_mul (mul_nonneg (by positivity)
      (Finset.sum_nonneg fun n _ => CoarseFluxDiff.remWordConst_nonneg n Acl r i))]
    congr 2
    ring
  -- every word of the label force
  have hcw : ∀ i, 0 ≤ ((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
      CoarseFluxDiff.remWordConst n Acl r i) := fun i =>
    mul_nonneg (by positivity) (mul_nonneg (by positivity) (Finset.sum_nonneg fun n _ =>
      CoarseFluxDiff.remWordConst_nonneg n Acl r i))
  have hw : ∀ i ∈ Finset.range (j + 1), ∀ w : DerivativeWord2 i,
      scalInt π (fun x => rs ^ i • orderedDerivative w q x) ≤
        ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
          CoarseFluxDiff.remWordConst n Acl r i)) * Y0 := by
    intro i hi w
    have hir : i ≤ r := (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    have e1 : (fun x => rs ^ i • orderedDerivative w q x) = fun x =>
        ∑ hh ∈ Finset.range (H + 1), rs ^ i • orderedDerivative w (Qh hh) x := by
      funext x
      rw [MixedTail.orderedDerivative_sum _ w fun hh hhm => hQc hh hhm i hir, Finset.smul_sum]
    have hsum := scalInt_sum_le (Finset.range (H + 1))
      (fun hh x => rs ^ i • orderedDerivative w (Qh hh) x)
      (fun hh hhm => (continuous_orderedDerivative w (hQc hh hhm i hir)).fun_const_smul
        (rs ^ i)) π
    refine (le_of_eq (congrArg (scalInt π) e1)).trans (hsum.trans ?_)
    calc ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ hh ∈ Finset.range (H + 1),
          scalInt π (fun x => rs ^ i • orderedDerivative w (Qh hh) x)
        ≤ ((Finset.range (H + 1)).card : ℝ≥0∞) * ∑ _hh ∈ Finset.range (H + 1),
            ENNReal.ofReal (N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.remWordConst n Acl r i) * Y0 := by
          gcongr with hh hhm
          exact hgrade hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) i hir w
      _ = _ := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, ← mul_assoc, ← mul_assoc]
          congr 1
          rw [ENNReal.ofReal_mul (p := ((H + 1 : ℕ) : ℝ) ^ 2) (by positivity),
            ENNReal.ofReal_pow (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
          ring
  have hsum : ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
      scalInt π (fun x => rs ^ i • orderedDerivative w q x) ≤
      ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
        (((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
          CoarseFluxDiff.remWordConst n Acl r i))) * Y0 := by
    calc ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          scalInt π (fun x => rs ^ i • orderedDerivative w q x)
        ≤ ∑ i ∈ Finset.range (j + 1), ∑ _w : DerivativeWord2 i,
            ENNReal.ofReal (((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.remWordConst n Acl r i)) * Y0 :=
          Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun w _ => hw i hi w
      _ = ENNReal.ofReal (∑ i ∈ Finset.range (j + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.remWordConst n Acl r i))) * Y0 := by
          rw [ENNReal.ofReal_sum_of_nonneg fun i _ => mul_nonneg (by positivity) (hcw i),
            Finset.sum_mul]
          refine Finset.sum_congr rfl fun i _ => ?_
          have h2 : ((2 ^ i : ℕ) : ℝ≥0∞) = ENNReal.ofReal ((2 : ℝ) ^ i) := by
            rw [ENNReal.ofReal_pow (by norm_num)]
            simp
          rw [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul, h2]
          conv_rhs => rw [ENNReal.ofReal_mul (by positivity)]
          exact (mul_assoc _ _ _).symm
      _ ≤ _ := by
          gcongr ?_ * Y0
          exact ENNReal.ofReal_le_ofReal
            (Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.succ_le_succ hj))
              fun i _ _ => mul_nonneg (by positivity) (hcw i))
  have hFk : ∀ k', ContDiff ℝ (kres : ℕ∞) (fun x => F t x k') := fun k' =>
    (hF t k').of_le (by exact_mod_cast (by omega : kres ≤ kres + 2))
  have hχk : ContDiff ℝ ((kres + 1 : ℕ) : ℕ∞) (χ t) := (hχ t).of_le (by exact_mod_cast le_top)
  have hpi := fluxDensity_invPiola_le (χ := χ) (ψ := ψ) hC hNχ hχk hDχ P.ρ_pos hρR hJχN π F hFk
    hFp
  calc ENNReal.ofReal (scalarConst Dχ r) *
        ∑ i ∈ Finset.range (j + 1), ∑ w : DerivativeWord2 i,
          scalInt π (fun x => rs ^ i • orderedDerivative w q x)
      ≤ ENNReal.ofReal (scalarConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.remWordConst n Acl r i))) * Y0) := by gcongr
    _ ≤ ENNReal.ofReal (scalarConst Dχ r) *
          (ENNReal.ofReal (∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.remWordConst n Acl r i))) *
          (ENNReal.ofReal ((ρ⁻¹ * (e / ρ) ^ Acl) ^ 2 * εc ^ 2 * θ ^ 2) *
            (ENNReal.ofReal (2 * ChartTransport.densConst kres 0 2
              (2 ^ Nχ * Dχ * compConst Dχ Nχ)) * CoarseFluxDiff.fluxDensity ρ kres π F t))) := by
        rw [hY0, hX0]
        gcongr
    _ = _ := by
        unfold liftForceConst
        have h1 : 0 ≤ scalarConst Dχ r := scalarConst_nonneg r
        have h2 : 0 ≤ ∑ i ∈ Finset.range (r + 1), (2 : ℝ) ^ i *
            (((H + 1 : ℕ) : ℝ) ^ 2 * (N * ∑ n ∈ Finset.Icc 1 N,
              CoarseFluxDiff.remWordConst n Acl r i)) :=
          Finset.sum_nonneg fun i _ => mul_nonneg (by positivity) (hcw i)
        rw [ENNReal.ofReal_mul (mul_nonneg h1 h2), ENNReal.ofReal_mul h1]
        ring

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVenhance AVRegularity.ChartTransport
open scoped ENNReal
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The partition term of the glued lift: the label fields of one pulse**.

The partition term of the forcing of the glued lift is `∑_k ϖ_k'(t) (𝒯_k a)(t, x)`. The degree-zero
part of the pulse lift `𝒯_k a` is the coarse field itself (`pulsePhysicalLift_split`), so on the
interior of the window, where `∑_k ϖ_k' = 0`, only the positive-degree parts survive. The grade-`hh`
positive-degree part of a lift, read at the label, is the label field `labelSrc`; with a time
weight `ψ` it is the transition source field `transitionSourceField` of the quiet-gap statement
(`transitionSourceField_eq_smul`).

* `labelSrc`, `labelSrc_apply`, `labelSrc_contDiff`, `setting_labelSrc_periodic`: the label field,
  its finite smoothness and its periodicity in the label on the lift window.
* `pulsePhysicalLift_split`: `𝒯_k a = a + ∑_hh labelSrc_hh(a ∘ χ) ∘ χ⁻¹` on the lift window.
* `orderedDerivative_smul_const`, `scalInt_smul`, `scalInt_word_smul`: word derivatives and the
  scalar slice norm of constant multiples.
* `support_transition_subset`, `lintegral_eq_zero_of_support_Icc`,
  `classicalStrongEnergy_mono_set`: time supports and monotonicity of the energy. -/

section
/-- Finite smoothness orders lie below `∞`. -/
theorem natCast_le_top_order (k : ℕ) : ((k : ℕ∞) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 le_top

/-- Monotonicity of finite smoothness orders. -/
theorem natCast_le_natCast_order {i r : ℕ} (h : i ≤ r) :
    ((i : ℕ∞) : WithTop ℕ∞) ≤ ((r : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.2 (Nat.cast_le.2 h)

section Fields

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- The positive-degree grade-`hh` label field of a lift at the physical time `t`: the transition
source field `transitionSourceField` without its time weight. -/
def labelSrc (N hh : ℕ) (ℓ ρ e εc : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (y : Vec 2) : ∀ i, h i :=
  diagSample (ℓ ^ 2)⁻¹ ρ e (fun s X z => ∑ n ∈ Finset.Icc 1 N,
    εc ^ n • liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) s X z) t y

/-- The transition source field is its time weight times the label field. -/
theorem transitionSourceField_eq_smul (N hh : ℕ) (ℓ ρ e εc : ℝ) (ψ : ℝ → ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) :
    transitionSourceField N hh ℓ ρ e εc ψ Cc a t =
      fun y => ψ t • labelSrc N hh ℓ ρ e εc Cc a t y :=
  rfl

/-- The transition source field vanishes at a time where its weight vanishes. -/
theorem transitionSourceField_of_eq_zero {ψ : ℝ → ℝ} {t : ℝ} (hψ : ψ t = 0) (N hh : ℕ)
    (ℓ ρ e εc : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i) :
    transitionSourceField N hh ℓ ρ e εc ψ Cc a t = fun _ => 0 := by
  rw [transitionSourceField_eq_smul, hψ]
  funext y
  exact zero_smul ℝ _

/-- The components of the label field. -/
theorem labelSrc_apply (N hh : ℕ) (ℓ ρ e εc : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (a : ℝ → Vec 2 → ∀ i, h i) (t : ℝ) (y : Vec 2) (v : ι) :
    labelSrc N hh ℓ ρ e εc Cc a t y v = ∑ n ∈ Finset.Icc 1 N, εc ^ n •
      liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) ((ℓ ^ 2)⁻¹ * t)
        (ρ⁻¹ • y) (e⁻¹ • y) v := by
  simp only [labelSrc, diagSample, Finset.sum_apply, Pi.smul_apply]

/-- Word derivatives commute with constant multiples (no smoothness is needed). -/
theorem orderedDerivative_smul_const {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {m : ℕ} (α : DerivativeWord2 m) (c : ℝ) (g : Vec 2 → E) :
    orderedDerivative α (fun x => c • g x) = fun x => c • orderedDerivative α g x := by
  have key : ∀ (l : List (Fin 2)) (g : Vec 2 → E),
      l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) (fun x => c • g x) =
        fun x => c • l.foldl (fun g' i => fun x => fderiv ℝ g' x (basisVec i)) g x := by
    intro l
    induction l with
    | nil => intro g; rfl
    | cons i l ih =>
      intro g
      have hstep : (fun x => fderiv ℝ (fun y => c • g y) x (basisVec i)) =
          fun x => c • fderiv ℝ g x (basisVec i) := by
        funext x
        have hfd : fderiv ℝ (fun y => c • g y) x = c • fderiv ℝ g x :=
          congrFun (fderiv_const_smul_field (𝕜 := ℝ) (f := g) c) x
        simp only [hfd, FunLike.coe_smul, Pi.smul_apply]
      simp only [List.foldl_cons]
      rw [hstep]
      exact ih _
  exact key _ g

/-- The scalar slice norm of a constant multiple. -/
theorem scalInt_smul (π : ι → ℝ) (c : ℝ) (f : Vec 2 → ∀ i, h i) :
    scalInt π (fun x => c • f x) = ENNReal.ofReal (c ^ 2) * scalInt π f := by
  have hpt : ∀ (v : ι) (x : Vec 2),
      ‖(c • f x) v‖ₑ ^ 2 = ENNReal.ofReal (c ^ 2) * ‖f x v‖ₑ ^ 2 := by
    intro v x
    rw [Pi.smul_apply, enorm_smul, mul_pow, Real.enorm_eq_ofReal_abs,
      ← ENNReal.ofReal_pow (abs_nonneg c), sq_abs]
  unfold scalInt
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  simp only [hpt v]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  ring

omit [∀ i, NormedSpace ℝ (h i)] in
/-- The scalar slice norm of the zero field. -/
theorem scalInt_zero (π : ι → ℝ) : scalInt π (fun _ => (0 : ∀ i, h i)) = 0 := by
  simp [scalInt]

/-- The scalar slice norm of a weighted word derivative of a constant multiple. -/
theorem scalInt_word_smul (π : ι → ℝ) (rs c : ℝ) {n : ℕ} (w : DerivativeWord2 n)
    (L : Vec 2 → ∀ i, h i) :
    scalInt π (fun y => rs ^ n • orderedDerivative w (fun y' => c • L y') y) =
      ENNReal.ofReal (c ^ 2) * scalInt π (fun y => rs ^ n • orderedDerivative w L y) := by
  rw [orderedDerivative_smul_const]
  simp only [smul_comm (rs ^ n) c]
  exact scalInt_smul π c _

/-- The weighted word derivatives of a transition source field vanish outside the support of
its time weight. -/
theorem support_transition_subset {ψ : ℝ → ℝ} {S : Set ℝ} (hψ : Function.support ψ ⊆ S)
    (N hh : ℕ) (ℓ ρ e εc : ℝ) (Cc : ℕ → ℕ → LiftCoeff ι h) (a : ℝ → Vec 2 → ∀ i, h i)
    (π : ι → ℝ) (rs : ℝ) {n : ℕ} (w : DerivativeWord2 n) :
    Function.support (fun t => scalInt π (fun y => rs ^ n • orderedDerivative w
      (transitionSourceField N hh ℓ ρ e εc ψ Cc a t) y) ^ (1 / 2 : ℝ)) ⊆ S := by
  intro t ht
  by_contra hnot
  apply ht
  have hψ0 : ψ t = 0 := by
    by_contra hne
    exact hnot (hψ hne)
  show scalInt π (fun y => rs ^ n • orderedDerivative w
      (transitionSourceField N hh ℓ ρ e εc ψ Cc a t) y) ^ (1 / 2 : ℝ) = 0
  rw [transitionSourceField_of_eq_zero hψ0]
  simp only [orderedDerivative_zero_fun, smul_zero, scalInt_zero]
  exact ENNReal.zero_rpow_of_pos (by norm_num)

/-- The strong energy is monotone in the time window. -/
theorem classicalStrongEnergy_mono_set (ρ B : ℝ) (π : ι → ℝ) {I J : Set ℝ} (hIJ : I ⊆ J)
    (m : ℕ) (a : ℝ → Vec 2 → ∀ i, h i) :
    classicalStrongEnergy ρ B π I m a ≤ classicalStrongEnergy ρ B π J m a := by
  unfold classicalStrongEnergy
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ => mul_le_mul_right ?_ _)
    (by norm_num)
  exact add_le_add (biSup_mono fun t ht => hIJ ht)
    (mul_le_mul_right (lintegral_mono_set hIJ) _)

end Fields

/-- A lower integral of a function supported in a degenerate interval vanishes. -/
theorem lintegral_eq_zero_of_support_Icc {f : ℝ → ℝ≥0∞} {a b : ℝ} (hab : b ≤ a)
    (hf : Function.support f ⊆ Set.Icc a b) : ∫⁻ t, f t = 0 := by
  rw [← setLIntegral_eq_of_support_subset hf]
  refine setLIntegral_measure_zero _ _ ?_
  rw [Real.volume_Icc, ENNReal.ofReal_eq_zero]
  linarith

/-- A point of a scaled interval, scaled back. -/
theorem mul_mem_Icc_of_mem_div {c g g' s : ℝ} (hc : 0 < c) (hs : s ∈ Set.Icc (g / c) (g' / c)) :
    c * s ∈ Set.Icc g g' := by
  obtain ⟨h1, h2⟩ := hs
  refine ⟨?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left h1 hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  · have := mul_le_mul_of_nonneg_left h2 hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **The pulse lift is the coarse field plus its positive-degree label fields.** On the lift
window, the degree-zero part of `𝒯 a` is `a` (identity in grade zero, zero in positive grades),
and the positive-degree part of grade `hh` is the label field of the chart-frame field `a ∘ χ`,
read at the label `χ⁻¹(t, x)`. -/
theorem pulsePhysicalLift_split {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ}
    {N H : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    {ℓ : ℝ} (hℓ : ℓ ≠ 0) {ρ : ℝ} (hρ : ρ ≠ 0) (e εc : ℝ) (χ χi : ℝ → Vec 2 → Vec 2)
    (hχ : ∀ t x, χ t (χi t x) = x) (a : ℝ → Vec 2 → ∀ i, h i) {s : ℝ}
    (hs : (ℓ ^ 2)⁻¹ * s ∈ Set.Icc t₀ t₁) (x : Vec 2) :
    pulsePhysicalLift (ℓ ^ 2) ρ e εc N H Cc χ χi a s x =
      a s x + ∑ hh ∈ Finset.range (H + 1),
        labelSrc N hh ℓ ρ e εc Cc (fun t y => a t (χ t y)) s (χi s x) := by
  have hc : ℓ ^ 2 ≠ 0 := pow_ne_zero 2 hℓ
  have hcs : ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s) = s := mul_inv_cancel_left₀ hc s
  have h0 := hseq.1 (fun _ => a s x) contDiff_const ((ℓ ^ 2)⁻¹ * s) hs (ρ⁻¹ • χi s x)
    (e⁻¹ • χi s x)
  have hdeg0 : ∑ hh ∈ Finset.range (H + 1), liftApply 0 (Cc hh 0)
      (fun s' X' => a (ℓ ^ 2 * s') (χ (ℓ ^ 2 * s') (ρ • X'))) ((ℓ ^ 2)⁻¹ * s)
      (ρ⁻¹ • χi s x) (e⁻¹ • χi s x) = a s x := by
    rw [Finset.sum_eq_single 0]
    · rw [liftApply_zero_eq_const]
      simp only [hcs, smul_smul, mul_inv_cancel₀ hρ, one_smul, hχ]
      exact h0
    · intro hh hhm hh0
      have hhH : hh ≤ H := Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)
      simp only [Lift.liftApply_of_coeff_zero 0 (Cc hh 0)
        (hseq.2.1 hh (Nat.one_le_iff_ne_zero.2 hh0) hhH), Pi.zero_apply]
    · intro h0'
      exact absurd (Finset.mem_range.2 (Nat.succ_pos H)) h0'
  have hsplit : ∀ hh, ∑ n ∈ Finset.range (N + 1), εc ^ n • liftApply n (Cc hh n)
        (fun s' X' => a (ℓ ^ 2 * s') (χ (ℓ ^ 2 * s') (ρ • X'))) ((ℓ ^ 2)⁻¹ * s)
        (ρ⁻¹ • χi s x) (e⁻¹ • χi s x) =
      liftApply 0 (Cc hh 0) (fun s' X' => a (ℓ ^ 2 * s') (χ (ℓ ^ 2 * s') (ρ • X')))
          ((ℓ ^ 2)⁻¹ * s) (ρ⁻¹ • χi s x) (e⁻¹ • χi s x) +
        ∑ n ∈ Finset.Icc 1 N, εc ^ n • liftApply n (Cc hh n)
          (fun s' X' => a (ℓ ^ 2 * s') (χ (ℓ ^ 2 * s') (ρ • X'))) ((ℓ ^ 2)⁻¹ * s)
          (ρ⁻¹ • χi s x) (e⁻¹ • χi s x) := by
    intro hh
    rw [Finset.sum_range_succ', sum_Icc_one_eq_sum_range, pow_zero, one_smul]
    exact add_comm _ _
  show ∑ hh ∈ Finset.range (H + 1), ∑ n ∈ Finset.range (N + 1), εc ^ n • liftApply n (Cc hh n)
        (fun s' X' => a (ℓ ^ 2 * s') (χ (ℓ ^ 2 * s') (ρ • X'))) ((ℓ ^ 2)⁻¹ * s)
        (ρ⁻¹ • χi s x) (e⁻¹ • χi s x) = _
  rw [Finset.sum_congr rfl fun hh _ => hsplit hh, Finset.sum_add_distrib, hdeg0]
  rfl

/-- **Finite smoothness of the label field** on the lift window. -/
theorem labelSrc_contDiff {Q : LiftOperatorData ι h D} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {hh : ℕ}
    (hhh : hh ≤ H) {J : ℕ} (hJX : J ≤ sX) (hJZ : J ≤ sZ) (ℓ ρ e εc : ℝ)
    (a : ℝ → Vec 2 → ∀ i, h i) (ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t)) {s : ℝ}
    (hs : (ℓ ^ 2)⁻¹ * s ∈ Set.Icc t₀ t₁) :
    ContDiff ℝ (J : ℕ∞) (labelSrc N hh ℓ ρ e εc Cc a s) := by
  refine contDiff_pi.2 fun v => ?_
  have he : (fun y => labelSrc N hh ℓ ρ e εc Cc a s y v) = fun y => ∑ n ∈ Finset.Icc 1 N,
      εc ^ n • liftApply n (Cc hh n) (fun s' X' => a (ℓ ^ 2 * s') (ρ • X'))
        ((ℓ ^ 2)⁻¹ * s) (ρ⁻¹ • y) (e⁻¹ • y) v :=
    funext fun y => labelSrc_apply N hh ℓ ρ e εc Cc a s y v
  rw [he]
  refine ContDiff.sum fun n _ => ContDiff.const_smul (εc ^ n) ?_
  have hF : ContDiff ℝ ((sX + n : ℕ) : ℕ∞)
      (fun X' : Vec 2 => a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • X')) :=
    ((ha _).comp (contDiff_const_smul ρ)).of_le (natCast_le_top_order _)
  have hbox := QuietDecay.Partition.isBoxSmooth_liftApply n sX sZ (Cc hh n)
    (fun s' X' => a (ℓ ^ 2 * s') (ρ • X')) ((ℓ ^ 2)⁻¹ * s)
    (fun m α v' u => (hseq.2.2.2.2.2.1 hh hhh n m α v' u _ hs).1) hF v
  exact CoarseFluxDiff.contDiff_sample hbox hJX hJZ ρ e

/-- **Periodicity of the label field in the label** on the lift window, for a coarse field
periodic in space, if the slow translations by `ρ⁻¹ℤ²` leave the metric and the source
coefficients invariant and `e⁻¹ ∈ ℕ`. -/
theorem setting_labelSrc_periodic {N H K k L qs qf : ℕ} {Q : LiftOperatorData ι h D}
    {π : ι → ℝ} {t₀ t₁ e₀ ν B ρ₀ E ℓ₀ dstar εc₀ lam : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {bm : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting Q π t₀ t₁ e₀ ν B ρ₀ E ℓ₀ dstar εc₀ lam par V H N K k L qs qf CG Cw Cj
      bm Θ)
    {sX sZ : ℕ} {Cc : ℕ → ℕ → LiftCoeff ι h} (hseq : IsLiftSequence Q sX sZ t₀ t₁ N H Cc)
    {hh : ℕ} (hhh : hh ≤ H) (ℓ ρ e εc : ℝ) (hρ : ρ ≠ 0) (M : ℕ) (hM : e⁻¹ = M)
    (a : ℝ → Vec 2 → ∀ i, h i) (ha : ∀ t, ContDiff ℝ (⊤ : ℕ∞) (a t))
    (hap : ∀ t, IsZ2Periodic (a t))
    (hGs : ∀ (n : Fin 2 → ℤ) t X i j, Q.G t (X + ρ⁻¹ • latticeShift n) i j = Q.G t X i j)
    (hcs : ∀ (n : Fin 2 → ℤ) v u d, ∀ γ ∈ Q.edge v u d, ∀ α t X z,
      γ.coeff α t (X + ρ⁻¹ • latticeShift n) z = γ.coeff α t X z)
    {s : ℝ} (hs : (ℓ ^ 2)⁻¹ * s ∈ Set.Icc t₀ t₁) :
    IsZ2Periodic (labelSrc N hh ℓ ρ e εc Cc a s) := by
  intro n y
  funext v
  rw [labelSrc_apply, labelSrc_apply]
  refine Finset.sum_congr rfl fun n' _ => ?_
  congr 1
  simp only [liftApply]
  refine Finset.sum_congr rfl fun m' _ => Finset.sum_congr rfl fun α _ =>
    Finset.sum_congr rfl fun u _ => ?_
  have hX : ρ⁻¹ • (y + latticeShift n) = ρ⁻¹ • y + ρ⁻¹ • latticeShift n := smul_add _ _ _
  have hz : e⁻¹ • (y + latticeShift n) = e⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i) := by
    rw [smul_add, hM, natCast_smul_latticeShift]
  have hslow := LiftMeanEntrywise.setting_liftSequence_slowShift_invariant P sX sZ Cc hseq
    (ρ⁻¹ • latticeShift n) (hGs n) (hcs n) hh hhh n' m' α ((ℓ ^ 2)⁻¹ * s) hs (ρ⁻¹ • y)
    (e⁻¹ • y + latticeShift (fun i => (M : ℤ) * n i)) v u
  have hfast := (hseq.2.2.2.2.2.1 hh hhh n' m' α v u ((ℓ ^ 2)⁻¹ * s) hs).2 (ρ⁻¹ • y)
    (fun i => (M : ℤ) * n i) (e⁻¹ • y)
  have hg : ContDiff ℝ (m' : ℕ∞) (fun X' : Vec 2 => a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • X')) :=
    ((ha _).comp (contDiff_const_smul ρ)).of_le (natCast_le_top_order _)
  have hT : ∀ Y : Vec 2, a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • (Y + ρ⁻¹ • latticeShift n)) =
      a (ℓ ^ 2 * ((ℓ ^ 2)⁻¹ * s)) (ρ • Y) := by
    intro Y
    rw [smul_add, smul_smul, mul_inv_cancel₀ hρ, one_smul, hap _ n (ρ • Y)]
  have hjet := Reconstruction.orderedDerivative_periodic hg (ρ⁻¹ • latticeShift n) hT α
    (ρ⁻¹ • y)
  simp only at hfast
  rw [hX, hz, hslow, hfast, hjet]

end Lift
end

/-! **The partition term of the glued lift at one time**.

At one time the partition term is a weighted sum `∑_p ψ_p G_p` of charted label fields
`G_p = (∑_hh L_{p,hh}) ∘ χ_p⁻¹` in which at most two weights are nonzero. Its weighted word
derivatives of order at most `r` are bounded by a constant times the weighted word derivatives of
the time-weighted label fields `ψ_p L_{p,hh}` (`slice_bound`): Cauchy–Schwarz over the active
pieces (`scalInt_sum_le`), exact chart transport of scalars (`ChartTransport.scalar_slice`) and
Cauchy–Schwarz over the grades. The bookkeeping of the nested finite sums (square roots, lower
integrals and counts) is in `rpow_half_nested_le`, `lintegral_nested_sum`, `nested_sum_const`. -/

section
/-- The constant of the time-slice bound of the partition term. -/
def sliceConst (H r : ℕ) (D : ℝ) : ℝ :=
  (∑ j ∈ Finset.range (r + 1), (2 : ℝ) ^ j) * (2 * (scalarConst D r * (H + 1)))

theorem sliceConst_nonneg (H r : ℕ) (D : ℝ) : 0 ≤ sliceConst H r D :=
  mul_nonneg (Finset.sum_nonneg fun j _ => by positivity)
    (mul_nonneg (by norm_num) (mul_nonneg (scalarConst_nonneg r) (by positivity)))

section Slice

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)]

/-- **One charted piece at one time.** A time-weighted charted grade sum
`c (∑_hh L_hh) ∘ χ⁻¹` has each weighted word derivative bounded by the weighted word derivatives
of the time-weighted label fields `c L_hh`. -/
theorem slice_piece_bound {H r j : ℕ} (hj : j ≤ r) {D Rχ rs : ℝ} (hD : 1 ≤ D) (hrs : 0 < rs)
    (hsR : rs ≤ Rχ) (π : ι → ℝ) (c : ℝ) {χ χi : Vec 2 → Vec 2} (L : ℕ → Vec 2 → ∀ i, h i)
    (hC : c ≠ 0 → IsChart χ χi) (hχi : c ≠ 0 → ContDiff ℝ (r : ℕ∞) χi)
    (hJ : c ≠ 0 → JetBound χi r D Rχ)
    (hL : c ≠ 0 → ∀ hh ∈ Finset.range (H + 1), ContDiff ℝ (r : ℕ∞) (L hh))
    (hLp : c ≠ 0 → ∀ hh ∈ Finset.range (H + 1), IsZ2Periodic (L hh)) (w : DerivativeWord2 j) :
    scalInt π (fun x => c • (rs ^ j • orderedDerivative w
        (fun x' => ∑ hh ∈ Finset.range (H + 1), L hh (χi x')) x)) ≤
      ENNReal.ofReal (scalarConst D r * (H + 1)) *
        ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1),
          scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' => c • L hh y') y) := by
  rw [scalInt_smul]
  by_cases hc : c = 0
  · rw [hc]
    simp
  have hq : ContDiff ℝ (r : ℕ∞) (fun y => ∑ hh ∈ Finset.range (H + 1), L hh y) :=
    ContDiff.sum fun hh hhm => hL hc hh hhm
  have hqp : IsZ2Periodic (fun y => ∑ hh ∈ Finset.range (H + 1), L hh y) := fun n y =>
    Finset.sum_congr rfl fun hh hhm => hLp hc hh hhm n y
  have h1 := scalar_slice (hC hc) hj (hχi hc) hq hqp hD hrs hsR (hJ hc) π w
  have h2 : ∀ i, i ≤ r → ∀ w' : DerivativeWord2 i,
      scalInt π (fun x => rs ^ i • orderedDerivative w'
          (fun y => ∑ hh ∈ Finset.range (H + 1), L hh y) x) ≤
        ((H + 1 : ℕ) : ℝ≥0∞) * ∑ hh ∈ Finset.range (H + 1),
          scalInt π (fun x => rs ^ i • orderedDerivative w' (L hh) x) := by
    intro i hir w'
    have hsm : ∀ hh ∈ Finset.range (H + 1), ContDiff ℝ (i : ℕ∞) (L hh) := fun hh hhm =>
      (hL hc hh hhm).of_le (natCast_le_natCast_order hir)
    have e2 : (fun x => rs ^ i • orderedDerivative w'
          (fun y => ∑ hh ∈ Finset.range (H + 1), L hh y) x) =
        fun x => ∑ hh ∈ Finset.range (H + 1), rs ^ i • orderedDerivative w' (L hh) x := by
      rw [MixedTail.orderedDerivative_sum (Finset.range (H + 1)) w' hsm]
      funext x
      simp only [Finset.smul_sum]
    rw [e2]
    have h3 := scalInt_sum_le (Finset.range (H + 1))
      (fun hh x => rs ^ i • orderedDerivative w' (L hh) x)
      (fun hh hhm => (continuous_orderedDerivative w' (hsm hh hhm)).const_smul (rs ^ i)) π
    rwa [Finset.card_range] at h3
  have hZ : ∀ i (w' : DerivativeWord2 i) hh,
      scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' => c • L hh y') y) =
        ENNReal.ofReal (c ^ 2) * scalInt π (fun x => rs ^ i • orderedDerivative w' (L hh) x) :=
    fun i w' hh => scalInt_word_smul π rs c w' (L hh)
  have hsub : Finset.range (j + 1) ⊆ Finset.range (r + 1) :=
    Finset.range_subset_range.2 (by omega)
  have hcast : ENNReal.ofReal ((H : ℝ) + 1) = ((H + 1 : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_add, Nat.cast_one]
  calc ENNReal.ofReal (c ^ 2) * scalInt π (fun x => rs ^ j • orderedDerivative w
          (fun x' => ∑ hh ∈ Finset.range (H + 1), L hh (χi x')) x)
      ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (scalarConst D r) *
          ∑ i ∈ Finset.range (j + 1), ∑ w' : DerivativeWord2 i, scalInt π (fun x => rs ^ i •
            orderedDerivative w' (fun y => ∑ hh ∈ Finset.range (H + 1), L hh y) x)) :=
        mul_le_mul_right h1 _
    _ ≤ ENNReal.ofReal (c ^ 2) * (ENNReal.ofReal (scalarConst D r) *
          ∑ i ∈ Finset.range (j + 1), ∑ w' : DerivativeWord2 i,
            ((H + 1 : ℕ) : ℝ≥0∞) * ∑ hh ∈ Finset.range (H + 1),
              scalInt π (fun x => rs ^ i • orderedDerivative w' (L hh) x)) := by
        refine mul_le_mul_right (mul_le_mul_right (Finset.sum_le_sum fun i hi =>
          Finset.sum_le_sum fun w' _ => h2 i ?_ w') _) _
        exact (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans hj
    _ = ENNReal.ofReal (scalarConst D r) * ((H + 1 : ℕ) : ℝ≥0∞) *
          ∑ i ∈ Finset.range (j + 1), ∑ w' : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1),
            scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' => c • L hh y') y) := by
        simp only [hZ, Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun w' _ =>
          Finset.sum_congr rfl fun hh _ => ?_
        ring
    _ ≤ ENNReal.ofReal (scalarConst D r) * ((H + 1 : ℕ) : ℝ≥0∞) *
          ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1),
            scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' => c • L hh y') y) :=
        mul_le_mul_right (Finset.sum_le_sum_of_subset hsub) _
    _ = _ := by
        rw [ENNReal.ofReal_mul (scalarConst_nonneg r), hcast]

/-- **The partition term at one time.** A weighted sum of charted grade sums with at most two
nonzero weights has its weighted word derivatives of order at most `r` bounded by
`sliceConst` times the weighted word derivatives of the time-weighted label fields. -/
theorem slice_bound {P : Finset (ℤ × Bool)} {H r : ℕ} {D Rχ rs : ℝ} (hD : 1 ≤ D)
    (hrs : 0 < rs) (hsR : rs ≤ Rχ) (π : ι → ℝ) (ψ : ℤ × Bool → ℝ)
    (χ χi : ℤ × Bool → Vec 2 → Vec 2) (L : ℤ × Bool → ℕ → Vec 2 → ∀ i, h i)
    (G : ℤ × Bool → Vec 2 → ∀ i, h i)
    (hG : ∀ p x', G p x' = ∑ hh ∈ Finset.range (H + 1), L p hh (χi p x'))
    (hC : ∀ p ∈ P, ψ p ≠ 0 → IsChart (χ p) (χi p))
    (hχi : ∀ p ∈ P, ψ p ≠ 0 → ContDiff ℝ (r : ℕ∞) (χi p))
    (hJ : ∀ p ∈ P, ψ p ≠ 0 → JetBound (χi p) r D Rχ)
    (hL : ∀ p ∈ P, ψ p ≠ 0 → ∀ hh ∈ Finset.range (H + 1), ContDiff ℝ (r : ℕ∞) (L p hh))
    (hLp : ∀ p ∈ P, ψ p ≠ 0 → ∀ hh ∈ Finset.range (H + 1), IsZ2Periodic (L p hh))
    (hcard : (P.filter fun p => ψ p ≠ 0).card ≤ 2) :
    ∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun x => rs ^ j • orderedDerivative w (fun x' => ∑ p ∈ P, ψ p • G p x') x) ≤
      ENNReal.ofReal (sliceConst H r D) *
        ∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i,
          ∑ hh ∈ Finset.range (H + 1),
            scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' => ψ p • L p hh y') y) := by
  have hGe : ∀ p, G p = fun x' => ∑ hh ∈ Finset.range (H + 1), L p hh (χi p x') :=
    fun p => funext (hG p)
  have hGs : ∀ p ∈ P, ψ p ≠ 0 → ContDiff ℝ (r : ℕ∞) (G p) := fun p hp hψ => by
    rw [hGe p]
    exact ContDiff.sum fun hh hhm => (hL p hp hψ hh hhm).comp (hχi p hp hψ)
  have hword : ∀ j, j ≤ r → ∀ w : DerivativeWord2 j,
      scalInt π (fun x => rs ^ j • orderedDerivative w (fun x' => ∑ p ∈ P, ψ p • G p x') x) ≤
        2 * (ENNReal.ofReal (scalarConst D r * (H + 1)) *
          ∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i,
            ∑ hh ∈ Finset.range (H + 1), scalInt π
              (fun y => rs ^ i • orderedDerivative w' (fun y' => ψ p • L p hh y') y)) := by
    intro j hj w
    have hsm : ∀ p ∈ P, ψ p ≠ 0 → ContDiff ℝ (j : ℕ∞) (G p) := fun p hp hψ =>
      (hGs p hp hψ).of_le (natCast_le_natCast_order hj)
    have e1 : (fun x => rs ^ j • orderedDerivative w (fun x' => ∑ p ∈ P, ψ p • G p x') x) =
        fun x => ∑ p ∈ P.filter (fun p => ψ p ≠ 0),
          ψ p • (rs ^ j • orderedDerivative w (G p) x) := by
      funext x
      rw [orderedDerivative_weighted_sum P ψ w G hsm x, Finset.smul_sum,
        Finset.sum_filter_of_ne]
      · exact Finset.sum_congr rfl fun p _ => smul_comm _ _ _
      · intro p _ hne h0
        exact hne (by rw [h0, zero_smul])
    rw [e1]
    have hcont : ∀ p ∈ P.filter (fun p => ψ p ≠ 0),
        Continuous (fun x => ψ p • (rs ^ j • orderedDerivative w (G p) x)) := fun p hp =>
      ((continuous_orderedDerivative w (hsm p (Finset.mem_filter.1 hp).1
        (Finset.mem_filter.1 hp).2)).const_smul (rs ^ j)).const_smul (ψ p)
    have hcardE : (((P.filter fun p => ψ p ≠ 0).card : ℕ) : ℝ≥0∞) ≤ 2 := by
      exact_mod_cast hcard
    have hpiece : ∀ p ∈ P,
        scalInt π (fun x => ψ p • (rs ^ j • orderedDerivative w (G p) x)) ≤
          ENNReal.ofReal (scalarConst D r * (H + 1)) *
            ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1),
              scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' => ψ p • L p hh y') y) := by
      intro p hp
      rw [hGe p]
      exact slice_piece_bound hj hD hrs hsR π (ψ p) (L p) (hC p hp) (hχi p hp) (hJ p hp)
        (hL p hp) (hLp p hp) w
    calc scalInt π (fun x => ∑ p ∈ P.filter (fun p => ψ p ≠ 0),
          ψ p • (rs ^ j • orderedDerivative w (G p) x))
        ≤ (((P.filter fun p => ψ p ≠ 0).card : ℕ) : ℝ≥0∞) *
            ∑ p ∈ P.filter (fun p => ψ p ≠ 0),
              scalInt π (fun x => ψ p • (rs ^ j • orderedDerivative w (G p) x)) :=
          scalInt_sum_le _ (fun p x => ψ p • (rs ^ j • orderedDerivative w (G p) x)) hcont π
      _ ≤ 2 * ∑ p ∈ P, scalInt π (fun x => ψ p • (rs ^ j • orderedDerivative w (G p) x)) :=
          mul_le_mul' hcardE (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
      _ ≤ 2 * ∑ p ∈ P, ENNReal.ofReal (scalarConst D r * (H + 1)) *
            ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1),
              scalInt π (fun y => rs ^ i • orderedDerivative w' (fun y' => ψ p • L p hh y') y) :=
          mul_le_mul_right (Finset.sum_le_sum hpiece) _
      _ = _ := by rw [← Finset.mul_sum]
  have hc2 : ENNReal.ofReal (∑ j ∈ Finset.range (r + 1), (2 : ℝ) ^ j) =
      ((∑ j ∈ Finset.range (r + 1), 2 ^ j : ℕ) : ℝ≥0∞) := by
    rw [← ENNReal.ofReal_natCast, Nat.cast_sum]
    simp only [Nat.cast_pow, Nat.cast_ofNat]
  calc ∑ j ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 j,
        scalInt π (fun x => rs ^ j • orderedDerivative w (fun x' => ∑ p ∈ P, ψ p • G p x') x)
      ≤ ∑ j ∈ Finset.range (r + 1), ∑ _w : DerivativeWord2 j,
          2 * (ENNReal.ofReal (scalarConst D r * (H + 1)) *
            ∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i,
              ∑ hh ∈ Finset.range (H + 1), scalInt π
                (fun y => rs ^ i • orderedDerivative w' (fun y' => ψ p • L p hh y') y)) :=
        Finset.sum_le_sum fun j hj => Finset.sum_le_sum fun w _ =>
          hword j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)) w
    _ = ((∑ j ∈ Finset.range (r + 1), 2 ^ j : ℕ) : ℝ≥0∞) *
          (2 * (ENNReal.ofReal (scalarConst D r * (H + 1)) *
            ∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w' : DerivativeWord2 i,
              ∑ hh ∈ Finset.range (H + 1), scalInt π
                (fun y => rs ^ i • orderedDerivative w' (fun y' => ψ p • L p hh y') y))) := by
        simp only [Finset.sum_const, card_derivativeWord2, nsmul_eq_mul]
        rw [← Finset.sum_mul, Nat.cast_sum]
    _ = _ := by
        unfold sliceConst
        rw [ENNReal.ofReal_mul (p := ∑ j ∈ Finset.range (r + 1), (2 : ℝ) ^ j)
            (Finset.sum_nonneg fun j _ => by positivity),
          ENNReal.ofReal_mul (p := (2 : ℝ)) (by norm_num), ENNReal.ofReal_ofNat, hc2]
        ring

end Slice

/-! ### Nested finite sums -/

/-- The square root of a nested finite sum is at most the nested sum of the square roots. -/
theorem rpow_half_nested_le {κ : Type*} (P : Finset κ) (r H : ℕ)
    (Z : κ → (i : ℕ) → DerivativeWord2 i → ℕ → ℝ≥0∞) :
    (∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
        ∑ hh ∈ Finset.range (H + 1), Z p i w hh) ^ (1 / 2 : ℝ) ≤
      ∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
        ∑ hh ∈ Finset.range (H + 1), Z p i w hh ^ (1 / 2 : ℝ) := by
  have hp : (0 : ℝ) < 1 / 2 := by norm_num
  have hp1 : (1 / 2 : ℝ) ≤ 1 := by norm_num
  refine (ChartTransport.rpow_sum_le P _ hp hp1).trans (Finset.sum_le_sum fun p _ => ?_)
  refine (ChartTransport.rpow_sum_le _ _ hp hp1).trans (Finset.sum_le_sum fun i _ => ?_)
  refine (ChartTransport.rpow_sum_le _ _ hp hp1).trans (Finset.sum_le_sum fun w _ => ?_)
  exact ChartTransport.rpow_sum_le _ _ hp hp1

/-- The lower integral of a nested finite sum of a.e.-measurable functions is the nested sum of
the lower integrals. -/
theorem lintegral_nested_sum {α : Type*} [MeasurableSpace α] {μ : Measure α} {κ : Type*}
    (P : Finset κ) (r H : ℕ) (f : κ → (i : ℕ) → DerivativeWord2 i → ℕ → α → ℝ≥0∞)
    (hf : ∀ p ∈ P, ∀ i ∈ Finset.range (r + 1), ∀ w : DerivativeWord2 i,
      ∀ hh ∈ Finset.range (H + 1), AEMeasurable (f p i w hh) μ) :
    ∫⁻ x, ∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
        ∑ hh ∈ Finset.range (H + 1), f p i w hh x ∂μ =
      ∑ p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ w : DerivativeWord2 i,
        ∑ hh ∈ Finset.range (H + 1), ∫⁻ x, f p i w hh x ∂μ := by
  have h4 : ∀ p ∈ P, ∀ i ∈ Finset.range (r + 1), ∀ w : DerivativeWord2 i,
      AEMeasurable (fun x => ∑ hh ∈ Finset.range (H + 1), f p i w hh x) μ :=
    fun p hp i hi w => Finset.aemeasurable_fun_sum _ fun hh hhm => hf p hp i hi w hh hhm
  have h3 : ∀ p ∈ P, ∀ i ∈ Finset.range (r + 1),
      AEMeasurable (fun x => ∑ w : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1),
        f p i w hh x) μ :=
    fun p hp i hi => Finset.aemeasurable_fun_sum _ fun w _ => h4 p hp i hi w
  have h2 : ∀ p ∈ P, AEMeasurable (fun x => ∑ i ∈ Finset.range (r + 1),
      ∑ w : DerivativeWord2 i, ∑ hh ∈ Finset.range (H + 1), f p i w hh x) μ :=
    fun p hp => Finset.aemeasurable_fun_sum _ fun i hi => h3 p hp i hi
  rw [lintegral_finsetSum' P h2]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [lintegral_finsetSum' _ (h3 p hp)]
  refine Finset.sum_congr rfl fun i hi => ?_
  rw [lintegral_finsetSum' _ fun w _ => h4 p hp i hi w]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [lintegral_finsetSum' _ fun hh hhm => hf p hp i hi w hh hhm]

/-- The nested finite sum of a constant. -/
theorem nested_sum_const {κ : Type*} (P : Finset κ) (r H : ℕ) (X : ℝ≥0∞) :
    ∑ _p ∈ P, ∑ i ∈ Finset.range (r + 1), ∑ _w : DerivativeWord2 i,
        ∑ _hh ∈ Finset.range (H + 1), X =
      ((P.card * ∑ i ∈ Finset.range (r + 1), 2 ^ i * (H + 1) : ℕ) : ℝ≥0∞) * X := by
  have h1 : ∀ i : ℕ, ∑ _w : DerivativeWord2 i, ∑ _hh ∈ Finset.range (H + 1), X =
      ((2 ^ i * (H + 1) : ℕ) : ℝ≥0∞) * X := by
    intro i
    rw [Finset.sum_const, Finset.sum_const, Finset.card_range, card_derivativeWord2, smul_smul,
      nsmul_eq_mul]
  simp only [h1]
  rw [← Finset.sum_mul, Finset.sum_const, nsmul_eq_mul, ← mul_assoc, ← Nat.cast_sum,
    ← Nat.cast_mul]

/-- Collecting a count and two real factors into one real factor. -/
theorem final_count_eq {A Y : ℝ} (hA : 0 ≤ A) (n : ℕ) (Ea : ℝ≥0∞) :
    ENNReal.ofReal A * ((n : ℝ≥0∞) * (ENNReal.ofReal Y * Ea)) =
      ENNReal.ofReal (A * n * Y) * Ea := by
  rw [ENNReal.ofReal_mul (mul_nonneg hA (Nat.cast_nonneg n)), ENNReal.ofReal_mul hA,
    ENNReal.ofReal_natCast]
  ring
end

end AVRegularity.CycleComparison.Reconstruction
end

section
open Homogenization MeasureTheory Set AVRegularity.Sobolev AVRegularity.CycleEvolution AVenhance
open AVRegularity.CycleComparison.Lift
open scoped Matrix
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The weak identity of one observed pulse**.
`setting_pulse_weak` for the lift data `Q = pulseLiftData … k edge` of the odd pulse `k`, in its
chart `χ_t = ocChart … l t`, `l = ocPulseChartIndex k`, with the time scale `c = ℓ²`, the slow
scale `ρ`, the fast scale `e = ε_m`, the diffusivity `ν` and `ε_c = d_*/ρ`, on a physical window
inside the pulse window `ocPulseWindow k` (`pulse_weak_instance`). On that window no other odd
pulse is active, so the pushed-forward pulse drift plus the chart drift `b_{m-1}` is the actual
drift `b_m` (`pulse_drift_physical`). -/

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [DecidableEq ι]
  [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]

/-- **The weak identity of one observed pulse lift** for a smooth periodic test, with the actual
drift `b_m = streamVel (Φ m)`. -/
theorem pulse_weak_instance {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ} {Φ : ℕ → ℝ → Vec 2 → ℝ}
    (hseqΦ : IsOCStreamSeq α q Λ ζ Φ) (hm : 1 ≤ m) (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ)
    (hφs : IsAdmissibleStream (Φ (m - 1))) {ν B : ℝ} (hν : 0 < ν) (hB : 0 < B)
    {ρ lam : ℝ} (hρ : 0 < ρ) {kp : ℤ} (hkp : Odd kp) {D : ℕ} (edge : ConstituentEdges D h)
    {π : ι → ℝ} {a b e₀ ν₀ B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ : ℝ} {par : Fin 2} {V : ℝ → ℝ → ℝ}
    {H N K k₀ L qs qf : ℕ} {CG Cw : ℕ → ℝ} {Cj : ℕ → ℕ → ℝ} {edgeM : ι → ι → ℝ} {Θ : ℝ}
    (P : IsLiftSetting (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam kp edge) π a b e₀ ν₀
      B₀' ρ₀ E₀ ℓ₀ dstar₀ εc₀ lam₀ par V H N K k₀ L qs qf CG Cw Cj edgeM Θ)
    (hwin : Icc (ocEll q Λ m ν ^ 2 * a) (ocEll q Λ m ν ^ 2 * b) ⊆ ocPulseWindow α q Λ m kp)
    (sX sZ : ℕ) (hsX : 2 ≤ sX) (hsZ : 2 ≤ sZ) (Cc : ℕ → ℕ → LiftCoeff ι h)
    (hseq : IsLiftSequence (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam kp edge) sX sZ
      a b N H Cc)
    {κ : Type*} [Fintype κ] (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, IsZ2Periodic (φ k)) (A₀ B₀ : ℝ)
    (hA : A₀ ≤ ocEll q Λ m ν ^ 2 * a) (hB₀ : ocEll q Λ m ν ^ 2 * b ≤ B₀)
    (hcf : ∀ k, IsPrimOn A₀ B₀ (cf k) (dcf k))
    (hcs : ∀ (n : Fin 2 → ℤ) v u d,
      ∀ γ ∈ (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam kp edge).edge v u d, ∀ w t X z,
        γ.coeff w t (X + ρ⁻¹ • latticeShift n) z = γ.coeff w t X z)
    (v : ι) (φt : Vec 2 → h v) (hφt : ContDiff ℝ 1 φt) (hφtp : IsZ2Periodic φt) :
    IsPrimOn (ocEll q Λ m ν ^ 2 * a) (ocEll q Λ m ν ^ 2 * b)
      (fun t => ∫ x in AVenhance.unitCube, inner ℝ
        (pulseLift Cc N H (ocDStar q Λ m ν B / ρ)
          (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp))
            (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2)
          (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp)) t x v) (φt x))
      (fun t => -(∫ x in AVenhance.unitCube, inner ℝ (∑ k, streamVel (Φ m) t x k •
          fderiv ℝ (fun x' => pulseLift Cc N H (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2)
            (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp)) t x' v) x
            (basisVec k)) (φt x)) -
        ν * (∫ x in AVenhance.unitCube, ∑ k, inner ℝ
          (fderiv ℝ (fun x' => pulseLift Cc N H (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp))
              (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m) (ocEll q Λ m ν ^ 2)
            (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp)) t x' v) x
            (basisVec k))
          (fderiv ℝ φt x (basisVec k))) +
        (ocEll q Λ m ν ^ 2)⁻¹ * ∫ x in AVenhance.unitCube, inner ℝ
          (labelRest (pulseLiftData α q Λ m ζ (Φ (m - 1)) hφs ν B ρ lam kp edge) Cc N H
            (ocDStar q Λ m ν B / ρ)
            (chartField cf φ (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp))
              (ocEll q Λ m ν ^ 2) ρ)
            (chartFieldDot cf dcf φ
              (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp))
              (streamVel (Φ (m - 1))) (ocEll q Λ m ν ^ 2) ρ) ρ (ocEpsilon q Λ m)
            (ocEll q Λ m ν ^ 2) t
            (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp) t x) v)
          (φt x)) := by
  have he : ocEpsilon q Λ m ≠ 0 := ocEpsilon_ne_zero_of m hΛ
  have hℓ : ocEll q Λ m ν ≠ 0 := ocEll_ne_zero_of hν he
  have hc : 0 < ocEll q Λ m ν ^ 2 := by positivity
  obtain ⟨M, hM⟩ := pulse_e_inv_nat q Λ m
  obtain ⟨hΨ', -⟩ := hseqΦ.2 (m + 1) (by omega)
  have hΨ : IsAdmissibleStream (Φ m) := hΨ'
  have hkl : ocLabel α q Λ m kp = ocPulseChartIndex α q Λ m kp :=
    ocLabel_eq_ocPulseChartIndex α q Λ m kp
      (AVRegularity.Construction.Stream.ocTauPP_pos hΛ)
  -- the velocity increment `b_m - b_{m-1}` is continuous
  have hcont : ∀ (j : ℕ) (hj : IsAdmissibleStream (Φ j)) (t : ℝ),
      Continuous (streamVel (Φ j) t) := fun j hj t =>
    ((AVenhance.Infra.Construction.smoothPeriodic_streamVel hj).smooth.comp
      (contDiff_const.prodMk contDiff_id)).continuous
  have hbk : ∀ t ∈ Icc (ocEll q Λ m ν ^ 2 * a) (ocEll q Λ m ν ^ 2 * b),
      Continuous (fun x => streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) := fun t _ =>
    (hcont m hΨ t).sub (hcont (m - 1) hφs t)
  -- on the window no other odd pulse is active
  have hwb : ∀ t ∈ Icc (ocEll q Λ m ν ^ 2 * a) (ocEll q Λ m ν ^ 2 * b), ∀ x,
      (jacMatrix (ocChart α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp) t)
        (ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp) t x)).mulVec
        (pulseCellDriftUnit α q Λ ζ m ν kp ((ocEll q Λ m ν ^ 2)⁻¹ * t)
          ((ocEpsilon q Λ m)⁻¹ •
            ocChartInv α q Λ m (Φ (m - 1)) hφs (ocPulseChartIndex α q Λ m kp) t x)) =
        streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x := fun t ht x =>
    pulse_drift_physical hseqΦ hm hφs ν hkp hkl he hℓ
      (fun k' hk' hne => Diagonal.ocPulse_eq_zero_of_mem_window hΛ hζ hkp hk' hne (hwin ht)) x
  refine (setting_pulse_weak P sX sZ hsX hsZ Cc hseq (ocDStar q Λ m ν B / ρ) cf dcf φ hφ hφp
    α q Λ m hφs (ocPulseChartIndex α q Λ m kp) hc hρ A₀ B₀ hA hB₀ hcf
    (pulse_G_differentiable α q Λ m ζ hφs ν B ρ lam kp edge)
    (pulseCellDriftUnit α q Λ ζ m ν kp)
    (pulse_v_factor α q Λ m ζ hφs ν B ρ lam kp edge)
    (pulse_scale_h1 hν he) (pulse_scale_h2 α q Λ m ζ hφs hν hB he ρ lam kp edge)
    (pulse_scale_h3 α q Λ m ζ hφs hν hB ρ lam kp edge) rfl M hM
    (pulse_G_slow_invariant α q Λ m ζ hφs ν B hρ.ne' lam kp edge) hcs
    (fun t _ y => pulse_G_chart α q Λ m ζ hφs ν B hρ.ne' lam kp edge hℓ t y)
    (fun t x => streamVel (Φ m) t x - streamVel (Φ (m - 1)) t x) hbk hwb v φt hφt
    hφtp).congr (mul_le_mul_of_nonneg_left P.window hc.le) (fun t _ => rfl) (fun t _ => ?_)
  simp only [Pi.sub_apply, sub_add_cancel]

end AVRegularity.CycleComparison.Reconstruction
end
