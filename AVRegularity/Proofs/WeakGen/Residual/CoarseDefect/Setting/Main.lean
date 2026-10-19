-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.CycleComparison.Coarse.SecondOrderResponse
public import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.FluxJets
import AVRegularity.Proofs.WeakGen.Residual.CoarseDefect.InitialValueProof
import AVRegularity.Proofs.WeakGen.Comparison.RowsHigh
import AVRegularity.Proofs.WeakGen.Residual.CoarseEnergy.ReadoutNamed
public import AVRegularity.Proofs.WeakGen.Residual.CoarseEnergy.PartBTransfer
import AVRegularity.Applications.Global.CompactRangeMain

section
@[expose] public noncomputable section

section
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **Powers of a nonnegative matrix**: a chain of entries at least `1` gives an entry
of the power at least `1`, and a matrix that lowers a bounded rank is nilpotent. -/

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem csPow_nonneg (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (n : ℕ) (v u : ι) :
    0 ≤ (A ^ n) v u := by
  induction n generalizing v u with
  | zero => rw [pow_zero, Matrix.one_apply]; split_ifs <;> norm_num
  | succ n ih =>
    rw [pow_succ', Matrix.mul_apply]
    exact Finset.sum_nonneg fun x _ => mul_nonneg (hA _ _) (ih _ _)

theorem csPow_succ_ge_one (A : Matrix ι ι ℝ) (hA : ∀ v u, 0 ≤ A v u) (n : ℕ) (x y z : ι)
    (h1 : 1 ≤ A x y) (h2 : 1 ≤ (A ^ n) y z) : 1 ≤ (A ^ (n + 1)) x z := by
  rw [pow_succ', Matrix.mul_apply]
  calc (1 : ℝ) = 1 * 1 := by norm_num
    _ ≤ A x y * (A ^ n) y z := mul_le_mul h1 h2 zero_le_one ((zero_le_one).trans h1)
    _ ≤ _ := Finset.single_le_sum (f := fun w => A x w * (A ^ n) w z)
        (fun w _ => mul_nonneg (hA _ _) (csPow_nonneg A hA n _ _)) (Finset.mem_univ y)

/-- A matrix whose nonzero entries lower a rank bounded by `H` has `A ^ (H + 1) = 0`. -/
theorem csPow_eq_zero_of_rank (A : Matrix ι ι ℝ) (rk : ι → ℕ) (H : ℕ) (hrk : ∀ v, rk v ≤ H)
    (hedge : ∀ v u, A v u ≠ 0 → rk u < rk v) : A ^ (H + 1) = 0 := by
  have key : ∀ n v u, (A ^ n) v u ≠ 0 → rk u + n ≤ rk v := by
    intro n
    induction n with
    | zero =>
      intro v u h
      rw [pow_zero, Matrix.one_apply] at h
      by_cases hvu : v = u
      · subst hvu; simp
      · simp [hvu] at h
    | succ n ih =>
      intro v u h
      rw [pow_succ', Matrix.mul_apply] at h
      obtain ⟨x, -, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
      have h1 := hedge _ _ (left_ne_zero_of_mul hx)
      have h2 := ih _ _ (right_ne_zero_of_mul hx)
      omega
  ext v u
  by_contra hne
  have := key (H + 1) v u hne
  have := hrk v
  omega

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **Closure of the regularity of a coefficient family**.

`CsGood ρ N t₀ t₁ f` collects the four regularity fields of `IsCoarseSetting` for a coefficient
family `f` (measurable, `C^N`, periodic, finite seminorm). The family is closed under zero, finite
sums, constant multiples and dependent choices; the stored coefficients of a passage stage are
`CsGood` at every order (`CoeffRegular`), hence so are `cdAD` and `cdCE`. -/

variable {k : ℕ}

/-- The operator space of a coefficient of order `k`. -/
abbrev CsOp (k : ℕ) : Type :=
  PiLp 2 (fun _ : DerivativeWord2 k => ℝ) →L[ℝ] PiLp 2 (fun _ : Fin 2 => ℝ)

/-- The regularity fields of a coefficient family in `IsCoarseSetting`. -/
structure CsGood (ρ : ℝ) (N : ℕ) (t₀ t₁ : ℝ) (f : ℝ → Vec 2 → CsOp k) : Prop where
  meas : Measurable fun q : Set.Icc t₀ t₁ × Vec 2 => f q.1 q.2
  smooth : ∀ t ∈ Set.Icc t₀ t₁, ContDiff ℝ (N : ℕ) (f t)
  per : ∀ t ∈ Set.Icc t₀ t₁, IsZ2Periodic (f t)
  fin : coefficientSeminorm ρ N t₀ t₁ f ≠ ⊤

theorem CsGood.zero (ρ : ℝ) (N : ℕ) (t₀ t₁ : ℝ) :
    CsGood ρ N t₀ t₁ (fun (_ : ℝ) (_ : Vec 2) => (0 : CsOp k)) :=
  ⟨measurable_const, fun _ _ => contDiff_const, fun _ _ _ _ => rfl, by
    rw [CycleComparison.Coarse.coefficientSeminorm_const_zero]; exact ENNReal.zero_ne_top⟩

theorem CsGood.sum {ι : Type*} {ρ : ℝ} {N : ℕ} {t₀ t₁ : ℝ} (S : Finset ι)
    (f : ι → ℝ → Vec 2 → CsOp k) (h : ∀ j ∈ S, CsGood ρ N t₀ t₁ (f j)) :
    CsGood ρ N t₀ t₁ (fun t x => ∑ j ∈ S, f j t x) := by
  refine ⟨?_, fun t ht => ContDiff.sum fun j hj => (h j hj).smooth t ht,
    fun t ht n x => Finset.sum_congr rfl fun j hj => (h j hj).per t ht n x, ?_⟩
  · exact Finset.measurable_sum S fun j hj => (h j hj).meas
  · exact CycleJointProofs.coefficientSeminorm_sum_ne_top S f ρ N t₀ t₁
      (fun j hj t ht => (h j hj).smooth t ht) fun j hj => (h j hj).fin

/-- A constant multiple has at most the seminorm times the modulus. -/
theorem cs_seminorm_smul_le (c : ℝ) (ρ : ℝ) (N : ℕ) (t₀ t₁ : ℝ) (f : ℝ → Vec 2 → CsOp k) :
    coefficientSeminorm ρ N t₀ t₁ (fun t x => c • f t x) ≤
      ENNReal.ofReal |c| * coefficientSeminorm ρ N t₀ t₁ f := by
  unfold coefficientSeminorm
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun j _ => ?_
  rw [mul_left_comm]
  refine mul_le_mul_right ?_ _
  refine iSup₂_le fun t ht => iSup_le fun x => ?_
  have h1 : (‖coefficientDerivativeArray (fun y => c • f t y) j x‖₊ : ℝ≥0∞) =
      ENNReal.ofReal |c| * (‖coefficientDerivativeArray (f t) j x‖₊ : ℝ≥0∞) := by
    rw [CycleJointProofs.coefficientDerivativeArray_const_smul, nnnorm_smul, ENNReal.coe_mul,
      ← Real.norm_eq_abs, ofReal_norm]
    rfl
  rw [h1]
  refine mul_le_mul_right ?_ _
  exact le_iSup₂_of_le t ht (le_iSup (fun y : Vec 2 =>
    (‖coefficientDerivativeArray (f t) j y‖₊ : ℝ≥0∞)) x)

theorem CsGood.smul {ρ : ℝ} {N : ℕ} {t₀ t₁ : ℝ} (c : ℝ) {f : ℝ → Vec 2 → CsOp k}
    (h : CsGood ρ N t₀ t₁ f) : CsGood ρ N t₀ t₁ (fun t x => c • f t x) := by
  refine ⟨?_, fun t ht => (h.smooth t ht).const_smul c, fun t ht n x => ?_, ?_⟩
  · exact h.meas.const_smul c
  · simp only [h.per t ht n x]
  · exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top h.fin)
      (cs_seminorm_smul_le c ρ N t₀ t₁ f)

theorem CsGood.dite {ρ : ℝ} {N : ℕ} {t₀ t₁ : ℝ} (P : Prop) [Decidable P]
    (f : P → ℝ → Vec 2 → CsOp k) (h : ∀ hp, CsGood ρ N t₀ t₁ (f hp)) :
    CsGood ρ N t₀ t₁ (fun t x => if hp : P then f hp t x else 0) := by
  by_cases hP : P
  · simp only [hP, dite_true]; exact h hP
  · simp only [hP, dite_false]; exact CsGood.zero ρ N t₀ t₁

theorem CsGood.ite {ρ : ℝ} {N : ℕ} {t₀ t₁ : ℝ} (P : Prop) [Decidable P]
    (f : ℝ → Vec 2 → CsOp k) (h : P → CsGood ρ N t₀ t₁ f) :
    CsGood ρ N t₀ t₁ (fun t x => if P then f t x else 0) := by
  by_cases hP : P
  · simp only [hP, ite_true]; exact h hP
  · simp only [hP, ite_false]; exact CsGood.zero ρ N t₀ t₁

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The coarse setting of the weak window** (the statement).

For a passage `M < i ≤ M + J_w` of an instance `c` the premises `IsCoarseSetting` of the coarse
defect equation hold on the window `[t_i, a + T₀]` at the radius `ρ_c = ρ ε_{i-1}` (`ρ` the radius
of the plan), the diffusivity `κ_M`, the drift `streamVel Φ_{i-1}`, the flux `Jm = κ_M I`, the
cap `D_c = N_w + (1 + J_wN_w)`, the grade bound `H = J_wR_w`, `p = 1`, `J = 0`, the data `cdAD`,
`cdCE` and the weak masses.

The statement is QUALITATIVE: the constants `a_C, B₀_C, lam_C, 𝖠, C_*, Θ_c` are existentials AFTER
the instance, because the bill of the window (`reconBillConst`) does not read them; every bound
on them is a finiteness statement. The only inequalities that tie the radius to the data are the
two drift inequalities, which the high-reserve energy statement already uses at the same radius (`weakCoarse_passage_drift`).
The edge matrix is the 0/1 matrix of the identities of the stage `i`; it is acyclic by the rank
and `C_*` is a maximum of finitely many finite seminorm sums.

Special cases: at the root `i = M + J_w` the stage has no identity, `cdCE = 0`, `𝖠 = 0`;
`k_c = 0` gives `N = (H + 3)L`; `r > H` is not asked. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

/-- **The coarse setting of the weak window.** -/
def WeakCoarseSettingStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps) (kc : ℕ),
    r.tq i ≤ r.a + A.T₀ →
    ∃ (aC B₀C lamC : ℝ) (Aedge : Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ)
      (Cstar Θc : ℝ),
      IsCoarseSetting (r.tq i) (r.a + A.T₀) (plan.radius R * c.D.eps (i - 1)) (c.D.κ c.M)
        aC B₀C lamC (streamVel (c.D.Φ (i - 1))) (A.Nw + (1 + A.Jw * A.Nw)) (A.Jw * A.Rw) 1 0 kc
        ((A.Nw + (1 + A.Jw * A.Nw)) + 8 * 1 + 4)
        (kc + (0 + A.Jw * A.Rw + 3) * ((A.Nw + (1 + A.Jw * A.Nw)) + 8 * 1 + 4))
        (fun _ => c.D.κ c.M • (1 : Matrix (Fin 2) (Fin 2) ℝ))
        (cdAD c (A.Nw + (1 + A.Jw * A.Nw)) i v₀)
        (cdCE c (A.Nw + (1 + A.Jw * A.Nw)) i hi hit)
        (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) Aedge Cstar Θc

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The regularity fields for the letters `cdAD`, `cdCE`**.

The stored coefficients of the stage `i - 1` are measurable, `C^n`, periodic with finite
seminorms at the radii `≤ ε_{i-2}` (`weakPassage_coeffRegular`); the letters are finite sums of
them, so `CsGood` at every order and every radius `0 < ρ ≤ ε_{i-2}`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

/-- A stored coefficient of the stage `i - 1` is `CsGood`. -/
theorem cd_physCoeff_good (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v u : CompIn (c.stage (i - 1)).comps)
    (γ : (c.stage (i - 1)).fam.Γ v u) (d N : ℕ) (t₀ t₁ ρ : ℝ) (hρ : 0 < ρ)
    (hρe : ρ ≤ c.D.eps (i - 1 - 1)) :
    CsGood ρ N t₀ t₁ ((c.stage (i - 1)).physCoeff v u γ d) := by
  obtain ⟨hm, hcd, hper, hfin⟩ := weakPassage_coeffRegular hcommon c (i - 1)
    (by show c.M ≤ i - 1; omega) (by show i - 1 < c.M + A.Jw; omega) v u γ N d t₀ t₁
  exact ⟨hm, fun t _ => hcd t, fun t _ => hper t, hfin ρ hρ hρe⟩

/-- `cdAD` is `CsGood`. -/
theorem cdAD_good (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (Dc i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (v₀ : CompIn (c.stage i).comps)
    (d : Finset.Icc 2 Dc) (N : ℕ) (t₀ t₁ ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ c.D.eps (i - 1 - 1)) :
    CsGood ρ N t₀ t₁ (cdAD c Dc i v₀ d) := by
  classical
  unfold cdAD
  refine CsGood.sum _ _ fun n _ => CsGood.dite _ _ fun hh => CsGood.sum _ _ fun γ _ => ?_
  exact (cd_physCoeff_good hcommon c i hi hit _ _ γ d.1 N t₀ t₁ ρ hρ hρe).smul _

/-- `cdCE` is `CsGood`. -/
theorem cdCE_good (hcommon : WeakPassageCommonOK plan) (c : WeakPassageInstance plan R)
    (Dc i : ℕ) (hi : c.M < i) (hit : i ≤ c.M + A.Jw) (r : ℕ) (v u : CompIn (c.stage i).comps)
    (d : Finset.Icc 2 Dc) (N : ℕ) (t₀ t₁ ρ : ℝ) (hρ : 0 < ρ) (hρe : ρ ≤ c.D.eps (i - 1 - 1)) :
    CsGood ρ N t₀ t₁ (cdCE c Dc i hi hit r v u d) := by
  classical
  unfold cdCE
  refine CsGood.dite _ _ fun hh => CsGood.sum _ _ fun γ _ => CsGood.ite _ _ fun _ => ?_
  exact cd_physCoeff_good hcommon c i hi hit _ _ γ d.1 N t₀ t₁ ρ hρ hρe
end

/-! **The edge matrix of the stage `i`**: the 0/1 matrix of its identities, acyclic by
the rank, and a stage path of length `h` gives an entry of the `h`-th power at least `1`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  EntryWeakProofs AVRegularity.Providers.WeakGen.Comparison

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

open scoped Classical in
/-- The 0/1 matrix of the identities `u → v` of the stage `i`. -/
def cdAedge (c : WeakPassageInstance plan R) (i : ℕ) :
    Matrix (CompIn (c.stage i).comps) (CompIn (c.stage i).comps) ℝ :=
  fun v u => if Nonempty ((c.stage i).fam.Γ v u) then 1 else 0

theorem cdAedge_nonneg (c : WeakPassageInstance plan R) (i : ℕ) (v u) : 0 ≤ cdAedge c i v u := by
  unfold cdAedge; split_ifs <;> norm_num

theorem cdAedge_le_one (c : WeakPassageInstance plan R) (i : ℕ) (v u) : cdAedge c i v u ≤ 1 := by
  unfold cdAedge; split_ifs <;> norm_num

theorem cdAedge_acyclic (c : WeakPassageInstance plan R) (i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) : cdAedge c i ^ (A.Jw * A.Rw + 1) = 0 := by
  refine csPow_eq_zero_of_rank _ (fun v => weakComponentRank v.1) (A.Jw * A.Rw) ?_ ?_
  · intro v
    have h := ((weakConstruction_rank_bounds c.P _ c.M A.Jw 0 _ c.stage c.construction i hi.le
      hit).1 v.1 v.2)
    exact h.trans (Nat.mul_le_mul_right A.Rw (by omega))
  · intro v u h
    have hne : Nonempty ((c.stage i).fam.Γ v u) := by
      by_contra hn
      simp [cdAedge, hn] at h
    exact weakComparison_edge_rank c i hi hit v u hne

theorem cdAedge_path (c : WeakPassageInstance plan R) (i : ℕ) {h : ℕ}
    (π : StagePath (c.stage i) h) (n : ℕ) (hn : 1 ≤ n) (hnh : n ≤ h) :
    1 ≤ (cdAedge c i ^ n) (π.step ⟨n - 1, by omega⟩).1 (π.step ⟨0, by omega⟩).2.1 := by
  have hA := cdAedge_nonneg c i
  revert hnh
  induction n, hn using Nat.le_induction with
  | base =>
    intro hnh
    rw [pow_one]
    have : Nonempty ((c.stage i).fam.Γ (π.step ⟨1 - 1, by omega⟩).1 (π.step ⟨0, by omega⟩).2.1) :=
      ⟨(π.step ⟨0, by omega⟩).2.2⟩
    simp [cdAedge, this]
  | succ n hn ih =>
    intro hnh
    have ih := ih (by omega)
    have hj := π.joined (n - 1) (by omega)
    have hn1 : n - 1 + 1 = n := by omega
    have h2 : (⟨n, by omega⟩ : Fin h) = ⟨n - 1 + 1, by omega⟩ := Fin.ext hn1.symm
    have e' : (π.step ⟨n, by omega⟩).2.1 = (π.step ⟨n - 1, by omega⟩).1 := by
      rw [h2]; exact hj
    refine csPow_succ_ge_one _ hA n _ (π.step ⟨n, by omega⟩).2.1 _ ?_ ?_
    · have h3 : (⟨n + 1 - 1, by omega⟩ : Fin h) = ⟨n, by omega⟩ := Fin.ext (by simp)
      rw [h3]
      have : Nonempty ((c.stage i).fam.Γ (π.step ⟨n, by omega⟩).1
          (π.step ⟨n, by omega⟩).2.1) := ⟨(π.step ⟨n, by omega⟩).2.2⟩
      simp [cdAedge, this]
    · rw [e']; exact ih
end

/-! **The supports of the grade-`r` letters**: `cdCE r v u = 0` unless the `r`-th power
of the edge matrix of the stage `i` is at least `1` at `(v, u)`. -/

section
open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  EntryWeakProofs AVRegularity.Providers.WeakGen.Comparison AVRegularity.Providers.WeakGen.Residual

variable {plan : WeakPassagePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A}

theorem cdCE_eq_zero_of_pow (c : WeakPassageInstance plan R) (Dc i : ℕ) (hi : c.M < i)
    (hit : i ≤ c.M + A.Jw) (r : ℕ) (v u : CompIn (c.stage i).comps)
    (h : ¬ 1 ≤ (cdAedge c i ^ r) v u) (d : Finset.Icc 2 Dc) (s : ℝ) (x : Vec 2) :
    cdCE c Dc i hi hit r v u d s x = 0 := by
  classical
  unfold cdCE
  split_ifs with hh
  · refine Finset.sum_eq_zero fun γ _ => ?_
    rw [ite_eq_right_iff]
    intro hg
    exfalso
    obtain ⟨hlev, hb⟩ := cd_stage_inv c i hi hit
    generalize hs : (cdEdgeSource c i hi hit ⟨v.1, hh.1⟩ ⟨u.1, hh.2⟩ γ).1 = s' at hg
    cases s' with
    | eddy a w n => exact hg
    | inherited w h' π n =>
      have hg' : h' = r := hg
      subst hg'
      obtain ⟨q1, q2, q3, q4, -, -, -, q5, -⟩ := cd_inh_facts c i hi hit γ hs
      have hu0 : compWord i u.1 = [] := compWord_nil_of_old i (by omega) u.1 (hb _ u.2)
      have hv0 : compWord i v.1 = [] := compWord_nil_of_old i (by omega) v.1 (hb _ v.2)
      have e1 : π.src = u.1 := by
        rw [← q1]; exact compParent_eq_of_compWord_nil i _ hu0
      have e2 : π.tgt = v.1 := by
        rw [← q3]; exact compParent_eq_of_compWord_nil i _ hv0
      have hp := cdAedge_path c i π h' q5 le_rfl
      have e3 : (π.step ⟨h' - 1, by omega⟩).1 = v := by
        apply Subtype.ext
        rw [← e2]; simp only [StagePath.tgt, show 0 < h' by omega, ↓reduceDIte]
      have e4 : (π.step ⟨0, by omega⟩).2.1 = u := by
        apply Subtype.ext
        rw [← e1]; simp only [StagePath.src, show 0 < h' by omega, ↓reduceDIte]
      rw [e3, e4] at hp
      exact h hp
  · rfl
end

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.Providers.WeakGen.Residual.CoarseDefect

/-! **The coarse setting of the weak window, proved**. The drift fields are
`weakCoarse_passage_drift`, the letters are `CsGood`, the edge matrix is `cdAedge`, and `C_*` is one
plus the sum of the finitely many finite sums in `edge_mean`. -/

open WeakEntryProofs WeakEntryProofs.Assembly AVRegularity.Providers.WeakGen.Reduction
  EntryWeakProofs AVRegularity.Providers.WeakGen.Comparison AVRegularity.Providers.WeakGen.Residual

/-- **The coarse setting of the weak window.** -/
theorem weakCoarseSetting (plan : WeakPassagePlan) (hcommon : WeakPassageCommonOK plan)
    (hok : WeakCoarsePlanOK plan) : WeakCoarseSettingStatement plan := by
  classical
  intro B A R c r i hi hit v₀ kc hwin
  have hfl := hok.1
  have hrad1 : plan.radius R ≤ 1 := (hfl.1 R).trans (by norm_num)
  have hM1 : 1 ≤ c.M := by have := weakPassage_two_le_M hcommon c; omega
  have hd := weakCoarse_passage_drift hfl c hM1 (i - 1) (by omega) (r.tq i) (r.a + A.T₀)
    (kc + (0 + A.Jw * A.Rw + 3) * ((A.Nw + (1 + A.Jw * A.Nw)) + 8 * 1 + 4))
  obtain ⟨aC, B₀C, lamC, haC, hB₀, hlam, hjets, hscale, hsmall⟩ := hd.jets
  obtain ⟨hρpos, -⟩ := weakComparison_rowRadius c (i - 1) hrad1
  obtain ⟨hDΛ, hq, -, -⟩ := weakPassageInstance_base c
  have hεL : 0 < c.D.eps (i - 1) := by
    by_contra hn
    have := mul_nonpos_of_nonneg_of_nonpos (plan.radius_pos R).le (not_lt.1 hn)
    linarith
  have hρe : plan.radius R * c.D.eps (i - 1) ≤ c.D.eps (i - 1 - 1) :=
    (mul_le_of_le_one_left hεL.le hrad1).trans
      (Applications.eps_antitone hq hDΛ (Nat.sub_le (i - 1) 1))
  have hκ : 0 < c.D.κ c.M := (weakPassageRawSetting c).kappa_pos
  set ρ := plan.radius R * c.D.eps (i - 1) with hρdef
  set Dc := A.Nw + (1 + A.Jw * A.Nw) with hDc
  set N := kc + (0 + A.Jw * A.Rw + 3) * ((A.Nw + (1 + A.Jw * A.Nw)) + 8 * 1 + 4) with hN
  have hADg := fun d => cdAD_good hcommon c Dc i hi hit v₀ d N (r.tq i) (r.a + A.T₀) ρ hρpos hρe
  have hCEg := fun r' v u d => cdCE_good hcommon c Dc i hi hit r' v u d N (r.tq i) (r.a + A.T₀) ρ
    hρpos hρe
  -- the left sides of `edge_mean`
  let lhs : ℕ → CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ≥0∞ := fun r' v u =>
    ENNReal.ofReal (Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ u.1 / weakMass c.D A.Nw A.Jw A.η₀ v.1)) *
      ∑ d : Finset.Icc 2 Dc, coefficientSeminorm ρ N (r.tq i) (r.a + A.T₀)
          (cdCE c Dc i hi hit r' v u d) * (ENNReal.ofReal (c.D.κ c.M * ρ ^ (d.1 - 2)))⁻¹
  have hlhs : ∀ r' v u, lhs r' v u ≠ ⊤ := by
    intro r' v u
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.sum_ne_top.2 fun d _ => ?_)
    refine ENNReal.mul_ne_top (hCEg r' v u d).fin (ENNReal.inv_ne_top.2 ?_)
    exact (ENNReal.ofReal_pos.2 (mul_pos hκ (pow_pos hρpos _))).ne'
  set Cstar : ℝ := 1 + ∑ r' ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ v, ∑ u, (lhs r' v u).toReal with hCs
  have hCs1 : 1 ≤ Cstar := by
    have : 0 ≤ ∑ r' ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ v, ∑ u, (lhs r' v u).toReal :=
      Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
        ENNReal.toReal_nonneg
    linarith
  refine ⟨aC, B₀C, lamC, cdAedge c i, Cstar, (Fintype.card (CompIn (c.stage i).comps) : ℝ), ?_⟩
  refine
    { window := hwin
      rho_pos := hρpos
      B_pos := hκ
      D_ge := by have := A.Nw_pos; omega
      p_pos := le_rfl
      L_eq := rfl
      N_eq := rfl
      mass_pos := fun v => PartB.partB_mass_pos c v.1
      drift_bdd := hd.bdd
      drift_meas := hd.meas
      drift_smooth := hd.smooth
      drift_div := hd.div
      drift_per := hd.per
      a_nonneg := haC
      B₀_ge := hB₀
      lam_pos := hlam
      drift_jets := hjets
      drift_scale := hscale
      drift_small := hsmall
      J_symm := ?_
      J_meas := fun _ _ => measurable_const
      J_bdd := ?_
      cov_small := ?_
      AD_meas := fun d => (hADg d).meas
      AD_smooth := fun d => (hADg d).smooth
      AD_per := fun d => (hADg d).per
      AD_fin := fun d => (hADg d).fin
      CE_meas := fun r' _ v u d => (hCEg r' v u d).meas
      CE_smooth := fun r' _ v u d => (hCEg r' v u d).smooth
      CE_per := fun r' _ v u d => (hCEg r' v u d).per
      CE_fin := fun r' _ v u d => (hCEg r' v u d).fin
      edge_nonneg := cdAedge_nonneg c i
      edge_row := fun v => ?_
      edge_col := fun u => ?_
      edge_acyclic := cdAedge_acyclic c i hi hit
      edge_mean := ?_ }
  · intro t a b
    simp [Matrix.smul_apply, Matrix.one_apply, eq_comm]
  · simp [matrixSupNorm]
  · simp [matrixSupNorm, covarianceMatrix]
  · calc ∑ u, cdAedge c i v u ≤ ∑ _u : CompIn (c.stage i).comps, (1 : ℝ) :=
        Finset.sum_le_sum fun u _ => cdAedge_le_one c i v u
      _ = _ := by simp
  · calc ∑ v, cdAedge c i v u ≤ ∑ _v : CompIn (c.stage i).comps, (1 : ℝ) :=
        Finset.sum_le_sum fun v _ => cdAedge_le_one c i v u
      _ = _ := by simp
  · intro r' hr' v u
    by_cases hp : 1 ≤ (cdAedge c i ^ r') v u
    · have hle : (lhs r' v u).toReal ≤ Cstar := by
        have h1 : (lhs r' v u).toReal ≤ ∑ r' ∈ Finset.Icc 1 (A.Jw * A.Rw), ∑ v, ∑ u,
            (lhs r' v u).toReal :=
          (Finset.single_le_sum (f := fun u => (lhs r' v u).toReal)
            (fun _ _ => ENNReal.toReal_nonneg) (Finset.mem_univ u)).trans
          ((Finset.single_le_sum (f := fun v => ∑ u, (lhs r' v u).toReal)
            (fun _ _ => Finset.sum_nonneg fun _ _ => ENNReal.toReal_nonneg)
            (Finset.mem_univ v)).trans
          (Finset.single_le_sum
            (f := fun r' => ∑ v, ∑ u, (lhs r' v u).toReal)
            (fun _ _ => Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ =>
              ENNReal.toReal_nonneg) hr'))
        linarith
      have hr1 : r' ≠ 0 := by have := (Finset.mem_Icc.1 hr').1; omega
      have hpow : Cstar ≤ Cstar ^ r' := le_self_pow₀ hCs1 hr1
      have hCp : 0 ≤ Cstar ^ r' := by positivity
      calc lhs r' v u = ENNReal.ofReal (lhs r' v u).toReal := (ENNReal.ofReal_toReal (hlhs r' v u)).symm
        _ ≤ ENNReal.ofReal (Cstar ^ r' * (cdAedge c i ^ r') v u) := by
          refine ENNReal.ofReal_le_ofReal ?_
          nlinarith
    · have hz : ∀ d : Finset.Icc 2 Dc, cdCE c Dc i hi hit r' v u d = fun _ _ => 0 := fun d => by
        funext s x
        exact cdCE_eq_zero_of_pow c Dc i hi hit r' v u hp d s x
      have : lhs r' v u = 0 := by
        simp only [lhs, hz, CycleComparison.Coarse.coefficientSeminorm_const_zero, zero_mul,
          Finset.sum_const_zero, mul_zero]
      exact this.trans_le zero_le

end AVRegularity.Providers.WeakGen.Residual.CoarseDefect
end
end
end
