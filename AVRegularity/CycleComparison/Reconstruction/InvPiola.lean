-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Statements.Intermediate.CycleOutput.IsLiftPartition
public import AVRegularity.Statements.Intermediate.CycleOutput.OcObsPulses
public import AVRegularity.Statements.Intermediate.CycleJoint.OcQuietTimes
import AVRegularity.CycleComparison.LiftSetting.Metric
import AVRegularity.CycleComparison.Reconstruction.Tested
import AVRegularity.CycleComparison.Reconstruction.Orders
public import AVRegularity.Statements.Intermediate.CycleJoint.EdgeCoefficient
public import AVRegularity.Statements.Intermediate.Families.FamilyEdges
public import AVRegularity.Statements.Intermediate.CycleOutput.LiftEdges
public import AVRegularity.Statements.Intermediate.Families.ChartedFiber
import AVRegularity.CycleComparison.Charts.ChartDeviation
import AVRegularity.CycleComparison.Residual.LiftStatements
public import AVRegularity.CycleComparison.Residual.CoarseFluxDiff.SlowJet
public import AVRegularity.CycleComparison.Reconstruction.GlueWeight
public import AVRegularity.Statements.Construction.IsFastProfile
public import AVRegularity.Statements.Intermediate.CycleReference.JacMatrix
import AVRegularity.CycleComparison.Residual.Antidivergence.Main
import Mathlib.Combinatorics.SimpleGraph.Basic

section
@[expose] public section
open Homogenization AVenhance Set
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The active pieces at a weighted time**.
Two distinct odd pulse windows `[(k ∓ 61/48)τ]` meet only in a quiet gap, where every pulse
vanishes (`mem_ocQuietTimes_of_two_windows`), and no three of them meet
(`not_mem_three_windows`). If the lift partition is the family partition read on the observed
pulses, `ϖ_k = F.weight (pp k)`, then at a time `t` of the window with `ϖ_k(t) ≠ 0` either the
piece `pp k` alone carries all the weight, or exactly one other observed pulse `j` is weighted,
`t` is quiet and lies in both windows, and the weights of `pp k`, `pp j` sum to one
(`active_pieces`). -/

section Family

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- Pieces outside a finite set of pieces whose weights already sum to one carry no weight at a
covered time. -/
theorem weight_eq_zero_of_sum (F : ChartedFamily ι h D P Ctx) (S : Finset P) {t : ℝ}
    (hcov : ∃ p, t ∈ (F.piece p).output) (hS : ∑ p ∈ S, F.weight p t = 1) {p : P}
    (hp : p ∉ S) : F.weight p t = 0 := by
  classical
  have hfin : (Function.support fun p' => F.weight p' t).Finite := by
    refine (F.locally_finite t t).subset fun p' hp' => ?_
    by_contra hno
    exact hp' (F.weight_zero p' t fun ht => hno ⟨t, ht, le_rfl, le_rfl⟩)
  set T : Finset P := hfin.toFinset ∪ S ∪ {p} with hT
  have hsub : (Function.support fun p' => F.weight p' t) ⊆ ↑T := fun p' hp' =>
    Finset.mem_coe.2 (Finset.mem_union_left _ (Finset.mem_union_left _ (hfin.mem_toFinset.2 hp')))
  have hST : S ⊆ T := fun p' hp' => Finset.mem_union_left _ (Finset.mem_union_right _ hp')
  have h1 := F.weight_sum t hcov
  rw [finsum_eq_sum_of_support_subset _ hsub, ← Finset.sum_sdiff hST, hS] at h1
  have h0 : ∑ p' ∈ T \ S, F.weight p' t = 0 := by linarith
  have hpT : p ∈ T \ S :=
    Finset.mem_sdiff.2 ⟨Finset.mem_union_right _ (Finset.mem_singleton_self p), hp⟩
  exact (Finset.sum_eq_zero_iff_of_nonneg (fun p' _ => F.weight_nonneg p' t)).1 h0 p hpT

end Family

section Geometry

variable {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}

/-- Every odd pulse vanishes at a common point of two windows `j < k`. -/
theorem ocPulse_eq_zero_of_two_windows_lt (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {j k : ℤ}
    (hj : Odd j) (hk : Odd k) (hlt : j < k) {t : ℝ} (htj : t ∈ ocPulseWindow α q Λ m j)
    (htk : t ∈ ocPulseWindow α q Λ m k) {k' : ℤ} (hk' : Odd k') : ocPulse α q Λ ζ m k' t = 0 := by
  by_contra hp
  obtain ⟨h1, h2⟩ := CycleReference.pulse_nonzero_center_distance hΛ hζ hp
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  have hk2 : j + 2 ≤ k := by
    obtain ⟨a, ha⟩ := hj
    obtain ⟨b, hb⟩ := hk
    omega
  have hjk : ((j : ℝ) + 2) ≤ (k : ℝ) := by exact_mod_cast hk2
  have hsplit : k' ≤ j ∨ j + 2 ≤ k' := by
    obtain ⟨a, ha⟩ := hj
    obtain ⟨c, hc⟩ := hk'
    omega
  have htj' : ((j : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t ∧ t ≤ ((j : ℝ) + 61 / 48) * ocTau α q Λ m :=
    htj
  have htk' : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t ∧ t ≤ ((k : ℝ) + 61 / 48) * ocTau α q Λ m :=
    htk
  rcases hsplit with hle | hge
  · have hle' : (k' : ℝ) ≤ j := by exact_mod_cast hle
    have e1 : ((j : ℝ) + 2 - 61 / 48) * ocTau α q Λ m ≤ ((k : ℝ) - 61 / 48) * ocTau α q Λ m :=
      mul_le_mul_of_nonneg_right (by linarith) hτ.le
    have e2 : (k' : ℝ) * ocTau α q Λ m ≤ (j : ℝ) * ocTau α q Λ m :=
      mul_le_mul_of_nonneg_right hle' hτ.le
    nlinarith
  · have hge' : (j : ℝ) + 2 ≤ k' := by exact_mod_cast hge
    have e2 : ((j : ℝ) + 2) * ocTau α q Λ m ≤ (k' : ℝ) * ocTau α q Λ m :=
      mul_le_mul_of_nonneg_right hge' hτ.le
    nlinarith

/-- Every odd pulse vanishes at a common point of two distinct odd windows. -/
theorem ocPulse_eq_zero_of_two_windows (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {j k : ℤ}
    (hj : Odd j) (hk : Odd k) (hjk : j ≠ k) {t : ℝ} (htj : t ∈ ocPulseWindow α q Λ m j)
    (htk : t ∈ ocPulseWindow α q Λ m k) {k' : ℤ} (hk' : Odd k') : ocPulse α q Λ ζ m k' t = 0 := by
  rcases lt_or_gt_of_ne hjk with hlt | hgt
  · exact ocPulse_eq_zero_of_two_windows_lt hΛ hζ hj hk hlt htj htk hk'
  · exact ocPulse_eq_zero_of_two_windows_lt hΛ hζ hk hj hgt htk htj hk'

/-- **A common point of two distinct odd windows is quiet.** -/
theorem mem_ocQuietTimes_of_two_windows (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) {j k : ℤ}
    (hj : Odd j) (hk : Odd k) (hjk : j ≠ k) {t : ℝ} (htj : t ∈ ocPulseWindow α q Λ m j)
    (htk : t ∈ ocPulseWindow α q Λ m k) : t ∈ ocQuietTimes α q Λ ζ m := by
  have hz : ocPulseStream α q Λ ζ m t = fun _ => 0 := funext fun y => by
    unfold ocPulseStream
    refine (tsum_congr fun k' => ?_).trans tsum_zero
    rw [ocPulse_eq_zero_of_two_windows hΛ hζ hj hk hjk htj htk k'.2, zero_mul]
  intro y
  have hg : spaceGrad (fun _ : Vec 2 => (0 : ℝ)) y = 0 := by
    funext i
    simp [spaceGrad]
  show sigmaMat.mulVec (spaceGrad (ocPulseStream α q Λ ζ m t) y) = 0
  rw [hz, hg, Matrix.mulVec_zero]

/-- Odd windows four apart are disjoint. -/
theorem not_mem_two_windows_far (hΛ : 1 ≤ Λ) {j k : ℤ} (hjk : j + 4 ≤ k) {t : ℝ}
    (htj : t ∈ ocPulseWindow α q Λ m j) (htk : t ∈ ocPulseWindow α q Λ m k) : False := by
  have hτ : 0 < ocTau α q Λ m := Construction.Stream.ocTau_pos hΛ
  have hjk' : (j : ℝ) + 4 ≤ k := by exact_mod_cast hjk
  have htj' : t ≤ ((j : ℝ) + 61 / 48) * ocTau α q Λ m := htj.2
  have htk' : ((k : ℝ) - 61 / 48) * ocTau α q Λ m ≤ t := htk.1
  have e : ((j : ℝ) + 4 - 61 / 48) * ocTau α q Λ m ≤ ((k : ℝ) - 61 / 48) * ocTau α q Λ m :=
    mul_le_mul_of_nonneg_right (by linarith) hτ.le
  nlinarith

/-- **No three distinct odd windows meet.** -/
theorem not_mem_three_windows (hΛ : 1 ≤ Λ) {j k l : ℤ} (hj : Odd j) (hk : Odd k) (hl : Odd l)
    (hjk : j ≠ k) (hjl : j ≠ l) (hkl : k ≠ l) {t : ℝ} (htj : t ∈ ocPulseWindow α q Λ m j)
    (htk : t ∈ ocPulseWindow α q Λ m k) (htl : t ∈ ocPulseWindow α q Λ m l) : False := by
  have hcases : j + 4 ≤ k ∨ k + 4 ≤ j ∨ j + 4 ≤ l ∨ l + 4 ≤ j ∨ k + 4 ≤ l ∨ l + 4 ≤ k := by
    obtain ⟨a, ha⟩ := hj
    obtain ⟨b, hb⟩ := hk
    obtain ⟨c, hc⟩ := hl
    omega
  rcases hcases with h | h | h | h | h | h
  · exact not_mem_two_windows_far hΛ h htj htk
  · exact not_mem_two_windows_far hΛ h htk htj
  · exact not_mem_two_windows_far hΛ h htj htl
  · exact not_mem_two_windows_far hΛ h htl htj
  · exact not_mem_two_windows_far hΛ h htk htl
  · exact not_mem_two_windows_far hΛ h htl htk

end Geometry

variable {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)]
  {D : ℕ} {P : Type*} {Ctx : P → Type*} {α q : ℝ} {Λ m : ℕ} {ζ : ℝ → ℝ}

/-- **The active pieces at a weighted time of the window.** -/
theorem active_pieces (hΛ : 1 ≤ Λ) (hζ : IsFastProfile ζ) (F : ChartedFamily ι h D P Ctx)
    (pp : ℤ → P) {tA tZ : ℝ} {quiet : Set ℝ} {Cpart : ℝ}
    (hppinj : Set.InjOn pp ↑(ocObsPulses α q Λ m tA tZ))
    (hpart : IsLiftPartition (ocObsPulses α q Λ m tA tZ) (fun k => F.weight (pp k))
      (ocPulseWindow α q Λ m) quiet (Icc tA tZ) (ocTau α q Λ m) Cpart)
    (hcov : ∀ t ∈ Icc tA tZ, ∃ p, t ∈ (F.piece p).output)
    {k : ℤ} (hk : k ∈ ocObsPulses α q Λ m tA tZ) {t : ℝ} (ht : t ∈ Icc tA tZ)
    (hw : F.weight (pp k) t ≠ 0) :
    (F.weight (pp k) t = 1 ∧ ∀ p, p ≠ pp k → F.weight p t = 0) ∨
      ∃ j ∈ ocObsPulses α q Λ m tA tZ, j ≠ k ∧ t ∈ ocQuietTimes α q Λ ζ m ∧
        t ∈ ocPulseWindow α q Λ m j ∧ t ∈ ocPulseWindow α q Λ m k ∧
        F.weight (pp k) t + F.weight (pp j) t = 1 ∧
        ∀ p, F.weight p t ≠ 0 → p = pp k ∨ p = pp j := by
  classical
  set S := ocObsPulses α q Λ m tA tZ with hSdef
  have hsum : ∑ j ∈ S, F.weight (pp j) t = 1 := hpart.2.2.1 t ht
  have himg : ∑ p ∈ S.image pp, F.weight p t = 1 := by
    rw [Finset.sum_image fun a ha b hb hab => hppinj ha hb hab]
    exact hsum
  have hoff : ∀ p ∉ S.image pp, F.weight p t = 0 := fun p hp =>
    weight_eq_zero_of_sum F _ (hcov t ht) himg hp
  have hwin : ∀ j ∈ S, F.weight (pp j) t ≠ 0 → t ∈ ocPulseWindow α q Λ m j :=
    fun j hj hwj => hpart.2.2.2.1 j hj t hwj
  by_cases hex : ∃ j ∈ S, j ≠ k ∧ F.weight (pp j) t ≠ 0
  · right
    obtain ⟨j, hj, hjk, hwj⟩ := hex
    have htj := hwin j hj hwj
    have htk := hwin k hk hw
    have hl : ∀ l ∈ S, l ≠ k → l ≠ j → F.weight (pp l) t = 0 := fun l hl hlk hlj => by
      by_contra hwl
      exact not_mem_three_windows hΛ (LiftSetting.obsPulse_odd hl) (LiftSetting.obsPulse_odd hj)
        (LiftSetting.obsPulse_odd hk) hlj hlk hjk (hwin l hl hwl) htj htk
    refine ⟨j, hj, hjk, mem_ocQuietTimes_of_two_windows hΛ hζ (LiftSetting.obsPulse_odd hj)
      (LiftSetting.obsPulse_odd hk) hjk htj htk, htj, htk, ?_, fun p hp => ?_⟩
    · rw [Finset.sum_eq_add k j hjk.symm (fun c hc hck => hl c hc hck.1 hck.2)
        (fun h' => absurd hk h') (fun h' => absurd hj h')] at hsum
      exact hsum
    · by_contra hne
      push Not at hne
      by_cases hpS : p ∈ S.image pp
      · obtain ⟨l, hlS, rfl⟩ := Finset.mem_image.1 hpS
        exact hp (hl l hlS (fun h' => hne.1 (by rw [h'])) (fun h' => hne.2 (by rw [h'])))
      · exact hp (hoff p hpS)
  · left
    push Not at hex
    have h1 : F.weight (pp k) t = 1 := by
      rw [← hsum, Finset.sum_eq_single k (fun j hj hjk => hex j hj hjk) (fun h' => absurd hk h')]
    refine ⟨h1, fun p hp => ?_⟩
    by_cases hpS : p ∈ S.image pp
    · obtain ⟨l, hlS, rfl⟩ := Finset.mem_image.1 hpS
      exact hex l hlS fun h' => hp (by rw [h'])
    · exact hoff p hpS

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open MeasureTheory Set Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The coarse field in a moving chart** (the lift of a pulse acts on the coarse field read in
the renewal chart of the background flow, `a_lift(𝗍, X) = a(c𝗍, χ(c𝗍, ρX))`). For a coarse field of
finite rank in time, `a(t, x) = ∑_k c_k(t) φ_k(x)` with scalar coefficients of integral type and
smooth periodic fields, and a chart `χ` that is the flow of a smooth periodic velocity `W` and
commutes with integer translations, every slow jet of the chart-frame field is of integral type in
the cell time with density `c` times the material derivative `∂_t a + W·∇a` read in the chart. This
is the time regularity that the time-dependent lift identity (`cycle_lift_identity_prim_td`)
consumes; with `W = 𝐛_{m-1}` the background drift disappears from the chart frame. -/

/-- A continuous function on `ℝ × ℝ²` that is periodic in the second variable with respect to the
lattice `ρ⁻¹ℤ²` is bounded on `[a, b] × ℝ²`. -/
theorem exists_bound_of_periodic {a b ρ : ℝ} (hρ : 0 < ρ) (g : ℝ × Vec 2 → ℝ)
    (hg : Continuous g) (hper : ∀ s X (n : Fin 2 → ℤ), g (s, X + ρ⁻¹ • latticeShift n) = g (s, X)) :
    ∃ C, ∀ s ∈ Icc a b, ∀ X, g (s, X) ≤ C := by
  let K : Set (ℝ × Vec 2) := Icc a b ×ˢ Set.pi univ (fun _ => Icc 0 ρ⁻¹)
  have hK : IsCompact K := isCompact_Icc.prod (isCompact_univ_pi fun _ => isCompact_Icc)
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hg.continuousOn
  refine ⟨C, fun s hs X => ?_⟩
  let n : Fin 2 → ℤ := fun i => ⌊ρ * X i⌋
  let Y : Vec 2 := X - ρ⁻¹ • latticeShift n
  have hY : Y ∈ Set.pi univ (fun _ => Icc 0 ρ⁻¹) := by
    intro i _
    have h1 := Int.floor_le (ρ * X i)
    have h2 := Int.lt_floor_add_one (ρ * X i)
    have hYi : Y i = X i - ρ⁻¹ * (⌊ρ * X i⌋ : ℝ) := by
      simp [Y, n, latticeShift, smul_eq_mul]
    rw [hYi]
    have e1 : ρ⁻¹ * (ρ * X i) = X i := by field_simp
    have hl := mul_le_mul_of_nonneg_left h1 (inv_nonneg.2 hρ.le)
    have hu := mul_lt_mul_of_pos_left h2 (inv_pos.2 hρ)
    rw [e1] at hl hu
    constructor
    · linarith
    · rw [mul_add, mul_one] at hu
      linarith
  have hXY : X = Y + ρ⁻¹ • latticeShift n := by simp [Y]
  rw [hXY, hper]
  exact (le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC (s, Y) ⟨hs, hY⟩)

/-- Rescaled time: a scalar function of integral type on `[A, B]` read at `c s` is of integral
type on `[a, b]` (`A ≤ c a`, `c b ≤ B`, `c > 0`) with density `c · dg(c s)`. -/
theorem IsPrimOn.comp_mul {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    {A B a b c : ℝ} {g dg : ℝ → F} (hc : 0 < c) (hab : a ≤ b)
    (hA : A ≤ c * a) (hB : c * b ≤ B) (hg : IsPrimOn A B g dg) :
    IsPrimOn a b (fun s => g (c * s)) (fun s => c • dg (c * s)) := by
  have hca : c * a ≤ c * b := mul_le_mul_of_nonneg_left hab hc.le
  have hAB : A ≤ B := hA.trans (hca.trans hB)
  have hsub : ∀ {x y}, A ≤ x → x ≤ y → y ≤ B → IntervalIntegrable dg volume x y := by
    intro x y hx hxy hy
    exact hg.1.mono_set (by
      rw [uIcc_of_le hxy, uIcc_of_le hAB]
      exact Icc_subset_Icc hx hy)
  have hI : IntervalIntegrable (fun s => dg (c * s)) volume a b := by
    have h := (hsub hA hca hB).comp_mul_left (c := c)
    simpa [mul_div_cancel_left₀ _ hc.ne'] using h
  refine ⟨hI.smul c, fun s hs => ?_⟩
  have hcs : c * a ≤ c * s := mul_le_mul_of_nonneg_left hs.1 hc.le
  have hcs' : c * s ≤ B := (mul_le_mul_of_nonneg_left hs.2 hc.le).trans hB
  beta_reduce
  have h1 := hg.2 (c * s) ⟨hA.trans hcs, hcs'⟩
  have h2 := hg.2 (c * a) ⟨hA, hca.trans hB⟩
  have h3 : (∫ σ in a..s, c • dg (c * σ)) = ∫ σ in c * a..c * s, dg σ := by
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_comp_mul_left _ hc.ne',
      smul_smul, mul_inv_cancel₀ hc.ne', one_smul]
  rw [h3, h1, h2, add_assoc, add_right_inj]
  rw [← intervalIntegral.integral_interval_sub_left (hsub le_rfl (hA.trans hcs) hcs')
    (hsub le_rfl hA (hca.trans hB))]
  abel

section Chart

variable {ι : Type*} [Fintype ι] {h : ι → Type*}
  [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
  [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
  {κ : Type*} [Fintype κ]

/-- The chart-frame cell field of the finite-rank coarse field `∑_k c_k(t) φ_k(x)`:
`(𝗍, X) ↦ a(c𝗍, χ(c𝗍, ρX))`. -/
def chartField (cf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i) (χ : ℝ → Vec 2 → Vec 2)
    (c ρ : ℝ) (s : ℝ) (X : Vec 2) : ∀ i, h i :=
  ∑ k, cf k (c * s) • φ k (χ (c * s) (ρ • X))

/-- The cell-time density of the chart-frame field: `c` times the material derivative
`∂_t a + W·∇a` read in the chart. -/
def chartFieldDot (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i) (χ W : ℝ → Vec 2 → Vec 2)
    (c ρ : ℝ) (s : ℝ) (X : Vec 2) : ∀ i, h i :=
  (∑ k, (c * dcf k (c * s)) • φ k (χ (c * s) (ρ • X))) +
    ∑ k, cf k (c * s) • (c • fderiv ℝ (φ k) (χ (c * s) (ρ • X)) (W (c * s) (χ (c * s) (ρ • X))))

omit [Fintype ι] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)] in
/-- The fderiv of a `ℤ²`-periodic function is `ℤ²`-periodic. -/
theorem fderiv_periodic {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {f : Vec 2 → F}
    (hf : AVenhance.IsZ2Periodic f) (n : Fin 2 → ℤ) (y : Vec 2) :
    fderiv ℝ f (y + latticeShift n) = fderiv ℝ f y := by
  have hd : (fun y' => f (y' + latticeShift n)) = f := funext fun y' => hf n y'
  rw [← fderiv_comp_add_right (𝕜 := ℝ) (f := f) (latticeShift n), hd]

/-- **Slow jets of the chart-frame field are of integral type** (component `u`), with the
jets of `chartFieldDot` (the material derivative read in the chart) as densities. -/
theorem chartField_jet_prim (cf dcf : κ → ℝ → ℝ) (φ : κ → Vec 2 → ∀ i, h i)
    (hφ : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (φ k)) (hφp : ∀ k, AVenhance.IsZ2Periodic (φ k))
    (χ W : ℝ → Vec 2 → Vec 2)
    (hχ : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ p.1 p.2))
    (hW : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W p.1 p.2))
    (hχt : ∀ t y, HasDerivAt (fun t' => χ t' y) (W t (χ t y)) t)
    (hχl : ∀ t y (n : Fin 2 → ℤ), χ t (y + latticeShift n) = χ t y + latticeShift n)
    (hWp : ∀ t, AVenhance.IsZ2Periodic (W t))
    (c ρ : ℝ) (hc : 0 < c) (hρ : 0 < ρ) (A B a b : ℝ) (hab : a ≤ b) (hA : A ≤ c * a)
    (hB : c * b ≤ B) (hcf : ∀ k, IsPrimOn A B (cf k) (dcf k))
    (m : ℕ) (α : DerivativeWord2 m) (X : Vec 2) (u : ι) :
    IsPrimOn a b (fun s => orderedDerivative α (chartField cf φ χ c ρ s) X u)
      (fun s => orderedDerivative α (chartFieldDot cf dcf φ χ W c ρ s) X u) := by
  classical
  let Ψ : κ → ℝ → Vec 2 → ∀ i, h i := fun k s X => φ k (χ (c * s) (ρ • X))
  let Ψ' : κ → ℝ → Vec 2 → ∀ i, h i := fun k s X =>
    c • fderiv ℝ (φ k) (χ (c * s) (ρ • X)) (W (c * s) (χ (c * s) (ρ • X)))
  have hpos : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => χ (c * p.1) (ρ • p.2)) :=
    hχ.comp (((contDiff_const (c := c)).mul contDiff_fst).prodMk
      ((contDiff_const (c := ρ)).smul contDiff_snd))
  have hΨj : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => Ψ k p.1 p.2) := fun k =>
    (hφ k).comp hpos
  have hWj : ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => W (c * p.1) (χ (c * p.1) (ρ • p.2))) :=
    hW.comp (((contDiff_const (c := c)).mul contDiff_fst).prodMk hpos)
  have hΨ'j : ∀ k, ContDiff ℝ (⊤ : ℕ∞) (fun p : ℝ × Vec 2 => Ψ' k p.1 p.2) := fun k =>
    (contDiff_const (c := c)).smul ((((hφ k).fderiv_right (by simp)).comp hpos).clm_apply hWj)
  have hslice : ∀ {F : ℝ × Vec 2 → ∀ i, h i}, ContDiff ℝ (⊤ : ℕ∞) F → ∀ s,
      ContDiff ℝ (⊤ : ℕ∞) (fun Y => F (s, Y)) := fun hF s =>
    hF.comp (contDiff_const.prodMk contDiff_id)
  have hcompu : ∀ (F : Vec 2 → ∀ i, h i), ContDiff ℝ (m : ℕ∞) F →
      orderedDerivative α F X u = orderedDerivative α (fun Y => F Y u) X := by
    intro F hF
    exact (congrFun (AVRegularity.orderedDerivative_clm_comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := h) u) α hF) X).symm
  -- the jets of the moving fields
  have hJ : ∀ k, IsPrimOn a b (fun s => orderedDerivative α (Ψ k s) X u)
      (fun s => orderedDerivative α (Ψ' k s) X u) := by
    intro k
    have hder : ∀ s ∈ Icc a b, ∀ Y, HasDerivAt (fun s' => Ψ k s' Y u) (Ψ' k s Y u) s := by
      intro s _ Y
      have h1 : HasDerivAt (fun s' => χ (c * s') (ρ • Y)) (c • W (c * s) (χ (c * s) (ρ • Y))) s :=
        (hχt (c * s) (ρ • Y)).scomp s (((hasDerivAt_id s).const_mul c).congr_deriv (mul_one c))
      have h2 := (((hφ k).differentiable (by simp)) _).hasFDerivAt.comp_hasDerivAt s h1
      have h3 := hasDerivAt_pi.1 h2 u
      refine h3.congr_deriv ?_
      simp only [Ψ', map_smul, Pi.smul_apply]
    have hcont : ∀ Y, ContinuousOn (fun s => Ψ' k s Y u) (Icc a b) := fun Y =>
      ((continuous_apply u).comp ((hΨ'j k).continuous.comp
        (continuous_id.prodMk continuous_const))).continuousOn
    have hsm : ∀ s ∈ Icc a b, ContDiff ℝ (m : ℕ∞) (fun Y => Ψ k s Y u) := fun s _ =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp (hslice (hΨj k) s)).of_le (by simp)
    have hsm' : ∀ s ∈ Icc a b, ContDiff ℝ (m : ℕ∞) (fun Y => Ψ' k s Y u) := fun s _ =>
      ((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp (hslice (hΨ'j k) s)).of_le (by simp)
    have hper : ∀ s (Y : Vec 2) (n : Fin 2 → ℤ),
        Ψ' k s (Y + ρ⁻¹ • latticeShift n) = Ψ' k s Y := by
      intro s Y n
      have hρY : ρ • (Y + ρ⁻¹ • latticeShift n) = ρ • Y + latticeShift n := by
        rw [smul_add, smul_smul, mul_inv_cancel₀ hρ.ne', one_smul]
      simp only [Ψ', hρY, hχl, fderiv_periodic (hφp k), hWp _ n]
    have hbound : ∀ j, ∃ C, ∀ s ∈ Icc a b, ∀ x,
        ‖iteratedFDeriv ℝ j (fun Y => Ψ' k s Y u) x‖ ≤ C := by
      intro j
      have hcj := (Weighted.joint_partialIteratedFDeriv_right_contDiff 0 j
        (fun p : ℝ × Vec 2 => Ψ' k p.1 p.2 u)
        (((ContinuousLinearMap.proj (R := ℝ) (φ := h) u).contDiff.comp (hΨ'j k)).of_le (by simp))).continuous.norm
      refine exists_bound_of_periodic hρ _ hcj fun s Y n => ?_
      simp only
      rw [← iteratedFDeriv_comp_add_right]
      congr 2
      funext Y'
      rw [hper s Y' n]
    choose C hC using hbound
    have hjp := jet_prim_of_timeDeriv hab m (fun s Y => Ψ k s Y u) (fun s Y => Ψ' k s Y u)
      hder hcont hsm hsm' C (fun j _ => hC j) m le_rfl α X
    exact hjp.congr hab
      (fun s _ => (hcompu (Ψ k s) ((hslice (hΨj k) s).of_le (by simp))).symm)
      (fun s _ => (hcompu (Ψ' k s) ((hslice (hΨ'j k) s).of_le (by simp))).symm)
  have hterm : ∀ k ∈ (Finset.univ : Finset κ), IsPrimOn a b
      (fun s => cf k (c * s) • orderedDerivative α (Ψ k s) X u)
      (fun s => (c * dcf k (c * s)) • orderedDerivative α (Ψ k s) X u +
        cf k (c * s) • orderedDerivative α (Ψ' k s) X u) := fun k _ =>
    IsPrimOn.smul hab (by simpa only [smul_eq_mul] using (hcf k).comp_mul hc hab hA hB) (hJ k)
  refine (IsPrimOn.sum Finset.univ hterm).congr hab (fun s _ => ?_) (fun s _ => ?_)
  · have hsyn := Lift.orderedDerivative_finite_synthesis α (fun k => cf k (c * s))
      (fun k => Ψ k s) (fun k => (hslice (hΨj k) s).of_le (by simp)) X
    show _ = orderedDerivative α (fun Y => ∑ k, cf k (c * s) • Ψ k s Y) X u
    rw [hsyn, Finset.sum_apply]
    simp only [Pi.smul_apply]
  · have hs1 : ContDiff ℝ (m : ℕ∞) (fun Y => ∑ k, (c * dcf k (c * s)) • Ψ k s Y) :=
      (ContDiff.sum fun k _ => (hslice (hΨj k) s).const_smul _).of_le (by simp)
    have hs2 : ContDiff ℝ (m : ℕ∞) (fun Y => ∑ k, cf k (c * s) • Ψ' k s Y) :=
      (ContDiff.sum fun k _ => (hslice (hΨ'j k) s).const_smul _).of_le (by simp)
    show _ = orderedDerivative α
      (fun Y => (∑ k, (c * dcf k (c * s)) • Ψ k s Y) + ∑ k, cf k (c * s) • Ψ' k s Y) X u
    rw [AVRegularity.orderedDerivative_add α hs1 hs2]
    beta_reduce
    rw [Lift.orderedDerivative_finite_synthesis α (fun k => c * dcf k (c * s)) (fun k => Ψ k s)
        (fun k => (hslice (hΨj k) s).of_le (by simp)) X,
      Lift.orderedDerivative_finite_synthesis α (fun k => cf k (c * s)) (fun k => Ψ' k s)
        (fun k => (hslice (hΨ'j k) s).of_le (by simp)) X]
    simp only [Pi.add_apply, Finset.sum_apply, Pi.smul_apply, Finset.sum_add_distrib]

end Chart

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The physical edge coefficient applied to the jets of a smooth field**.

Exact Piola transports flux by `(DΦR)∘Φ⁻¹`, and chart jets pay the chain rule.

For a charted family `F` and a smooth physical field `U`, the flux term of the actual equation
(`IsCoupledWeakSolutionTorus`) is `∑_{u} ∑_{d ∈ admissibleOrders} edgeCoefficient … d t x
(∇^{d-1} U_u)`. At a time `t`, for every finite set `S` of pieces containing the active ones,
`edgeFlux_eq_sum_pieces_of_contDiff` writes its `a₀`-component as
`∑_{p ∈ S} ϖ_p(t) ∑_{i₀} K_p(x)_{a₀ i₀} G_p(ψ_p x)_{i₀}`, where `ψ_p = Φ_p(t,·)⁻¹` is the label map
of the piece, `K_p = chartInvJacobian ψ_p` and `G_p = labelEdgeFlux` is the **label edge flux**
of the piece applied to the label field `U ∘ Φ_p(t,·)`:
`G_p(y)_{i₀} = ∑_u ∑_γ C_γ (∑_{d=1}^{D_γ} ∑_{|I|=d-1} 𝔞[p,γ,d,I](t, y, e⁻¹y)_{i₀} ∂^I_y V_u(y))`.
For a single active piece (`edgeFlux_single_piece_of_contDiff`) only `p₀` remains, and if its
material map preserves area the physical divergence of the flux term is the label divergence of
`G_{p₀}` at `ψ_{p₀} x`.

Order bookkeeping. `edgeCoefficient` sums the physical orders `d ∈ admissibleOrders K D v u`
(`2 ≤ d ≤ D`, `K v + d ≤ K u + 2`); a label order `d' ≤ D_γ` feeds the physical orders `2,…,d'`
(`transportedCoeff`). Under `F.IsDescending K` every physical order `2 ≤ d ≤ D_γ` is admissible,
physical orders above `D_γ` vanish (empty range of label orders), and the physical order `1`
vanishes (`T_{I,∅} = 0` for `I ≠ ∅`, and the label order `1` carries the zero field,
`flux_zero`); so the admissible sum is the full sum over `[1, D_γ]` of
`transportedCoeff_flux_orders_of_contDiff`.
The jets enter as `WithLp.toLp 2 (word ↦ ∂^{word} U_u(x))`, the constant maps `C_γ` act on each
jet, and the `a₀`-component is the `PiLp` coordinate. -/

section
section Sums

/-- A sum over a set of orders containing `[2, Dγ]` and contained in `[2, ∞)`, of a function
vanishing above `Dγ` and at `1`, is the sum over `[1, Dγ]`. -/
theorem sum_orders_eq_Icc_one {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (Dγ : ℕ) (f : ℕ → M)
    (hsub : Finset.Icc 2 Dγ ⊆ s) (hs : ∀ d ∈ s, 2 ≤ d) (hhi : ∀ d, Dγ < d → f d = 0)
    (h1 : f 1 = 0) : ∑ d ∈ s, f d = ∑ d ∈ Finset.Icc 1 Dγ, f d := by
  have e1 : ∑ d ∈ Finset.Icc 2 Dγ, f d = ∑ d ∈ s, f d :=
    Finset.sum_subset hsub fun d hd hnd => hhi d (by
      have h2 := hs d hd
      simp only [Finset.mem_Icc] at hnd
      omega)
  have e2 : ∑ d ∈ Finset.Icc 2 Dγ, f d = ∑ d ∈ Finset.Icc 1 Dγ, f d :=
    Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun d hd hnd => by
      have hd1 : d = 1 := by
        simp only [Finset.mem_Icc] at hd hnd
        omega
      rw [hd1, h1]
  rw [← e1, e2]

/-- `sum_orders_eq_Icc_one` for a sum over the subtype of a set of orders. -/
theorem sum_coe_sort_orders {M : Type*} [AddCommMonoid M] (s : Finset ℕ) (Dγ : ℕ) (f : ℕ → M)
    (hsub : Finset.Icc 2 Dγ ⊆ s) (hs : ∀ d ∈ s, 2 ≤ d) (hhi : ∀ d, Dγ < d → f d = 0)
    (h1 : f 1 = 0) : ∑ d : s, f d.1 = ∑ d ∈ Finset.Icc 1 Dγ, f d := by
  rw [Finset.sum_coe_sort s f]
  exact sum_orders_eq_Icc_one s Dγ f hsub hs hhi h1

/-- Pulling a finite inner sum out of a dependent double sum. -/
theorem sum_dep_pull {M : Type*} [AddCommMonoid M] {α : Type*} {κ : α → Type*}
    [∀ a, Fintype (κ a)] {T : Type*} [Fintype T] (s : Finset α) (f : ∀ a, κ a → T → M) :
    ∑ a ∈ s, ∑ b : κ a, ∑ j : T, f a b j = ∑ j : T, ∑ a ∈ s, ∑ b : κ a, f a b j :=
  Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) Finset.sum_comm

/-- Pulling a weighted sum over pieces out of a dependent double sum. -/
theorem sum_sum_pieces {M : Type*} [AddCommMonoid M] [Module ℝ M] {α : Type*} {κ : α → Type*}
    [∀ a, Fintype (κ a)] {P : Type*} (s : Finset α) (S : Finset P) (w : P → ℝ)
    (X : ∀ a, κ a → P → M) :
    ∑ a ∈ s, ∑ b : κ a, ∑ p ∈ S, w p • X a b p = ∑ p ∈ S, w p • ∑ a ∈ s, ∑ b : κ a, X a b p := by
  calc ∑ a ∈ s, ∑ b : κ a, ∑ p ∈ S, w p • X a b p
      = ∑ p ∈ S, ∑ a ∈ s, ∑ b : κ a, w p • X a b p :=
        Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) Finset.sum_comm
    _ = ∑ p ∈ S, w p • ∑ a ∈ s, ∑ b : κ a, X a b p := by
        simp only [Finset.smul_sum]

end Sums

section Linear

variable {M N : Type*} [NormedAddCommGroup M] [NormedSpace ℝ M] [NormedAddCommGroup N]
  [NormedSpace ℝ N]

/-- The action of an assembled native coefficient array on a word array, one component. -/
theorem pieceCLM_apply (C : M →L[ℝ] N) {r : ℕ} (b : Fin 2 → DerivativeWord2 r → ℝ)
    (g : PiLp 2 (fun _ : DerivativeWord2 r => M)) (k : Fin 2) :
    ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => N)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k : Fin 2 => ∑ A : DerivativeWord2 r,
        b k A • C.comp (PiLp.proj 2 (fun _ : DerivativeWord2 r => M) A))) g k =
      ∑ A : DerivativeWord2 r, b k A • C (g A) := by
  show (∑ A : DerivativeWord2 r,
      b k A • C.comp (PiLp.proj 2 (fun _ : DerivativeWord2 r => M) A)) g = _
  exact Eq.trans (_root_.sum_apply _ _ _) (Finset.sum_congr rfl fun _ _ => rfl)

/-- A continuous linear map commutes with a dependent double sum of scalar multiples. -/
theorem sum_sum_smul_map (L : M →L[ℝ] N) {κ : Type*} {τ : κ → Type*} [∀ a, Fintype (τ a)]
    (s : Finset κ) (c : ∀ a, τ a → ℝ) (w : ∀ a, τ a → M) :
    ∑ a ∈ s, ∑ b : τ a, c a b • L (w a b) = L (∑ a ∈ s, ∑ b : τ a, c a b • w a b) := by
  simp only [map_sum, map_smul]

/-- Separating the flux direction from an order- and word-indexed sum under a linear map. -/
theorem map_sum_dir (L : M →L[ℝ] N) (s : Finset ℕ) (k : Fin 2 → ℝ)
    (b : ∀ d, DerivativeWord2 (d - 1) → Fin 2 → ℝ) (w : ∀ d, DerivativeWord2 (d - 1) → M) :
    L (∑ d ∈ s, ∑ I : DerivativeWord2 (d - 1), ∑ j : Fin 2, (k j * b d I j) • w d I) =
      ∑ j : Fin 2, k j • L (∑ d ∈ s, ∑ I : DerivativeWord2 (d - 1), b d I j • w d I) := by
  rw [transition_sum_swap_dir s (fun d I j => (k j * b d I j) • w d I)]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]

end Linear

section Coeff

/-- The transported array of order `r + 1` vanishes for `r + 1` above the maximal order. -/
theorem transportedCoeff_eq_zero_of_lt (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) {r : ℕ} (A : DerivativeWord2 r) (y : Vec 2)
    (a₀ : Fin 2) (h : Dγ < r + 1) : transportedCoeff K Dγ B r A y a₀ = 0 := by
  have h0 : Finset.Icc (r + 1) Dγ = ∅ := Finset.Icc_eq_empty (by omega)
  simp only [transportedCoeff, h0, Finset.sum_empty]

/-- The transported array of physical order `1` vanishes when the label order `1` is absent:
`T_{I,∅} = 0` for `I ≠ ∅`. -/
theorem transportedCoeff_low_eq_zero (K : Vec 2 → Matrix (Fin 2) (Fin 2) ℝ) (Dγ : ℕ)
    (B : ∀ d : ℕ, DerivativeWord2 (d - 1) → Vec 2) {r : ℕ} (hr : r = 0) (A : DerivativeWord2 r)
    (y : Vec 2) (a₀ : Fin 2) (hB : ∀ I, B 1 I = 0) : transportedCoeff K Dγ B r A y a₀ = 0 := by
  subst hr
  simp only [transportedCoeff]
  refine Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun I _ =>
    Finset.sum_eq_zero fun i₀ _ => ?_
  by_cases hd1 : d = 1
  · subst hd1
    rw [hB I, Pi.zero_apply, mul_zero, zero_mul]
  · have hne : List.ofFn I ≠ [] := by
      rw [Ne, List.ofFn_eq_nil_iff]
      simp only [Finset.mem_Icc] at hd
      omega
    obtain ⟨j, J, hJ⟩ := List.exists_cons_of_ne_nil hne
    rw [hJ, List.ofFn_zero,
      AVRegularity.CycleJointProofs.transitionT_empty_output_nonempty_native, Pi.zero_apply,
      mul_zero]

end Coeff

section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **The label edge flux** of the piece `p` in the context `c` at time `t`, applied to the label
field `V`, component `v`, flux direction `i₀`:
`G(y)_{i₀} = ∑_u ∑_γ C_γ (∑_{d=1}^{D_γ} ∑_{|I|=d-1} 𝔞[p,c,γ,d,I](t, y, e⁻¹y)_{i₀} ∂^I_y V_u(y))`. -/
def labelEdgeFlux (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (p : P) (c : Ctx p) (t : ℝ)
    (V : Vec 2 → ∀ i, h i) (v : ι) (y : Vec 2) (i₀ : Fin 2) : h v :=
  ∑ u : ι, ∑ γ : F.Γ v u, (F.identity v u γ).map
    (∑ d ∈ Finset.Icc 1 (F.identity v u γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
      F.dimFlux ν e E p c v u γ d I t y (e⁻¹ • y) i₀ • orderedDerivative I (fun y' => V y' u) y)

omit [Fintype ι] in
/-- The label order `1` carries the zero field. -/
theorem dimFlux_one_eq_zero (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (p : P) (c : Ctx p)
    (v u : ι) (γ : F.Γ v u) (I : DerivativeWord2 (1 - 1)) (t : ℝ) (Y z : Vec 2) :
    F.dimFlux ν e E p c v u γ 1 I t Y z = 0 := by
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux,
    F.flux_zero p c v u γ 1 I (by omega), smul_zero]

/-- **The edge coefficient as a weighted sum over the active pieces.** For any finite set `S` of
pieces containing every piece of nonzero weight at `t`, one component of the edge coefficient
applied to a word array `g` is the weighted sum over `S` of the native arrays of the pieces. -/
theorem edgeCoefficient_apply_sum_pieces (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) {t : ℝ} (S : Finset P)
    (hS : ∀ p, F.weight p t ≠ 0 → p ∈ S) (i i' : ι) (d : admissibleOrders K D i i')
    (x : Vec 2) (g : PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) (a₀ : Fin 2) :
    edgeCoefficient F ν e E actual K i i' d t x g a₀ =
      ∑ p ∈ S, F.weight p t • ∑ γ : F.Γ i i', ∑ A : DerivativeWord2 (d.1 - 1),
        transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
          (F.identity i i' γ).maxOrder
          (fun d' I => F.dimFlux ν e E p (actual p) i i' γ d' I t
            (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x))
          (d.1 - 1) A x a₀ • (F.identity i i' γ).map (g A) := by
  let b : P → F.Γ i i' → Fin 2 → DerivativeWord2 (d.1 - 1) → ℝ := fun p γ k A =>
    transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
      (F.identity i i' γ).maxOrder
      (fun d' I => F.dimFlux ν e E p (actual p) i i' γ d' I t
        (((F.piece p).material t).symm x) (e⁻¹ • ((F.piece p).material t).symm x))
      (d.1 - 1) A x k
  let L : P → F.Γ i i' → (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i)) := fun p γ =>
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => h i)).symm.toContinuousLinearMap.comp
      (ContinuousLinearMap.pi fun k : Fin 2 => ∑ A : DerivativeWord2 (d.1 - 1),
        b p γ k A •
          (F.identity i i' γ).map.comp
            (PiLp.proj 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i') A))
  let ev : ((PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i))) →L[ℝ] h i :=
    (PiLp.proj (𝕜 := ℝ) 2 (fun _ : Fin 2 => h i) a₀).comp
      (ContinuousLinearMap.apply ℝ (PiLp 2 (fun _ : Fin 2 => h i)) g)
  have hev : ∀ Λ : (PiLp 2 (fun _ : DerivativeWord2 (d.1 - 1) => h i')) →L[ℝ]
      (PiLp 2 (fun _ : Fin 2 => h i)), ev Λ = Λ g a₀ := fun _ => rfl
  have h1 : ∀ γ : F.Γ i i', constituentPhysical F ν e E actual i i' γ d.1 t x =
      ∑ p ∈ S, F.weight p t • L p γ := fun γ =>
    finsum_eq_sum_of_support_subset _ fun p hp => Finset.mem_coe.mpr
      (hS p fun hw => (Function.mem_support.mp hp) (by
        rw [hw]
        exact ContinuousLinearMap.ext fun z => by simp))
  calc edgeCoefficient F ν e E actual K i i' d t x g a₀
      = ev (∑ γ : F.Γ i i', constituentPhysical F ν e E actual i i' γ d.1 t x) :=
        (hev (edgeCoefficient F ν e E actual K i i' d t x)).symm
    _ = ∑ γ : F.Γ i i', ∑ p ∈ S, F.weight p t • ev (L p γ) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun γ _ => ?_
        rw [h1 γ, map_sum]
        exact Finset.sum_congr rfl fun p _ => map_smul ev _ _
    _ = ∑ p ∈ S, F.weight p t • ∑ γ : F.Γ i i', ev (L p γ) := by
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun p _ => Finset.smul_sum.symm
    _ = _ := Finset.sum_congr rfl fun p _ => congrArg (F.weight p t • ·)
        (Finset.sum_congr rfl fun γ _ =>
          (hev (L p γ)).trans (pieceCLM_apply (F.identity i i' γ).map (b p γ) g a₀))

end Family
end

/-! **The lifted pulse flux is the label edge flux**.

In a lift setting (`IsLiftSetting`) the cell time `𝗍` has `t = ℓ²𝗍`, the lift slow variable is
`X = y/ρ`, and `λ_s = ρ/E`.

The inner flux of `sample_sourceOp_label` for the lifted fiber `liftEdges cℓ lam (F.fiber p c)` of
one piece, at the cell time `s`, the label point `y` and the flux direction `k`, applied to a label
field `V` (in `sample_sourceOp_label`, `V = twoScaleSample ρ e Φ`), is
`∑_u ∑_{d ∈ [2,D]} ∑_{γ ∈ fiber} ∑_α a'_{γ,α}(s, ρ⁻¹y, e⁻¹y)_k C_γ(e^{d-1} ∂^α V_u(y))`.
With `lam ρ⁻¹ = E⁻¹` the lift coefficient is `a♭(cℓ s, E⁻¹y, e⁻¹y)`, and
`e^{d-1} a♭ = (e/ν) · ν e^{d-2} a♭ = (e/ν) 𝔞` for `d ≥ 2`; so
(`liftFlux_eq_labelEdgeFlux_of_contDiff`) the inner flux is `(e/ν) G(y)_k`,
`G = labelEdgeFlux F ν e E p c (cℓ s) V v`. Order bookkeeping: the fiber lists the constituent `γ`
at the orders `2 ≤ d ≤ D_γ` (`liftFlux_list`, `sum_Icc_subtype_ite_gen`); the label order `1` of `G`
carries the zero field.

Combined with `edgeFlux_single_piece_of_contDiff` this gives: at a time `t = cℓ s` with
the single active piece `p₀`, `(e/ν)` times the flux term of the actual equation at `x` is
`∑_{i₀} K_{p₀}(x)_{a₀ i₀}` times the inner lifted flux of `p₀` at `ψ_{p₀} x`, for the label field
`U ∘ Φ_{p₀}(t,·)`. -/

section
section Generic

/-- The sum over a filtered and mapped list. -/
theorem list_sum_map_filterMap_elim {α β M : Type*} [AddCommMonoid M] (l : List α)
    (φ : α → Option β) (ψ : β → M) :
    ((l.filterMap φ).map ψ).sum = (l.map fun a => (φ a).elim 0 ψ).sum := by
  induction l with
  | nil => rfl
  | cons a l ih =>
      cases hφ : φ a <;> simp [hφ, ih]

/-- Exchange of the sum over the orders `[2, D]` with the sum over the identities. -/
theorem sum_Icc_subtype_ite_gen {M : Type*} [AddCommMonoid M] {Γ : Type*} [Fintype Γ] (D : ℕ)
    (mo : Γ → ℕ) (hmo : ∀ γ, mo γ ≤ D) (T : Γ → ℕ → M) :
    ∑ d : Finset.Icc 2 D, ∑ γ : Γ, (if d.1 ≤ mo γ then T γ d.1 else 0) =
      ∑ γ : Γ, ∑ d ∈ Finset.Icc 2 (mo γ), T γ d := by
  rw [Finset.sum_coe_sort (s := Finset.Icc 2 D)
    (f := fun d => ∑ γ : Γ, if d ≤ mo γ then T γ d else 0), Finset.sum_comm]
  refine Finset.sum_congr rfl fun γ _ => ?_
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext d
  have hγ := hmo γ
  simp only [Finset.mem_filter, Finset.mem_Icc]
  omega

/-- The sum over `[1, n]` of a function vanishing at `1` is the sum over `[2, n]`. -/
theorem sum_Icc_one_eq_two {M : Type*} [AddCommMonoid M] (n : ℕ) (f : ℕ → M) (h1 : f 1 = 0) :
    ∑ d ∈ Finset.Icc 1 n, f d = ∑ d ∈ Finset.Icc 2 n, f d := by
  symm
  refine Finset.sum_subset (Finset.Icc_subset_Icc_left (by norm_num)) fun d hd hnd => ?_
  have hd1 : d = 1 := by
    simp only [Finset.mem_Icc] at hd hnd
    omega
  rw [hd1, h1]

/-- The scale identity of the lift: `(e/ν) (ν e^{d-2}) a = a e^{d-1}` for `d ≥ 2`. -/
theorem lift_scale (ν e a : ℝ) (hν : ν ≠ 0) {d : ℕ} (hd : 2 ≤ d) :
    e / ν * (ν * e ^ (d - 2) * a) = a * e ^ (d - 1) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hd
  have h1 : 2 + n - 2 = n := by omega
  have h2 : 2 + n - 1 = n + 1 := by omega
  have hνν : ν⁻¹ * ν = 1 := inv_mul_cancel₀ hν
  rw [h1, h2, pow_succ]
  calc e / ν * (ν * e ^ n * a) = ν⁻¹ * ν * (a * (e ^ n * e)) := by ring
    _ = a * (e ^ n * e) := by rw [hνν, one_mul]

end Generic

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- One order of the lifted fiber, as a sum over the identities: the lift coefficient of the
constituent `γ₀` at the order `d ≤ D_{γ₀}` is `a♭(cℓ s, lam ρ⁻¹ y, e⁻¹ y)`. -/
theorem liftFlux_list (F : ChartedFamily ι h D P Ctx) (p : P) (c : Ctx p) (cℓ lam ρ e s : ℝ)
    (V : Vec 2 → ∀ i, h i) (v u : ι) (d : Finset.Icc 2 D) (y : Vec 2) (k : Fin 2) :
    ((liftEdges cℓ lam (F.fiber p c) v u d).map fun γ =>
        ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α s (ρ⁻¹ • y) (e⁻¹ • y) k) •
          γ.map (e ^ (d.1 - 1) • orderedDerivative α V y u)).sum =
      ∑ γ₀ : F.Γ v u, if d.1 ≤ (F.identity v u γ₀).maxOrder then
        ∑ α : DerivativeWord2 (d.1 - 1),
          (F.flux p c v u γ₀ d.1 α (cℓ * s) (lam • ρ⁻¹ • y) (e⁻¹ • y) k) •
            (F.identity v u γ₀).map (e ^ (d.1 - 1) • orderedDerivative α V y u)
      else 0 := by
  simp only [liftEdges, ChartedFamily.fiber, List.map_map]
  rw [list_sum_map_filterMap_elim, Finset.sum_map_toList]
  refine Finset.sum_congr rfl fun γ₀ _ => ?_
  by_cases hd : d.1 ≤ (F.identity v u γ₀).maxOrder
  · rewrite [dite_eq_left hd, ite_eq_left hd]
    rfl
  · rewrite [dite_eq_right hd, ite_eq_right hd]
    rfl

end Lift
end

/-! **The physical edge coefficient applied to the jets of a `C^r` field**.

The identities above for a field of finite smoothness (the declarations named `…_of_contDiff`).
The physical field `U` (and the label field `V`) is only `C^r`; the charts stay smooth. The
label words of the flux have length `≤ D - 1`, so the pointwise flux identities need `D ≤ r + 1`
(`transportedCoeff_flux_orders_of_contDiff`); the label edge flux is differentiable for `D ≤ r`
when its coefficients are, which is what the divergence form of the single-piece identity uses. -/

section
section Family

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **One constituent, all orders**, for a `C^r` field `U` with `D ≤ r + 1`: the admissible sum of
the transported coefficients of the constituent `γ` applied to the jets of `U` is the full sum
over the label orders `[1, D_γ]` of its label flux, applied to the label jets of `U ∘ Φ_p(t,·)`
and read through `chartInvJacobian ψ_p`. -/
theorem constituent_orders_flux_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (p : P)
    (c : Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) (t : ℝ) {r : ℕ}
    {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i i' : ι)
    (γ : F.Γ i i') (x : Vec 2) (a₀ : Fin 2) :
    ∑ d : admissibleOrders K D i i', ∑ A : DerivativeWord2 (d.1 - 1),
        transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
          (F.identity i i' γ).maxOrder
          (fun d' I => F.dimFlux ν e E p c i i' γ d' I t (((F.piece p).material t).symm x)
            (e⁻¹ • ((F.piece p).material t).symm x)) (d.1 - 1) A x a₀ •
          orderedDerivative A (fun y => U y i') x =
      ∑ d ∈ Finset.Icc 1 (F.identity i i' γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        ∑ i₀ : Fin 2,
          (chartInvJacobian ⇑((F.piece p).material t).symm x a₀ i₀ *
            F.dimFlux ν e E p c i i' γ d I t (((F.piece p).material t).symm x)
              (e⁻¹ • ((F.piece p).material t).symm x) i₀) •
          orderedDerivative I (fun y => U ((F.piece p).material t y) i')
            (((F.piece p).material t).symm x) := by
  have hχ : ContDiff ℝ (⊤ : ℕ∞) ⇑((F.piece p).material t) := (F.piece p).material_smooth t
  have hψ : ContDiff ℝ (⊤ : ℕ∞) ⇑((F.piece p).material t).symm :=
    (F.piece p).material_symm_smooth t
  have hψχ : ∀ y, ((F.piece p).material t).symm ((F.piece p).material t y) = y :=
    ((F.piece p).material t).symm_apply_apply
  have hχψ : ∀ y, (F.piece p).material t (((F.piece p).material t).symm y) = y :=
    ((F.piece p).material t).apply_symm_apply
  have hV : ContDiff ℝ (r : ℕ∞) (fun y => U ((F.piece p).material t y) i') :=
    contDiff_pi.1 (hU.comp (hχ.of_le (WithTop.coe_le_coe.mpr le_top))) i'
  have hVψ : (fun y => U ((F.piece p).material t y) i') ∘ ⇑((F.piece p).material t).symm =
      fun y => U y i' := funext fun y => by simp only [Function.comp_apply, hχψ]
  have hflux := transportedCoeff_flux_orders_of_contDiff hχ hψ hψχ hχψ hV
    (F.identity i i' γ).maxOrder ((F.identity i i' γ).le_D.trans hrD)
    (fun d' I => F.dimFlux ν e E p c i i' γ d' I t (((F.piece p).material t).symm x)
      (e⁻¹ • ((F.piece p).material t).symm x)) x a₀
  rw [hVψ] at hflux
  refine Eq.trans ?_ hflux
  exact sum_coe_sort_orders (admissibleOrders K D i i') (F.identity i i' γ).maxOrder
    (fun n => ∑ A : DerivativeWord2 (n - 1),
      transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
        (F.identity i i' γ).maxOrder
        (fun d' I => F.dimFlux ν e E p c i i' γ d' I t (((F.piece p).material t).symm x)
          (e⁻¹ • ((F.piece p).material t).symm x)) (n - 1) A x a₀ •
        orderedDerivative A (fun y => U y i') x)
    (by
      intro n hn
      have hD := hdesc i i' γ
      have hle := (F.identity i i' γ).le_D
      simp only [admissibleOrders, Finset.mem_filter, Finset.mem_Icc] at hn ⊢
      omega)
    (by
      intro n hn
      simp only [admissibleOrders, Finset.mem_filter, Finset.mem_Icc] at hn
      omega)
    (by
      intro n hn
      refine Finset.sum_eq_zero fun A _ => ?_
      have h0 : Finset.Icc (n - 1 + 1) (F.identity i i' γ).maxOrder = ∅ :=
        Finset.Icc_eq_empty (by omega)
      simp only [transportedCoeff, h0, Finset.sum_empty, zero_smul])
    (Finset.sum_eq_zero fun A _ => by
      rw [transportedCoeff_low_eq_zero (chartInvJacobian ⇑((F.piece p).material t).symm)
        (F.identity i i' γ).maxOrder
        (fun d' I => F.dimFlux ν e E p c i i' γ d' I t (((F.piece p).material t).symm x)
          (e⁻¹ • ((F.piece p).material t).symm x)) (r := 1 - 1) rfl A x a₀
        (fun I => dimFlux_one_eq_zero F ν e E p c i i' γ I t _ _), zero_smul])

/-- **The edge flux of one piece is the transported label edge flux**, for a `C^r` field with
`D ≤ r + 1`: `∑_{i₀} K_p(x)_{a₀ i₀} G_p(ψ_p x)_{i₀}`, `G_p = labelEdgeFlux`. -/
theorem pieceEdgeFlux_eq_label_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (p : P)
    (c : Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) (t : ℝ) {r : ℕ}
    {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι) (x : Vec 2)
    (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i', ∑ γ : F.Γ i i', ∑ A : DerivativeWord2 (d.1 - 1),
        transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
          (F.identity i i' γ).maxOrder
          (fun d' I => F.dimFlux ν e E p c i i' γ d' I t (((F.piece p).material t).symm x)
            (e⁻¹ • ((F.piece p).material t).symm x)) (d.1 - 1) A x a₀ •
          (F.identity i i' γ).map (orderedDerivative A (fun y => U y i') x) =
      ∑ i₀ : Fin 2, chartInvJacobian ⇑((F.piece p).material t).symm x a₀ i₀ •
        labelEdgeFlux F ν e E p c t (fun y => U ((F.piece p).material t y)) i
          (((F.piece p).material t).symm x) i₀ := by
  have hγ : ∀ (i' : ι) (γ : F.Γ i i'), ∑ d : admissibleOrders K D i i',
      ∑ A : DerivativeWord2 (d.1 - 1),
        transportedCoeff (chartInvJacobian ⇑((F.piece p).material t).symm)
          (F.identity i i' γ).maxOrder
          (fun d' I => F.dimFlux ν e E p c i i' γ d' I t (((F.piece p).material t).symm x)
            (e⁻¹ • ((F.piece p).material t).symm x)) (d.1 - 1) A x a₀ •
          (F.identity i i' γ).map (orderedDerivative A (fun y => U y i') x) =
      ∑ i₀ : Fin 2, chartInvJacobian ⇑((F.piece p).material t).symm x a₀ i₀ •
        (F.identity i i' γ).map
          (∑ d ∈ Finset.Icc 1 (F.identity i i' γ).maxOrder, ∑ I : DerivativeWord2 (d - 1),
            F.dimFlux ν e E p c i i' γ d I t (((F.piece p).material t).symm x)
              (e⁻¹ • ((F.piece p).material t).symm x) i₀ •
            orderedDerivative I (fun y => U ((F.piece p).material t y) i')
              (((F.piece p).material t).symm x)) := by
    intro i' γ
    rw [sum_sum_smul_map (F.identity i i' γ).map,
      constituent_orders_flux_of_contDiff F ν e E p c K hdesc t hU hrD i i' γ x a₀]
    exact map_sum_dir _ _ _ _ _
  refine Eq.trans (Finset.sum_congr rfl fun _ _ => Finset.sum_comm) ?_
  refine Eq.trans (Finset.sum_congr rfl fun i' _ => Finset.sum_congr rfl fun γ _ => hγ i' γ) ?_
  refine Eq.trans (sum_dep_pull _ _) ?_
  refine Finset.sum_congr rfl fun i₀ _ => ?_
  simp only [labelEdgeFlux, Finset.smul_sum]

/-- **The flux term as a weighted sum over the pieces**, for a `C^r` field with `D ≤ r + 1`:
for a finite set `S` of pieces containing the active ones, the `a₀`-component of the flux term
is `∑_{p ∈ S} ϖ_p(t) ∑_{i₀} K_p(x)_{a₀ i₀} G_p(ψ_p x)_{i₀}`. -/
theorem edgeFlux_eq_sum_pieces_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) {t : ℝ} (S : Finset P)
    (hS : ∀ p, F.weight p t ≠ 0 → p ∈ S) {r : ℕ} {U : Vec 2 → ∀ i, h i}
    (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι) (x : Vec 2) (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        edgeCoefficient F ν e E actual K i i' d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => U y i') x) a₀ =
      ∑ p ∈ S, F.weight p t • ∑ i₀ : Fin 2,
        chartInvJacobian ⇑((F.piece p).material t).symm x a₀ i₀ •
          labelEdgeFlux F ν e E p (actual p) t (fun y => U ((F.piece p).material t y)) i
            (((F.piece p).material t).symm x) i₀ := by
  simp only [edgeCoefficient_apply_sum_pieces F ν e E actual K S hS]
  rw [sum_sum_pieces]
  exact Finset.sum_congr rfl fun p _ => congrArg (F.weight p t • ·)
    (pieceEdgeFlux_eq_label_of_contDiff F ν e E p (actual p) K hdesc t hU hrD i x a₀)

/-- **A single active piece**: if only `p₀` carries weight at `t`, the flux term of a `C^r` field
with `D ≤ r + 1` is `∑_{i₀} K_{p₀}(x)_{a₀ i₀} G_{p₀}(ψ_{p₀} x)_{i₀}`. -/
theorem edgeFlux_single_piece_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (actual : ∀ p, Ctx p) (K : ι → ℕ) (hdesc : F.IsDescending K) {t : ℝ} {p₀ : P}
    (hw₀ : F.weight p₀ t = 1) (hw : ∀ p, p ≠ p₀ → F.weight p t = 0) {r : ℕ}
    {U : Vec 2 → ∀ i, h i} (hU : ContDiff ℝ (r : ℕ∞) U) (hrD : D ≤ r + 1) (i : ι) (x : Vec 2)
    (a₀ : Fin 2) :
    ∑ i' : ι, ∑ d : admissibleOrders K D i i',
        edgeCoefficient F ν e E actual K i i' d t x
          (WithLp.toLp 2 fun word : DerivativeWord2 (d.1 - 1) =>
            orderedDerivative word (fun y => U y i') x) a₀ =
      ∑ i₀ : Fin 2, chartInvJacobian ⇑((F.piece p₀).material t).symm x a₀ i₀ •
        labelEdgeFlux F ν e E p₀ (actual p₀) t (fun y => U ((F.piece p₀).material t y)) i
          (((F.piece p₀).material t).symm x) i₀ := by
  have hS : ∀ p, F.weight p t ≠ 0 → p ∈ ({p₀} : Finset P) := fun p hp =>
    Finset.mem_singleton.mpr (by
      by_contra hne
      exact hp (hw p hne))
  rw [edgeFlux_eq_sum_pieces_of_contDiff F ν e E actual K hdesc {p₀} hS hU hrD i x a₀,
    Finset.sum_singleton, hw₀, one_smul]

end Family

section Lift

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] {D : ℕ} {P : Type*} {Ctx : P → Type*}

/-- **One constituent of the lifted flux**, for a `C^r` label field with `D ≤ r + 1` and
`lam ρ⁻¹ = E⁻¹`: its lifted flux over the orders `2 ≤ d ≤ D_γ` is `(e/ν)` times its label flux
over the orders `[1, D_γ]`. -/
theorem liftFlux_constituent_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ) (p : P)
    (c : Ctx p) (cℓ lam ρ s : ℝ) (hlam : lam * ρ⁻¹ = E⁻¹) (hν : ν ≠ 0) {r : ℕ}
    {V : Vec 2 → ∀ i, h i} (hV : ContDiff ℝ (r : ℕ∞) V) (hrD : D ≤ r + 1) (v u : ι)
    (γ₀ : F.Γ v u) (y : Vec 2) (k : Fin 2) :
    ∑ d ∈ Finset.Icc 2 (F.identity v u γ₀).maxOrder, ∑ α : DerivativeWord2 (d - 1),
        (F.flux p c v u γ₀ d α (cℓ * s) (lam • ρ⁻¹ • y) (e⁻¹ • y) k) •
          (F.identity v u γ₀).map (e ^ (d - 1) • orderedDerivative α V y u) =
      (e / ν) • (F.identity v u γ₀).map
        (∑ d ∈ Finset.Icc 1 (F.identity v u γ₀).maxOrder, ∑ I : DerivativeWord2 (d - 1),
          F.dimFlux ν e E p c v u γ₀ d I (cℓ * s) y (e⁻¹ • y) k •
            orderedDerivative I (fun y' => V y' u) y) := by
  have hX : lam • ρ⁻¹ • y = E⁻¹ • y := by rw [smul_smul, hlam]
  have h12 : ∑ d ∈ Finset.Icc 1 (F.identity v u γ₀).maxOrder, ∑ I : DerivativeWord2 (d - 1),
      F.dimFlux ν e E p c v u γ₀ d I (cℓ * s) y (e⁻¹ • y) k •
        orderedDerivative I (fun y' => V y' u) y =
      ∑ d ∈ Finset.Icc 2 (F.identity v u γ₀).maxOrder, ∑ I : DerivativeWord2 (d - 1),
        F.dimFlux ν e E p c v u γ₀ d I (cℓ * s) y (e⁻¹ • y) k •
          orderedDerivative I (fun y' => V y' u) y := by
    refine sum_Icc_one_eq_two _ _ ?_
    refine Finset.sum_eq_zero fun I _ => ?_
    rw [dimFlux_one_eq_zero F ν e E p c v u γ₀ I (cℓ * s) y (e⁻¹ • y), Pi.zero_apply, zero_smul]
  rw [hX, h12]
  simp only [map_sum, map_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun α _ => ?_
  have hdm := Finset.mem_Icc.mp hd
  have hle := (F.identity v u γ₀).le_D
  have hj : orderedDerivative α V y u = orderedDerivative α (fun y' => V y' u) y :=
    AVRegularity.ChartTransport.orderedDerivative_apply α
      (hV.of_le (by exact_mod_cast (show d - 1 ≤ r by omega))) u y
  rw [hj]
  congr 1
  simp only [ChartedFamily.dimFlux, ChartedFamily.slowFlux, Pi.smul_apply, smul_eq_mul]
  exact (lift_scale ν e _ hν hdm.1).symm

/-- **The lifted pulse flux is the label edge flux**, for a `C^r` label field with `D ≤ r + 1`:
the inner flux of the lifted fiber is `(e/ν) G(y)_k`, `G = labelEdgeFlux F ν e E p c (cℓ s) V v`.
-/
theorem liftFlux_eq_labelEdgeFlux_of_contDiff (F : ChartedFamily ι h D P Ctx) (ν e E : ℝ)
    (p : P) (c : Ctx p) (cℓ lam ρ s : ℝ) (hlam : lam * ρ⁻¹ = E⁻¹) (hν : ν ≠ 0) {r : ℕ}
    {V : Vec 2 → ∀ i, h i} (hV : ContDiff ℝ (r : ℕ∞) V) (hrD : D ≤ r + 1) (v : ι) (y : Vec 2)
    (k : Fin 2) :
    ∑ u : ι, ∑ d : Finset.Icc 2 D, ((liftEdges cℓ lam (F.fiber p c) v u d).map fun γ =>
        ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α s (ρ⁻¹ • y) (e⁻¹ • y) k) •
          γ.map (e ^ (d.1 - 1) • orderedDerivative α V y u)).sum =
      (e / ν) • labelEdgeFlux F ν e E p c (cℓ * s) V v y k := by
  have hsum : ∀ u : ι, ∑ d : Finset.Icc 2 D, ((liftEdges cℓ lam (F.fiber p c) v u d).map
      fun γ => ∑ α : DerivativeWord2 (d.1 - 1), (γ.coeff α s (ρ⁻¹ • y) (e⁻¹ • y) k) •
        γ.map (e ^ (d.1 - 1) • orderedDerivative α V y u)).sum =
      ∑ γ₀ : F.Γ v u, ∑ d ∈ Finset.Icc 2 (F.identity v u γ₀).maxOrder,
        ∑ α : DerivativeWord2 (d - 1),
          (F.flux p c v u γ₀ d α (cℓ * s) (lam • ρ⁻¹ • y) (e⁻¹ • y) k) •
            (F.identity v u γ₀).map (e ^ (d - 1) • orderedDerivative α V y u) := fun u =>
    Eq.trans (Finset.sum_congr rfl fun d _ => liftFlux_list F p c cℓ lam ρ e s V v u d y k)
      (sum_Icc_subtype_ite_gen D (fun γ₀ : F.Γ v u => (F.identity v u γ₀).maxOrder)
        (fun γ₀ => (F.identity v u γ₀).le_D)
        (fun γ₀ n => ∑ α : DerivativeWord2 (n - 1),
          (F.flux p c v u γ₀ n α (cℓ * s) (lam • ρ⁻¹ • y) (e⁻¹ • y) k) •
            (F.identity v u γ₀).map (e ^ (n - 1) • orderedDerivative α V y u)))
  refine Eq.trans (Finset.sum_congr rfl fun u _ => hsum u) ?_
  simp only [labelEdgeFlux, Finset.smul_sum]
  exact Finset.sum_congr rfl fun u _ => Finset.sum_congr rfl fun γ₀ _ =>
    liftFlux_constituent_of_contDiff F ν e E p c cℓ lam ρ s hlam hν hV hrD v u γ₀ y k

end Lift
end

end AVRegularity.CycleComparison.Reconstruction
end
end

section
@[expose] public noncomputable section
open Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.CycleComparison.Reconstruction

/-! **The inverse-Piola pull-back of a flux** (exact Piola transports flux by `(DΦR)∘Φ⁻¹`, as in
`cycle_residual_chart_transport`). For an area-preserving
chart `χ` with inverse `ψ`, the pull-back `F'(y) = (Dχ(y))⁻¹ F(χ y)` (`invPiola`) is the flux
whose Piola transport is `F` (`piola_invPiola`), so its divergence is the pull-back of the
divergence (`div_invPiola`). Read at the slow variable, the coarse field of the pull-back is `ρ`
times the chart-frame field of the divergence of `F` (`coarseField_invPiola`): the lifted
coarse flux of a charted pulse is the straight lifted coarse flux of the pull-back. -/

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The inverse-Piola pull-back `F'(y) = (Dχ(y))⁻¹ F(χ y)`. -/
def invPiola (χ : Vec 2 → Vec 2) (F : Vec 2 → Fin 2 → E) (y : Vec 2) (k : Fin 2) : E :=
  ∑ l : Fin 2, (jacMatrix χ y)⁻¹ k l • F (χ y) l

/-- The Piola transport of the inverse-Piola pull-back is the flux. -/
theorem piola_invPiola {χ ψ : Vec 2 → Vec 2} (hχψ : ∀ x, χ (ψ x) = x)
    (hd : ∀ y, (jacMatrix χ y).det = 1) (F : Vec 2 → Fin 2 → E) (x : Vec 2) (k : Fin 2) :
    ∑ l : Fin 2, jacMatrix χ (ψ x) k l • invPiola χ F (ψ x) l = F x k := by
  have hJ : jacMatrix χ (ψ x) * (jacMatrix χ (ψ x))⁻¹ = 1 :=
    Matrix.mul_nonsing_inv _ (by rw [hd]; exact isUnit_one)
  simp only [invPiola]
  calc ∑ l : Fin 2, jacMatrix χ (ψ x) k l • ∑ l' : Fin 2,
        (jacMatrix χ (ψ x))⁻¹ l l' • F (χ (ψ x)) l'
      = ∑ l' : Fin 2, (∑ l : Fin 2, jacMatrix χ (ψ x) k l * (jacMatrix χ (ψ x))⁻¹ l l') •
          F (χ (ψ x)) l' := by
        simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
        exact Finset.sum_comm
    _ = ∑ l' : Fin 2, (jacMatrix χ (ψ x) * (jacMatrix χ (ψ x))⁻¹) k l' • F x l' := by
        simp only [Matrix.mul_apply, hχψ x]
    _ = F x k := by
        rw [hJ]
        simp [Matrix.one_apply]

/-- **The divergence of the inverse-Piola pull-back is the pull-back of the divergence.** -/
theorem div_invPiola {χ ψ : Vec 2 → Vec 2} (hχ : ContDiff ℝ (⊤ : ℕ∞) χ)
    (hψ : Differentiable ℝ ψ) (hψχ : ∀ y, ψ (χ y) = y) (hχψ : ∀ x, χ (ψ x) = x)
    (hd : ∀ y, (jacMatrix χ y).det = 1) {F : Vec 2 → Fin 2 → E}
    (hF' : ∀ l, Differentiable ℝ (fun y => invPiola χ F y l)) (y : Vec 2) :
    ∑ k : Fin 2, fderiv ℝ (fun y' => invPiola χ F y' k) y (basisVec k) =
      ∑ k : Fin 2, fderiv ℝ (fun x => F x k) (χ y) (basisVec k) := by
  have h := AVRegularity.CycleComparison.Charts.piola_forward_vector hχ hψ hψχ hχψ hd hF' (χ y)
  have he : ∀ k : Fin 2, (fun x' => ∑ l : Fin 2, jacMatrix χ (ψ x') k l •
      invPiola χ F (ψ x') l) = fun x' => F x' k := fun k =>
    funext fun x' => piola_invPiola hχψ hd F x' k
  simp only [he, hψχ y] at h
  exact h.symm

/-- **The coarse field of the inverse-Piola pull-back** is `ρ` times the chart-frame field of the
divergence of the flux. -/
theorem coarseField_invPiola {ι : Type*} [Fintype ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, NormedSpace ℝ (h i)] {χ ψ : ℝ → Vec 2 → Vec 2}
    {ℓ ρ s : ℝ} (hχ : ContDiff ℝ (⊤ : ℕ∞) (χ (ℓ ^ 2 * s)))
    (hψ : Differentiable ℝ (ψ (ℓ ^ 2 * s))) (hψχ : ∀ y, ψ (ℓ ^ 2 * s) (χ (ℓ ^ 2 * s) y) = y)
    (hχψ : ∀ x, χ (ℓ ^ 2 * s) (ψ (ℓ ^ 2 * s) x) = x)
    (hd : ∀ y, (jacMatrix (χ (ℓ ^ 2 * s)) y).det = 1) (F : ℝ → Vec 2 → Fin 2 → ∀ i, h i)
    (hF' : ∀ l, Differentiable ℝ (fun y => invPiola (χ (ℓ ^ 2 * s)) (F (ℓ ^ 2 * s)) y l))
    (X : Vec 2) :
    CoarseFluxDiff.coarseField (fun t y k => invPiola (χ t) (F t) y k) ℓ ρ s X =
      ρ • ∑ k : Fin 2, fderiv ℝ (fun x => F (ℓ ^ 2 * s) x k) (χ (ℓ ^ 2 * s) (ρ • X))
        (basisVec k) := by
  unfold CoarseFluxDiff.coarseField
  have hc : ∀ k : Fin 2, fderiv ℝ (fun X' => invPiola (χ (ℓ ^ 2 * s)) (F (ℓ ^ 2 * s))
      (ρ • X') k) X (basisVec k) = ρ • fderiv ℝ (fun y => invPiola (χ (ℓ ^ 2 * s))
        (F (ℓ ^ 2 * s)) y k) (ρ • X) (basisVec k) := fun k =>
    fderiv_comp_smul_apply ρ ((hF' k) (ρ • X)) (basisVec k)
  simp only [hc]
  rw [← Finset.smul_sum, div_invPiola hχ hψ hψχ hχψ hd hF' (ρ • X)]

end AVRegularity.CycleComparison.Reconstruction
end
end
