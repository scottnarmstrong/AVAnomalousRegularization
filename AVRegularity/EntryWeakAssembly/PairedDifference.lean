-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighPassage
import AVRegularity.CycleComparison.Error.Main
import AVRegularity.Proofs.WeakGen.Reduction.PassageEnergy
import AVRegularity.EntryWeakAssembly.PairedForcingCost

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs

/-! **The paired difference, step 2: the energy of the truncated high family `Uhi M`.**
`weak_entry_raw_energy_at_offset` bounds the strong energy of the truncations to `K_w`; the
cost of the forcing is stated with the truncation to `K_w + m`, which is also at most the
energy at the reserves (`weakHigh_inner_le`). -/

section
open AVRegularity.WeakEntryProofs.Assembly Providers.WeakGen.Reduction

section High

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
  {x : WeakEntryData plan C} {g : WeakEntryStages x} {s : WeakEntrySchedule g}
  {f : Vec 2 → ℝ} {θ : ℝ → Vec 2 → ℝ} {r : WeakEntryReduced s θ} {m : ℕ}
  {Uhi : ∀ i, WeakReductionFamily g m i} {Whi : ∀ i, WeakReductionLift g m i}

/-- The strong energy of the truncation to `K_w + m` is at most the energy at the reserves. -/
theorem pd_high_le_inner :
    strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
        (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (s.tq (x.M + 1)) (x.a + A.T₀)
        (weakHighFamily g m (Uhi x.M)) (weakHighLift g m (Whi x.M)) ≤
      (∑ v : CompIn (g.stage x.M).comps,
      ENNReal.ofReal (weakMass x.D A.Nw A.Jw A.η₀ v.1)⁻¹ *
        ((⨆ t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀), ENNReal.ofReal
            (factorialNormSq (x.D.termRStar (plan.radius R) x.M) (Uhi x.M v t).val)) +
          ENNReal.ofReal (x.D.κ x.M) * ∫⁻ τ in Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
            ENNReal.ofReal (gradFactorialNormSq (x.D.termRStar (plan.radius R) x.M)
              (Whi x.M v τ).val))) ^ (1 / 2 : ℝ) := by
  unfold strongEnergy
  refine ENNReal.rpow_le_rpow (Finset.sum_le_sum fun v _ => ?_) (by norm_num)
  refine mul_le_mul_right (add_le_add (iSup₂_mono fun t ht => ?_) (mul_le_mul_right ?_ _)) _
  · exact ENNReal.ofReal_le_ofReal
      (CycleComparison.Error.factorialNormSq_truncateTorusHk_le _ _ _)
  · refine lintegral_mono fun τ => ?_
    exact ENNReal.ofReal_le_ofReal
      (CycleComparison.Error.gradFactorialNormSq_truncateTorusHk_le
        (weakReductionReserve_kw R m v.1) _ _)

/-- **The energy of the truncated high family** at the offset `m ≤ m_max(R)`: at most
`C_raw(R, C, m) ‖f‖₂`. -/
theorem pd_high_energy_le (hA : WeakEntryPassageEnergyStatement plan)
    (hB : WeakEntryQuietTraceHighStatement plan) (hm : m ≤ weakEntryMmax R)
    (hθ : IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ)
    (hfam : WeakHigherFamilies s θ r m Uhi Whi) :
    strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
        (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (s.tq (x.M + 1)) (x.a + A.T₀)
        (weakHighFamily g m (Uhi x.M)) (weakHighLift g m (Whi x.M)) ≤
      ENNReal.ofReal (weakEntryRawConst plan R C m * Real.sqrt (l2NormSq f)) := by
  obtain ⟨hCp, hAb⟩ := weakEntryPassageConst_spec (C := C) hA hm
  obtain ⟨hCq, hBb⟩ := weakEntryQuietConst_spec (C := C) hB hm
  refine pd_high_le_inner.trans ?_
  refine (ENNReal.rpow_le_rpow (weakHigh_inner_le hCp hCq hAb hBb hθ hfam) (by norm_num)).trans ?_
  have hL : 0 ≤ l2NormSq f := integral_nonneg fun _ => sq_nonneg _
  have hQ := mul_nonneg hCp hCq
  have hb : 0 ≤ ((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) : ℝ) + 2 := by positivity
  have hy : 0 ≤ (((weakStoredWordBudget A.Nw A.Rw ^ A.Jw : ℕ) : ℝ) + 2) *
      ((weakEntryPassageConst plan R C m * weakEntryQuietConst plan R C m) ^ A.Jw *
        (2 * l2NormSq f)) := by positivity
  rw [ENNReal.ofReal_rpow_of_nonneg hy (by norm_num), ← Real.sqrt_eq_rpow,
    rawEnergy_sqrt_eq _ _ _ _ hb hQ]
  unfold weakEntryRawConst
  exact le_of_eq (by ring_nf)

end High
end

/-! **The paired difference of the weak entry from its ingredients**.

`weak_entry_paired_difference_of_ingredients` assembles
* the forcing equation (`WeakEntryPairedForcingStatement`): `W = U - V` solves the paired system with the forcing
  `F` of `weakPairedForcing`;
* the forced energy (`pd_forced_strongEnergy`): `𝓔(W)² ≤ (24/κ_M) ∫ |F|²_{ρ_M}`;
* the forcing cost (`WeakEntryPairedForcingCostStatement`): `∫ |F|² ≤ C_mom ε^{2(χ_w + σ_w L)} κ_M 𝓔_hi(U)²`
  (the factor `κ_M` cancels the `1/κ_M` of the forced energy);
* the passage energy and the quiet trace bound (through `pd_high_energy_le`): `𝓔_hi(U) ≤ C_raw(R, C, J_w N_w + L) ‖f‖₂`.
The constant is `C_diff = √(24 C_mom) · C_raw(R, C, J_w N_w + L)`, with `C_mom` the classically
chosen constant of the forcing cost. `weak_entry_paired_difference` is the unconditional corollary.

Special cases: `f = 0` gives `𝓔_hi = 0` and the bound `0`; a stage without identities has
`F = 0`; `C_mom = 0` is allowed. -/

section
open AVRegularity.WeakEntryProofs.Assembly Providers.WeakGen.Reduction AVRegularity.CoupledEnergy.Variational

/-- The conclusion of the forcing cost at a constant `Cmom` (the body of `WeakEntryPairedForcingCostStatement`
after the existential). -/
def WeakEntryPairedForcingCostBound (plan : WeakEntryGluePlan)
    (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedPlanOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (Cmom : ℝ) : Prop :=
  ∀ {x : WeakEntryData plan C} (g : WeakEntryStages x) (s : WeakEntrySchedule g)
      (law : BirthLaw) (hm : law.rootMass = g.rootM)
      (f : Vec 2 → ℝ) (θ : ℝ → Vec 2 → ℝ),
      IsWeakSolutionOn (streamVel (x.D.Φ (x.M + A.Jw))) (x.D.κ x.M) x.a (x.a + A.T₀) f θ →
    ∀ (r : WeakEntryReduced s θ)
      (Uk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)),
      g.Gw.IsRegSolution x.P (fun _ => isoPairedKernel 0 R.nW) (fun _ => isoPairedKernel 0 R.nW)
        A.φ₀ A.hφ₀ (x.D.κ x.M) (streamVel (x.D.Φ x.M)) R.Kw (s.tq (x.M + 1)) (x.a + A.T₀)
        (fun v => rerootFamily g.relabel (r.Ur x.M) v (s.tq (x.M + 1))) (fun _ _ => 0)
        (fun _ _ => 0) (rerootFamily g.relabel (r.Ur x.M)) (rerootFamily g.relabel (r.Urw x.M))
        Uk →
    ∀ (Uhi : ∀ i, Providers.WeakGen.Reduction.WeakReductionFamily g (A.Jw * A.Nw + R.L) i)
      (Whi : ∀ i, Providers.WeakGen.Reduction.WeakReductionLift g (A.Jw * A.Nw + R.L) i),
      (∀ v : CompIn (g.stage x.M).comps, ∀ t ∈ Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
        truncateTorusHk (Providers.WeakGen.Reduction.weakReductionReserve_kw_le R
          (A.Jw * A.Nw + R.L) v.1) (Uhi x.M v t) = r.Ur x.M v t) →
      (∀ v : CompIn (g.stage x.M).comps,
        ∀ᵐ t ∂(volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀))),
          truncateTorusHk (Nat.succ_le_succ (Providers.WeakGen.Reduction.weakReductionReserve_kw_le R
            (A.Jw * A.Nw + R.L) v.1)) (Whi x.M v t) = r.Urw x.M v t) →
      ∫⁻ t in Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀),
          ENNReal.ofReal (massNormSq (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law)
            (fun v => (weakPairedForcing hcommon hok g s law hm
              (rerootFamily g.relabel (r.Urw x.M)) Uk v t).val)) ≤
        ENNReal.ofReal (Cmom * x.D.eps x.M ^ (2 * (weakChi B.α B.q A.η₀ + A.σw * R.L)) *
          x.D.κ x.M) *
          strongEnergy (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M)
            (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (s.tq (x.M + 1)) (x.a + A.T₀)
            (weakHighFamily g (A.Jw * A.Nw + R.L) (Uhi x.M))
            (weakHighLift g (A.Jw * A.Nw + R.L) (Whi x.M)) ^ 2

open scoped Classical in
/-- The constant `C_mom` of the forcing cost, chosen classically (`0` if none exists). -/
def pdCmom (plan : WeakEntryGluePlan) (hcommon : WeakEntryCommonOK plan)
    (hok : WeakEntryPairedPlanOK plan) {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (C : WeakEntryAllocation R (plan.radius R)) : ℝ :=
  if h : ∃ Cmom : ℝ, 0 ≤ Cmom ∧ WeakEntryPairedForcingCostBound plan hcommon hok R C Cmom then
    Classical.choose h else 0

/-- **The constant `C_diff(R, C) = √(24 C_mom) · C_raw(R, C, J_w N_w + L)`.** -/
def pdConst (plan : WeakEntryGluePlan) (hcommon : WeakEntryCommonOK plan)
    (hok : WeakEntryPairedPlanOK plan) {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    (R : WeakPassageRequest A) (C : WeakEntryAllocation R (plan.radius R)) : ℝ :=
  Real.sqrt (24 * pdCmom plan hcommon hok R C) * weakEntryRawConst plan R C (weakEntryMmax R)

/-- **Plan condition of the paired difference** (lower bounds on `CK` and the level floor, an
upper bound on the radius): the plan conditions of the passage energy (which contains `WeakEntryPairedPlanOK`)
and of the quiet trace bound (which contains the radius comparison and the floors at the lifted request of the
offset `J_w N_w + L`), the plan condition of the forcing cost, and `C_diff(R, C) ≤ CK`. -/
def WeakEntryPairedDiffPlanOK (plan : WeakEntryGluePlan) : Prop :=
  WeakEntryPassageEnergyPlanOK plan ∧ WeakEntryQuietTraceHighPlanOK plan ∧
  WeakEntryPairedForcingCostPlanOK plan ∧
  ∀ (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedPlanOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)), pdConst plan hcommon hok R C ≤ plan.CK R C

theorem pdCmom_spec {plan : WeakEntryGluePlan} {hcommon : WeakEntryCommonOK plan}
    {hok : WeakEntryPairedPlanOK plan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
    {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}
    (h : ∃ Cmom : ℝ, 0 ≤ Cmom ∧ WeakEntryPairedForcingCostBound plan hcommon hok R C Cmom) :
    0 ≤ pdCmom plan hcommon hok R C ∧
      WeakEntryPairedForcingCostBound plan hcommon hok R C (pdCmom plan hcommon hok R C) := by
  rw [pdCmom, dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

/-- The real arithmetic of the assembly. -/
theorem pd_arith {κ ε e Cm Cr Lf CK I : ℝ} (hκ : 0 < κ) (hε : 0 < ε) (hCm : 0 ≤ Cm)
    (hCr : 0 ≤ Cr) (hLf : 0 ≤ Lf) (hI : I ≤ Cm * ε ^ (2 * e) * κ * (Cr * Lf) ^ 2)
    (hCK : Real.sqrt (24 * Cm) * Cr ≤ CK) :
    Real.sqrt ((24 / κ) * I) ≤ CK * ε ^ e * Lf := by
  have hpow : ε ^ (2 * e) = (ε ^ e) ^ 2 := by
    rw [← Real.rpow_natCast (ε ^ e) 2, ← Real.rpow_mul hε.le]
    congr 1
    push_cast
    ring
  have hεe : 0 ≤ ε ^ e := (Real.rpow_pos_of_pos hε _).le
  have hs0 : 0 ≤ Real.sqrt (24 * Cm) := Real.sqrt_nonneg _
  have hY : 0 ≤ CK * ε ^ e * Lf :=
    mul_nonneg (mul_nonneg ((mul_nonneg hs0 hCr).trans hCK) hεe) hLf
  refine Real.sqrt_le_iff.2 ⟨hY, ?_⟩
  have h1 : (24 / κ) * I ≤ 24 * Cm * (ε ^ e) ^ 2 * (Cr * Lf) ^ 2 := by
    calc (24 / κ) * I ≤ (24 / κ) * (Cm * ε ^ (2 * e) * κ * (Cr * Lf) ^ 2) :=
          mul_le_mul_of_nonneg_left hI (by positivity)
      _ = 24 * Cm * (ε ^ e) ^ 2 * (Cr * Lf) ^ 2 := by rw [hpow]; field_simp
  refine h1.trans ?_
  have h2 : Real.sqrt (24 * Cm) * Cr * ε ^ e * Lf ≤ CK * ε ^ e * Lf :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCK hεe) hLf
  have h3 := pow_le_pow_left₀ (mul_nonneg (mul_nonneg (mul_nonneg hs0 hCr) hεe) hLf) h2 2
  have h4 : (Real.sqrt (24 * Cm) * Cr * ε ^ e * Lf) ^ 2 =
      24 * Cm * (ε ^ e) ^ 2 * (Cr * Lf) ^ 2 := by
    have := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 24 * Cm)
    calc _ = (Real.sqrt (24 * Cm)) ^ 2 * (ε ^ e) ^ 2 * (Cr * Lf) ^ 2 := by ring
      _ = _ := by rw [this]
  rw [h4] at h3
  exact h3

/-- The integral of a nonnegative function with a lintegral bound `a E²` and `E ≤ b`. -/
theorem pd_integral_bound {μ : Measure ℝ} (Fm : ℝ → ℝ) (hFnn : ∀ t, 0 ≤ Fm t) {a b : ℝ}
    {E : ℝ≥0∞} (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hcost : ∫⁻ t, ENNReal.ofReal (Fm t) ∂μ ≤ ENNReal.ofReal a * E ^ 2)
    (hE : E ≤ ENNReal.ofReal b) : ∫ t, Fm t ∂μ ≤ a * b ^ 2 := by
  have hI : ENNReal.ofReal (∫ t, Fm t ∂μ) ≤ ∫⁻ t, ENNReal.ofReal (Fm t) ∂μ := by
    by_cases hi : Integrable Fm μ
    · rw [ofReal_integral_eq_lintegral_ofReal hi (Filter.Eventually.of_forall hFnn)]
    · rw [integral_undef hi]; simp
  have h2 : ENNReal.ofReal (∫ t, Fm t ∂μ) ≤ ENNReal.ofReal (a * b ^ 2) := by
    refine hI.trans (hcost.trans ?_)
    rw [ENNReal.ofReal_mul ha, ENNReal.ofReal_pow hb]
    exact mul_le_mul_right (pow_le_pow_left' hE 2) _
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg ha (sq_nonneg b))).1 h2

/-- **The paired difference from its four ingredients.** -/
theorem weak_entry_paired_difference_of_ingredients (plan : WeakEntryGluePlan)
    (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedDiffPlanOK plan)
    (hA : WeakEntryPairedForcingStatement plan) (hB : WeakEntryPairedForcingCostStatement plan)
    (hP2A : WeakEntryPassageEnergyStatement plan) (hP2B : WeakEntryQuietTraceHighStatement plan) :
    WeakEntryPairedDifferenceStatement plan := by
  intro B A R C x g s law hm hr f θ hθ r V Vw Vk hV
  have hokP : WeakEntryPairedPlanOK plan := hok.1.1
  obtain ⟨Uk, hU⟩ := weak_entry_raw_solution plan g s f θ hθ r
  obtain ⟨hcoup, -⟩ := hA hcommon hokP g s law hm f θ hθ r Uk hU V Vw Vk hV
  have hFmem : ∀ v, MemLp (weakPairedForcing hcommon hokP g s law hm
      (rerootFamily g.relabel (r.Urw x.M)) Uk v) 2
      (volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀))) :=
    fun v => (weakPairedOp hcommon hokP g s law hm).liftForcing_memLp Uk _ hU.2.2.2.2.1 hU.2.1 v
  have hforced := pd_forced_strongEnergy hcommon hokP g s law hm _ hFmem _ _ hcoup
  obtain ⟨Uhi, Whi, hfam⟩ := weakReduction_higher_families (m := A.Jw * A.Nw + R.L) hcommon s f θ
    hθ r
  obtain ⟨hC0, hCb⟩ := pdCmom_spec (hB hcommon hokP hok.2.2.1 R C)
  have hcost := hCb g s law hm f θ hθ r Uk hU Uhi Whi
    (fun v t ht => hfam.2.2.1 x.M le_rfl (Nat.le_add_right _ _) v t ht)
    (fun v => hfam.2.2.2 x.M le_rfl (by have := A.Jw_pos; omega) v)
  have hhigh := pd_high_energy_le (m := A.Jw * A.Nw + R.L) hP2A hP2B le_rfl hθ hfam
  have hCr0 : 0 ≤ weakEntryRawConst plan R C (A.Jw * A.Nw + R.L) := by
    unfold weakEntryRawConst; positivity
  have hLf : 0 ≤ Real.sqrt (l2NormSq f) := Real.sqrt_nonneg _
  have hεpos : 0 < x.D.eps x.M := by rw [weakPaired_eps_eq]; exact weakPaired_eps_pos x
  have hκ0 := weakPaired_kappa_pos x
  have hpe := Real.rpow_nonneg hεpos.le (2 * (weakChi B.α B.q A.η₀ + A.σw * R.L))
  have hIle := pd_integral_bound _ (fun t => massNormSq_nonneg _ _
    (fun v => weakPaired_mass_pos g law hm v) _) (by positivity)
    (mul_nonneg hCr0 hLf) hcost hhigh
  exact hforced.trans (ENNReal.ofReal_le_ofReal (pd_arith hκ0 hεpos hC0 hCr0 hLf hIle
    (hok.2.2.2 hcommon hokP R C)))

/-- **The paired difference** (`WeakEntryPairedDifferenceStatement`), unconditional: the four
ingredients are proved. -/
theorem weak_entry_paired_difference (plan : WeakEntryGluePlan)
    (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedDiffPlanOK plan) :
    WeakEntryPairedDifferenceStatement plan :=
  weak_entry_paired_difference_of_ingredients plan hcommon hok (weak_entry_paired_forcing plan)
    (weak_entry_paired_forcing_cost plan) (weakEntryPassageEnergy hcommon hok.1)
    (weak_entry_quiet_trace_high hcommon hok.2.1)
end

end AVRegularity.WeakEntryProofs
end
