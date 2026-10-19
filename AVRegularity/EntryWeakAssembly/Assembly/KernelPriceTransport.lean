-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.Assembly.PassageInterfaces
import AVRegularity.Construction.EntryScales.TerminalCore

@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! One-passage comparison: the literal error is a zero-data forced solution of
 the incoming system. The forcing estimate and component-sup energy estimate are
 separate obligations. No mass-sup estimate is substituted for strong energy. -/

/-- All supplied comparison objects, with exactly the
representative and window hypotheses. No residual equation or estimate is assumed here. -/
structure WeakComparisonInput {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {c : WeakPassageInstance plan R} (r : WeakPassageRun c) (i : ℕ) where
  CcR : (j : ℕ) → ℤ → ℕ → ℕ → LiftCoeff (CompIn (c.stage j).comps) (fun v => ScalarH v.1.root)
  lifts : ∀ j, c.M < j → j ≤ c.M + A.Jw →
    IsWeakReadoutLifts j A.Nw (A.Jw * A.Rw) R.sX R.sZ (c.stage j) (CcR j)
  Φ : ℝ
  aU : ℝ → CompIn (c.stage (i - 1)).comps → Vec 2 → ℝ
  e : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root)
  ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 1 (ScalarH v.1.root)
  mass_bound : ∀ t ∈ Set.Icc (r.tq (i + 1)) (r.a + A.T₀),
    weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
      (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ Φ
  representative : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
    IsClassicalRep (r.Ur (i - 1) v t) (aU t v) A.Lw
  identity : ∀ v, ∀ t ∈ Set.Icc (r.tq i) (r.a + A.T₀),
    (e v t).toFunction.jet (valueIndex2 0) =ᵐ[volume.restrict unitCube]
      fun x => (truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)).toFunction.jet (valueIndex2 0) x -
        weakGluedLift i A.Nw (A.Jw * A.Rw) (c.stage i) (CcR i) t
          (weakReadoutStep i A.η₀ (c.stage i) (c.stage (i - 1)) (aU t)) v x
  truncation : ∀ v, ∀ᵐ t ∂volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)),
    truncateTorusHk (Nat.le_succ 0) (ew v t) = e v t
  /-- The lift orders are above the plan's floor. -/
  sX_ge : plan.liftFloor A ≤ R.sX
  sZ_ge : plan.liftFloor A ≤ R.sZ
  /-- The scalar solution starts strictly before the root time. -/
  start : r.a < r.tq (c.M + A.Jw + 1)

/-- **The system of the comparison error at the cap `1 + J_wN_w`**: the kernel weak
solution of the stage `c.stage i` at order zero on the window `[t_i, T]`, with the width-zero
kernels, the diffusivity `κ_M` and the drift `Φ_i`, the flux summed over the orders
`d ≤ 1 + J_wN_w` and the kernel lift `Y` at the order `J_wN_w`. It is `IsRegSolution` with the
ambient cap `D_m` of the instance replaced by `1 + J_wN_w`: the identities of a weak stage have
order at most `1 + J_wN_w` (`weak_comparison_physCoeff_zero_above`), so it is the same equation,
and `D_m` does not enter the regularity asked of the solution. -/
def WeakErrSol {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A} (c : WeakPassageInstance plan R)
    (r : WeakPassageRun c) (i : ℕ)
    (f : ∀ v : CompIn (c.stage i).comps, TorusHk 0 (ScalarH v.1.root))
    (F : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (u : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (w : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (0 + 1) (ScalarH v.1.root))
    (Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ →
      TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)) : Prop :=
  IsKernelWeakSolutionTorus (ι := CompIn (c.stage i).comps) (h := fun v => ScalarH v.1.root)
    (Γ := (c.stage i).fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
    (c.D.κ c.M) (r.tq i) (r.a + A.T₀) (streamVel (c.D.Φ i)) 0 (1 + A.Jw * A.Nw)
    (fun v u γ d => (c.stage i).physCoeff v u γ d.1)
    (fun _ u _ => ContinuousLinearMap.id ℝ (ScalarH u.1.root))
    (fun v u γ => (c.stage i).sysS c.P (fun _ => isoPairedKernel 0 R.nW)
      (fun _ => isoPairedKernel 0 R.nW) A.φ₀ A.hφ₀ v u γ) f F g u w Y

/-- Component forcing cost: sum after each component's L1-in-time scalar norm.
This order supports the component suprema in the strong energy. -/
def weakComparisonForcingCost {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {c : WeakPassageInstance plan R} (r : WeakPassageRun c) (i : ℕ)
    (F : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root)) : ℝ≥0∞ :=
  (∑ v, (ENNReal.ofReal (weakMass c.D A.Nw A.Jw A.η₀ v.1))⁻¹ *
    ((ENNReal.ofReal (c.D.κ c.M))⁻¹ *
      (∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀), ENNReal.ofReal (factorialNormSq (plan.radius R * c.D.eps i) (F v t).val)) +
      (∫⁻ t in Set.Icc (r.tq i) (r.a + A.T₀),
        ENNReal.ofReal (Real.sqrt (factorialNormSq (plan.radius R * c.D.eps i) (g v t).val))) ^ 2)) ^ (1 / 2 : ℝ)

/-- The exact weak residual, including initial vanishing and both gluing
terms, with the old incoming coupling left in the equation. Its proof uses the
quiet margin midpoint and trimmed quiet overlaps, never untrimmed independence. -/
def WeakComparisonResidualStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A},
    A.Pw + 2 * B.q ^ A.Jw + 1 + 2 < A.Nw * (B.q - 1) →
    A.Pw + 2 * B.q ^ A.Jw + 1 + B.q ^ A.Jw + 1 < 2 * weakAStar B.α B.q * (A.Rw + 1) →
  ∀ (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → ∀ h : WeakComparisonInput r i,
    ∃ (F : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
      (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root))
      (Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
      (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) ∧
      WeakErrSol c r i (fun _ => 0)
        (fun v t => truncateTorusHk (Nat.zero_le _) (F v t))
        (fun v t => truncateTorusHk (Nat.zero_le _) (g v t)) h.e h.ew Y ∧
      weakComparisonForcingCost r i F g ≤
        ENNReal.ofReal (plan.forceC R * c.D.eps c.M ^ (A.Pw + 2 * B.q ^ A.Jw + 1) * h.Φ)

/-- The zero-data energy for an actual weak stage, retaining each row's
supremum before summation. The forcings are measurable in time: the cost is a
lower integral otherwise, and the statement would be false. The forcing reserve covers all derivative losses along source paths. A mere
order-zero forcing estimate would be false for higher differential sources.
The constant and reserve are fixed before Dm or the family size. -/
def WeakComparisonEnergyStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw →
  ∀ (F : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)))
    (g : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk (plan.forcingOrder R) (ScalarH v.1.root))
    (e : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 0 (ScalarH v.1.root))
    (ew : ∀ v : CompIn (c.stage i).comps, ℝ → TorusHk 1 (ScalarH v.1.root))
    (Y : ∀ v u (_ : (c.stage i).fam.Γ v u), ℝ → TorusHk (0 + (1 + A.Jw * A.Nw) - 1) (ScalarH u.1.root)),
    (∀ v, AEStronglyMeasurable (F v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) →
    (∀ v, AEStronglyMeasurable (g v) (volume.restrict (Set.Icc (r.tq i) (r.a + A.T₀)))) →
    WeakErrSol c r i (fun _ => 0)
      (fun v t => truncateTorusHk (Nat.zero_le _) (F v t))
      (fun v t => truncateTorusHk (Nat.zero_le _) (g v t)) e ew Y →
    strongEnergy 1 (c.D.κ c.M) (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1)
      (r.tq i) (r.a + A.T₀) e ew ≤ ENNReal.ofReal (plan.energyC R) * weakComparisonForcingCost r i F g

/-- Exact comparison from residual production and component energy. -/
theorem weak_passage_comparison_at_of_ingredients (plan : WeakPassagePlan)
    (hres : WeakComparisonResidualStatement plan) (henergy : WeakComparisonEnergyStatement plan) :
    WeakPassageComparisonAt 1 400 := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : WeakCoefficientBase := ⟨α, s, hα₀, hα₁, hs₀, hs₁, q, hq, ζ, hζ⟩
  refine ⟨plan.baseFloor B, plan.base_ge B, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hsm hnn hmass hsupp bw hbw hbwsmall Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hηsmall Nw Rw Lw hN hLw hNorder hRorder σw hσ hσsmall
  let A : WeakCoefficientPhysical B :=
    ⟨Λ, φ₀, hφ₀, hsm, hnn, hmass, hsupp, bw, hbw, hbwsmall, Jw, τ, T₀, Pw, η₀,
      hJ, hτ, hτT, hP, hη, hηsmall, Nw, Rw, Lw, hN, hLw, σw, hσ, hσsmall⟩
  refine ⟨plan.momentFloor A, plan.liftFloor A, plan.liftFloor A, ?_⟩
  intro L Kw sX sZ nW kReq hG hL hSX hSZ hn hK
  let R : WeakPassageRequest A := ⟨L, Kw, sX, sZ, nW, kReq, hG, hn, hK⟩
  let kW := { EntryWeakProofs.requestedWeakAllocation kReq L with c₀ := plan.radius R }
  have hk : IsWeakAllocation kW kReq L := (EntryWeakProofs.requestedWeakAllocation_valid kReq L hG).2
  refine ⟨plan.radius R, plan.energyC R * plan.forceC R, 0, 0, 0, 0, kW,
    plan.radius_pos R, rfl, hk, ?_⟩
  intro j₀ hcar
  refine ⟨plan.levelFloor R j₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hΦ hκ hterm Dm hDm P stage CcR hstage hlifts a f θ hθ tq Ur Urw Urk hred hstart
  let c : WeakPassageInstance plan R :=
    ⟨hΛ, hL, j₀, hcar, M, hM, D, hDα, hDq, hDΛ, hDζ, hΦ, hκ, hterm, Dm, hDm, P, stage, hstage⟩
  let r : WeakPassageRun c := ⟨a, f, θ, hθ, tq, Ur, Urw, Urk, hred⟩
  intro i hi hit Φ aU e ew hbound hrep hid htrunc
  let h : WeakComparisonInput r i :=
    ⟨CcR, hlifts, Φ, aU, e, ew, hbound, hrep, hid, htrunc, hSX, hSZ, hstart⟩
  obtain ⟨F, g, Y, hFm, hgm, hsol, hcost⟩ := hres hNorder hRorder c r i hi hit h
  calc
    _ ≤ ENNReal.ofReal (plan.energyC R) * weakComparisonForcingCost r i F g :=
      henergy c r i hi hit F g e ew Y hFm hgm hsol
    _ ≤ ENNReal.ofReal (plan.energyC R) *
        ENNReal.ofReal (plan.forceC R * D.eps M ^ (Pw + 2 * q ^ Jw + 1) * Φ) :=
      mul_le_mul' le_rfl hcost
    _ = _ := by rw [← ENNReal.ofReal_mul (plan.energyC_nonneg R)]; congr 1; ring


/-- The statement, at the carrier constants `CH = 1`, `Υ = 400`. -/
theorem weak_passage_comparison_of_ingredients (plan : WeakPassagePlan)
    (hres : WeakComparisonResidualStatement plan) (henergy : WeakComparisonEnergyStatement plan) :
    WeakPassageComparisonStatement :=
  weakPassageComparison_of_at le_rfl (by norm_num)
    (weak_passage_comparison_at_of_ingredients plan hres henergy)

/-! Quiet trace at the middle of a slow quiet margin. The coefficient statement uses only
its middle half, with enough room for the whole finer history; it is not a claim
of fast independence on the untrimmed quiet set. -/

/-- Parent-scale coefficient bounds on the backward heat interval inside the middle
half of the chosen slow quiet margin. The matrix has both mass-conjugated Schur bounds.
All orders are finite and chosen in the plan before Dm or the construction. -/
def WeakParentQuietMarginBounds {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) : Prop :=
  0 < c.D.eps (i - 1) ∧ 0 < c.D.κ c.M ∧
  r.tq (i + 1) ≤ r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M ∧
  r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2 ≤
    r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M ∧
  ∃ b : CompIn (c.stage i).comps → CompIn (c.stage i).comps → ℝ,
    (∀ v u, 0 ≤ b v u) ∧ (∀ v, ∑ u, b v u ≤ plan.coeffC R) ∧
    (∀ u, ∑ v, b v u ≤ plan.coeffC R) ∧
    (∀ v u (γ : (c.stage i).fam.Γ v u) d, 2 ≤ d → d ≤ c.Dm →
      ∀ t ∈ Set.Icc (r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M) (r.tq i),
        ContDiff ℝ (plan.jetOrder R) ((c.stage i).physCoeff v u γ d t)) ∧
    ∀ v u,
      ENNReal.ofReal (Real.sqrt (weakMass c.D A.Nw A.Jw A.η₀ u.1 /
        weakMass c.D A.Nw A.Jw A.η₀ v.1)) *
      ∑ γ : (c.stage i).fam.Γ v u, ∑ d ∈ Finset.Icc 2 c.Dm,
        coefficientSeminorm (c.D.eps (i - 1)) (plan.jetOrder R)
          (r.tq i - c.D.eps (i - 1) ^ 2 / c.D.κ c.M) (r.tq i)
          ((c.stage i).physCoeff v u γ d) *
          (ENNReal.ofReal (c.D.κ c.M * c.D.eps (i - 1) ^ (d - 2)))⁻¹ ≤ ENNReal.ofReal (b v u)

/-- The pinned quiet margin lies inside the scalar solution window; its middle half is
strictly after the preceding passage time. This uses the upper bound on the final quiet time. -/
def WeakQuietWindow {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ) : Prop :=
  r.a ≤ r.tq (i + 1) ∧ r.tq i ≤ r.a + A.T₀ ∧
  r.tq (i + 1) < r.tq i ∧
  (∃ l : ℤ, r.tq i = ((l : ℝ) + 1 / 2) * ocTauPP c.D.α c.D.q c.D.Λ i) ∧
  Set.Icc (r.tq i - ocTauP c.D.α c.D.q c.D.Λ i / 2) (r.tq i) ⊆
    Set.Icc (r.tq (i + 1)) (r.a + A.T₀)

/-- Routine time geometry, discharged from the actual reduction rather than assumed
as an extra quiet-time hypothesis. No independence on an untrimmed set is asserted. -/
theorem weak_quiet_window {plan : WeakPassagePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ)
    (hi : c.M < i) (hit : i ≤ c.M + A.Jw) : WeakQuietWindow c r i := by
  have hΛ : 1 ≤ c.D.Λ := by
    rw [c.base_eq]
    exact (show 1 ≤ 128 by omega).trans ((plan.base_ge B).trans c.base_ge)
  have hleft := weakReduction_quietTimes_mem_window hΛ r.reduction (i + 1)
    (by omega) (by omega)
  have hright := weakReduction_quietTimes_mem_window hΛ r.reduction i
    (by omega) (by omega)
  have hp := Velocity.Jets.ocTauP_pos (α := c.D.α) (q := c.D.q)
    (Λ := c.D.Λ) (m := i) hΛ
  have hstep := r.reduction.2.2.2 i hi hit
  refine ⟨hleft.1, hright.2, ?_, hstep.1, ?_⟩
  · exact (lt_add_of_pos_right _ hp).trans_le hstep.2.1
  · intro t ht
    exact ⟨by linarith [ht.1, hstep.2.1], ht.2.trans hright.2⟩

/-- Coefficient layer: uniform parent-scale jets on a quiet margin interior, with the backward
heat interval fitting inside it. This requires the history-quiet child identities
and Cauchy/Piola conversion, not merely vanishing of the current pulse. -/
def WeakQuietCoefficientStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → WeakQuietWindow c r i → WeakParentQuietMarginBounds c r i

/-- Smoothing layer: finite ordered-source-path smoothing, from the mass bound of the
whole vector to its parent-scale factorial trace. No estimate on an individual
forced row is substituted for this vector estimate. -/
def WeakQuietSmoothingStatement (plan : WeakPassagePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (r : WeakPassageRun c) (i : ℕ),
    c.M < i → i ≤ c.M + A.Jw → WeakQuietWindow c r i → WeakParentQuietMarginBounds c r i →
    ∀ bound : ℝ,
      (∀ t ∈ Set.Icc (r.tq (i + 1)) (r.tq i),
        weightedNorm 1 (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
          (fun v => truncateTorusHk (Nat.zero_le R.Kw) (r.Ur i v t)) ≤ bound) →
      weightedNorm (plan.radius R * c.D.eps (i - 1))
        (fun v => weakMass c.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1)
        (fun v => r.Ur i v (r.tq i)) ≤ plan.traceC R * bound

/-- Exact quiet trace from its coefficient and smoothing layers. -/
theorem weak_passage_quiet_trace_at_of_ingredients (plan : WeakPassagePlan)
    (hcoeff : WeakQuietCoefficientStatement plan) (hsmooth : WeakQuietSmoothingStatement plan) :
    WeakPassageQuietTraceAt 1 400 := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : WeakCoefficientBase := ⟨α, s, hα₀, hα₁, hs₀, hs₁, q, hq, ζ, hζ⟩
  refine ⟨plan.baseFloor B, plan.base_ge B, ?_⟩
  intro Λ hΛ φ₀ hφ₀ hsm hnn hmass hsupp bw hbw hbwsmall Jw τ T₀ Pw η₀ hJ hτ hτT hP hη hηsmall Nw Rw Lw hN hLw σw hσ hσsmall
  let A : WeakCoefficientPhysical B :=
    ⟨Λ, φ₀, hφ₀, hsm, hnn, hmass, hsupp, bw, hbw, hbwsmall, Jw, τ, T₀, Pw, η₀,
      hJ, hτ, hτT, hP, hη, hηsmall, Nw, Rw, Lw, hN, hLw, σw, hσ, hσsmall⟩
  refine ⟨plan.momentFloor A, ?_⟩
  intro L Kw sX sZ nW kReq hG hL hn hK
  let R : WeakPassageRequest A := ⟨L, Kw, sX, sZ, nW, kReq, hG, hn, hK⟩
  let kW := { EntryWeakProofs.requestedWeakAllocation kReq L with c₀ := plan.radius R }
  have hk : IsWeakAllocation kW kReq L := (EntryWeakProofs.requestedWeakAllocation_valid kReq L hG).2
  refine ⟨plan.radius R, plan.traceC R, 0, 0, 0, 0, kW, plan.radius_pos R, rfl, hk, ?_⟩
  intro j₀ hcar
  refine ⟨plan.levelFloor R j₀, ?_⟩
  intro M hM D hDα hDq hDΛ hDζ hΦ hκ hterm Dm hDm P stage hstage a f θ hθ tq Ur Urw Urk hred
  let c : WeakPassageInstance plan R :=
    ⟨hΛ, hL, j₀, hcar, M, hM, D, hDα, hDq, hDΛ, hDζ, hΦ, hκ, hterm, Dm, hDm, P, stage, hstage⟩
  let r : WeakPassageRun c := ⟨a, f, θ, hθ, tq, Ur, Urw, Urk, hred⟩
  intro i hi hit bound hbound
  exact hsmooth c r i hi hit (weak_quiet_window c r i hi hit) (hcoeff c r i hi hit (weak_quiet_window c r i hi hit)) bound hbound


/-- The statement, at the carrier constants `CH = 1`, `Υ = 400`. -/
theorem weak_passage_quiet_trace_of_ingredients (plan : WeakPassagePlan)
    (hcoeff : WeakQuietCoefficientStatement plan) (hsmooth : WeakQuietSmoothingStatement plan) :
    WeakPassageQuietTraceStatement :=
  weakPassageQuietTrace_of_at le_rfl (by norm_num)
    (weak_passage_quiet_trace_at_of_ingredients plan hcoeff hsmooth)

end AVRegularity.WeakEntryProofs.Assembly
end

section
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Uniform constants and thresholds for the weak stored ledger, before the carrier and flow. -/

open Filter Topology

/-- Decay and unit original-order price at one uniform threshold. -/
structure WeakStoredLedgerData {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) where
  C : ℝ
  positive : 0 < C
  threshold : ℕ
  total : 128 ≤ A.Λ → ∀ M, threshold ≤ M → ∀ D : OCData,
    D.α = B.α → D.q = B.q → D.Λ = A.Λ → D.term = M →
    IsOCBandChain B.α B.q A.Λ B.ζ M D.κ → ∀ (Dm : ℕ) (j₀ : ℕ) (P : ProvParams)
      (sX sZ : ℕ) (stage : ℕ → GenStage D ScalarH Dm A.bw j₀),
    IsWeakConstruction D P ⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ M A.Jw
      (D.termRW A.σw M) 0 stage →
    weakStoredTotal (stage M) A.Nw A.Jw A.η₀ ≤ C * D.eps M ^ weakChi B.α B.q A.η₀
  price : 128 ≤ A.Λ → ∀ M, threshold ≤ M →
    ocEpsilon B.q A.Λ (M + 1) ≤ ocEpsilon B.q A.Λ M ^ (1 + A.σw)

/-- The finite recurrence closes when its uniform final majorant is at most one. -/
theorem exists_weakStoredLedgerData {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) :
    Nonempty (WeakStoredLedgerData A) := by
  obtain ⟨Ce, hCe, heddy⟩ := exists_weakStoredEddy_constant B A
  let Q : ℝ := weakStoredPassageBudget A.Nw A.Jw A.Rw
  let C : ℝ := (2 * Q) ^ A.Jw * Ce
  have hQ : 0 < Q := by
    dsimp [Q]
    exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one (weakStoredPassageBudget_one_le A.Nw A.Jw A.Rw))
  have hC : 0 < C := mul_pos (pow_pos (by positivity) _) (zero_lt_one.trans_le hCe)
  by_cases hΛ : 128 ≤ A.Λ
  · have hχ := weakChi_pos B.hα₀ B.hq.1 B.hq.2.1 A.η₀_small
    obtain ⟨Ms, hMs⟩ := eventually_atTop.mp
      ((EntryScales.epsilon_rpow_tendsto_zero B.hq.1 hΛ hχ).eventually
        (gt_mem_nhds (inv_pos.mpr hC)))
    have hgap : 0 < B.q - 1 - A.σw := sub_pos.mpr (A.σw_small.trans_le (min_le_right _ _))
    obtain ⟨Mp, hMp⟩ := eventually_atTop.mp
      ((EntryScales.epsilon_rpow_tendsto_zero B.hq.1 hΛ hgap).eventually
        (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2)))
    refine ⟨⟨C, hC, max Ms (max Mp 0), ?_, ?_⟩⟩
    · intro _ M hM D hα hq hbase ht hband Dm j₀ P sX sZ stage hc
      have heps (i : ℕ) : 0 < D.eps i := Construction.Stream.ocEpsilon_pos (by rw [hbase]; omega)
      have hsmall : C * D.eps M ^ weakChi B.α B.q A.η₀ ≤ 1 := by
        have hh := mul_le_mul_of_nonneg_left (hMs M ((le_max_left _ _).trans hM)).le hC.le
        rw [mul_inv_cancel₀ hC.ne'] at hh
        simpa only [OCData.eps, hq, hbase] using hh
      have hh := weakConstruction_storedTotal_bound P
        (⟨A.Nw, A.Rw, sX, sZ, A.η₀, M + A.Jw⟩ : WeakMenu) M A.Jw 0
        (D.termRW A.σw M) stage hc A.Nw_pos A.Jw_pos heps
        (Ce * D.eps M ^ weakChi B.α B.q A.η₀)
        (mul_nonneg (zero_lt_one.trans_le hCe).le (Real.rpow_nonneg (heps M).le _))
        (fun i hi _ => heddy M D hα hq hbase ht hband hΛ i hi)
        (by simpa only [C, Q, mul_assoc] using hsmall)
      simpa only [C, Q, mul_assoc] using hh
    · intro _ M hM
      have hx := (Scales.epsilon_basic (m := M) B.hq.1 hΛ).1
      have hs : 2 * ocEpsilon B.q A.Λ M ^ (B.q - 1 - A.σw) ≤ 1 := by
        have hh := mul_le_mul_of_nonneg_left
          (hMp M ((le_max_left _ _).trans ((le_max_right _ _).trans hM))).le
          (by norm_num : (0 : ℝ) ≤ 2)
        norm_num at hh ⊢
        exact hh
      have hstep := Scales.epsilon_q_step B.hq.1 B.hq.2.1 hΛ (Nat.succ_pos M)
      calc
        ocEpsilon B.q A.Λ (M + 1) ≤ 2 * ocEpsilon B.q A.Λ M ^ B.q := hstep
        _ = (2 * ocEpsilon B.q A.Λ M ^ (B.q - 1 - A.σw)) *
            ocEpsilon B.q A.Λ M ^ (1 + A.σw) := by
          rw [mul_assoc, ← Real.rpow_add hx]
          congr 2
          ring
        _ ≤ _ := mul_le_of_le_one_left (Real.rpow_nonneg hx.le _) hs
  · exact ⟨⟨C, hC, 0, fun hh => (hΛ hh).elim, fun hh => (hΛ hh).elim⟩⟩

def weakStoredLedgerData {B : WeakCoefficientBase} (A : WeakCoefficientPhysical B) :
    WeakStoredLedgerData A := Classical.choice (exists_weakStoredLedgerData A)

end AVRegularity.WeakEntryProofs.Assembly
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.Construction.Preservation.Ledger
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Finite ordered-source-path smoothing: analytic path domination, positive
ledger budgets, and dimension-free finite Schur summation. -/

/-- Scalar path prices and the maximal retained source depth. Both precede Dm. -/
structure WeakQuietPathPrices where
  depth : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ
  scalar : ∀ {B} {A : WeakCoefficientPhysical B}, WeakPassageRequest A → ℕ → ℝ
  nonneg : ∀ {B} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A) n, 0 ≤ scalar R n

/-- The positive path matrix includes the empty scalar path on the diagonal. -/
def weakQuietPathKernel {plan : WeakPassagePlan} (prices : WeakQuietPathPrices)
    {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ)
    (v u : CompIn (c.stage i).comps) : ℝ :=
  (if v = u then prices.scalar R 0 else 0) +
    ∑ n ∈ Finset.range (prices.depth R), prices.scalar R (n + 1) *
      ∑ π : StagePath (c.stage i) (n + 1),
        if (π.step (Fin.last n)).1 = v ∧ (π.step 0).2.1 = u then
          pathWeight (weakStoredEdgeWeight (c.stage i) A.Nw A.Jw A.η₀) π else 0

/-- Enlarging paths to arbitrary stored-edge lists gives this explicit price. -/
def weakQuietPathCost {plan : WeakPassagePlan} (prices : WeakQuietPathPrices)
    {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ) : ℝ :=
  prices.scalar R 0 + ∑ n ∈ Finset.range (prices.depth R),
    prices.scalar R (n + 1) * weakStoredTotal (c.stage i) A.Nw A.Jw A.η₀ ^ (n + 1)

/-- The purely finite path-price calculation, independent of solutions. -/
def WeakQuietPathSchurStatement (plan : WeakPassagePlan) (prices : WeakQuietPathPrices) : Prop :=
  ∀ {B} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    (c : WeakPassageInstance plan R) (i : ℕ),
    (∀ v u, 0 ≤ weakQuietPathKernel prices c i v u) ∧
    0 ≤ weakQuietPathCost prices c i ∧
    (∀ v, ∑ u, weakQuietPathKernel prices c i v u ≤ weakQuietPathCost prices c i) ∧
    (∀ u, ∑ v, weakQuietPathKernel prices c i v u ≤ weakQuietPathCost prices c i)

/-- Dimension-free finite Schur summation of nonnegative row norms. -/
def QuietFiniteSchurStatement : Prop :=
  ∀ {ι : Type} [Fintype ι] (K : ι → ι → ℝ) (x y : ι → ℝ) (C : ℝ),
    0 ≤ C → (∀ v u, 0 ≤ K v u) → (∀ v, 0 ≤ y v) →
    (∀ v, y v ≤ ∑ u, K v u * x u) →
    (∀ v, ∑ u, K v u ≤ C) → (∀ u, ∑ v, K v u ≤ C) →
    Real.sqrt (∑ v, y v ^ 2) ≤ C * Real.sqrt (∑ u, x u ^ 2)

end AVRegularity.WeakEntryProofs.Assembly
end

section
open Homogenization AVRegularity.Sobolev AVRegularity.Construction.Preservation.Ledger
namespace AVRegularity.WeakEntryProofs.Assembly

/-! Re-rooting and enlarging a record witness do not change physical coefficients.
The positive stored-weight total controls a relabeled kernel matrix without counting identities. -/

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The scalar physical coefficient has no dependence on record witness size or root labels. -/
theorem weakScaledRootStage_physCoeff (G : GenStage D ScalarH Dm b j₀)
    (C : ℝ) (hC : 1 ≤ C) (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) :
    (weakScaledRootStage G C hC).physCoeff (weakRootEquiv G.comps v)
      (weakRootEquiv G.comps u)
      (relabelWeakEdge G _ (weakRootEquiv G.comps) v u γ) d = G.physCoeff v u γ d := by
  let e := weakRootEquiv G.comps
  change G.physCoeff (e.symm (e v)) (e.symm (e u)) (cast _ γ) d = G.physCoeff v u γ d
  have bridge {v u v' u' : CompIn G.comps} (hv : v = v') (hu : u = u')
      (hΓ : G.fam.Γ v u = G.fam.Γ v' u') (γ : G.fam.Γ v u) :
      G.physCoeff v' u' (cast hΓ γ) d = G.physCoeff v u γ d := by
    subst v'
    subst u'
    rfl
  exact bridge (e.symm_apply_apply v).symm (e.symm_apply_apply u).symm _ γ

/-- A matrix dominated by a relabeled positive stored sum has both Schur bounds. -/
theorem weakRelabel_schur_of_stored (N J : ℕ) (η : ℝ)
    (G Gw : GenStage D ScalarH Dm b j₀) (e : CompIn G.comps ≃ CompIn Gw.comps)
    (A : ℝ) (hA : 0 ≤ A)
    (B : CompIn Gw.comps → CompIn Gw.comps → ℝ)
    (hB : ∀ v u, B (e v) (e u) ≤ A * Real.sqrt (weakMass D N J η u.1 /
      weakMass D N J η v.1) * ∑ γ : G.fam.Γ v u, (G.fam.identity v u γ).record.size) :
    SchurBound (A * weakStoredTotal G N J η) B := by
  classical
  let W (v u : CompIn G.comps) := ∑ γ : G.fam.Γ v u,
    weakStoredEdgeWeight G N J η ⟨v, u, γ⟩
  have hW (v u) : 0 ≤ W v u := Finset.sum_nonneg fun γ _ =>
    weakStoredEdgeWeight_nonneg G N J η ⟨v, u, γ⟩
  have hb (v u) : B (e v) (e u) ≤ A * W v u := by
    simpa only [W, weakStoredEdgeWeight, ← Finset.mul_sum, mul_assoc] using hB v u
  have ht : (∑ v, ∑ u, W v u) = weakStoredTotal G N J η := by
    simp only [W, weakStoredTotal, LedgerEdge, Fintype.sum_sigma]
  have hr (v) : (∑ u, W v u) ≤ weakStoredTotal G N J η := by
    rw [← ht]
    exact Finset.single_le_sum (fun v _ => Finset.sum_nonneg (fun u _ => hW v u))
      (Finset.mem_univ v)
  have hc (u) : (∑ v, W v u) ≤ weakStoredTotal G N J η := by
    rw [← ht, Finset.sum_comm]
    exact Finset.single_le_sum (fun u _ => Finset.sum_nonneg (fun v _ => hW v u))
      (Finset.mem_univ u)
  constructor
  · intro v'
    obtain ⟨v, rfl⟩ := e.surjective v'
    rw [← e.sum_comp]
    calc
      _ ≤ A * ∑ u, W v u := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun u _ => hb v u
      _ ≤ A * weakStoredTotal G N J η := mul_le_mul_of_nonneg_left (hr v) hA
  · intro u'
    obtain ⟨u, rfl⟩ := e.surjective u'
    rw [← e.sum_comp]
    calc
      _ ≤ A * ∑ v, W v u := by
        rw [Finset.mul_sum]
        exact Finset.sum_le_sum fun v _ => hb v u
      _ ≤ A * weakStoredTotal G N J η := mul_le_mul_of_nonneg_left (hc u) hA

end AVRegularity.WeakEntryProofs.Assembly
end
