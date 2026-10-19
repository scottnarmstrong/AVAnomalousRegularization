-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryWeakAssembly.QuietWordIntegral
import AVRegularity.EntryTerminal.Ingredients.LiftField.LiftField
import AVRegularity.Applications.Global.CompactRangeMain
public import AVRegularity.Proofs.WeakGen.Reduction.QuietTraceHighRestriction
public import AVRegularity.KernelEnergy.TorusKernelFiniteTraceLimit
public import AVRegularity.Definitions.Finite.FiniteLiftBridge
public import AVRegularity.EntryWeakAssembly.FullReadoutLocalReserves

section
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal
namespace AVRegularity.WeakEntryProofs.Assembly

/-! **The readout bound from its two layers**.

For a family `z` of the order `L_w + 5` with classical representatives `a_z` of the order
`L_w + 3`:
1. the representation with zero base and the single profile `compField π a_z` at the label `ε_M`
   is a representation at `ε_M` of the order `L_w + 3`; its size is the profile norm of the
   field, `≤ C_B ε_M^{-(1+s)} |z|_{c_K ε_M, L_w+5; π}` (`WeakReadoutBaseSizeStatement`, a case of
   the `SobolevProfileStatement` of the iteration argument);
2. the represented lift (`weak_lift_rep`, read on the entry data as `WeakEntryLiftRepAt`) gives a
   representation at `ε_{M+J_w}` of the order `3` whose root readout is `Ww t a_z`, of size at most
   `C_w` times the size of the input;
3. the root readout has norm `≤ 1` and `scalar_rep_readout` turns the size into `CsNormLe`, with
   the factor `3`;
4. `ε_M^{-(1+s)} ≤ ε_{M+J_w}^{-(1+s)}`.
The constant is `3 C_w C_B`. -/


/-- The level tail of `weak_lift_rep` on the entry data at the order `L_w + 3`, with the constant
`Cw`. -/
def WeakEntryLiftRepAt {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} (s : WeakEntrySchedule g) (law : BirthLaw) (Cw : ℝ) : Prop :=
  ∀ (t : ℝ) (a : Vec 2 → ∀ v : CompIn g.Gw.comps, ScalarH v.1.root)
    (rT : Representation (CompSpace g.Gw.comps)),
    IsRepresentationAt (x.D.eps x.M) (A.Lw + 3) rT → rT.value = compField (g.Gw.mass law) a →
    ∃ rW : Representation (CompSpace (g.stage (x.M + A.Jw)).comps),
      IsRepresentationAt (x.D.eps (x.M + A.Jw)) 3 rW ∧
      (∀ y, compReadoutCLM (fun v => weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) (rW.value y) =
        s.W x.M t (fun v y' => a y' (g.relabel v)) y) ∧
      representedSize B.s 3 (x.D.eps (x.M + A.Jw)) rW ≤
        ENNReal.ofReal Cw * representedSize B.s (A.Lw + 3) (x.D.eps x.M) rT

/-- The partial derivatives of the zero field vanish. -/
theorem partialDerivative_zero_field {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (α : Fin 2 → ℕ) : partialDerivative α (0 : Vec 2 → H) = 0 := by
  have h : ∀ e : Vec 2, (fun G : Vec 2 → H => fun x => fderiv ℝ G x e) (0 : Vec 2 → H) = 0 := by
    intro e
    funext x
    simp
  unfold partialDerivative
  rw [Function.iterate_fixed (h (basisVec 0)) (α 0)]
  exact Function.iterate_fixed (h (basisVec 1)) (α 1)

/-- The size of the representation with zero base and one profile at the label `e` is the
profile norm of the profile. -/
theorem representedSize_single_profile {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    (s : ℝ) (K : ℕ) (e : ℝ) (F : Vec 2 → H) :
    representedSize s K e (⟨0, [(F, e)]⟩ : Representation H) = profileNorm e K s F := by
  have h0 : supNorm (0 : Vec 2 → H) = 0 := by simp [supNorm]
  have h1 : profileSeminorm e K s (0 : Vec 2 → H) = 0 := by
    unfold profileSeminorm
    refine Finset.sum_eq_zero fun α _ => ?_
    rw [partialDerivative_zero_field, h0, mul_zero]
  have h2 : holderSeminorm s (0 : Vec 2 → H) = 0 := by simp [holderSeminorm]
  simp only [representedSize, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, h0, h1, h2,
    add_zero, zero_add]

/-- **The readout bound on one entry datum**, from the profile norm at the order `L_w + 3` with
the constant `CB` and the represented lift with the constant `Cw`. -/
theorem weak_readout_bound_of_lift {plan : WeakEntryGluePlan} {B : WeakCoefficientBase}
    {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    {g : WeakEntryStages x} (s : WeakEntrySchedule g) (law : BirthLaw)
    {CB Cw : ℝ} (hCB : 0 ≤ CB) (hCw : 0 ≤ Cw)
    (hbase : ∀ (e : ℝ), 0 < e → e ≤ 1 →
      ∀ (z : ∀ v : CompIn g.Gw.comps, TorusHk (A.Lw + 5) (ScalarH v.1.root))
        (az : CompIn g.Gw.comps → Vec 2 → ℝ), (∀ v, IsClassicalRep (z v) (az v) (A.Lw + 3)) →
      profileNorm e (A.Lw + 3) B.s (compField (g.Gw.mass law) (fun y v => az v y)) ≤
        ENNReal.ofReal (CB * e ^ (-(1 + B.s)) *
          weightedNorm (plan.radius R * e) (g.Gw.mass law) (fun _ => 1) z))
    (hlift : WeakEntryLiftRepAt s law Cw)
    (t : ℝ) (z : ∀ v : CompIn g.Gw.comps, TorusHk (A.Lw + 5) (ScalarH v.1.root))
    (az : CompIn g.Gw.comps → Vec 2 → ℝ) (haz : ∀ v, IsClassicalRep (z v) (az v) (A.Lw + 3)) :
    CsNormLe B.s (weakEntryReadoutMap s t az)
      (3 * (Cw * CB) * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (x.D.termRStar (plan.radius R) x.M) (g.Gw.mass law) (fun _ => 1) z) := by
  have hΛ : 128 ≤ x.D.Λ := by rw [x.base_eq]; exact x.base128
  have hΛ1 : 1 ≤ x.D.Λ := (by norm_num : 1 ≤ 128).trans hΛ
  have hq : 1 < x.D.q := by rw [x.q_eq]; exact B.hq.1
  have heM : 0 < x.D.eps x.M := Construction.Stream.ocEpsilon_pos hΛ1
  have heM1 : x.D.eps x.M ≤ 1 := ocEpsilon_le_one hΛ1 _
  have heJ : 0 < x.D.eps (x.M + A.Jw) := Construction.Stream.ocEpsilon_pos hΛ1
  have hanti : x.D.eps (x.M + A.Jw) ≤ x.D.eps x.M :=
    Applications.eps_antitone hq hΛ (Nat.le_add_right _ _)
  have hs1 : B.s < 1 := by have h1 := B.hs₁; have h2 := B.hα₀; linarith
  have hFc := EntryTerminal.Ingredients.compField_contDiff_periodic (g.Gw.mass law) (A.Lw + 3) az
    (fun v => (haz v).2.1) (fun v => (haz v).2.2.1)
  have hrT : IsRepresentationAt (x.D.eps x.M) (A.Lw + 3)
      (⟨0, [(compField (g.Gw.mass law) (fun y v => az v y), x.D.eps x.M)]⟩ :
        Representation (CompSpace g.Gw.comps)) := by
    refine ⟨heM, heM1, contDiff_const, fun _ _ => rfl, fun p hp => ?_⟩
    obtain rfl := List.mem_singleton.mp hp
    exact ⟨hFc.1, hFc.2, le_rfl, heM1⟩
  have hval : (⟨0, [(compField (g.Gw.mass law) (fun y v => az v y), x.D.eps x.M)]⟩ :
      Representation (CompSpace g.Gw.comps)).value =
      compField (g.Gw.mass law) (fun y v => az v y) := by
    funext y
    simp only [Representation.value, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      Pi.zero_apply, zero_add, add_zero]
  obtain ⟨rW, hrW, hread, hsize⟩ := hlift t (fun y v => az v y) _ hrT hval
  rw [representedSize_single_profile] at hsize
  have hW := hbase (x.D.eps x.M) heM heM1 z az haz
  have hWn0 : 0 ≤ weightedNorm (plan.radius R * x.D.eps x.M) (g.Gw.mass law) (fun _ => 1) z :=
    Real.sqrt_nonneg _
  have hpowM : 0 ≤ x.D.eps x.M ^ (-(1 + B.s)) := Real.rpow_nonneg heM.le _
  have hA0 : 0 ≤ Cw * (CB * x.D.eps x.M ^ (-(1 + B.s)) *
      weightedNorm (plan.radius R * x.D.eps x.M) (g.Gw.mass law) (fun _ => 1) z) :=
    mul_nonneg hCw (mul_nonneg (mul_nonneg hCB hpowM) hWn0)
  have hsizeA : representedSize B.s 3 (x.D.eps (x.M + A.Jw)) rW ≤
      ENNReal.ofReal (Cw * (CB * x.D.eps x.M ^ (-(1 + B.s)) *
        weightedNorm (plan.radius R * x.D.eps x.M) (g.Gw.mass law) (fun _ => 1) z)) := by
    refine hsize.trans ?_
    rw [ENNReal.ofReal_mul hCw]
    exact mul_le_mul' le_rfl hW
  have hroot : (g.stage (x.M + A.Jw)).comps = {⟨0, []⟩} := g.construction.2.1.2.1
  have hcs := Finite.Assembly.scalar_rep_readout B.s B.hs₀ hs1 (x.D.eps (x.M + A.Jw)) _ hA0 rW hrW
    (compReadoutCLM (fun v : CompIn (g.stage (x.M + A.Jw)).comps =>
      weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1))
    (Finite.Assembly.weak_root_readout_norm x.D A.Nw A.Jw A.η₀ _ hroot) hsizeA
  have hfun : (fun y => compReadoutCLM (fun v : CompIn (g.stage (x.M + A.Jw)).comps =>
      weakMass x.D A.Nw A.Jw A.η₀ v.1) (fun _ => 1) (rW.value y)) =
      weakEntryReadoutMap s t az := by
    funext y
    rw [hread y]
    rfl
  rw [hfun] at hcs
  refine Applications.csNormLe_mono hcs ?_
  have hpow : x.D.eps x.M ^ (-(1 + B.s)) ≤ x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) :=
    Real.rpow_le_rpow_of_nonpos heJ hanti (by have h := B.hs₀; linarith)
  have hCC : 0 ≤ Cw * CB := mul_nonneg hCw hCB
  have hstep : Cw * CB * x.D.eps x.M ^ (-(1 + B.s)) *
        weightedNorm (plan.radius R * x.D.eps x.M) (g.Gw.mass law) (fun _ => 1) z ≤
      Cw * CB * x.D.eps (x.M + A.Jw) ^ (-(1 + B.s)) *
        weightedNorm (plan.radius R * x.D.eps x.M) (g.Gw.mass law) (fun _ => 1) z :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hCC) hWn0
  have hterm : x.D.termRStar (plan.radius R) x.M = plan.radius R * x.D.eps x.M := rfl
  rw [hterm]
  linarith

end AVRegularity.WeakEntryProofs.Assembly
end
end

section
/-! **The paired difference split in two bounded statements** (statements only; no proofs).

Notation: `U = rerootFamily g.relabel (r.Ur M)` is the raw family, `V` a paired solution from the
same trace, `S_w = isoPairedKernel r_w` the paired kernel, and `P = weakPairedOp ..` the
`TorusKernelOperator` of the paired system of `Gw` on `[t_{M+1}, a + T₀]`.

* `TorusKernelOperator.fluxTermOf`, `TorusKernelOperator.liftForcing`: for a family `y` of
  higher-order lifts and a family `w` of gradient lifts, `liftForcing y w` is the carrier-valued
  flux `∑_{u, γ, d} a^phys_{γ,d} ∇^{d-1} (y_{uγ} - S_w C w_u)` of the difference between the lift
  `y` and the regularized lift of `w`. It is a plain sum of the carrier flux terms
  (`torusKernelFluxTerm`) of `P`, at the order `K_w`; it does not depend on `D_m` except through
  the order of the lift `y`, which is `K_w + D_m - 1`.
* `weakPairedForcing`: the forcing `F` of the difference equation. With `y = Uk`, the raw lift of
  `U` (the raw lift of the raw system), and `w = Uw`, the gradient lift of `U`, it is the raw flux minus the
  paired flux, both evaluated on `U`:
  `F_v = ∑_{u, γ, d} a^phys_{γ,d} ∇^{d-1} (I - S_w) U_u`.
* `WeakEntryPairedForcingStatement`: `U - V` solves, on `[t_{M+1}, a + T₀]` at the order
  `K_w`, the coupled system with zero data, the paired flux `P.carrierFlux (Uw - Vw)` and the
  forcing `F`; and `F` is measurable in time.
* `WeakEntryPairedForcingCostStatement`: moment cancellation. With `ρ_M = c ε_M` and
  `m = J_w N_w + L`, the time integral of the `ρ_M`-mass of `F` is at most
  `C_mom ε_M^{2(χ_w + σ_w L)} 𝓔_hi(U)²`, where `𝓔_hi(U)` is the strong energy at the radius `ρ_M`
  of the family `Uhi M` of the higher-order lemma at the offset `m`, truncated to the order `K_w + m`.
* `WeakEntryPairedForcingCostPlanOK`: the level floor that makes `ε_M^{σ_w} ≤ c` (so
  `r_w ≤ ρ_M`, the hypothesis of the paired Taylor estimate).

Special cases:
- `f = 0`: `θ = 0`, so `U = 0`, `Uk = 0`, `F = 0` and both sides of the cost bound are `0`.
- `Gw` without identities: the sum defining `F` is empty, so `F = 0`.
- `L = 0` is excluded by `L + 1 ≤ 2 n_W` together with `plan.momentFloor ≤ L`; with `L = 0` the
  gain `ε_M^{σ_w L}` would be `1`.
- Constants: `C_mom` is chosen after `R` and `C`, before the data `x`, the stages `g`, the
  schedule `s`, the solution and the order `D_m`. -/
@[expose] public noncomputable section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open scoped ENNReal

namespace AVRegularity.KernelEnergy

variable
    {ι : Type*} [Fintype ι] [DecidableEq ι] {h : ι → Type*}
    [∀ i, NormedAddCommGroup (h i)] [∀ i, InnerProductSpace ℝ (h i)]
    [∀ i, FiniteDimensional ℝ (h i)] [∀ i, MeasurableSpace (h i)] [∀ i, BorelSpace (h i)]
    [∀ i, CompleteSpace (h i)]
    {Γ : ι → ι → Type*} [∀ i j, Fintype (Γ i j)]
    {G : ∀ i j, Γ i j → Type*} [∀ i j α, NormedAddCommGroup (G i j α)]
    [∀ i j α, InnerProductSpace ℝ (G i j α)] [∀ i j α, FiniteDimensional ℝ (G i j α)]
    [∀ i j α, MeasurableSpace (G i j α)] [∀ i j α, BorelSpace (G i j α)]
    [∀ i j α, CompleteSpace (G i j α)]
variable {a b ρ ν : ℝ} {k D : ℕ}

namespace TorusKernelOperator
variable (P : TorusKernelOperator (h := h) (Γ := Γ) (G := G) a b ρ ν k D)

/-- The carrier flux term of one identity `(i, j, α)` at the order `d`, of a given lift `Y` of
order `k + D - 1` (`P.fluxTerm` is the case of the regularized lift of `V`). -/
def fluxTermOf (t : ℝ) (ht : t ∈ Set.Icc a b) (i j : ι) (α : Γ i j) (d : ↥(Finset.Icc 2 D))
    (Y : TorusHk (k + D - 1) (G i j α)) : TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  torusKernelFluxTerm (m := d.1 - 2) (r := d.1 - 1)
    (by have := Finset.mem_Icc.1 d.2; omega) ρ P.radius_pos a b
    (P.B i j α d) (P.hB_fin i j α d) t ht (P.hB_smooth i j α d t ht) (P.hB_per i j α d t ht)
    (truncateTorusHk (by have := Finset.mem_Icc.1 d.2; omega) Y)

/-- **The flux of the difference between a family of lifts `y` and the regularized lift of `w`**,
as a carrier of order `k`: `∑_{j, α, d} B_{α,d} ∇^{d-1} (y_{jα} - S C w_j)`. The time is clamped to
`[a, b]`, as for `carrierFlux`. -/
def liftForcing (y : ∀ i j (α : Γ i j), ℝ → TorusHk (k + D - 1) (G i j α))
    (w : ∀ i, ℝ → TorusHk (k + 1) (h i)) (i : ι) (t : ℝ) :
    TorusHk k (PiLp 2 (fun _ : Fin 2 => h i)) :=
  ∑ j : ι, ∑ α : Γ i j, ∑ d : ↥(Finset.Icc 2 D),
    P.fluxTermOf (Set.projIcc a b P.htime t) (Set.projIcc a b P.htime t).property i j α d
      (y i j α t - P.higherInput w i j α t)

end TorusKernelOperator
end AVRegularity.KernelEnergy

namespace AVRegularity.WeakEntryProofs
open AVRegularity.WeakEntryProofs.Assembly AVRegularity.KernelEnergy

section Operator

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- The window `[t_{M+1}, a + T₀]` is nonempty. -/
theorem weakPaired_window_le {x : WeakEntryData plan C} {g : WeakEntryStages x}
    (s : WeakEntrySchedule g) : s.tq (x.M + 1) ≤ x.a + A.T₀ :=
  s.finish.trans (by linarith [A.τ_small])

/-- **The `TorusKernelOperator` of the paired system of `Gw`** on its window (the
operator of the paired system, with the bijection of the identities chosen once). -/
def weakPairedOp (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedPlanOK plan)
    {x : WeakEntryData plan C} (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw) (hm : law.rootMass = g.rootM) :
    TorusKernelOperator (h := fun v : CompIn g.Gw.comps => ScalarH v.1.root)
      (Γ := g.Gw.fam.Γ) (G := fun _ u _ => ScalarH u.1.root) (s.tq (x.M + 1)) (x.a + A.T₀)
      (x.D.termRStar (plan.radius R) x.M) (x.D.κ x.M) R.Kw x.Dm :=
  weakPairedOperator hcommon hok g law hm
    (Classical.choose (weakEncoding_physCoeff g.encoding))
    (Classical.choose_spec (weakEncoding_physCoeff g.encoding)) (weakPaired_window_le s)

/-- **The forcing `F` of the paired difference** (explicit): the flux of `(I - S_w) U`, where
`Uk` is the raw lift of `U` of order `K_w + D_m - 1` and `Uw` its gradient lift.
`F_v = ∑_{u, γ, d} a^phys_{γ,d} ∇^{d-1} (I - S_w) U_u` (the raw flux minus the paired flux). -/
def weakPairedForcing (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedPlanOK plan)
    {x : WeakEntryData plan C} (g : WeakEntryStages x) (s : WeakEntrySchedule g)
    (law : BirthLaw) (hm : law.rootMass = g.rootM)
    (Uw : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root))
    (Uk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)) :
    ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (PiLp 2 (fun _ : Fin 2 => ScalarH v.1.root)) :=
  (weakPairedOp hcommon hok g s law hm).liftForcing Uk Uw

end Operator

namespace Assembly

variable {plan : WeakEntryGluePlan} {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}
  {R : WeakPassageRequest A} {C : WeakEntryAllocation R (plan.radius R)}

/-- **The difference equation with an explicit forcing.** Let `U` be the re-rooted level-`M`
family of a reduction `r`, with a raw lift `Uk` (the raw system) and gradient
lift `Uw`, and let `V` be any solution of the paired system from the trace of `U`. Then `U - V`
solves, on the window `[t_{M+1}, a + T₀]` at the order `K_w`, the coupled system
`(∂ₜ + 𝐛·∇ - κ_M Δ) W = div (F + P.carrierFlux (Uw - Vw))` with zero data, where `F` is
`weakPairedForcing`; and `F` is measurable in time on the window. -/
def WeakEntryPairedForcingStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedPlanOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} {R : WeakPassageRequest A}
    {C : WeakEntryAllocation R (plan.radius R)} {x : WeakEntryData plan C}
    (g : WeakEntryStages x) (s : WeakEntrySchedule g)
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
  ∀ (V : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk R.Kw (ScalarH v.1.root))
    (Vw : ∀ v : CompIn g.Gw.comps, ℝ → TorusHk (R.Kw + 1) (ScalarH v.1.root))
    (Vk : ∀ v u (_ : g.Gw.fam.Γ v u), ℝ → TorusHk (R.Kw + x.Dm - 1) (ScalarH u.1.root)),
    g.Gw.IsRegSolution x.P (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW)
      (fun _ => isoPairedKernel (x.D.termRW A.σw x.M) R.nW) A.φ₀ A.hφ₀ (x.D.κ x.M)
      (streamVel (x.D.Φ x.M)) R.Kw (s.tq (x.M + 1)) (x.a + A.T₀)
      (fun v => rerootFamily g.relabel (r.Ur x.M) v (s.tq (x.M + 1))) (fun _ _ => 0)
      (fun _ _ => 0) V Vw Vk →
    IsCoupledWeakSolutionTorus (x.D.κ x.M) (s.tq (x.M + 1)) (x.a + A.T₀)
      (streamVel (x.D.Φ x.M)) 0 (fun _ => R.Kw) TorusKernelOperator.noLocalCoefficient (fun _ => 0)
      (fun v t => weakPairedForcing hcommon hok g s law hm
          (rerootFamily g.relabel (r.Urw x.M)) Uk v t +
        (weakPairedOp hcommon hok g s law hm).carrierFlux
          (fun v t => rerootFamily g.relabel (r.Urw x.M) v t - Vw v t) v t)
      (fun _ _ => 0)
      (fun v t => rerootFamily g.relabel (r.Ur x.M) v t - V v t)
      (fun v t => rerootFamily g.relabel (r.Urw x.M) v t - Vw v t) ∧
    ∀ v, AEStronglyMeasurable
      (weakPairedForcing hcommon hok g s law hm (rerootFamily g.relabel (r.Urw x.M)) Uk v)
      (volume.restrict (Set.Icc (s.tq (x.M + 1)) (x.a + A.T₀)))

/-- **Plan condition of the forcing cost** (a lower bound on the level floor): from the floor on,
`ε_M^{σ_w} ≤ c`, i.e. the width `r_w = ε_M^{1+σ_w}` of the paired kernel is at most the radius
`ρ_M = c ε_M`. -/
def WeakEntryPairedForcingCostPlanOK (plan : WeakEntryGluePlan) : Prop :=
  ∀ {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)) (j₀ M : ℕ), 128 ≤ A.Λ →
    plan.levelFloor R C j₀ ≤ M → ocEpsilon B.q A.Λ M ^ A.σw ≤ plan.radius R

/-- **The truncation of the family `Uhi M` of (H) to the order `K_w + m`.** -/
def weakHighFamily {x : WeakEntryData plan C} (g : WeakEntryStages x) (m : ℕ)
    (Uhi : Providers.WeakGen.Reduction.WeakReductionFamily g m x.M) :
    ∀ v : CompIn (g.stage x.M).comps, ℝ → TorusHk (R.Kw + m) (ScalarH v.1.root) :=
  fun v t => truncateTorusHk (Providers.WeakGen.Reduction.weakReductionReserve_kw R m v.1) (Uhi v t)

/-- **The truncation of the gradient lifts `Whi M` of (H) to the order `K_w + m + 1`.** -/
def weakHighLift {x : WeakEntryData plan C} (g : WeakEntryStages x) (m : ℕ)
    (Whi : Providers.WeakGen.Reduction.WeakReductionLift g m x.M) :
    ∀ v : CompIn (g.stage x.M).comps, ℝ → TorusHk (R.Kw + m + 1) (ScalarH v.1.root) :=
  fun v t => truncateTorusHk
    (Nat.succ_le_succ (Providers.WeakGen.Reduction.weakReductionReserve_kw R m v.1)) (Whi v t)

/-- **Moment cancellation, the cost of the forcing.** Under the plan conditions, for all
`R`, `C` there is `C_mom ≥ 0`, before the data, such that for every solution `U` (a reduction `r`
with raw lift `Uk`) and every family `Uhi, Whi` of the higher-order lemma at the offset `m = J_w N_w + L` (whose
truncations to `K_w` are `r.Ur M` on `[t_{M+1}, T]` and `r.Urw M` almost everywhere):
`∫ |F|²_{ρ_M} ≤ C_mom ε_M^{2(χ_w + σ_w L)} κ_M 𝓔_hi(U)²`,
the factor `κ_M` being there because the forced energy divides the forcing by `ν = κ_M`
(the coefficient price carries one `κ_M`, the other is absorbed in the dissipation of `𝓔_hi`),
where `ρ_M = plan.radius R · ε_M`, the left side is the `Gw`-mass of the carrier flux `F` of
`weakPairedForcing`, and `𝓔_hi(U)` is the strong energy at the radius `ρ_M` with the weak masses
of the truncated family `Uhi M, Whi M`. -/
def WeakEntryPairedForcingCostStatement (plan : WeakEntryGluePlan) : Prop :=
  ∀ (hcommon : WeakEntryCommonOK plan) (hok : WeakEntryPairedPlanOK plan)
    (_hcost : WeakEntryPairedForcingCostPlanOK plan)
    {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B} (R : WeakPassageRequest A)
    (C : WeakEntryAllocation R (plan.radius R)),
  ∃ Cmom : ℝ, 0 ≤ Cmom ∧
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

end Assembly
end AVRegularity.WeakEntryProofs
end
end
