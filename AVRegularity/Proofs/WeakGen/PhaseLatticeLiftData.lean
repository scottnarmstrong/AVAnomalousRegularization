-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov
import AVRegularity.Proofs.GenSem.LiftOn.Omega
import AVRegularity.Proofs.ComplexContext.ExtFam
public import AVRegularity.EntryWeakAssembly.FirstMeanZero
public import AVRegularity.Proofs.WeakGen.EddyModes
public import AVRegularity.Proofs.CascadeInvariants.Graded.SlotFam
public import AVRegularity.Proofs.WeakGen.Assembly.WeakLedgerOfIngredients
import AVRegularity.EntryWeakAssembly.ReadoutLinearLevel
public import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.Complex.Liouville
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.RingTheory.PicardGroup

section
section
/-! Time-uniform local bounds for every derivative of a holomorphic family. These are
qualitative local bounds; no ambient order cap enters a weak coefficient constant. -/
@[expose] public noncomputable section
open Set Metric Filter Topology
namespace AVRegularity.Providers.WeakGen

/-- Local boundedness of a family, uniformly in its time parameter. -/
def UniformLocalBound {E F : Type*} [TopologicalSpace E] [NormedAddCommGroup F]
    (T : Set ℝ) (U : Set E) (f : ℝ → E → F) : Prop :=
  ∀ x ∈ U, ∃ V ∈ 𝓝 x, ∃ M : ℝ, ∀ t ∈ T, ∀ y ∈ V, ‖f t y‖ ≤ M

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [NormedAddCommGroup F] [NormedSpace ℂ F]

/-- Cauchy's bound for a vector-valued function, read in operator norm. -/
theorem norm_fderiv_le_of_bound {f : E → F} {x : E} {r M : ℝ} (hr : 0 < r)
    (hd : DifferentiableOn ℂ f (closedBall x r))
    (hb : ∀ y ∈ closedBall x r, ‖f y‖ ≤ M) : ‖fderiv ℂ f x‖ ≤ M / r := by
  have hM : 0 ≤ M := (norm_nonneg _).trans (hb x (mem_closedBall_self hr.le))
  have hdx := hd.differentiableAt (closedBall_mem_nhds x hr)
  refine ContinuousLinearMap.opNorm_le_of_unit_norm (div_nonneg hM hr.le) fun v hv => ?_
  have hmap : ∀ z ∈ closedBall (0 : ℂ) r, x + z • v ∈ closedBall x r := by
    intro z hz
    rw [mem_closedBall, dist_eq_norm, add_sub_cancel_left, norm_smul, hv, mul_one]
    exact mem_closedBall_zero_iff.mp hz
  have hh : DifferentiableOn ℂ (fun z : ℂ => f (x + z • v)) (closedBall 0 r) :=
    hd.comp ((differentiable_const _).add (differentiable_id.smul_const v)).differentiableOn hmap
  have he : deriv (fun z : ℂ => f (x + z • v)) 0 = fderiv ℂ f x v := by
    have h1 : HasDerivAt (fun z : ℂ => x + z • v) v 0 := by
      simpa only [id_eq, one_smul, zero_smul, add_zero] using ((hasDerivAt_id (0 : ℂ)).smul_const v).const_add x
    have h2 : HasFDerivAt f (fderiv ℂ f x) (x + (0 : ℂ) • v) := by
      simpa only [zero_smul, add_zero] using hdx.hasFDerivAt
    exact (h2.comp_hasDerivAt 0 h1).deriv
  have hb' := Complex.norm_deriv_le_of_forall_mem_sphere_norm_le hr
    ((hh.mono closure_ball_subset_closedBall).diffContOnCl)
    (fun z hz => hb _ (hmap z (sphere_subset_closedBall hz)))
  rwa [he] at hb'

/-- Differentiation preserves local bounds uniform in time. -/
theorem UniformLocalBound.fderiv {T : Set ℝ} {U : Set E} {f : ℝ → E → F}
    (hU : IsOpen U) (hf : UniformLocalBound T U f)
    (hd : ∀ t ∈ T, DifferentiableOn ℂ (f t) U) :
    UniformLocalBound T U (fun t x => fderiv ℂ (f t) x) := by
  intro x hx
  obtain ⟨V, hV, M, hM⟩ := hf x hx
  obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.mp hU x hx
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  let r := min ε δ / 4
  have hr : 0 < r := by dsimp only [r]; positivity
  have hsub : closedBall x (3 * r) ⊆ U ∩ V := by
    intro y hy
    refine ⟨hεU ?_, hδV ?_⟩ <;> rw [mem_ball]
    · have := mem_closedBall.mp hy
      have := min_le_left ε δ
      dsimp only [r] at *
      linarith only [this, ‹dist y x ≤ 3 * (min ε δ / 4)›, hε]
    · have := mem_closedBall.mp hy
      have := min_le_right ε δ
      dsimp only [r] at *
      linarith only [this, ‹dist y x ≤ 3 * (min ε δ / 4)›, hδ]
  refine ⟨ball x r, ball_mem_nhds x hr, M / r, fun t ht y hy => ?_⟩
  have hball : closedBall y r ⊆ closedBall x (3 * r) := by
    intro z hz
    rw [mem_closedBall] at hz ⊢
    have hxy := mem_ball.mp hy
    have htri := dist_triangle z y x
    linarith only [hz, hxy, htri, hr]
  exact norm_fderiv_le_of_bound hr ((hd t ht).mono fun z hz => (hsub (hball hz)).1)
    (fun z hz => hM t ht z (hsub (hball hz)).2)

/-- Every complex derivative retains the local time-uniform bound. -/
theorem UniformLocalBound.complexJets {T : Set ℝ} {U : Set E} {f : ℝ → E → F}
    (hU : IsOpen U) (hf : UniformLocalBound T U f)
    (hd : ∀ t ∈ T, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U) (n : ℕ) :
    UniformLocalBound T U (fun t x => iteratedFDeriv ℂ n (f t) x) := by
  induction n with
  | zero => simpa only [UniformLocalBound, norm_iteratedFDeriv_zero] using hf
  | succ n ih =>
    have hd' : ∀ t ∈ T, DifferentiableOn ℂ (iteratedFDeriv ℂ n (f t)) U := by
      intro t ht
      exact ((hd t ht).differentiableOn_iteratedFDerivWithin (m := n)
        (WithTop.coe_lt_coe.mpr (ENat.natCast_lt_top n)) hU.uniqueDiffOn).congr
        (fun x hx => (iteratedFDerivWithin_of_isOpen n hU hx).symm)
    have hh := ih.fderiv hU hd'
    simpa only [UniformLocalBound, norm_fderiv_iteratedFDeriv] using hh

omit [NormedSpace ℂ E] [NormedSpace ℂ F] in
/-- A locally bounded family is bounded on each compact subset. -/
theorem UniformLocalBound.on_compact {T : Set ℝ} {U : Set E} {f : ℝ → E → F}
    (hf : UniformLocalBound T U f) {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ T, ∀ x ∈ K, ‖f t x‖ ≤ M := by
  classical
  choose V hV M hM using fun x (hx : x ∈ K) => hf x (hKU hx)
  obtain ⟨s, hs⟩ := hK.elim_nhds_subcover' V hV
  refine ⟨∑ x ∈ s, |M x.1 x.2|, Finset.sum_nonneg (fun _ _ => abs_nonneg _), ?_⟩
  intro t ht x hx
  obtain ⟨y, hy, hxy⟩ := mem_iUnion₂.mp (hs hx)
  exact (hM y.1 y.2 t ht x hxy).trans ((le_abs_self _).trans
    (Finset.single_le_sum (f := fun x : K => |M x.1 x.2|) (fun _ _ => abs_nonneg _) hy))

/-- Real derivatives of a smooth holomorphic family have finite bounds on compact sets. -/
theorem UniformLocalBound.realJets_on_compact {T : Set ℝ} {U : Set E} {f : ℝ → E → F}
    (hU : IsOpen U) (hf : UniformLocalBound T U f)
    (hd : ∀ t ∈ T, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U)
    {K : Set E} (hK : IsCompact K) (hKU : K ⊆ U) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ T, ∀ x ∈ K, ‖iteratedFDeriv ℝ n (f t) x‖ ≤ M := by
  obtain ⟨M, hM, hb⟩ := (hf.complexJets hU hd n).on_compact hK hKU
  refine ⟨M, hM, fun t ht x hx => ?_⟩
  have hc : ContDiffAt ℂ (n : WithTop ℕ∞) (f t) x :=
    ((hd t ht).contDiffAt (hU.mem_nhds (hKU hx))).of_le
      (WithTop.coe_le_coe.mpr (show (n : ℕ∞) ≤ ⊤ from le_top))
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ), Function.comp_apply,
    ContinuousMultilinearMap.norm_restrictScalars]
  exact hb t ht x hx

/-- Smooth real parameterizations preserve finite time-uniform jet bounds on compact sets. -/
theorem UniformLocalBound.compact_comp {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
    {T : Set ℝ} {U : Set E} {f : ℝ → E → F} (hU : IsOpen U)
    (hf : UniformLocalBound T U f) (hd : ∀ t ∈ T, ContDiffOn ℂ (⊤ : ℕ∞) (f t) U)
    (Φ : V → E) (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) {K : Set V} (hK : IsCompact K)
    (hKU : MapsTo Φ K U) (n : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ t ∈ T, ∀ x ∈ K,
      ‖iteratedFDeriv ℝ n (fun y => f t (Φ y)) x‖ ≤ M := by
  classical
  have hb i := hf.realJets_on_compact hU hd (hK.image hΦ.continuous) (by
    rintro _ ⟨x, hx, rfl⟩; exact hKU hx) i
  choose B hB hbound using hb
  have hp i : ∃ C : ℝ, ∀ x ∈ K, ‖iteratedFDeriv ℝ i Φ x‖ ≤ C :=
    hK.exists_bound_of_continuousOn
      ((hΦ.continuous_iteratedFDeriv (m := i) (by simp)).continuousOn)
  choose C hC using hp
  let A := ∑ i ∈ Finset.range (n + 1), B i
  let D := 1 + ∑ i ∈ Finset.range (n + 1), |C i|
  have hA : 0 ≤ A := Finset.sum_nonneg fun i _ => hB i
  have hD : 1 ≤ D := le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => abs_nonneg _)
  have hopen : IsOpen (Φ ⁻¹' U) := hU.preimage hΦ.continuous
  refine ⟨n.factorial * A * D ^ n, mul_nonneg (mul_nonneg (by positivity) hA)
    (pow_nonneg (zero_le_one.trans hD) _), fun t ht x hx => ?_⟩
  have hb' := norm_iteratedFDerivWithin_comp_le
    ((hd t ht).restrict_scalars ℝ) hΦ.contDiffOn (by simp : (n : WithTop ℕ∞) ≤ (⊤ : ℕ∞))
    hU.uniqueDiffOn hopen.uniqueDiffOn (Set.mapsTo_preimage Φ U) (hKU hx)
    (C := A) (D := D) ?_ ?_
  · rw [iteratedFDerivWithin_of_isOpen n hopen (hKU hx)] at hb'
    exact hb'
  · intro i hi
    rw [iteratedFDerivWithin_of_isOpen i hU (hKU hx)]
    exact (hbound i t ht _ (mem_image_of_mem Φ hx)).trans
      (Finset.single_le_sum (fun i _ => hB i) (Finset.mem_range.mpr (by omega)))
  · intro i hi hin
    rw [iteratedFDerivWithin_of_isOpen i hopen (hKU hx)]
    have hCD : C i ≤ D := (le_abs_self _).trans ((Finset.single_le_sum (f := fun i : ℕ => |C i|)
      (fun _ _ => abs_nonneg _) (Finset.mem_range.mpr (by omega))).trans
        (le_add_of_nonneg_left zero_le_one))
    exact (hC i x hx).trans (hCD.trans (le_self_pow₀ hD (by omega)))

end AVRegularity.Providers.WeakGen
end
end

section
/-! A holomorphic context extension supplies smooth recentered real coefficients,
measurable on their time window, with time-uniform jet bounds on every compact subset. -/
@[expose] public noncomputable section
open Homogenization MeasureTheory Set Filter Topology
namespace AVRegularity.Providers.WeakGen
open AVRegularity.Providers.GenSem

/-- The local real data of a holomorphic context, in the fast-first order of source reserves. -/
theorem holomorphic_recenter_data {D : OCData} (hΛ : 1 ≤ D.Λ) {b : ℝ} (hb : 0 < b)
    {j₀ i : ℕ} {p : ℤ} {f : GenSort.Sem .ctx}
    {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ}
    (hF : IsHolExtension D b j₀ i p f F) (A : RealChain) (ρ : ℝ)
    (T : Set ℝ) (clock : ℝ → ℝ) (hc : Continuous clock)
    (hclock : MapsTo clock T (ocPulseWindow D.α D.q D.Λ i p)) :
    let Ω := ladderOmega D b j₀ i p A ρ
    let g := fun t (z Y : Vec 2) => f (clock t) (A.recenter D (ρ • Y)) z
    (∀ t ∈ T, ContDiffOn ℝ (⊤ : ℕ∞)
      (fun X : Vec 2 × Vec 2 => g t X.1 X.2) {X | X.2 ∈ Ω}) ∧
    (∀ Y ∈ Ω, Measurable (fun Z : T × Vec 2 => g Z.1 Z.2 Y)) ∧
    (∀ K : Set (Vec 2 × Vec 2), IsCompact K → K ⊆ {X | X.2 ∈ Ω} → ∀ n,
      ∃ B : ℝ, 0 ≤ B ∧ ∀ t ∈ T, ∀ X ∈ K,
        ‖iteratedFDeriv ℝ n (fun Z : Vec 2 × Vec 2 => g t Z.1 Z.2) X‖ ≤ B) := by
  dsimp only
  let Ω := ladderOmega D b j₀ i p A ρ
  let U := carrierC D b A.data A.children.length 2
  obtain ⟨Pm, hPm, hPmeq⟩ := exists_recenter_model D A ρ
  let Φ : Vec 2 × Vec 2 → ChainParamsC A.children.length := fun X => Pm X.2 X.1
  have hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ := hPm.comp (contDiff_snd.prodMk contDiff_fst)
  have hU : IsOpen U := isOpen_carrierC D b A.data A.children.length 2
  have hΩ : IsOpen {X : Vec 2 × Vec 2 | X.2 ∈ Ω} :=
    (isOpen_ladderOmega D b j₀ i p A ρ).preimage continuous_snd
  have hkey : ∀ X : Vec 2 × Vec 2, X.2 ∈ Ω →
      Φ X ∈ U ∧ ∀ t ∈ T,
        f (clock t) (A.recenter D (ρ • X.2)) X.1 =
          (F A.data A.children.length (clock t) (Φ X)).re := by
    intro X hX
    have hd := recenter_data D A (ρ • X.2)
    have hn := recenter_children_length D A (ρ • X.2)
    have he := hPmeq X.2 hn X.1
    have hmem := paramsC_mem_carrierC hΛ hb hX X.1
    refine ⟨paramsC_transport _ A.data A.children.length hd hn _ X.1 he
      (fun dd n x => x ∈ carrierC D b dd n 2) hmem, ?_⟩
    intro t ht
    have hv := hF.2.2 (A.recenter D (ρ • X.2)) (clock t) (hclock ht) X.1 hX
    have hv' := paramsC_transport _ A.data A.children.length hd hn _ X.1 he
      (fun dd n x => F dd n (clock t) x =
        (f (clock t) (A.recenter D (ρ • X.2)) X.1 : ℂ)) hv
    exact (congrArg Complex.re hv').symm
  have hd t (ht : t ∈ T) : ContDiffOn ℂ (⊤ : ℕ∞)
      (F A.data A.children.length (clock t)) U :=
    contDiffOn_top_of_differentiableOn hU (hF.1 A.data A.children.length _ (hclock ht))
  have hl : UniformLocalBound T U (fun t => F A.data A.children.length (clock t)) := by
    intro x hx
    obtain ⟨V, hV, M, hM⟩ := hF.2.1.2.2 A.data A.children.length x hx
    exact ⟨V, hV, M, fun t ht y hy => hM _ (hclock ht) y hy⟩
  have hs t (ht : t ∈ T) : ContDiffOn ℝ (⊤ : ℕ∞)
      (fun X : Vec 2 × Vec 2 => (F A.data A.children.length (clock t) (Φ X)).re)
      {X | X.2 ∈ Ω} :=
    (Complex.reCLM.contDiff.comp_contDiffOn
      (((hd t ht).restrict_scalars ℝ).comp hΦ.contDiffOn (fun X hX => (hkey X hX).1)))
  refine ⟨fun t ht => (hs t ht).congr (fun X hX => (hkey X hX).2 t ht), ?_, ?_⟩
  · intro Y hY
    let τ : T × Vec 2 → ocPulseWindow D.α D.q D.Λ i p :=
      fun Z => ⟨clock Z.1, hclock Z.1.2⟩
    let ψ : T × Vec 2 → U := fun Z => ⟨Φ (Z.2, Y), (hkey (Z.2, Y) hY).1⟩
    have hτ : Continuous τ := (hc.comp (continuous_subtype_val.comp continuous_fst)).subtype_mk _
    have hψ : Continuous ψ := (hΦ.continuous.comp
      (continuous_snd.prodMk continuous_const)).subtype_mk _
    have hm := ComplexContext.measurable_caratheodory_comp
      (fun t ht => (hF.1 A.data A.children.length t ht).continuousOn)
      (fun y _ => hF.2.1.1 A.data A.children.length y) τ hτ ψ hψ
    have heq : (fun Z : T × Vec 2 => f (clock Z.1) (A.recenter D (ρ • Y)) Z.2) =
        (fun Z => (F A.data A.children.length (τ Z) (ψ Z)).re) :=
      funext (fun Z => (hkey (Z.2, Y) hY).2 Z.1 Z.1.2)
    rw [heq]
    exact Complex.continuous_re.measurable.comp hm
  · intro K hK hKO n
    obtain ⟨B, hB, hb⟩ := hl.compact_comp hU hd Φ hΦ hK
      (fun X hX => (hkey X (hKO hX)).1) n
    refine ⟨B, hB, fun t ht X hX => ?_⟩
    have he : (fun Z : Vec 2 × Vec 2 => f (clock t) (A.recenter D (ρ • Z.2)) Z.1) =ᶠ[𝓝 X]
        (fun Z : Vec 2 × Vec 2 => (F A.data A.children.length (clock t) (Φ Z)).re) := by
      filter_upwards [hΩ.mem_nhds (hKO hX)] with Z hZ
      exact (hkey Z hZ).2 t ht
    rw [(he.iteratedFDeriv ℝ n).self_of_nhds]
    have hfAt : ContDiffAt ℝ (⊤ : ℕ∞)
        (fun Z : Vec 2 × Vec 2 => F A.data A.children.length (clock t) (Φ Z)) X :=
      ((hd t ht).restrict_scalars ℝ).contDiffAt (hU.mem_nhds ((hkey X (hKO hX)).1))
        |>.comp X hΦ.contDiffAt
    have hr := Complex.reCLM.norm_iteratedFDeriv_comp_left hfAt
      (n := n) (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
    simp only [Complex.reCLM_norm, one_mul, Function.comp_def, Complex.reCLM_apply] at hr
    exact hr.trans (hb t ht X hX)

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The coefficients of the eddy flux** (weak entry). The coefficient of tested order
`d` of the eddy flux of degree `n` is the dimensional prefactor of the path means times the cell
mean of the drift term `fluxXA` of the grade-zero lift array (`fluxCoeff_weakEddyFlux`):
`J^eddy = -ℓ^{-2}(d_*/ρ)^n ρ ⟨√η v C_{n-1}⟩` reads the lift coefficients only through
`√η v · C_{n-1}`. An expression generated with no export has no solved node
(`Gen.FromSeed.solvedFree_noExports`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory

namespace AVRegularity.Providers.WeakGen

open GenSem

/-- An expression generated with no export has no solved node. -/
theorem Gen.FromSeed.solvedFree_noExports
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ENNReal))
    {s : GenSort} {i : ℕ} {p : ℤ} {e : Gen s i p}
    (h : Gen.FromSeed (fun {_ _} _ => False) e) : Gen.SolvedFree leaf e := by
  induction h with
  | «export» he => exact he.elim
  | geo => simp [Gen.SolvedFree]
  | drift => simp [Gen.SolvedFree]
  | time => simp [Gen.SolvedFree]
  | add _ _ iha ihb => exact Or.inr ⟨iha, ihb⟩
  | mul _ _ iha ihb => exact Or.inr ⟨iha, ihb⟩
  | dOld _ _ ih => exact Or.inr ih
  | dPhase _ ih => exact Or.inr ih
  | dSlowFam _ _ ih => exact Or.inr ih
  | dSlowCell _ _ ih => exact Or.inr ih
  | dInternal _ ih => exact Or.inr ih
  | restrict _ ih => exact Or.inr ih
  | cellInv _ _ _ ihF ihι => exact Or.inr ⟨ihF, ihι⟩
  | transPrim _ ih => exact Or.inr ih
  | mean _ ih => exact Or.inr ih
  | famCell _ ih => exact Or.inr ih
  | evalChild _ _ ih => exact Or.inr ih

/-- **The coefficients of the eddy flux.** `Q` is the lift data of the scalar grade-zero family,
`s = (ℓ²)⁻¹ t`; hypothesis: the lift data are `C^{Dm+2}` at the time `s` (grade `0`, orders
`≤ n`). -/
theorem fluxCoeff_weakEddyFlux (D : OCData) (m : ℕ) {ρ : ℝ} {Dm : ℕ}
    (Q : LiftOperatorData (Fin 1) (fun _ => ℝ) Dm)
    (Cc0 : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (n : ℕ) (t : ℝ) (hn : 1 ≤ n)
    (hreg : LiftRegular Q Cc0 (0 : Fin 1) ((D.cellScaleSq m)⁻¹ * t) 0 n (Dm + 2))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    fluxCoeff (weakEddyFlux D m ρ Q Cc0 n t) d I 0 κ =
      -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
        ρ ^ (d - 1) * ((d - 1).factorial : ℝ)⁻¹ *
        fieldCellMean (fun z => ∑ σ : Equiv.Perm (Fin (d - 1)),
          fluxXA Q Cc0 0 0 n ((D.cellScaleSq m)⁻¹ * t) 0 κ (d - 1) (I ∘ σ) 0 z) := by
  set s := (D.cellScaleSq m)⁻¹ * t with hs
  set c₀ := -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ)
    with hc₀
  set a : Vec 2 → ℝ := fun Y => ρ ^ (d - 1) * mono 0 I Y with ha
  have hfield : (fun (_ : ℝ) (X : Vec 2) =>
      (Pi.single (0 : Fin 1) (mono 0 I (ρ • X)) : Fin 1 → ℝ)) =
      fun _ Y => (Pi.single (0 : Fin 1) (a Y) : Fin 1 → ℝ) := by
    funext _ Y
    rw [mono_zero_smul]
  have hasm : ContDiff ℝ ((n - 1 : ℕ) : WithTop ℕ∞) a :=
    (contDiff_const.mul (contDiff_mono 0 I)).of_le (by exact_mod_cast le_top)
  have hlift := liftApply_single_fun Cc0 (0 : Fin 1) (a := a) 0 (n - 1) s hasm
  -- the integrand, coefficientwise
  have hψ : ∀ z (u : Fin 1),
      ((Real.sqrt Q.η * Q.v s z κ) • liftApply (n - 1) (Cc0 0 (n - 1))
        (fun _ (X : Vec 2) => (Pi.single (0 : Fin 1) (mono 0 I (ρ • X)) : Fin 1 → ℝ)) s
        (ρ⁻¹ • (0 : Vec 2)) z) u =
      applyArr (n - 1) (fluxXA Q Cc0 0 0 n s u κ) a 0 z := by
    intro z u
    rw [hfield, hlift, smul_zero]
    simp only [Pi.smul_apply, smul_eq_mul]
    unfold fluxXA
    rw [applyArr_mulArr]
  have hψ' : ∀ z, ((Real.sqrt Q.η * Q.v s z κ) • liftApply (n - 1) (Cc0 0 (n - 1))
        (fun _ (X : Vec 2) => (Pi.single (0 : Fin 1) (mono 0 I (ρ • X)) : Fin 1 → ℝ)) s
        (ρ⁻¹ • (0 : Vec 2)) z) 0 =
      ρ ^ (d - 1) * ∑ σ : Equiv.Perm (Fin (d - 1)),
        fluxXA Q Cc0 0 0 n s 0 κ (d - 1) (I ∘ σ) 0 z := fun z => by
    rw [hψ z 0]
    exact applyArr_mono_scaled (n - 1) (arrSupp_fluxXA Q Cc0 0 0 n s 0 κ) _ 0 z I
  -- continuity and the cell mean
  have hsmA : ∀ u : Fin 1, ArrSmooth 0 (fluxXA Q Cc0 0 0 n s u κ) := fun u => by
    unfold fluxXA
    refine arrSmooth_mulArr ?_ (arrSmooth_entryArr _ _ _ _ _ fun m' α =>
      ((hreg.coeff 0 le_rfl (n - 1) (by omega) m' α u).of_le (by exact_mod_cast Nat.zero_le _)))
    exact (contDiff_const.mul (hreg.drift κ)).of_le (by exact_mod_cast Nat.zero_le _)
  have hcont : Continuous (fun z => (Real.sqrt Q.η * Q.v s z κ) • liftApply (n - 1) (Cc0 0 (n - 1))
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin 1) (mono 0 I (ρ • X)) : Fin 1 → ℝ)) s
      (ρ⁻¹ • (0 : Vec 2)) z) := by
    refine continuous_pi fun u => ?_
    have : (fun z => ((Real.sqrt Q.η * Q.v s z κ) • liftApply (n - 1) (Cc0 0 (n - 1))
        (fun _ (X : Vec 2) => (Pi.single (0 : Fin 1) (mono 0 I (ρ • X)) : Fin 1 → ℝ)) s
        (ρ⁻¹ • (0 : Vec 2)) z) u) = fun z => applyArr (n - 1) (fluxXA Q Cc0 0 0 n s u κ) a 0 z :=
      funext fun z => hψ z u
    rw [this]
    exact continuous_applyArr_z (hsmA u) a 0
  have hint := integrableOn_unitCube_of_continuous hcont
  have hcomm := (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin 1 => ℝ) 0).integral_comp_comm
    hint
  simp only [ContinuousLinearMap.proj_apply] at hcomm
  have hmean : fieldCellMean (fun z => (Real.sqrt Q.η * Q.v s z κ) • liftApply (n - 1)
      (Cc0 0 (n - 1))
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin 1) (mono 0 I (ρ • X)) : Fin 1 → ℝ)) s
      (ρ⁻¹ • (0 : Vec 2)) z) 0 =
      ρ ^ (d - 1) * fieldCellMean (fun z => ∑ σ : Equiv.Perm (Fin (d - 1)),
        fluxXA Q Cc0 0 0 n s 0 κ (d - 1) (I ∘ σ) 0 z) := by
    unfold fieldCellMean
    rw [← hcomm]
    simp only [hψ']
    rw [integral_const_mul]
  unfold fluxCoeff weakEddyFlux
  simp only [Pi.smul_apply, smul_eq_mul]
  change ((d - 1).factorial : ℝ)⁻¹ * (c₀ * fieldCellMean (fun z =>
      (Real.sqrt Q.η * Q.v s z κ) • liftApply (n - 1) (Cc0 0 (n - 1))
      (fun _ (X : Vec 2) => (Pi.single (0 : Fin 1) (mono 0 I (ρ • X)) : Fin 1 → ℝ)) s
      (ρ⁻¹ • (0 : Vec 2)) z) 0) = _
  rw [hmean]
  ring

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The levels of the drift letters of an expression** (weak entry). Only the child
evaluation `evalChild` changes the level of an expression, and it raises it by one. So every drift
letter of an expression of level `i` is at a level `≥ i` (`driftIn_ge`). A context expression
reaches the cell and family sorts only through a child evaluation, so every drift letter of a
context expression of level `i` is at a level `≥ i + 1` (`driftIn_ctx`). The weak ledger of the
passage at the level `i` asks the drift letters of the context expressions of the outgoing level
`i - 1` at the levels `≥ i` (`ComplexContext.DriftIn leaf (i ≤ ·)`); every expression satisfies it. -/

@[expose] public noncomputable section

open Homogenization AVRegularity
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen

variable (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

/-- **Every drift letter of an expression of level `i` is at a level `≥ i`.** -/
theorem driftIn_ge : ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) {m : ℕ}, m ≤ i →
    ComplexContext.DriftIn leaf (m ≤ ·) e := by
  intro s i p e
  induction e with
  | geo => intro m _; simp [ComplexContext.DriftIn]
  | drift => intro m hm; simpa [ComplexContext.DriftIn] using hm
  | time => intro m _; simp [ComplexContext.DriftIn]
  | add a b iha ihb => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr ⟨iha hm, ihb hm⟩
  | mul a b iha ihb => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr ⟨iha hm, ihb hm⟩
  | dOld _ a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | dPhase a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | dSlowFam _ a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | dSlowCell _ a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | dInternal a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | restrict a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | cellInv F _ ι ihF ihι =>
    intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr ⟨fun k => ihF k hm, ihι hm⟩
  | transPrim a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | solved G v F q _ _ _ _ ι ihG ihv ihF ihq ihι =>
    intro m hm; simp only [ComplexContext.DriftIn]
    exact Or.inr ⟨fun a c => ihG a c hm, fun k => ihv k hm, fun k => ihF k hm, ihq hm, ihι hm⟩
  | mean a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | famCell a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hm)
  | evalChild _ a ih => intro m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih (by omega))

/-- The context case, with the sort as an equation. -/
theorem driftIn_ctx_aux : ∀ {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p), s = .ctx →
    ∀ {m : ℕ}, m ≤ i + 1 → ComplexContext.DriftIn leaf (m ≤ ·) e := by
  intro s i p e
  induction e with
  | geo => intro _ _ _; simp [ComplexContext.DriftIn]
  | drift => intro h; cases h
  | time => intro _ _ _; simp [ComplexContext.DriftIn]
  | add a b iha ihb =>
    intro hs m hm; simp only [ComplexContext.DriftIn]; exact Or.inr ⟨iha hs hm, ihb hs hm⟩
  | mul a b iha ihb =>
    intro hs m hm; simp only [ComplexContext.DriftIn]; exact Or.inr ⟨iha hs hm, ihb hs hm⟩
  | dOld _ a ih => intro hs m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hs hm)
  | dPhase a ih => intro hs m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (ih hs hm)
  | dSlowFam => intro h; cases h
  | dSlowCell => intro h; cases h
  | dInternal => intro h; cases h
  | restrict => intro h; cases h
  | cellInv => intro h; cases h
  | transPrim => intro h; cases h
  | solved => intro h; cases h
  | mean => intro h; cases h
  | famCell => intro h; cases h
  | evalChild _ a _ =>
    intro _ m hm; simp only [ComplexContext.DriftIn]; exact Or.inr (driftIn_ge leaf a hm)

/-- **Every drift letter of a context expression of level `i` is at a level `≥ i + 1`.** -/
theorem driftIn_ctx {i : ℕ} {p : ℤ} (e : Gen .ctx i p) {m : ℕ} (hm : m ≤ i + 1) :
    ComplexContext.DriftIn leaf (m ≤ ·) e :=
  driftIn_ctx_aux leaf e rfl hm

end AVRegularity.Providers.WeakGen
end
end
end

section
section
/-! Fixed representatives of real child phases modulo the integer lattice. Selecting lift
families at these representatives makes their history dependence exactly periodic. -/
@[expose] public noncomputable section
open Homogenization AVenhance
namespace AVRegularity.Providers.WeakGen
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs

/-- Keep a child's center and replace each phase by its fractional part. -/
def childPhaseRepresentative (c : ChainChild) : ChainChild :=
  ⟨c.center, fun a => Int.fract (c.phase a)⟩

/-- Normalize the stored child phases, preserving all other history data. -/
def phaseRepresentative (A : RealChain) : RealChain :=
  { A with children := A.children.map childPhaseRepresentative }

/-- Normalization changes only integer child phases. -/
theorem phaseRepresentative_equivalent (A : RealChain) :
    WeakChainPhaseLatticeEquivalent A (phaseRepresentative A) := by
  refine ⟨rfl, rfl, rfl, ?_⟩
  change List.Forall₂ childPhaseLatticeEquivalent A.children
    (A.children.map childPhaseRepresentative)
  rw [List.forall₂_map_right_iff]
  apply List.forall₂_same.mpr
  intro c _
  refine ⟨rfl, fun a => ⌊c.phase a⌋, ?_⟩
  funext a
  exact (Int.fract_add_floor (c.phase a)).symm

/-- Integer phase-equivalent children have the same representative. -/
theorem childPhaseRepresentative_eq {c d : ChainChild} (h : childPhaseLatticeEquivalent c d) :
    childPhaseRepresentative c = childPhaseRepresentative d := by
  obtain ⟨hc, n, hn⟩ := h
  apply congrArg₂ ChainChild.mk hc
  funext a
  rw [congrFun hn a]
  exact Int.fract_add_intCast _ _

/-- Equivalent histories are assigned literally the same normalized history. -/
theorem phaseRepresentative_eq {A B : RealChain} (h : WeakChainPhaseLatticeEquivalent A B) :
    phaseRepresentative A = phaseRepresentative B := by
  have hmap : ∀ cs ds : List ChainChild, List.Forall₂ childPhaseLatticeEquivalent cs ds →
      cs.map childPhaseRepresentative = ds.map childPhaseRepresentative := by
    intro cs ds hh
    induction hh with
    | nil => rfl
    | @cons c d cs ds hc _ ih =>
      simp only [List.map_cons, childPhaseRepresentative_eq hc, ih]
  have h1 : (A.baseLevel, A.slots) = (B.baseLevel, B.slots) := Prod.ext h.baseLevel_eq h.slots_eq
  have h2 : (A.base, A.children.map childPhaseRepresentative) =
      (B.base, B.children.map childPhaseRepresentative) :=
    Prod.ext h.base_eq (hmap _ _ h.children_rel)
  exact congrArg₂ (fun (x : ℕ × List ℤ) (y : Vec 2 × List ChainChild) =>
    (⟨x.1, x.2, y.1, y.2⟩ : RealChain)) h1 h2

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The finer outputs of an eddy source** (weak entry, eddy ledger). Over the slot `k` of the
level `m`, the coefficient of tested order `d` of the eddy flux of degree `n ≥ 2` is a graded slot
family function whose size carries the drift twice (`eddyFamRepP`): it is the prefactor of the path
means times the cell mean of `√η v · C_{n-1}`, represented by the explicit expression
`c · mean(∑_σ drift · e_σ)`, with `e_σ` the graded representations of the ledger of the grade-zero lift
coefficients at the uniform constants (the context `X₁`). In the context of the eddy entry
(`eddyCtx X₁ κ m`: the passage constants `κ`, the means of the level `m` as leaves) its structural
norm is `|c|` times the zero mode of the mean (`genNorm_constMulMean`), which reads the modes `±1`
of the lift coefficients through the drift letter and is at most `D_d λ` times their norms at the
uniform constants (`genMode_mulDrift_zero_le`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal

namespace AVRegularity.Providers.WeakGen

open GenSem CascadeInvariants Majorant

/-- The context of the eddy entry: the constants `κ` of the passage, the means of the level `m`
as leaves, the budgets of `X₁`. -/
def eddyCtx (D : OCData) (X₁ : GCtx) (κ : MajConsts) (m : ℕ) : GCtx :=
  { X₁ with κ := κ, leaf := leafMeanAt D κ X₁.Δ m }

/-- **The eddy flux at the offset `0`** reads its lift coefficients at the offset `0` only. -/
theorem weakEddyFlux_congr0 (D : OCData) (m : ℕ) (ρ : ℝ) {Dm : ℕ}
    {Q Q' : LiftOperatorData (Fin 1) (fun _ => ℝ) Dm} (hη : Q.η = Q'.η) (hv : Q.v = Q'.v)
    {Cc Cc' : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)} (n : ℕ) (t : ℝ)
    (hC : ∀ m' (α : DerivativeWord2 m') z, Cc 0 (n - 1) m' α ((D.cellScaleSq m)⁻¹ * t) 0 z =
      Cc' 0 (n - 1) m' α ((D.cellScaleSq m)⁻¹ * t) 0 z) (f : Vec 2 → ℝ) :
    weakEddyFlux D m ρ Q Cc n t f 0 = weakEddyFlux D m ρ Q' Cc' n t f 0 := by
  have hL : liftApply (n - 1) (Cc 0 (n - 1))
      (fun _ X => (Pi.single (0 : Fin 1) (f (ρ • X)) : Fin 1 → ℝ)) ((D.cellScaleSq m)⁻¹ * t)
      (ρ⁻¹ • (0 : Vec 2)) = liftApply (n - 1) (Cc' 0 (n - 1))
      (fun _ X => (Pi.single (0 : Fin 1) (f (ρ • X)) : Fin 1 → ℝ)) ((D.cellScaleSq m)⁻¹ * t)
      (ρ⁻¹ • (0 : Vec 2)) := by
    funext z v
    simp only [liftApply, smul_zero, hC]
  funext κ
  unfold weakEddyFlux
  rw [hη, hv, hL]

/-- The context of the uniform constants: the constants `κ₁`, the child atoms as leaves of trivial
profile (`leafTop`), all times. -/
def topCtx (κ₁ : MajConsts) (Δ a₀ μ₀ : ℝ) (L₀ : ℕ) (S Kg Kd : ℝ≥0) : GCtx :=
  ⟨κ₁, Δ, a₀, leafTop, μ₀, L₀, Set.univ, S, Kg, Kd⟩

/-- The uniform representation of a drift-weighted sum, with abstract summands. -/
theorem URep.driftSum {Λ : Type} {V : UEnv Λ} {ι : Type*} (L : List ι)
    {g : Λ → Vec 2 → Vec 2 → ℝ} {dr : Gen .cell V.E.i V.E.p} (hdr : V.URep g dr)
    {φ : ι → Λ → Vec 2 → Vec 2 → ℝ} {E : ι → Gen .cell V.E.i V.E.p}
    (hE : ∀ σ, V.URep (φ σ) (E σ)) :
    V.URep (fun l X z => (L.map fun σ => g l X z * φ σ l X z).sum)
      (WeakGen.gsumList (L.map fun σ => Gen.mul dr (E σ))) :=
  WeakGen.URep.gsumList L (fun σ l X z => g l X z * φ σ l X z) (fun σ => Gen.mul dr (E σ))
    fun σ _ => hdr.mul (hE σ)

section Fine

variable {D : OCData} {b : ℝ} {j₀ : ℕ} {m : ℕ} {k : ℤ} {ρ : ℝ} {Dm : ℕ}
  {edge' : RealChain → ConstituentEdges Dm (fun _ : Fin 1 => ℝ)} {U : RealChain → Set (Vec 2)}
  {sX sZ N : ℕ} {t₀ t₁ : ℝ} {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
  {κ₁ : MajConsts} {Δ a₀ μ₀ : ℝ} {L₀ : ℕ} {S Kg Kd : ℝ≥0}

/-- **The eddy mean as a graded family function, with the drift twice.** -/
theorem eddyFamRepP
    (hS : LiftGenSetup D b j₀ (fun {_ _} _ => False) m k {A | IsAdmissibleChain D b j₀ m k A} ρ
      edge' U sX sZ t₀ t₁ N 0 Cc)
    (hX₁ : (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd).Ok)
    (hSl : UEnv.slowC (liftEnv D b j₀ (fun {_ _} _ => False) m k ρ
      {A | IsAdmissibleChain D b j₀ m k A} U t₀ t₁) (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) ≤ S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    (hed : ∀ (v u : Fin 1) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
      (liftEnv D b j₀ (fun {_ _} _ => False) m k ρ {A | IsAdmissibleChain D b j₀ m k A} U t₀
        t₁).IsURepP (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) (fun l Y z =>
          (((familyLiftData D m k l.1 ρ (edge' l.1)).edge v u d).map
            fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 0)
    (hL₀ : UEnv.liftWt Dm 0 N ≤ L₀) (h0 : ∀ A, IsAdmissibleChain D b j₀ m k A → (0 : Vec 2) ∈ U A)
    {n : ℕ} (hn : 2 ≤ n) (hLn : n - 1 ≤ L₀) (ha₀ : 0 ≤ a₀)
    {κ : MajConsts} {Dd lam : ℝ≥0} (hl0 : (lam : ℝ≥0∞) ≠ 0) (hl1 : (lam : ℝ≥0∞) ≤ 1)
    (hd : ∀ c h, κ.drift c h ≤ lam * κ₁.drift c h)
    (hg : ∀ L h, κ.geo .own L h ≤ κ₁.geo .own L h) (hg0 : ∀ L h, h ≠ 0 → κ.geo .own L h = 0)
    (hCold : κ.Cold ≤ κ₁.Cold) (hCslow : κ.Cslow ≤ κ₁.Cslow)
    (hDd : ∀ c h, κ.drift c h ≤ if h = 0 then 0 else (Dd : ℝ≥0∞))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κc : Fin 2) :
    (liftEnv D b j₀ (fun {_ _} _ => False) m k ρ {A | IsAdmissibleChain D b j₀ m k A} U t₀
      t₁).FamURepP (eddyCtx D (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) κ m)
      (fun l => LiftGenSetup.pathMeanPref D m ρ n d * fieldCellMean (fun z =>
        ∑ σ : Equiv.Perm (Fin (d - 1)),
          Real.sqrt (D.kap m / D.kap (m - 1)) * (familyLiftData D m k l.1 ρ (edge' l.1)).v l.2 z κc *
            GenSem.entryArr (Cc l.1 0 (n - 1)) (n - 1) 0 l.2 0 (d - 1) (I ∘ σ) 0 z))
      (n - 1 - (d - 1))
      (Real.toNNReal |LiftGenSetup.pathMeanPref D m ρ n d| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
          (Dd * lam * liftB (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) Dm 0 (n - 1)))) := by
  set X₁ := topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd with hX₁def
  set V := liftEnv D b j₀ (fun {_ _} _ => False) m k ρ {A | IsAdmissibleChain D b j₀ m k A} U t₀ t₁
    with hV
  have hbelow : V.CoeffRepBelowP X₁ Dm Cc (pathW fun _ _ => (0 : ℝ≥0)) (liftB X₁ Dm) 0 n :=
    fun hh' k' h1 _ m'' α' v' u' => hS.coeffRepP hX₁ hSl hη0 hη1 hed hL₀ h1 k' m'' α' v' u'
  have hB1 := UEnv.urepArrP_entryArr hX₁ (hbelow 0 (n - 1) le_rfl (by omega)) (0 : Fin 1) (0 : Fin 1)
  have hpw : pathW (fun _ _ => (0 : ℝ≥0)) 0 (0 : Fin 1) 0 = 1 := by simp [pathW_zero]
  rw [hpw, mul_one] at hB1
  choose e he hsf hnorm using fun σ : Equiv.Perm (Fin (d - 1)) => hB1 (d - 1) (I ∘ σ)
  -- the drift letter
  have h1 : V.URep (fun l _ z => Real.sqrt (D.kap m / D.kap (m - 1)) *
      ocPulseCellDrift D.α D.q D.Λ D.ζ m (D.kap m) k (V.time l / D.cellScaleSq m) z κc)
      (Gen.drift (i := m) (p := k) κc) :=
    ⟨.drift κc, .drift κc, driftSem D m k κc, .drift κc, fun _ _ _ _ _ => rfl,
      fun l _ Y _ z s => driftSem_phase D m k κc (V.time l) ((V.base l).recenter D (V.E.ρ • Y)) z s⟩
  have hdr : V.URep (fun l _ z => Real.sqrt (D.kap m / D.kap (m - 1)) *
      (familyLiftData D m k l.1 ρ (edge' l.1)).v l.2 z κc) (Gen.drift (i := m) (p := k) κc) :=
    h1.congr fun l _ Y _ z => by
      have hτ : V.time l / D.cellScaleSq m = l.2 := by
        show D.cellScaleSq m * l.2 / D.cellScaleSq m = l.2
        field_simp [hS.hc.ne']
      simp only [hτ, familyLiftData]
  -- the sum and the mean
  set L := (Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).toList with hL
  have hw := URep.driftSum L hdr he
  have hmean := hw.mean0 hS.hζ fun l hl => h0 l.1 hl.1
  have hc := (UEnv.famURep_const V (LiftGenSetup.pathMeanPref D m ρ n d)).mul hmean
  refine ⟨_, hc.congr fun l _ => ?_, ?_, fun t _ mres hm => ?_⟩
  · rw [hL]; simp only [Finset.sum_map_toList]
  · exact Or.inr ⟨by simp [Gen.SolvedFree], Or.inl (by simp [eddyCtx, leafMeanAt]; rfl)⟩
  · show genNorm D κ Δ a₀ (leafMeanAt D κ Δ m)
      (Gen.mul (Gen.time (.const (LiftGenSetup.pathMeanPref D m ρ n d))) (Gen.mean
        (gsumList (L.map fun σ => Gen.mul (Gen.drift (i := m) (p := k) κc) (e σ))))) a₀ mres 0 t ≤ _
    rw [genNorm_constMulMean]
    have hterm : ∀ σ ∈ L, ∀ t', genMode D κ Δ leafNone
        (Gen.mul (Gen.drift (i := m) (p := k) κc) (e σ)) mres 0 t' ≤
        (Dd * lam * liftB X₁ Dm 0 (n - 1) : ℝ≥0) := by
      intro σ _ t'
      refine (genMode_mulDrift_zero_le D Δ a₀ ha₀ hl0 hl1 hd hg hg0 hCold hCslow hDd κc (e σ) mres
        t' a₀ ha₀ 0).trans ?_
      have hn' := hnorm σ t' (Set.mem_univ _) mres 0 hm
        (by show 0 + UEnv.liftWt Dm 0 (n - 1) ≤ L₀; simp only [UEnv.liftWt]; omega)
      simp only [ENNReal.coe_mul]
      exact mul_le_mul' le_rfl hn'
    have hsup : (⨆ t', genMode D κ Δ leafNone
        (gsumList (L.map fun σ => Gen.mul (Gen.drift (i := m) (p := k) κc) (e σ))) mres 0 t') ≤
        (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
          (Dd * lam * liftB X₁ Dm 0 (n - 1)) : ℝ≥0) := by
      refine iSup_le fun t' => (genMode_gsumList_le D κ Δ _ mres 0 t').trans ?_
      rw [List.map_map]
      refine (List.sum_le_length_nsmul _ ((Dd * lam * liftB X₁ Dm 0 (n - 1) : ℝ≥0) : ℝ≥0∞)
        fun x hx => ?_).trans (le_of_eq ?_)
      · obtain ⟨σ, hσ, rfl⟩ := List.mem_map.mp hx
        exact hterm σ hσ t'
      · rw [List.length_map, hL, Finset.length_toList, nsmul_eq_mul]
        push_cast
        rfl
    calc ENNReal.ofReal |LiftGenSetup.pathMeanPref D m ρ n d| * _
        ≤ ENNReal.ofReal |LiftGenSetup.pathMeanPref D m ρ n d| *
          (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
            (Dd * lam * liftB X₁ Dm 0 (n - 1)) : ℝ≥0) := mul_le_mul' le_rfl hsup
      _ = _ := by rw [ENNReal.ofReal, ← ENNReal.coe_mul]

end Fine

end AVRegularity.Providers.WeakGen
end
end

section
/-! The phase-periodicity clause of a holomorphic context extension acts on every stored
child phase, hence on phase-lattice-equivalent real histories on the output window. -/
@[expose] public noncomputable section
open Homogenization AVenhance Set
namespace AVRegularity.Providers.WeakGen
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs AVRegularity.Providers.GenSem

/-- Translate the first `m` child phases, leaving the centers and final phase fixed. -/
def childPhasePrefix {n : ℕ} (x : ChainParamsC n) (v : Fin n → Vec 2) (m : ℕ) : ChainParamsC n :=
  (x.1, fun k => ((x.2.1 k).1,
    fun a => (x.2.1 k).2 a + if k.val < m then (v k a : ℂ) else 0), x.2.2)

/-- Real child-phase translations leave the complex carrier unchanged. -/
theorem childPhasePrefix_mem {D : OCData} {b r : ℝ} {dd : ChainData} {n : ℕ}
    (x : ChainParamsC n) (v : Fin n → Vec 2) (m : ℕ)
    (hx : x ∈ carrierC D b dd n r) : childPhasePrefix x v m ∈ carrierC D b dd n r := by
  have him (k : Fin n) (a : Fin 2) : (if k.val < m then (v k a : ℂ) else 0).im = 0 := by
    split_ifs <;> simp only [Complex.ofReal_im, Complex.zero_im]
  simpa only [childPhasePrefix, carrierC, Set.mem_ofPred_eq, Complex.add_im, him, add_zero] using hx

/-- Translating all child phases preserves the extension's value. -/
theorem holExtension_childPhasePrefix {D : OCData} {b : ℝ} {j₀ i : ℕ} {p : ℤ}
    {f : GenSort.Sem .ctx} {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ}
    (hF : IsHolExtension D b j₀ i p f F) (dd : ChainData) (n : ℕ) (t : ℝ)
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) (x : ChainParamsC n)
    (hx : x ∈ carrierC D b dd n 2) (v : Fin n → Vec 2)
    (hv : ∀ k, ∃ z : ℤ, v k (transverseIndex (dd.slots.getD k 0)) = z) :
    ∀ m ≤ n, F dd n t (childPhasePrefix x v m) = F dd n t x := by
  intro m
  induction m with
  | zero =>
    intro _
    have he : childPhasePrefix x v 0 = x := by
      refine Prod.ext rfl (Prod.ext (funext fun k => ?_) rfl)
      exact Prod.ext rfl (funext fun a => by simp only [childPhasePrefix, Nat.not_lt_zero, ite_false, add_zero])
    rw [he]
  | succ m ih =>
    intro hm
    have hmn : m < n := by omega
    let k : Fin n := ⟨m, hmn⟩
    have he : childPhasePrefix x v (m + 1) = (childPhasePrefix x v m).shiftChild k (v k) := by
      refine Prod.ext rfl (Prod.ext (funext fun j => ?_) rfl)
      by_cases hj : j = k
      · subst j
        dsimp only [childPhasePrefix, ChainParamsC.shiftChild]
        rw [Function.update_self]
        apply Prod.ext
        · rfl
        · funext a
          simp only [k, Nat.lt_succ_self, Nat.lt_irrefl, ite_true, ite_false, add_zero, Pi.add_apply]
      · have hjm : j.val ≠ m := fun hh => hj (Fin.ext hh)
        have hh : j.val < m + 1 ↔ j.val < m := by omega
        simp only [childPhasePrefix, ChainParamsC.shiftChild, Function.update_of_ne hj, hh]
    rw [he, (hF.2.1.2.1 dd n t ht _ (childPhasePrefix_mem x v m hx)).2 k (v k) (hv k), ih (by omega)]

/-- Equivalent real phase histories have equal context values on the extension's window. -/
theorem holExtension_phase_lattice {D : OCData} (hΛ : 1 ≤ D.Λ) {b : ℝ} (hb : 0 < b)
    {j₀ i : ℕ} {p : ℤ} {f : GenSort.Sem .ctx}
    {F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ}
    (hF : IsHolExtension D b j₀ i p f F) (A B : RealChain)
    (hA : IsAdmissibleChain D b j₀ i p A) (hphase : WeakChainPhaseLatticeEquivalent A B)
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ i p) (z : Vec 2) :
    f t A z = f t B z := by
  classical
  have hB := hphase.admissible D b j₀ i p hA
  have hn := hphase.children_length
  have hrel (k : Fin A.children.length) :
      childPhaseLatticeEquivalent (A.children.get k) (B.children.get (Fin.cast hn k)) := by
    simpa only [List.get_eq_getElem, Fin.val_cast] using
      hphase.children_rel.get k.isLt (show k.val < B.children.length from hn ▸ k.isLt)
  choose shifts hshifts using fun k => (hrel k).2
  let v : Fin A.children.length → Vec 2 := fun k => latticeShift (shifts k)
  let x := B.paramsN A.children.length hn.symm z
  have hd : B.data = A.data := by
    simp only [RealChain.data, hphase.baseLevel_eq, hphase.slots_eq]
  have hmem : x ∈ carrierC D b A.data A.children.length 2 :=
    paramsC_transport B A.data A.children.length hd hn.symm x z rfl
      (fun dd n x => x ∈ carrierC D b dd n 2) (paramsC_mem_carrierC hΛ hb hB z)
  have hprefix : childPhasePrefix x v A.children.length = A.paramsC z := by
    refine Prod.ext (funext fun a => ?_) (Prod.ext (funext fun k => ?_) rfl)
    · change (B.base a : ℂ) = (A.base a : ℂ)
      rw [hphase.base_eq]
    · refine Prod.ext (funext fun a => ?_) (funext fun a => ?_)
      · change ((B.children.get (Fin.cast hn k)).center a : ℂ) = ((A.children.get k).center a : ℂ)
        rw [(hrel k).1]
      · change ((B.children.get (Fin.cast hn k)).phase a : ℂ) +
          (if k.val < A.children.length then (v k a : ℂ) else 0) = ((A.children.get k).phase a : ℂ)
        rw [ite_eq_left k.isLt]
        exact_mod_cast (congrFun (hshifts k) a).symm
  have hper := holExtension_childPhasePrefix hF A.data A.children.length t ht x hmem v
    (fun k => ⟨shifts k (transverseIndex (A.data.slots.getD k 0)), rfl⟩)
    A.children.length le_rfl
  rw [hprefix, hF.2.2 A t ht z hA] at hper
  have hval : F A.data A.children.length t x = (f t B z : ℂ) :=
    paramsC_transport B A.data A.children.length hd hn.symm x z rfl
      (fun dd n x => F dd n t x = (f t B z : ℂ)) (hF.2.2 B t ht z hB)
  rw [hval] at hper
  exact Complex.ofReal_injective hper

end AVRegularity.Providers.WeakGen
end
end

section
/-! **Re-capping a stage** (weak entry). The order cap `Dm` of a stage
(`GenStage D hr Dm b j₀`) bounds the maximal orders of its identities and nothing else. A stage
whose orders are at most `N ≤ Dm` is the same stage with the cap `N` (`GenStage.recap`), with any
registry: the same level, components, identities (maps, records, orders), pieces, fluxes,
provenance and actual contexts. Its paths are the paths of the stage (`StagePath.recap`), its path
edges the restricted edges (`pathEdges_recap`), which vanish above `N` (`edgesBelow_pathEdges`). A
weak certificate is a coefficient certificate of the re-capped stage
(`WeakCertified.recap_oldCert`), with the record factor `2^N C` when the record lengths are at most
`ε_i`. With `N = 1 + J_wN_w` the energy estimates run with constants independent of `Dm`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal

namespace AVRegularity.Providers.WeakGen

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- An identity with the order cap `N`. -/
def _root_.AVRegularity.CoefficientIdentity.recap {Dc N : ℕ} {Hu Hv : Type*} [NormedAddCommGroup Hu]
    [NormedSpace ℝ Hu] [NormedAddCommGroup Hv] [NormedSpace ℝ Hv]
    (c : CoefficientIdentity Dc Hu Hv) (h : c.maxOrder ≤ N) : CoefficientIdentity N Hu Hv :=
  ⟨c.map, c.record, c.maxOrder, c.two_le, h, c.le_birth⟩

/-- **The stage with the order cap `N`** and the registry `𝒮`. -/
def _root_.AVRegularity.GenStage.recap (G : GenStage D ScalarH Dm b j₀) (N : ℕ)
    (h : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N) (𝒮 : SeedExports) :
    GenStage D ScalarH N b j₀ where
  level := G.level
  comps := G.comps
  fam :=
    { Γ := G.fam.Γ
      fintypeΓ := G.fam.fintypeΓ
      identity := fun v u γ => (G.fam.identity v u γ).recap (h v u γ)
      piece := G.fam.piece
      flux := G.fam.flux
      flux_periodic := G.fam.flux_periodic
      flux_zero := G.fam.flux_zero
      weight := G.fam.weight
      weight_nonneg := G.fam.weight_nonneg
      weight_zero := G.fam.weight_zero
      locally_finite := G.fam.locally_finite
      weight_sum := G.fam.weight_sum }
  prov := G.prov
  actual := G.actual
  exports := 𝒮

variable {G : GenStage D ScalarH Dm b j₀} {N : ℕ}
  {hN : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N} {𝒮 : SeedExports}

/-- A path of the stage as a path of the re-capped stage. -/
def _root_.AVRegularity.StagePath.recap {h : ℕ} (π : StagePath G h) : StagePath (G.recap N hN 𝒮) h :=
  ⟨π.step, π.joined⟩

/-- **The path edges of the re-capped stage are the restricted path edges.** -/
theorem pathEdges_recap (hND : N ≤ Dm) {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) :
    pathEdges (G.recap N hN 𝒮) π.recap p c = restrictEdges hND (pathEdges G π p c) := rfl

/-- The path edges vanish above the maximal orders. -/
theorem edgesBelow_pathEdges (hN : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).maxOrder ≤ N)
    {h : ℕ} (π : StagePath G h) (p : OddSlot) (c : StageCtx D b j₀ G.level p) :
    EdgesBelow N (pathEdges G π p c) := by
  intro v u d hd
  simp only [pathEdges]
  split_ifs with hvu hdo
  · exact absurd (hdo.trans (hN _ _ _)) (not_le.mpr hd)
  · rfl
  · rfl

/-- The lift data of a path family of the re-capped stage are the restricted lift data. -/
theorem familyLiftData_recap_of (hND : N ≤ Dm) {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (k : ℤ) (A : RealChain) (ρ : ℝ) :
    familyLiftData D (G.recap N hN 𝒮).level k A ρ (pathEdges (G.recap N hN 𝒮) π.recap p c) =
      restrictData hND (familyLiftData D G.level k A ρ (pathEdges G π p c)) := by
  unfold restrictData
  rw [pathEdges_recap hND]
  rfl

/-- The same, for a context of the re-capped stage. -/
theorem familyLiftData_recap (hND : N ≤ Dm) {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (c : StageCtx D b j₀ (G.recap N hN 𝒮).level p) (k : ℤ) (A : RealChain) (ρ : ℝ) :
    familyLiftData D (G.recap N hN 𝒮).level k A ρ (pathEdges (G.recap N hN 𝒮) π.recap p c) =
      restrictData hND (familyLiftData D G.level k A ρ (pathEdges G π p c)) :=
  familyLiftData_recap_of hND π p c k A ρ

/-- **The lift sequences of a path family are lift sequences of the re-capped path family.** -/
theorem isLiftSequenceOn_recap (hND : N ≤ Dm) {h : ℕ} (π : StagePath G h) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) (k : ℤ) (A : RealChain) (ρ : ℝ) {Ω : Set (Vec 2)}
    {sX sZ Nl H : ℕ} {t₀ t₁ : ℝ} {Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}
    (hNl : Nl ≤ N)
    (hC : IsLiftSequenceOn Ω (familyLiftData D G.level k A ρ (pathEdges G π p c)) sX sZ t₀ t₁ Nl
      H Cc) :
    IsLiftSequenceOn Ω (familyLiftData D (G.recap N hN 𝒮).level k A ρ
      (pathEdges (G.recap N hN 𝒮) π.recap p c)) sX sZ t₀ t₁ Nl H Cc := by
  rw [familyLiftData_recap_of hND]
  exact isLiftSequenceOn_restrict hND (edgesBelow_liftEdges (edgesBelow_pathEdges hN π p c) _ _)
    Cc hNl hC

/-- **A weak certificate gives a coefficient certificate of the re-capped stage**, with the
reserve `mres`, the weight `L` and the record factor `2^N C`, when the record lengths are at most
`ε_i`. -/
theorem WeakCertified.recap_oldCert {C mres : ℝ} {L : ℕ} (hW : WeakCertified C mres L G)
    (hC : 0 ≤ C) (hε : 0 < D.eps G.level)
    (hlen : ∀ v u (γ : G.fam.Γ v u), (G.fam.identity v u γ).record.length ≤ D.eps G.level) :
    (G.recap N hN 𝒮).OldCert noExports (fun _ => mres) L (2 ^ N * C) := by
  intro v u γ
  set n := (G.fam.identity v u γ).maxOrder with hn
  set ρ := (G.fam.identity v u γ).record.length / D.eps G.level with hρ
  have hρ0 : 0 < ρ := div_pos (G.fam.identity v u γ).record.length_pos hε
  have hρ1 : ρ ≤ 1 := (div_le_one hε).mpr (hlen v u γ)
  set θ₀ := C * (G.fam.identity v u γ).record.size * ρ ^ (n - 2) with hθ₀
  have hθ₀0 : 0 ≤ θ₀ :=
    mul_nonneg (mul_nonneg hC (G.fam.identity v u γ).record.size_nonneg) (pow_nonneg hρ0.le _)
  refine ⟨fun _ _ _ => θ₀, fun _ _ _ => hθ₀0, fun d hd hdn => ?_, fun d α c => ?_⟩
  · have hsum : ∑ _α : DerivativeWord2 (d - 1), ∑ _c : Fin 2, θ₀ = 2 ^ d * θ₀ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
        DerivativeWord2, DerivativeWord, Fintype.card_fun]
      push_cast
      rw [← mul_assoc, ← pow_succ]
      congr 2
      omega
    show (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) * _ ≤ _
    rw [hsum, show D.eps G.level / (G.fam.identity v u γ).record.length = ρ⁻¹ by rw [hρ, inv_div]]
    exact witness_algebra hρ0 hρ1 hC (G.fam.identity v u γ).record.size_nonneg hd hdn (hN v u γ)
  · obtain ⟨f, F, hf, hc, hsz⟩ := hW v u γ d α c
    exact ⟨f, F, fun p => ⟨isGeneratedCtxFrom_of_noExports (hf p).1, (hf p).2, hc p⟩, hsz⟩

end AVRegularity.Providers.WeakGen
end
end

section
/-! On the original window, phase-equivalent contexts give identical path edges and lift data.
The localized recurrence can therefore be transported without an independent production box. -/
@[expose] public noncomputable section
open Homogenization Set AVRegularity.Sobolev
namespace AVRegularity.Providers.WeakGen
open AVRegularity.EntryWeakProofs AVRegularity.WeakEntryProofs AVRegularity.Providers.GenSem

/-- The lift relation reads edge fields only on its solving window. -/
theorem isLiftSequenceOn_edge_window_congr {ι : Type*} [Fintype ι] {hv : ι → Type*}
    [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)]
    [∀ i, FiniteDimensional ℝ (hv i)] {Dm : ℕ}
    {Ω : Set (Vec 2)} (hΩ : IsOpen Ω) (Q : LiftOperatorData ι hv Dm)
    (edge : ConstituentEdges Dm hv) (a b : ℝ) (sX sZ N H : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff ι hv)
    (hc : IsLiftSequenceOn Ω Q sX sZ a b N H Cc)
    (he : ∀ t ∈ Icc a b, SlowOpenEdgeEq Ω t Q.edge edge) :
    IsLiftSequenceOn Ω {Q with edge := edge} sX sZ a b N H Cc := by
  refine ⟨hc.1, hc.2.1, hc.2.2.1, hc.2.2.2.1, hc.2.2.2.2.1, hc.2.2.2.2.2.1, ?_⟩
  intro hh hhh n hn hnN f hf X hX
  apply CycleComparison.Lift.cellFieldInverse_source_congr_on _ _ sZ a b 0 _ _ _ _
    (hc.2.2.2.2.2.2 hh hhh n hn hnN f hf X hX)
  intro t ht
  funext z
  exact (liftCellSource_edge_slow_open_congr hΩ Q edge Cc (fun _ => f) hh n t
    (he t ht) X hX z)

/-- Weak holomorphic generation gives integer child-phase invariance on the output window. -/
theorem weakHolGen_flux_phase_lattice {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hb : 0 < b) (G : GenStage D ScalarH Dm b j₀) (hgen : WeakHolGen G)
    (p : OddSlot) (A B : StageCtx D b j₀ G.level p)
    (hphase : WeakChainPhaseLatticeEquivalent A.1 B.1)
    (v u : CompIn G.comps) (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1))
    (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) (X z : Vec 2) :
    G.fam.flux p A v u γ d I t X z = G.fam.flux p B v u γ d I t X z := by
  funext c
  obtain ⟨f, F, hF, hval⟩ := hgen v u γ d I c
  rw [hval p A t ht, hval p B t ht]
  have hr := hphase.recenter D hΛ B.2.2.2.2.2.1 (D.eps (G.level - 1) • X)
  by_cases hA : IsAdmissibleChain D b j₀ G.level p.1
      (A.1.recenter D (D.eps (G.level - 1) • X))
  · have hB := hr.admissible D b j₀ G.level p.1 hA
    rw [ite_eq_left hA, ite_eq_left hB]
    exact holExtension_phase_lattice hΛ hb (hF p).2 _ _ hA hr t ht z
  · have hB : ¬ IsAdmissibleChain D b j₀ G.level p.1
        (B.1.recenter D (D.eps (G.level - 1) • X)) :=
      fun hB => hA (hr.symm.admissible D b j₀ G.level p.1 hB)
    rw [ite_eq_right hA, ite_eq_right hB]

/-- The lifted path edges agree on every slow offset throughout their original window. -/
theorem weakHolGen_lifted_edges_phase_lattice {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D ScalarH Dm b j₀) (hgen : WeakHolGen G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A B : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A)
    (hB : IsAdmissibleChain D b j₀ G.level k B)
    (hphase : WeakChainPhaseLatticeEquivalent A B) (t : ℝ)
    (ht : t ∈ Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level)) :
    SlowOpenEdgeEq univ t
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)).edge := by
  have ht' := cellScaleSq_mul_mem_ocPulseWindow
    (weakData_cellScaleSq_pos D hΛ hζ hband G.level) ht
  intro v u d
  simp only [familyLiftData, liftEdges, pathEdges]
  split_ifs with hvu hd
  · refine List.Forall₂.cons ⟨rfl, ?_⟩ .nil
    intro I X _ z
    exact weakHolGen_flux_phase_lattice hΛ hb G hgen ⟨k, hk⟩ ⟨A, hA⟩ ⟨B, hB⟩
      hphase _ _ (π.step ⟨u, hvu.2⟩).2.2 d.1 I _ ht' _ z
  · exact .nil
  · exact .nil

/-- Transport a path lift along an integer phase change of its history. -/
theorem weakHolGen_path_lift_transport {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}
    (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hband : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b)
    (G : GenStage D ScalarH Dm b j₀) (hgen : WeakHolGen G)
    {h : ℕ} (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (A B : RealChain) (hA : IsAdmissibleChain D b j₀ G.level k A)
    (hB : IsAdmissibleChain D b j₀ G.level k B)
    (hphase : WeakChainPhaseLatticeEquivalent A B) (sX sZ N : ℕ)
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hc : IsLiftSequenceOn (ladderOmega D b j₀ G.level k B ρ)
      (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc) :
    IsLiftSequenceOn (ladderOmega D b j₀ G.level k A ρ)
      (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) sX sZ
      (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc := by
  have hΩ := hphase.ladderOmega D hΛ hB.2.2.2.2.1 b j₀ G.level k ρ
  rw [← hΩ] at hc
  let Q := familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨B, hB⟩)
  let edge := (familyLiftData D G.level k A ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)).edge
  have he : ∀ t ∈ Icc (D.slotStart G.level k / D.cellScaleSq G.level)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      SlowOpenEdgeEq (ladderOmega D b j₀ G.level k A ρ) t Q.edge edge := by
    intro t ht v u d
    exact (weakHolGen_lifted_edges_phase_lattice hΛ hζ hband hb G hgen π k hk ρ B A hB hA
      hphase.symm t ht v u d).imp (fun _ _ hh =>
        ⟨hh.1, fun I X _ z => hh.2 I X (mem_univ X) z⟩)
  have hs := isLiftSequenceOn_edge_window_congr (isOpen_ladderOmega D b j₀ G.level k A ρ)
    Q edge _ _ sX sZ N h Cc hc he
  change IsLiftSequenceOn _
    (familyLiftData D G.level k B ρ (pathEdges G π ⟨k, hk⟩ ⟨A, hA⟩)) _ _ _ _ _ _ _ at hs
  rw [familyLiftData_geometry_congr D G.level k B A hB.2.2.1 hA.2.2.1
    (hphase.geom D hΛ hB.2.2.2.2.1).symm ρ] at hs
  exact hs

/-- At one time, global equality of edge fields preserves the path mean. -/
theorem pathMeanFlux_edge_time_congr (D : OCData) (m : ℕ) (ρ : ℝ) {Dm h : ℕ}
    (Q : LiftOperatorData (Fin (h + 1)) (fun _ => ℝ) Dm)
    (edge : ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ))
    (Cc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) (n : ℕ) (t : ℝ)
    (he : SlowOpenEdgeEq univ ((D.cellScaleSq m)⁻¹ * t) Q.edge edge) :
    pathMeanFlux D m ρ Q Cc n t = pathMeanFlux D m ρ {Q with edge := edge} Cc n t := by
  funext f y k
  unfold pathMeanFlux
  have heq := funext (fun z => liftFluxX_edge_slow_open_congr isOpen_univ Q edge Cc
    (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n _ he k
    (ρ⁻¹ • y) (mem_univ _) z)
  dsimp only at heq
  rw [heq]

end AVRegularity.Providers.WeakGen
end
end
end
