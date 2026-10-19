-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Construction.Preservation.FullLift.ReadoutIndexedFiber
public import AVRegularity.CycleComparison.Coarse.Fact.GradFluxIdent
public import AVRegularity.IterationPassage.Assembly.IterationCascadeAssemblyProbe
import AVRegularity.CycleReference.TorusStreamFluxEquation
import AVRegularity.Construction.Preservation.FullLift.AmbientLiftActionPointwise
import AVRegularity.Construction.Preservation.Buffer.KernelMaterialIncrement
import AVRegularity.KernelEnergy.TorusKernelStrongTraceExistence
import AVRegularity.Construction.EntryScales.TerminalCore
import AVRegularity.Construction.Preservation.FullLift.HigherRetainedTraceAtOrder
import AVRegularity.CycleComparison.Reconstruction.ApproxJets
import Mathlib.Algebra.Order.Star.Real

section
@[expose] public noncomputable section

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.IterationPassage.Amplitude

/-! A small covariance polynomial differs from the identity by a small operator.
The identity term is kept separate; a bound on the whole polynomial would lose
its coefficient one in the amplitude recurrence. -/

open CycleComparison.Coarse Construction.Preservation.FullLift

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E]

private def tailCoeff (l : ℕ) : ℝ := (-1 : ℝ) ^ (l + 1) / ((l + 1).factorial : ℝ)

private def tailConst (M : ℝ) (p : ℕ) : ℝ :=
  ∑ l ∈ Finset.range p, |tailCoeff l| * M ^ (l + 1)

private theorem tailCoeff_abs_le (l : ℕ) : |tailCoeff l| ≤ 1 := by
  simp only [tailCoeff, abs_div, abs_pow, abs_neg, abs_one, one_pow,
    abs_of_nonneg (Nat.cast_nonneg (l + 1).factorial : (0 : ℝ) ≤ _)]
  apply (div_le_one (by exact_mod_cast Nat.factorial_pos (l + 1))).mpr
  exact_mod_cast Nat.factorial_pos (l + 1)

private theorem tailConst_le {M : ℝ} (hM : 0 ≤ M) (hM1 : M ≤ 1) (p : ℕ) :
    tailConst M p ≤ p * M := by
  calc
    tailConst M p ≤ ∑ l ∈ Finset.range p, M := by
      apply Finset.sum_le_sum
      intro l _
      exact (mul_le_of_le_one_left (pow_nonneg hM _) (tailCoeff_abs_le l)).trans
        (by rw [pow_succ]; exact mul_le_of_le_one_left hM (pow_le_one₀ hM hM1))
    _ = p * M := by simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

omit [MeasurableSpace E] [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] in
private theorem covPolyQ_eq_id_tail (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p : ℕ)
    (ψ : Vec 2 → E) : covPolyQ Hc p ψ = ψ +
      fun x => ∑ l ∈ Finset.range p, tailCoeff l • ((covOperator Hc)^[l + 1] ψ) x := by
  funext x
  unfold covPolyQ
  rw [Finset.sum_apply, Finset.sum_range_succ']
  simp only [Pi.smul_apply, pow_zero, Nat.factorial_zero, Nat.cast_one, div_one,
    Function.iterate_zero, id_eq, one_smul, Pi.add_apply, tailCoeff]
  exact add_comm _ _

private def tailAdj (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p Kc : ℕ) :
    TorusAdj (fun ψ : Vec 2 → E => fun x =>
      ∑ l ∈ Finset.range p, tailCoeff l • ((covOperator Hc)^[l + 1] ψ) x)
      (2 * p) 0 Kc (tailConst (covBound Hc) p) :=
  (TorusAdj.sumMem (Finset.range p) (fun l hl =>
    ((TorusAdj.covIter (E := E) Hc le_rfl (l + 1) 0 Kc).liftOrder
      (by have := Finset.mem_range.mp hl; omega)).smul (tailCoeff l)))
      |>.ofOp (by funext ψ x; simp only [Pi.smul_apply])

private theorem tailAdj_bound {ρ : ℝ} (hρ : 0 < ρ)
    (Hc : Matrix (Fin 2) (Fin 2) ℝ) (p Kc : ℕ) :
    (tailAdj (E := E) Hc p Kc).FBound ρ (tailConst (fbCovConst ρ Hc Kc) p) := by
  have h := TorusAdj.FBound.sumMem (Finset.range p) (fun l hl =>
    ((TorusAdj.FBound.covIter (E := E) hρ Hc le_rfl (l + 1) 0 Kc).liftOrder (m' := 2 * p)
      (pow_nonneg (fbCovConst_nonneg hρ Hc Kc) _) (by have := Finset.mem_range.mp hl; omega)).smul
        (tailCoeff l))
  exact TorusAdj.FBound.ofOp _ h

/-- The covariance correction costs at most `p*M` of the reserved input norm. -/
theorem amplitude_covariance_difference_le {ρ M : ℝ} {p R : ℕ}
    (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hR : 2 * p ≤ R)
    (hM : fbCovConst ρ Hc R ≤ M) (hM1 : M ≤ 1)
    (Z : TorusHk R E) (W : TorusHk 0 E) (hW : IsCovImage (covPolyQ Hc p) Z W) :
    Real.sqrt (factorialNormSq ρ
      (W - truncateTorusHk (Nat.zero_le R) Z).val) ≤
        p * M * Real.sqrt (factorialNormSq ρ Z.val) := by
  let A := (tailAdj (E := E) Hc p R).liftOrder hR
  let Z0 := truncateTorusHk (Nat.zero_le R) Z
  let Zr := torusCast (Nat.zero_add R).symm Z
  have hA : IsCovImage (covPolyQ Hc p) Z (Z0 + A.adj 0 (by omega) Zr) := by
    intro ψ hψ hp
    change cellInner (CycleComparison.Coarse.tval (Z0 + A.adj 0 (by omega) Zr)) ψ =
      cellInner (CycleComparison.Coarse.tval Z) (covPolyQ Hc p ψ)
    rw [cellInner_tval_add _ _ hψ.continuous,
      A.ident 0 (by omega) Zr ψ (hψ.of_le (by exact_mod_cast le_top)) hp, tval_torusCast]
    rw [show CycleComparison.Coarse.tval Z0 = CycleComparison.Coarse.tval Z from
      tval_truncateTorusHk _ Z]
    rw [covPolyQ_eq_id_tail]
    exact (cellInner_add_right _ (integrable_tval_inner Z hψ.continuous)
      (integrable_tval_inner Z (A.continuous_apply
        (hψ.of_le (by exact_mod_cast le_top)) hp))).symm
  have he := covImage_unique (covPolyQ Hc p) Z W _ hW hA
  have htail0 : 0 ≤ tailConst (fbCovConst ρ Hc R) p :=
    Finset.sum_nonneg fun l _ => mul_nonneg (abs_nonneg _) (pow_nonneg (fbCovConst_nonneg hρ Hc R) _)
  have hb := ((tailAdj_bound (E := E) hρ Hc p R).liftOrder htail0 hR) 0 (by omega) Zr
  dsimp only [Zr] at hb
  rw [sqrt_fNSq_torusCast] at hb
  have hconst : tailConst (fbCovConst ρ Hc R) p ≤ p * M := by
    calc
      _ ≤ tailConst M p := Finset.sum_le_sum fun l _ =>
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (fbCovConst_nonneg hρ Hc R) hM _) (abs_nonneg _)
      _ ≤ _ := tailConst_le ((fbCovConst_nonneg hρ Hc R).trans hM) hM1 p
  rw [he]
  change Real.sqrt (factorialNormSq ρ ((Z0 + A.adj 0 (by omega) Zr) - Z0).val) ≤ _
  rw [add_sub_cancel_left]
  exact hb.trans (mul_le_mul_of_nonneg_right hconst (Real.sqrt_nonneg _))

end AVRegularity.IterationPassage.Amplitude
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Amplitude

/-! The fixed parameters and an actual arbitrary cascade run used by the amplitude assembly.
No datum-dependent field is included in the uniform constant choices. -/

structure Base where
  α : ℝ
  s : ℝ
  q : ℝ
  ζ : ℝ → ℝ
  alpha_pos : 0 < α
  alpha_lt : α < 1 / 3
  s_pos : 0 < s
  s_lt : s < (1 - α) / 2
  admissible : IsAdmissibleQ α s q
  profile : IsFastProfile ζ

structure Parameters (B : Base) where
  Λ : ℕ
  large : 128 ≤ Λ
  φ₀ : Vec 2 → ℝ
  hφ₀ : Integrable φ₀
  smooth : ContDiff ℝ (⊤ : ℕ∞) φ₀
  nonneg : ∀ z, 0 ≤ φ₀ z
  integral_one : ∫ z, φ₀ z = 1
  support : Function.support φ₀ ⊆ Analysis.Convolution.closedEuclideanUnitBall
  bw : ℝ
  bw_pos : 0 < bw
  bw_small : bw ≤ 1 / 10000
  K : ℕ
  Pacc : ℝ
  t₀ : ℝ
  T₀ : ℝ
  K_three : 3 ≤ K
  accuracy_pos : 0 < Pacc
  wait_pos : 0 < t₀
  horizon_lt : t₀ < T₀
  r₀ : ℕ
  D₀ : ℕ
  τe : ℝ
  lamE : ℝ
  σE : ℝ
  entry_pos : 0 < τe
  lambda_pos : 0 < lamE
  sigma_pos : 0 < σE
  Q : ℝ
  H : ℕ
  J : ℕ
  N : ℕ
  p : ℕ
  nk : ℕ
  Lc : ℕ
  Lf : ℕ
  Lpr : ℕ
  Acl : ℕ
  Naux : ℕ
  Nout : ℕ
  Kres : ℕ
  L : ℕ
  σ₀ : ℝ
  a : ℝ
  σ : ℝ
  schedule : IsCascadeSchedule B.α B.s B.q K Pacc lamE σE D₀ Q H J N p nk Lc Lf Lpr
    Acl Naux Nout Kres L σ₀ a σ
  npad : ℕ
  sX : ℕ
  sZ : ℕ
  Ce : ℝ
  kS : InvConsts
  seed_constant : 1 ≤ Ce
  c0_pos : 0 < kS.c₀
  c0_small : kS.c₀ ≤ 1
  cr_pos : 0 < kS.cr
  cr_small : kS.cr ≤ 1
  seed_sigma : kS.σf = σE
  seed_lambda : kS.lamC = lamE
  allocation : IsSeedAllocation kS r₀ D₀ H J N p Kres Lpr Lc Lf
  kI : InvConsts
  invariant_constants : IsInvariantAdmissible kS kS kI H J N p nk Kres Lpr Lc Lf
    σ₀ (ocDelta B.α B.q) B.q (ocC B.α B.q)
  CI : ℝ
  Cw : ℝ
  j₀ : ℕ
  ledger : IsLedgerAdmissible Ce CI Cw Ce 1
  carrier : IsCarrierStart B.α B.q Λ bw 1 1 j₀
  CQ : ℝ
  Cp : ℝ

def Parameters.cap {B : Base} (A : Parameters B) : ℕ := succSchedD A.D₀ A.N A.p (A.H + 1)

def Parameters.menu {B : Base} (A : Parameters B) (Mnat : ℕ) : SuccMenu :=
  succMenu Mnat A.r₀ A.D₀ A.H A.J A.N A.p A.npad A.sX A.sZ (succEta0 B.α B.q B.s)

def Parameters.provenance {B : Base} (A : Parameters B) (D : OCData) : ProvParams :=
  succProvParams D A.Cw A.kI.cr A.σ₀ (succEta0 B.α B.q B.s) A.N A.p

structure Constants where
  C : ℝ
  mA : ℕ
  positive : 0 < C

structure Plan (B : Base) where
  Λ₀ : ℕ
  large : 128 ≤ Λ₀
  constants : Parameters B → Constants

structure Run {B : Base} (A : Parameters B) (K : Constants) where
  m₀ : ℕ
  above_floor : K.mA ≤ m₀
  D : OCData
  alpha_eq : D.α = B.α
  q_eq : D.q = B.q
  lambda_eq : D.Λ = A.Λ
  profile_eq : D.ζ = B.ζ
  stream : IsOCStreamSeq B.α B.q A.Λ B.ζ D.Φ
  M : ℕ
  band : IsOCBandChain B.α B.q A.Λ B.ζ M D.κ
  terminal : D.term = M
  Mnat : ℕ
  top : M ≤ Mnat
  law : BirthLaw
  birth_law : IsSuccessorLaw B.α B.q B.s
    (wordsUpTo (succAlphabetOf A.r₀ A.D₀ A.H A.J A.N A.p A.npad) (A.J + 1)).card law
  seedK : ℕ → KernelSpec
  freshK : ℕ → KernelSpec
  fresh : ∀ b', 1 ≤ b' → b' < M → IsFreshKernel D A.kI.cr A.σ₀ A.nk.toPNat' b' (freshK b')
  seed : GenStage D ScalarH A.cap A.bw A.j₀
  n : ℕ
  tS : ℝ
  tf : ℝ
  wait : tS + A.t₀ < tf
  horizon : tf - tS ≤ A.T₀
  generated : IsGeneratedSeed law (A.provenance D) seedK freshK A.φ₀ A.hφ₀
    Mnat A.kS seed n tS tf A.Ce A.τe A.r₀ A.D₀
  bottom_lt : m₀ < n
  n_lt : n < M
  stage : ℕ → GenStage D ScalarH A.cap A.bw A.j₀
  ext : ℕ → GenStage D ScalarH A.cap A.bw A.j₀
  hist : ℕ → ℝ
  st : ℕ → ℝ
  tp : ℕ → ℝ
  Preg : (j : ℕ) → (∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)) →ₗ[ℝ]
    (∀ v : CompIn (stage j).comps, TorusHk A.Nout (ScalarH v.1.root))
  frame : CascadeFrame law (A.provenance D) (A.menu Mnat) seedK freshK A.φ₀ A.hφ₀ Mnat A.kI
    A.CI A.τe (succEta0 B.α B.q B.s) A.Kres
    (wordsUpTo (succAlphabetOf A.r₀ A.D₀ A.H A.J A.N A.p A.npad) (A.J + 1)).card A.p
    A.Nout A.Naux A.Q A.CQ A.Cp seed n m₀ tS A.t₀ tf stage ext hist st tp Preg
  f : ∀ v : CompIn (stage n).comps, TorusHk 0 (ScalarH v.1.root)
  U : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 0 (ScalarH v.1.root)
  Uw : (j : ℕ) → ∀ v : CompIn (stage j).comps, ℝ → TorusHk 1 (ScalarH v.1.root)
  Uk : (j : ℕ) → ∀ v u (_ : (stage j).fam.Γ v u), ℝ → TorusHk (0 + A.cap - 1) (ScalarH u.1.root)
  Y0 : (j : ℕ) → ∀ v : CompIn (stage j).comps, TorusHk 0 (ScalarH v.1.root)
  datum : Y0 n = f
  solution : ∀ j, m₀ ≤ j → j ≤ n →
    (stage j).IsRegSolution (A.provenance D) seedK freshK A.φ₀ A.hφ₀
      (D.κ j) (streamVel (D.Φ j)) 0 (st j) tf (Y0 j) (fun _ _ => 0) (fun _ _ => 0)
      (U j) (Uw j) (Uk j)
  trace : ∀ j, m₀ < j → j ≤ n → IsRetainedTrace (stage j) (stage (j - 1)) j A.p (tp j)
    (Preg j (fun v => U j v (cascadeRestart D hist st j))) (Y0 (j - 1))

def Run.initialNorm {B : Base} {A : Parameters B} {K : Constants} (r : Run A K) : ℝ :=
  weightedNorm 1 ((r.stage r.n).mass r.law) (fun _ => 1) r.f

def Run.markedNorm {B : Base} {A : Parameters B} {K : Constants} (r : Run A K) (j : ℕ) (t : ℝ) : ℝ :=
  weightedNorm 1 ((r.stage j).mass r.law) ((r.stage j).marker r.law) (fun v => r.U j v t)

def Run.reference {B : Base} {A : Parameters B} {K : Constants} (r : Run A K) (j : ℕ) : ℝ :=
  ampRef r.D K.C A.Q r.n r.initialNorm j

def Run.Restart {B : Base} {A : Parameters B} {K : Constants} (r : Run A K) (j : ℕ) : Prop :=
  cascadeRestart r.D r.hist r.st j ∈ Set.Icc (r.st j) r.tf ∧
    (r.stage j).IsRegSolution (A.provenance r.D) r.seedK r.freshK A.φ₀ A.hφ₀
      (r.D.κ j) (streamVel (r.D.Φ j)) 0 (cascadeRestart r.D r.hist r.st j) r.tf
      (fun v => r.U j v (cascadeRestart r.D r.hist r.st j))
      (fun _ _ => 0) (fun _ _ => 0) (r.U j) (r.Uw j) (r.Uk j)

/-! Composition of the arbitrary-frame amplitude estimate. The analytic ingredients
read the given frame, rather than a particular output of `iteration_passage`. -/

/-- Contraction of the seed solution, including identification of its unit marker. -/
def BaseBoundStatement (B : Base) (plan : Plan B) : Prop :=
  ∀ (A : Parameters B), plan.Λ₀ ≤ A.Λ → ∀ r : Run A (plan.constants A),
    ∀ t ∈ Set.Icc (r.st r.n) r.tf, r.markedNorm r.n t ≤ r.initialNorm

/-- The near-unit marked estimate obtained from preparation, covariance transfer,
the retained trace and homogeneous contraction on the retained stage. -/
def OneStepBoundStatement (B : Base) (plan : Plan B) : Prop :=
  ∀ (A : Parameters B), plan.Λ₀ ≤ A.Λ → ∀ r : Run A (plan.constants A),
    ∀ j, r.m₀ < j → j ≤ r.n → r.Restart j →
    ∀ Ain : ℝ, r.markedNorm j (cascadeRestart r.D r.hist r.st j) ≤ Ain →
    ∀ t ∈ Set.Icc (r.st (j - 1)) r.tf,
      r.markedNorm (j - 1) t ≤
        (1 + (plan.constants A).C *
          (r.D.eps (j - 1) ^ A.Q + r.D.eps (j - 1) ^ ocDelta r.D.α r.D.q)) * Ain

/-- The actual solution can be restarted at the frame's preparation time. -/
def RestartStatement (B : Base) (plan : Plan B) : Prop :=
  ∀ (A : Parameters B), plan.Λ₀ ≤ A.Λ → ∀ r : Run A (plan.constants A),
    ∀ j, r.m₀ < j → j ≤ r.n → r.Restart j

/-- Finite recurrences suffice for the globally quantified recurrence lemma. -/
def FiniteRecurrenceExtensionStatement : Prop :=
  ∀ (X g c : ℕ → ℝ) (m₀ n : ℕ), 0 ≤ X m₀ →
    (∀ j, 0 ≤ g j) → (∀ j, 0 ≤ c j) →
    (∀ j, m₀ < j → j ≤ n → X j ≤ (1 + g j) * X (j - 1) + c j) →
    ∀ k, m₀ ≤ k → k ≤ n →
      X k ≤ Real.exp (∑ j ∈ Finset.Ioc m₀ k, g j) *
        (X m₀ + ∑ j ∈ Finset.Ioc m₀ k, c j)

/-- Summability of the scale errors bounds every reference product uniformly in
both endpoints. The extension adapter is an explicit input on this proof path. -/
def ProductBoundStatement (B : Base) (plan : Plan B) : Prop :=
  FiniteRecurrenceExtensionStatement →
  ∀ (A : Parameters B), plan.Λ₀ ≤ A.Λ → ∀ r : Run A (plan.constants A),
    ∀ j, r.m₀ ≤ j → j ≤ r.n → r.reference j ≤ (plan.constants A).C * r.initialNorm

private theorem reference_step {B : Base} {A : Parameters B} {K : Constants}
    (r : Run A K) {i : ℕ} (hi : i < r.n) :
    r.reference i = (1 + K.C * (r.D.eps i ^ A.Q + r.D.eps i ^ ocDelta r.D.α r.D.q)) *
      r.reference (i + 1) := by
  let g := fun k => 1 + K.C *
    (r.D.eps (k - 1) ^ A.Q + r.D.eps (k - 1) ^ ocDelta r.D.α r.D.q)
  have hsplit := Finset.prod_Ioc_consecutive g (Nat.le_succ i) (Nat.succ_le_of_lt hi)
  simp only [Nat.Ioc_succ_singleton, Finset.prod_singleton] at hsplit
  change r.initialNorm * (∏ k ∈ Finset.Ioc i r.n, g k) =
    _ * (r.initialNorm * ∏ k ∈ Finset.Ioc (i + 1) r.n, g k)
  rw [← hsplit]
  dsimp only [g]
  simp only [Nat.add_sub_cancel]
  ring

/-- The finite downward induction uses only the three local analytic ingredients. -/
theorem amplitude_run_of_ingredients {B : Base} (plan : Plan B)
    (hbase : BaseBoundStatement B plan) (hstep : OneStepBoundStatement B plan)
    (hrestart : RestartStatement B plan) (A : Parameters B) (hΛ : plan.Λ₀ ≤ A.Λ)
    (r : Run A (plan.constants A)) (j : ℕ) (hj : r.m₀ ≤ j) (hjn : j ≤ r.n) :
    ∀ t ∈ Set.Icc (r.st j) r.tf, r.markedNorm j t ≤ r.reference j := by
  apply Nat.decreasingInduction' (m := j) (n := r.n)
      (P := fun i => ∀ t ∈ Set.Icc (r.st i) r.tf, r.markedNorm i t ≤ r.reference i)
      ?_ hjn ?_
  · intro i hin hji ih
    have hi : r.m₀ < i + 1 := by omega
    have hit : i + 1 ≤ r.n := by omega
    have hr := hrestart A hΛ r (i + 1) hi hit
    have hs := hstep A hΛ r (i + 1) hi hit hr (r.reference (i + 1))
      (ih _ hr.1)
    simpa only [Nat.add_sub_cancel, reference_step r hin] using hs
  · simpa only [Run.reference, ampRef, Finset.Ioc_self, Finset.prod_empty, mul_one]
      using hbase A hΛ r

/-- Exact statement, assembled with coherent uniform constants.
The five named ingredients are the only proof hypotheses. -/
theorem cascade_amplitude_product_of_ingredients (plans : ∀ B : Base, Plan B)
    (hbase : ∀ B, BaseBoundStatement B (plans B))
    (hstep : ∀ B, OneStepBoundStatement B (plans B))
    (hrestart : ∀ B, RestartStatement B (plans B))
    (hfinite : FiniteRecurrenceExtensionStatement)
    (hproduct : ∀ B, ProductBoundStatement B (plans B)) :
    Assembly.CascadeAmplitudeProductStatement := by
  intro α s hα₀ hα₁ hs₀ hs₁ q hq ζ hζ
  let B : Base := ⟨α, s, q, ζ, hα₀, hα₁, hs₀, hs₁, hq, hζ⟩
  let plan := plans B
  refine ⟨plan.Λ₀, plan.large, ?_⟩
  intro Λ hΛ
  refine ⟨1, zero_lt_one, ?_⟩
  intro φ₀ hφ₀ hsm hnon hint hsupp bw hbw hbws K Pacc t₀ T₀ hK hP ht hT
    r₀ D₀ τe lamE σE hτ hlam hσ Q H J N p nk Lc Lf Lpr Acl Naux Nout Kres L σ₀ a σ hsch npad
  refine ⟨0, 0, ?_⟩
  intro sX sZ _ _ Ce kS hCe hc₀ hc₀max hcr hcrmax hσf hlamC halloc
  refine ⟨kS, 1, 1, le_refl 1, zero_lt_one, ?_⟩
  intro kI hInv
  refine ⟨Ce, 1, ?_⟩
  intro CI Cw j₀ hled hcar CQ Cp
  let A : Parameters B := {
    Λ := Λ, large := plan.large.trans hΛ, φ₀ := φ₀, hφ₀ := hφ₀
    smooth := hsm, nonneg := hnon, integral_one := hint, support := hsupp
    bw := bw, bw_pos := hbw, bw_small := hbws, K := K, Pacc := Pacc, t₀ := t₀, T₀ := T₀
    K_three := hK, accuracy_pos := hP, wait_pos := ht, horizon_lt := hT
    r₀ := r₀, D₀ := D₀, τe := τe, lamE := lamE, σE := σE
    entry_pos := hτ, lambda_pos := hlam, sigma_pos := hσ
    Q := Q, H := H, J := J, N := N, p := p, nk := nk, Lc := Lc, Lf := Lf, Lpr := Lpr
    Acl := Acl, Naux := Naux, Nout := Nout, Kres := Kres, L := L, σ₀ := σ₀, a := a, σ := σ
    schedule := hsch, npad := npad, sX := sX, sZ := sZ, Ce := Ce, kS := kS
    seed_constant := hCe, c0_pos := hc₀, c0_small := hc₀max, cr_pos := hcr, cr_small := hcrmax
    seed_sigma := hσf, seed_lambda := hlamC, allocation := halloc
    kI := kI, invariant_constants := hInv, CI := CI, Cw := Cw, j₀ := j₀
    ledger := hled, carrier := hcar, CQ := CQ, Cp := Cp }
  refine ⟨(plan.constants A).C, (plan.constants A).mA, (plan.constants A).positive, ?_⟩
  intro m₀ hm D hDα hDq hDΛ hDζ hstream M hband hterm Mnat htop law hlaw seedK freshK hfresh
    seed n tS tf hwait hhorizon hseed hmn hnM stage ext hist st tp Preg hframe
    f U Uw Uk Y0 hdatum hsol htrace j hj hjn
  let r : Run A (plan.constants A) := {
    m₀ := m₀, above_floor := hm, D := D, alpha_eq := hDα, q_eq := hDq, lambda_eq := hDΛ
    profile_eq := hDζ, stream := hstream, M := M, band := hband, terminal := hterm
    Mnat := Mnat, top := htop, law := law, birth_law := hlaw, seedK := seedK, freshK := freshK
    fresh := hfresh, seed := seed, n := n, tS := tS, tf := tf, wait := hwait, horizon := hhorizon
    generated := hseed, bottom_lt := hmn, n_lt := hnM, stage := stage, ext := ext
    hist := hist, st := st, tp := tp, Preg := Preg, frame := hframe
    f := f, U := U, Uw := Uw, Uk := Uk, Y0 := Y0, datum := hdatum, solution := hsol, trace := htrace }
  exact ⟨amplitude_run_of_ingredients plan (hbase B) (hstep B) (hrestart B) A hΛ r j hj hjn,
    hproduct B hfinite A hΛ r j hj hjn⟩

end AVRegularity.IterationPassage.Amplitude
end

section
namespace AVRegularity.IterationPassage.Amplitude

/-! An arbitrary finite recurrence is extended without changing its values or sums
on the interval where it is used. -/

/-- The global recurrence interface applies to a recurrence given only up to `n`. -/
theorem amplitude_finite_recurrence_extension : FiniteRecurrenceExtensionStatement := by
  intro X g c m₀ n hX hg hc hrec k hk hkn
  have hmn : m₀ ≤ n := hk.trans hkn
  let Xe := fun j => X (min j n)
  let ge := fun j => if j ≤ n then g j else 0
  let ce := fun j => if j ≤ n then c j else 0
  have hXe : 0 ≤ Xe m₀ := by simpa only [Xe, min_eq_left hmn] using hX
  have hge (j : ℕ) : 0 ≤ ge j := by
    dsimp only [ge]
    split_ifs
    · exact hg j
    · exact le_rfl
  have hce (j : ℕ) : 0 ≤ ce j := by
    dsimp only [ce]
    split_ifs
    · exact hc j
    · exact le_rfl
  have he (j : ℕ) (hj : m₀ < j) : Xe j ≤ (1 + ge j) * Xe (j - 1) + ce j := by
    by_cases hjn : j ≤ n
    · simpa only [Xe, ge, ce, ite_eq_left hjn, min_eq_left hjn,
        min_eq_left (show j - 1 ≤ n by omega)] using hrec j hj hjn
    · have hprev : n ≤ j - 1 := by omega
      simp only [Xe, ge, ce, ite_eq_right hjn, min_eq_right (by omega : n ≤ j),
        min_eq_right hprev, add_zero, one_mul, le_refl]
  have hbound := recurrence_product_bound Xe ge ce m₀ hXe hge hce he k hk
  have hgs : (∑ j ∈ Finset.Ioc m₀ k, ge j) = ∑ j ∈ Finset.Ioc m₀ k, g j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_left ((Finset.mem_Ioc.mp hj).2.trans hkn)
  have hcs : (∑ j ∈ Finset.Ioc m₀ k, ce j) = ∑ j ∈ Finset.Ioc m₀ k, c j := by
    apply Finset.sum_congr rfl
    intro j hj
    exact ite_eq_left ((Finset.mem_Ioc.mp hj).2.trans hkn)
  simpa only [hgs, hcs, Xe, min_eq_left hkn, min_eq_left hmn] using hbound

end AVRegularity.IterationPassage.Amplitude
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Amplitude

/-! Restart the supplied solution by subtracting its integrated weak identities.
No new solution or energy estimate is needed for this ingredient. -/

/-- Every actual cascade solution has the restart required by its preparation frame. -/
theorem amplitude_restart (B : Base) (plan : Plan B) : RestartStatement B plan := by
  intro A _ r j hj hjn
  have hf := r.frame.2.2.2.2.2 j hj hjn
  have hΛ : 1 ≤ r.D.Λ := by
    rw [r.lambda_eq]
    exact (by norm_num : 1 ≤ 128).trans A.large
  have hτ := Construction.Stream.ocTauPP_pos (α := r.D.α) (q := r.D.q) (m := j) hΛ
  have hs : cascadeRestart r.D r.hist r.st j ∈ Set.Icc (r.st j) r.tf :=
    ⟨le_max_left _ _, (le_add_of_nonneg_right (mul_nonneg (by norm_num) hτ.le)).trans
      hf.2.2.2.2.1⟩
  refine ⟨hs, ?_⟩
  have hsub : Set.Icc (cascadeRestart r.D r.hist r.st j) r.tf ⊆ Set.Icc (r.st j) r.tf :=
    Set.Icc_subset_Icc hs.1 le_rfl
  have hμ : volume.restrict (Set.Icc (cascadeRestart r.D r.hist r.st j) r.tf) ≤
      volume.restrict (Set.Icc (r.st j) r.tf) := Measure.restrict_mono hsub le_rfl
  have hsol := r.solution j hj.le hjn
  refine ⟨(fun v => (hsol.1 v).mono hsub),
    (fun v => (hsol.2.1 v).mono_measure hμ),
    (fun v => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.1 v)),
    (fun _ => rfl), (fun v u γ => (hsol.2.2.2.2.1 v u γ).mono_measure hμ),
    (fun v u γ => ae_restrict_of_ae_restrict_of_subset hsub (hsol.2.2.2.2.2.1 v u γ)), ?_⟩
  intro v t ht φ
  exact KernelEnergy.weakIdentity_restart (volume.restrict unitCube) (r.D.κ j)
    (r.st j) (cascadeRestart r.D r.hist r.st j) t hs.1 ht.1 _ _ _ _ _ _ _ _ _ _
    (hsol.2.2.2.2.2.2 v t (hsub ht) φ) (hsol.2.2.2.2.2.2 v _ hs φ)

end AVRegularity.IterationPassage.Amplitude
end
end
end

section
@[expose] public noncomputable section

section
open Filter Topology
namespace AVRegularity.IterationPassage.Amplitude

/-! The reference product needs only positive scale exponents. Its lower threshold
is chosen uniformly before the endpoint, the OC data and the initial datum. -/

private theorem scale_sum_le_tail {q : ℝ} {Λ j n : ℕ} {p : ℝ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hj : 1 ≤ j) (hp : 0 < p) :
    (∑ k ∈ Finset.Ioc j n, ocEpsilon q Λ (k - 1) ^ p) ≤
      ocEpsilon q Λ j ^ p / (1 - (Λ : ℝ) ^ (-p)) := by
  obtain ⟨hsum, htail⟩ := Scales.epsilon_forward_tail hq hΛ hj hp
  have hre : (∑ k ∈ Finset.Ioc j n, ocEpsilon q Λ (k - 1) ^ p) =
      ∑ k ∈ Finset.range (n - j), ocEpsilon q Λ (j + k) ^ p := by
    have hI : Finset.Ioc j n = Finset.Ico (j + 1) (n + 1) := by
      ext k
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    rw [hI, Finset.sum_Ico_eq_sum_range]
    refine Finset.sum_congr (by congr 1; omega) fun k _ => ?_
    congr 2
    omega
  rw [hre]
  exact (hsum.sum_le_tsum _ (fun k _ =>
    Real.rpow_nonneg (Scales.epsilon_basic (m := j + k) hq hΛ).1.le p)).trans htail

/-- The error sum can be made at most one, uniformly over both endpoints. -/
theorem amplitude_scale_error_floor {q Q δ C : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hQ : 0 < Q) (hδ : 0 < δ) (hC : 0 < C) :
    ∃ mA : ℕ, 1 ≤ mA ∧ ∀ j, mA ≤ j → ∀ n,
      C * (∑ k ∈ Finset.Ioc j n,
        (ocEpsilon q Λ (k - 1) ^ Q + ocEpsilon q Λ (k - 1) ^ δ)) ≤ 1 := by
  have hlimQ := (Scales.epsilon_forward_tail (m := 1) hq hΛ le_rfl hQ).1.tendsto_atTop_zero
  have hlimδ := (Scales.epsilon_forward_tail (m := 1) hq hΛ le_rfl hδ).1.tendsto_atTop_zero
  have hlim : Tendsto (fun k : ℕ => C *
      (ocEpsilon q Λ (1 + k) ^ Q / (1 - (Λ : ℝ) ^ (-Q)) +
        ocEpsilon q Λ (1 + k) ^ δ / (1 - (Λ : ℝ) ^ (-δ)))) atTop (𝓝 0) := by
    simpa only [zero_div, zero_add, mul_zero] using
      ((hlimQ.div_const (1 - (Λ : ℝ) ^ (-Q))).add
        (hlimδ.div_const (1 - (Λ : ℝ) ^ (-δ)))).const_mul C
  obtain ⟨m, hm⟩ := eventually_atTop.mp (hlim (gt_mem_nhds zero_lt_one))
  refine ⟨m + 1, by omega, ?_⟩
  intro j hj n
  have hs := hm (j - 1) (by omega)
  dsimp only [Set.mem_ofPred_eq] at hs
  rw [show 1 + (j - 1) = j by omega] at hs
  have hsum := add_le_add (scale_sum_le_tail (j := j) (n := n) hq hΛ (by omega) hQ)
    (scale_sum_le_tail (j := j) (n := n) hq hΛ (by omega) hδ)
  rw [← Finset.sum_add_distrib] at hsum
  exact (mul_le_mul_of_nonneg_left hsum hC.le).trans hs.le

/-- The numeric part of the uniform plan, stated without any cascade data. -/
def ProductPlanOK {B : Base} (plan : Plan B) : Prop :=
  ∀ A : Parameters B, Real.exp 1 ≤ (plan.constants A).C ∧
    1 ≤ (plan.constants A).mA ∧
    ∀ j, (plan.constants A).mA ≤ j → ∀ n,
      (plan.constants A).C * (∑ k ∈ Finset.Ioc j n,
        (ocEpsilon B.q A.Λ (k - 1) ^ A.Q +
          ocEpsilon B.q A.Λ (k - 1) ^ ocDelta B.α B.q)) ≤ 1

/-- The finite recurrence adapter and the summable tail control the stored reference. -/
theorem amplitude_product_bound {B : Base} (plan : Plan B) (hplan : ProductPlanOK plan) :
    ProductBoundStatement B plan := by
  intro hfinite A _ r j hj hjn
  have hq := B.admissible.1
  have hΛ := A.large
  have hε (k : ℕ) : 0 < r.D.eps k := by
    simpa only [OCData.eps, r.q_eq, r.lambda_eq] using (Scales.epsilon_basic (m := k) hq hΛ).1
  let g := fun k => (plan.constants A).C *
    (r.D.eps (k - 1) ^ A.Q + r.D.eps (k - 1) ^ ocDelta r.D.α r.D.q)
  let X := fun k => r.initialNorm * ∏ l ∈ Finset.Ioc j k, (1 + g l)
  have hX : 0 ≤ X j := by
    simpa only [X, Finset.Ioc_self, Finset.prod_empty, mul_one, Run.initialNorm, weightedNorm]
      using Real.sqrt_nonneg _
  have hg (k : ℕ) : 0 ≤ g k := mul_nonneg (plan.constants A).positive.le
    (add_nonneg (Real.rpow_nonneg (hε _).le _) (Real.rpow_nonneg (hε _).le _))
  have hrec (k : ℕ) (hk : j < k) (_hkn : k ≤ r.n) :
      X k ≤ (1 + g k) * X (k - 1) + (0 : ℕ → ℝ) k := by
    obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (show k ≠ 0 by omega)
    simp only [X, Nat.succ_eq_add_one, Nat.add_sub_cancel, Pi.zero_apply, add_zero]
    rw [Finset.prod_Ioc_succ_top (by omega : j ≤ l)]
    exact le_of_eq (by ring)
  have hb := hfinite X g 0 j r.n hX hg (fun _ => le_rfl) hrec r.n hjn le_rfl
  have hs : (∑ k ∈ Finset.Ioc j r.n, g k) ≤ 1 := by
    dsimp only [g]
    rw [← Finset.mul_sum]
    simpa only [OCData.eps, r.q_eq, r.lambda_eq, r.alpha_eq] using
      (hplan A).2.2 j (r.above_floor.trans hj) r.n
  have hfactor : Real.exp (∑ k ∈ Finset.Ioc j r.n, g k) ≤ (plan.constants A).C :=
    (Real.exp_le_exp.mpr hs).trans (hplan A).1
  have hnorm : 0 ≤ r.initialNorm := Real.sqrt_nonneg _
  have hb' : r.reference j ≤ Real.exp (∑ k ∈ Finset.Ioc j r.n, g k) * r.initialNorm := by
    simpa only [X, Pi.zero_apply, Finset.sum_const_zero, add_zero, Finset.Ioc_self,
      Finset.prod_empty, mul_one, Run.reference, ampRef, g] using hb
  exact hb'.trans (mul_le_mul_of_nonneg_right hfactor hnorm)

end AVRegularity.IterationPassage.Amplitude
end

section
namespace AVRegularity.IterationPassage.Amplitude

/-! Keep the small normalized covariance factor at the enhanced preparation radius. -/

open CycleComparison.Coarse Construction.Preservation.FullLift

/-- Uniform normalized covariance information, chosen before Lambda and all cascade data. -/
structure CovarianceControl (B : Base) where
  C : ℝ
  one_le : 1 ≤ C
  Λ₀ : ℕ
  large : 128 ≤ Λ₀
  bound : ∀ Λ, Λ₀ ≤ Λ → ∀ M, 1 ≤ M → ∀ κ : ℕ → ℝ,
    IsOCBandChain B.α B.q Λ B.ζ M κ → ∀ m, 2 ≤ m → m ≤ M →
    ∀ s t i j, |ocCovariance B.α B.q Λ B.ζ m (κ m) (κ (m - 1)) s t i j| /
      ocRh B.α B.q Λ m (κ (m - 1)) ^ 2 ≤ C * ocEpsilon B.q Λ (m - 1) ^ ocDelta B.α B.q

/-- The band-chain estimate supplies the uniform control record. -/
theorem amplitude_covariance_control (B : Base) : Nonempty (CovarianceControl B) := by
  obtain ⟨C, hC, Λ₀, hΛ₀, hb⟩ := CycleReference.bandChain_covariance_estimates
    B.alpha_pos B.alpha_lt B.s_pos B.s_lt B.admissible B.profile
  exact ⟨⟨C, hC, Λ₀, hΛ₀, fun Λ hΛ M hM κ hκ m hm hmM s t i j =>
    (hb Λ hΛ M hM κ hκ m hm hmM s t i j).2.2.2⟩⟩

/-- The finite-order coefficient multiplying the small parent-scale power. -/
def Parameters.covPrice {B : Base} (A : Parameters B) (Ccov : ℝ) : ℝ :=
  4 * Ccov * (A.Nout : ℝ) ^ 2 / A.kI.cr ^ 2

/-- The normalized covariance price remains small at the literal enhanced radius. -/
theorem amplitude_covariance_scale {B : Base} (ctrl : CovarianceControl B)
    (A : Parameters B) (hΛ : ctrl.Λ₀ ≤ A.Λ) {K : Constants} (r : Run A K)
    (j : ℕ) (hj : 2 ≤ j) (hjn : j ≤ r.n) (t : ℝ) :
    0 < rhoEnh r.D A.kI.cr j ∧
    fbCovConst (rhoEnh r.D A.kI.cr j) (covPrimitive r.D j t) A.Nout ≤
      A.covPrice ctrl.C * r.D.eps (j - 1) ^ ocDelta r.D.α r.D.q := by
  have hnM := r.n_lt
  have hM : 1 ≤ r.M := by omega
  have hcr : 0 < A.kI.cr := by rw [A.invariant_constants.2.1]; exact A.cr_pos
  have hΛD : 1 ≤ r.D.Λ := by rw [r.lambda_eq]; exact (by norm_num : 1 ≤ 128).trans A.large
  have hζD : IsFastProfile r.D.ζ := r.profile_eq.symm ▸ B.profile
  have hbandD : IsOCBandChain r.D.α r.D.q r.D.Λ r.D.ζ r.M r.D.κ := by
    simpa only [r.alpha_eq, r.q_eq, r.lambda_eq, r.profile_eq] using r.band
  have hκ := CycleReference.bandChain_pos hΛD hζD hbandD (show j - 1 ≤ r.M by omega)
  have hτ := Construction.Stream.ocTauPP_pos (α := r.D.α) (q := r.D.q) (m := j) hΛD
  have hRh : 0 < ocRh r.D.α r.D.q r.D.Λ j (r.D.κ (j - 1)) := Real.sqrt_pos.mpr (mul_pos hκ hτ)
  have hρ : 0 < rhoEnh r.D A.kI.cr j := mul_pos hcr hRh
  have he (i k : Fin 2) := ctrl.bound A.Λ hΛ r.M hM r.D.κ r.band j hj (by omega) 0 t i k
  have heD (i k : Fin 2) : |covPrimitive r.D j t i k| /
      ocRh r.D.α r.D.q r.D.Λ j (r.D.κ (j - 1)) ^ 2 ≤
        ctrl.C * r.D.eps (j - 1) ^ ocDelta r.D.α r.D.q := by
    simpa only [covPrimitive, OCData.eps, r.alpha_eq, r.q_eq, r.lambda_eq, r.profile_eq] using he i k
  have hentry (i k : Fin 2) : |covPrimitive r.D j t i k| ≤
      (ctrl.C / A.kI.cr ^ 2 * r.D.eps (j - 1) ^ ocDelta r.D.α r.D.q) *
        rhoEnh r.D A.kI.cr j ^ 2 := by
    have hb := (div_le_iff₀ (sq_pos_of_pos hRh)).mp (heD i k)
    convert hb using 1
    unfold rhoEnh ocRh
    field_simp
  refine ⟨hρ, ?_⟩
  have hp := fbCovConst_le_of_radius_entries hρ (covPrimitive r.D j t)
    (ctrl.C / A.kI.cr ^ 2 * r.D.eps (j - 1) ^ ocDelta r.D.α r.D.q) A.Nout hentry
  convert hp using 1
  unfold Parameters.covPrice
  ring

end AVRegularity.IterationPassage.Amplitude
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Amplitude

/-! The actual invariant gives order-zero contraction after its uniform price is small.
This applies to each supplied stage solution, including the root stage. -/

open Construction.Preservation.Buffer

/-- Only numerical lower-floor requirements enter the order-zero contraction. -/
def ContractionPlanOK {B : Base} (plan : Plan B) : Prop :=
  ∀ A : Parameters B, 1 ≤ (plan.constants A).mA ∧ A.j₀ ≤ (plan.constants A).mA ∧
    ∀ j, (plan.constants A).mA ≤ j →
      A.CI * ocEpsilon B.q A.Λ (j - 1) ^
        (B.q * min (ocDelta B.α B.q / 4) A.τe) ≤ 1 / 8

private def runKernelOperator {B : Base} (plan : Plan B) (hplan : ContractionPlanOK plan)
    (A : Parameters B) (r : Run A (plan.constants A)) (j : ℕ)
    (hj : r.m₀ ≤ j) (hjn : j ≤ r.n) (hwindow : r.st j ≤ r.tf) :
    KernelEnergy.TorusKernelOperator (h := fun v : CompIn (r.stage j).comps => ScalarH v.1.root)
      (Γ := (r.stage j).fam.Γ) (G := fun _ u _ => ScalarH u.1.root)
      (r.st j) r.tf (rhoStar r.D A.kI.c₀ (r.stage j).level)
      (r.D.kap (r.stage j).level) 0 A.cap := by
  have hf := r.frame.2.2.2.2.1 j hj hjn
  have hlevel := hf.1
  have hnM := r.n_lt
  have hq : 1 < r.D.q := r.q_eq.symm ▸ B.admissible.1
  have hΛ : 128 ≤ r.D.Λ := r.lambda_eq.symm ▸ A.large
  have hζ : IsFastProfile r.D.ζ := r.profile_eq.symm ▸ B.profile
  have hband : IsOCBandChain r.D.α r.D.q r.D.Λ r.D.ζ r.M r.D.κ := by
    simpa only [r.alpha_eq, r.q_eq, r.lambda_eq, r.profile_eq] using r.band
  have hterm : (r.stage j).level ≤ r.D.term := by rw [hlevel, r.terminal]; omega
  have hκ : 0 < r.D.κ (r.stage j).level :=
    CycleReference.bandChain_pos (by omega) hζ hband (by rw [hlevel]; omega)
  have hν : 0 < r.D.kap (r.stage j).level := by
    simpa only [OCData.kap, min_eq_left hterm] using hκ
  have he (i : ℕ) : 0 < r.D.eps i := (Scales.epsilon_basic (m := i) hq hΛ).1
  have hc0 : 0 < A.kI.c₀ := by rw [A.invariant_constants.1]; exact A.c0_pos
  have hc0le : A.kI.c₀ ≤ 1 := by rw [A.invariant_constants.1]; exact A.c0_small
  have hρ : 0 < rhoStar r.D A.kI.c₀ (r.stage j).level :=
    mul_pos hc0 (lt_min (he _) (Real.sqrt_pos.mpr
      (div_pos hκ (Real.rpow_pos_of_pos (he _) _))))
  have hρε : rhoStar r.D A.kI.c₀ (r.stage j).level ≤ r.D.eps ((r.stage j).level - 1) :=
    ((mul_le_mul_of_nonneg_left (min_le_left _ _) hc0.le).trans
      (mul_le_of_le_one_left (he _).le hc0le)).trans
      (EntryScales.epsilon_antitone hq hΛ (Nat.sub_le _ _))
  have hi : 1 ≤ (r.stage j).level := by
    rw [hlevel]
    exact (hplan A).1.trans (r.above_floor.trans hj)
  have hj0 : A.j₀ ≤ (r.stage j).level := by
    rw [hlevel]
    exact (hplan A).2.1.trans (r.above_floor.trans hj)
  have hD : 2 ≤ A.cap := by dsimp only [Parameters.cap, succSchedD]; omega
  have hprice : A.CI * r.D.eps (j - 1) ^
      (r.D.q * min (ocDelta r.D.α r.D.q / 4) A.τe) ≤ 1 / 8 := by
    simpa only [OCData.eps, r.q_eq, r.lambda_eq, r.alpha_eq] using
      (hplan A).2.2 j (r.above_floor.trans hj)
  have hprod : A.kI.Hprod = A.kI.G0 + (A.menu r.Mnat).H + 1 := by
    exact A.invariant_constants.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  let P := nativeInvariantKernelOperator r.law (A.provenance r.D) (A.menu r.Mnat)
    r.seedK r.freshK A.φ₀ A.hφ₀ r.Mnat A.kI (r.hist j) r.tf
    (A.CI * r.D.eps j ^ min (ocDelta r.D.α r.D.q / 4) A.τe)
    (A.CI * r.D.eps (j - 1) ^ (r.D.q * min (ocDelta r.D.α r.D.q / 4) A.τe))
    r.seed (r.stage j) hf.2.2.1 r.generated.2.1 hf.2.1 hprod hq hΛ hi hj0 A.bw_pos (he _)
    (hf.2.2.2.1.trans hwindow) hν hρ hρε hD hprice 0 (Nat.zero_le _)
    ((r.stage j).marker r.law) (Or.inr rfl)
  exact kernelOperator_time_restrict P (Set.Icc_subset_Icc hf.2.2.2.1 le_rfl) hwindow

/-- The homogeneous marked norm contracts on every actual stage of a small-price run. -/
theorem amplitude_stage_contraction {B : Base} (plan : Plan B)
    (hplan : ContractionPlanOK plan) (A : Parameters B) (r : Run A (plan.constants A))
    (j : ℕ) (hj : r.m₀ ≤ j) (hjn : j ≤ r.n) (t : ℝ) (ht : t ∈ Set.Icc (r.st j) r.tf) :
    r.markedNorm j t ≤ weightedNorm 1 ((r.stage j).mass r.law)
      ((r.stage j).marker r.law) (r.Y0 j) := by
  let P := runKernelOperator plan hplan A r j hj hjn (ht.1.trans ht.2)
  have hlevel := (r.frame.2.2.2.2.1 j hj hjn).1
  have hnM := r.n_lt
  have hνeq : r.D.kap (r.stage j).level = r.D.κ j := by
    rw [hlevel, OCData.kap, min_eq_left (by rw [r.terminal]; omega)]
  have hφ := Velocity.streamSeq_admissible B.profile A.large r.stream j
  obtain ⟨hv, _hp, _hd, ⟨V, hb⟩, _hm⟩ := stream_kernel_drift_data hφ (r.st j) r.tf
  have hb' : ∀ τ ∈ Set.Icc (r.st j) r.tf, ∀ x, ‖streamVel (r.D.Φ j) τ x‖ ≤ max V 0 :=
    fun τ hτ x => (hb τ hτ x).trans (le_max_left _ _)
  have hsol : IsKernelWeakSolutionTorus (r.D.kap (r.stage j).level) (r.st j) r.tf
      (streamVel (r.D.Φ j)) 0 A.cap P.B P.C P.S (r.Y0 j)
      (fun _ _ => 0) (fun _ _ => 0) (r.U j) (r.Uw j) (r.Uk j) := by
    change (r.stage j).IsRegSolution (A.provenance r.D) r.seedK r.freshK A.φ₀ A.hφ₀
      (r.D.kap (r.stage j).level) (streamVel (r.D.Φ j)) 0 (r.st j) r.tf (r.Y0 j)
      (fun _ _ => 0) (fun _ _ => 0) (r.U j) (r.Uw j) (r.Uk j)
    rw [hνeq]
    exact r.solution j hj hjn
  have hc := P.kernelWeakSolution_forcedWeakSolution (streamVel (r.D.Φ j)) hv
    (max V 0) (le_max_right _ _) hb' (r.Y0 j) (fun _ _ => 0) (fun _ _ => 0)
    (r.U j) (r.Uw j) (r.Uk j) hsol
  have hc' : IsCoupledWeakSolutionTorus (r.D.kap (r.stage j).level) (r.st j) r.tf
      (streamVel (r.D.Φ j)) 0 (fun _ => 0) KernelEnergy.TorusKernelOperator.noLocalCoefficient
      (r.Y0 j) (P.carrierFlux (r.Uw j)) (fun _ _ => 0) (r.U j) (r.Uw j) := by
    simpa only [zero_add] using hc
  have hm := Construction.Preservation.Buffer.TorusKernelOperator.stream_homogeneous_mass_at P hφ (max V 0) (le_max_right _ _) hb'
    (r.Y0 j) (r.Uw j) (r.U j) hc' t ht
  have hs := Real.sqrt_le_sqrt hm
  change weightedNorm _ _ _ _ ≤ weightedNorm _ _ _ _ at hs
  rw [weightedNorm_order_zero_radius _ 1, weightedNorm_order_zero_radius _ 1] at hs
  exact hs

/-- The seed has no births, so the marked seed norm is the unmarked datum norm. -/
theorem amplitude_base_bound {B : Base} (plan : Plan B) (hplan : ContractionPlanOK plan) :
    BaseBoundStatement B plan := by
  intro A _ r t ht
  have hmark : (r.stage r.n).marker r.law = fun _ => 1 := by
    funext v
    have hb : v.1.births = [] := by
      have hs := r.generated.2.1
      rw [← r.frame.1] at hs
      exact hs v
    simp only [GenStage.marker, compMarker, compBirthSet, hb, List.map_nil,
      List.toFinset_nil, Finset.prod_empty]
  have hc := amplitude_stage_contraction plan hplan A r r.n r.bottom_lt.le le_rfl t ht
  simpa only [hmark, r.datum, Run.initialNorm] using hc

end AVRegularity.IterationPassage.Amplitude
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev
namespace AVRegularity.IterationPassage.Amplitude

/-! The actual retained trace has the incoming norm plus the small covariance
correction. The added component words have zero trace and introduce no factor. -/

open CycleComparison.Coarse Construction.Preservation.FullLift

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  [∀ r, MeasurableSpace (hr r)] [∀ r, BorelSpace (hr r)] [∀ r, CompleteSpace (hr r)]
  [∀ r, FiniteDimensional ℝ (hr r)]

/-- The reserved covariance correction controls the weighted incoming family. -/
theorem amplitude_weighted_covariance_difference {S : Finset Comp} {ρ M : ℝ} {p R : ℕ}
    (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hR : 2 * p ≤ R)
    (hM : fbCovConst ρ Hc R ≤ M) (hM1 : M ≤ 1)
    (π w : CompIn S → ℝ) (hπ : ∀ v, 0 < π v / w v ^ 2)
    (Z : ∀ v : CompIn S, TorusHk R (hr v.1.root))
    (W : ∀ v : CompIn S, TorusHk 0 (hr v.1.root))
    (hW : ∀ v, IsCovImage (covPolyQ Hc p) (Z v) (W v)) :
    weightedNorm ρ π w (fun v => W v - truncateTorusHk (Nat.zero_le R) (Z v)) ≤
      p * M * weightedNorm ρ π w Z := by
  have hM0 := (fbCovConst_nonneg hρ Hc R).trans hM
  have hpM : 0 ≤ (p : ℝ) * M := mul_nonneg (Nat.cast_nonneg _) hM0
  have hv (v : CompIn S) := amplitude_covariance_difference_le hρ Hc hR hM hM1 (Z v) (W v) (hW v)
  have hv2 (v : CompIn S) : factorialNormSq ρ
      (W v - truncateTorusHk (Nat.zero_le R) (Z v)).val ≤
        ((p : ℝ) * M) ^ 2 * factorialNormSq ρ (Z v).val := by
    have h := pow_le_pow_left₀ (Real.sqrt_nonneg _) (hv v) 2
    simpa only [mul_pow, Real.sq_sqrt (factorialNormSq_nonneg _ _)] using h
  have hs : massNormSq ρ (fun v => π v / w v ^ 2)
      (fun v => (W v - truncateTorusHk (Nat.zero_le R) (Z v)).val) ≤
      ((p : ℝ) * M) ^ 2 * massNormSq ρ (fun v => π v / w v ^ 2) (fun v => (Z v).val) := by
    unfold massNormSq
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro v _
    calc
      _ ≤ (π v / w v ^ 2)⁻¹ * (((p : ℝ) * M) ^ 2 * factorialNormSq ρ (Z v).val) :=
        mul_le_mul_of_nonneg_left (hv2 v) (inv_nonneg.mpr (hπ v).le)
      _ = _ := by ring
  have hsqrt := Real.sqrt_le_sqrt hs
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq hpM] at hsqrt
  exact hsqrt

private theorem weighted_covariance_near_identity {S : Finset Comp} {ρ M : ℝ} {p R : ℕ}
    (hρ : 0 < ρ) (Hc : Matrix (Fin 2) (Fin 2) ℝ) (hR : 2 * p ≤ R)
    (hM : fbCovConst ρ Hc R ≤ M) (hM1 : M ≤ 1)
    (π w : CompIn S → ℝ) (hπ : ∀ v, 0 < π v / w v ^ 2)
    (Z : ∀ v : CompIn S, TorusHk R (hr v.1.root))
    (W : ∀ v : CompIn S, TorusHk 0 (hr v.1.root))
    (hW : ∀ v, IsCovImage (covPolyQ Hc p) (Z v) (W v)) :
    weightedNorm ρ π w W ≤ weightedNorm ρ π w
      (fun v => truncateTorusHk (Nat.zero_le R) (Z v)) + p * M * weightedNorm ρ π w Z := by
  let Z0 := fun v => truncateTorusHk (Nat.zero_le R) (Z v)
  have hb := amplitude_weighted_covariance_difference (hr := hr) hρ Hc hR hM hM1 π w hπ Z W hW
  have ht := CycleComparison.Reconstruction.sqrt_massNormSq_add_le
    (E := fun v : CompIn S => hr v.1.root) (fun _ : CompIn S => 0)
    ρ (fun v => π v / w v ^ 2) hπ (fun v => W v - Z0 v) Z0
  simp only [sub_add_cancel] at ht
  change weightedNorm ρ π w W ≤ weightedNorm ρ π w (fun v => W v - Z0 v) +
    weightedNorm ρ π w Z0 at ht
  have h := add_le_add hb (le_refl (weightedNorm ρ π w Z0))
  exact (ht.trans h).trans_eq (add_comm _ _)

/-- A retained trace agrees in weighted norm with its support on the old components. -/
theorem amplitude_retained_trace_near_identity {D : OCData} {Dm j₀ : ℕ} {b ρ M : ℝ}
    (law : BirthLaw) (G Gr : GenStage D hr Dm b j₀) (hST : G.comps ⊆ Gr.comps)
    (p R m : ℕ) (tp : ℝ) (hρ : 0 < ρ) (hR : 2 * p ≤ R)
    (hM : fbCovConst ρ (covPrimitive D m tp) R ≤ M) (hM1 : M ≤ 1)
    (w : Comp → ℝ) (hπ : ∀ v : CompIn G.comps, 0 < G.mass law v / w v.1 ^ 2)
    (Z : ∀ v : CompIn G.comps, TorusHk R (hr v.1.root))
    (Y0 : ∀ v : CompIn Gr.comps, TorusHk 0 (hr v.1.root))
    (htrace : IsRetainedTrace G Gr m p tp Z Y0) :
    weightedNorm 1 (Gr.mass law) (fun v => w v.1) Y0 ≤
      weightedNorm 1 (G.mass law) (fun v => w v.1)
        (fun v => truncateTorusHk (Nat.zero_le R) (Z v)) +
      p * M * weightedNorm ρ (G.mass law) (fun v => w v.1) Z := by
  let W := fun v : CompIn G.comps => Y0 ⟨v.1, hST v.2⟩
  have hb := weighted_covariance_near_identity (hr := hr) hρ (covPrimitive D m tp) hR hM hM1
    (G.mass law) (fun v => w v.1) hπ Z W (fun v => htrace.1 ⟨v.1, hST v.2⟩ v.2)
  rw [Construction.Preservation.Buffer.weightedNorm_order_zero_radius (hr := hr) ρ 1 _ _ W,
    Construction.Preservation.Buffer.weightedNorm_order_zero_radius (hr := hr) ρ 1 _ _
      (fun v => truncateTorusHk (Nat.zero_le R) (Z v))] at hb
  have he := weightedNorm_own_components (hr := hr) hST D.q 1 D.Λ law w Y0 htrace.2
  exact he.le.trans hb

end AVRegularity.IterationPassage.Amplitude
end

section
open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
namespace AVRegularity.IterationPassage.Amplitude

/-! The near-unit marked step follows from the supplied preparation and retained
trace, not from a particular passage producer's amplitude conclusion. -/

open CycleComparison.Coarse Construction.Preservation.FullLift Construction.Preservation.Buffer

/-- Numerical conditions on the shared constants for the one-step estimate. -/
def StepPlanOK {B : Base} (ctrl : CovarianceControl B) (plan : Plan B) : Prop :=
  ctrl.Λ₀ ≤ plan.Λ₀ ∧ ∀ A : Parameters B,
    2 ≤ (plan.constants A).mA ∧ |A.CQ| ≤ (plan.constants A).C ∧
    (A.p : ℝ) * A.covPrice ctrl.C * |A.CQ| ≤ (plan.constants A).C ∧
    ∀ j, (plan.constants A).mA ≤ j →
      A.covPrice ctrl.C * ocEpsilon B.q A.Λ (j - 1) ^ ocDelta B.α B.q ≤ 1

private theorem marked_step_algebra {x y C q r f A : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (hC : 0 ≤ C) (hf : 0 ≤ f)
    (hfA : f ≤ A) (hq : q ≤ C) (hr : r ≤ C) :
    (1 + q * x) * f + r * y * f ≤ (1 + C * (x + y)) * A := by
  have he : (1 + q * x) * f + r * y * f = (1 + q * x + r * y) * f := by ring
  rw [he]
  have hc : 1 + q * x + r * y ≤ 1 + C * (x + y) := by
    have h := add_le_add (mul_le_mul_of_nonneg_right hq hx) (mul_le_mul_of_nonneg_right hr hy)
    linarith only [h]
  exact (mul_le_mul_of_nonneg_right hc hf).trans
    (mul_le_mul_of_nonneg_left hfA (by positivity))

/-- Preparation, a small covariance correction and retained contraction give the
amplitude recurrence for an arbitrary supplied frame. -/
theorem amplitude_one_step_bound {B : Base} (ctrl : CovarianceControl B) (plan : Plan B)
    (hcontract : ContractionPlanOK plan) (hplan : StepPlanOK ctrl plan) :
    OneStepBoundStatement B plan := by
  intro A hΛ r j hj hjn _hr Ain hA t ht
  have hf := r.frame.2.2.2.2.1 j hj.le hjn
  have hs := r.frame.2.2.2.2.2 j hj hjn
  have hlevel := hf.1
  have hprep := hs.2.2.2.2.2.1
  have hST : (r.stage j).comps ⊆ (r.stage (j - 1)).comps := by
    rw [hs.2.1]
    exact incoming_mem_retained_of_cascade r.generated.2.1 hf.2.1 hs.1 hlevel
  have hfloor : (plan.constants A).mA ≤ j := r.above_floor.trans hj.le
  have hj2 : 2 ≤ j := (hplan.2 A).1.trans hfloor
  obtain ⟨hρ, hcov⟩ := amplitude_covariance_scale ctrl A (hplan.1.trans hΛ) r j hj2 hjn (r.tp j)
  let M := A.covPrice ctrl.C * r.D.eps (j - 1) ^ ocDelta r.D.α r.D.q
  have hM1 : M ≤ 1 := by
    simpa only [M, OCData.eps, r.q_eq, r.lambda_eq, r.alpha_eq] using (hplan.2 A).2.2.2 j hfloor
  have hM0 : 0 ≤ M := (fbCovConst_nonneg hρ _ _).trans hcov
  have hq : 1 < r.D.q := r.q_eq.symm ▸ B.admissible.1
  have hΛD : 128 ≤ r.D.Λ := r.lambda_eq.symm ▸ A.large
  have hπ (v : CompIn (r.stage j).comps) :
      0 < (r.stage j).mass r.law v / (r.stage j).marker r.law v ^ 2 :=
    div_pos (birth_compMass_pos hq hΛD r.law v.1) (pow_pos (birth_compMarker_pos hq hΛD r.law v.1) 2)
  have hR : 2 * A.p ≤ A.Nout := by have h := A.schedule.2.2.2.2.1; omega
  let f := fun v => r.U j v (cascadeRestart r.D r.hist r.st j)
  have hb := amplitude_retained_trace_near_identity r.law (r.stage j) (r.stage (j - 1)) hST
    A.p A.Nout j (r.tp j) hρ hR hcov hM1 (compMarker r.D.q r.D.Λ r.law) hπ
    (r.Preg j f) (r.Y0 (j - 1)) (r.trace j hj hjn)
  have hp := hprep.2.2.2.2 ((r.stage j).marker r.law) (Or.inr rfl) f
  have he (k : ℕ) : 0 < r.D.eps k := (Scales.epsilon_basic (m := k) hq hΛD).1
  have hfn : 0 ≤ weightedNorm 1 ((r.stage j).mass r.law) ((r.stage j).marker r.law) f :=
    Real.sqrt_nonneg _
  have hlo := hp.2.1
  have hhi := hp.2.2.1
  rw [hlevel] at hlo hhi
  have hlo' : weightedNorm 1 ((r.stage j).mass r.law) ((r.stage j).marker r.law)
      (fun v => truncateTorusHk (Nat.zero_le A.Nout) (r.Preg j f v)) ≤
      (1 + |A.CQ| * r.D.eps (j - 1) ^ A.Q) * weightedNorm 1 ((r.stage j).mass r.law)
        ((r.stage j).marker r.law) f :=
    hlo.trans (mul_le_mul_of_nonneg_right (add_le_add (le_refl (1 : ℝ))
      (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.rpow_nonneg (he _).le _))) hfn)
  have hhi' : weightedNorm (rhoEnh r.D A.kI.cr j) ((r.stage j).mass r.law)
      ((r.stage j).marker r.law) (r.Preg j f) ≤
        |A.CQ| * weightedNorm 1 ((r.stage j).mass r.law) ((r.stage j).marker r.law) f :=
    hhi.trans (mul_le_mul_of_nonneg_right (le_abs_self _) hfn)
  have hb' := hb.trans (add_le_add hlo' (mul_le_mul_of_nonneg_left hhi'
    (mul_nonneg (Nat.cast_nonneg _) hM0)))
  have hc := amplitude_stage_contraction plan hcontract A r (j - 1) (by omega) (by omega) t ht
  apply hc.trans (hb'.trans ?_)
  change (1 + |A.CQ| * r.D.eps (j - 1) ^ A.Q) * _ +
    (A.p : ℝ) * M * (|A.CQ| * _) ≤ _
  have halg := marked_step_algebra
    (Real.rpow_nonneg (he (j - 1)).le A.Q)
    (Real.rpow_nonneg (he (j - 1)).le (ocDelta r.D.α r.D.q))
    (plan.constants A).positive.le hfn hA (hplan.2 A).2.1 (hplan.2 A).2.2.1
  convert halg using 1
  dsimp only [M]
  ring

end AVRegularity.IterationPassage.Amplitude
end

section
open Filter Topology
namespace AVRegularity.IterationPassage.Amplitude

/-! Choose all smallness floors before the bottom level, endpoints or data. -/

private theorem scaled_power_floor {q p W η : ℝ} {Λ : ℕ}
    (hq : 1 < q) (hΛ : 128 ≤ Λ) (hp : 0 < p) (hη : 0 < η) :
    ∃ m : ℕ, ∀ j, m ≤ j → W * ocEpsilon q Λ j ^ p ≤ η := by
  have hlim := ((Scales.epsilon_forward_tail (m := 1) hq hΛ le_rfl hp).1.tendsto_atTop_zero).const_mul W
  have hlim' : Tendsto (fun j : ℕ => W * ocEpsilon q Λ (1 + j) ^ p) atTop (𝓝 0) := by
    simpa only [mul_zero] using hlim
  obtain ⟨m, hm⟩ := eventually_atTop.mp (hlim' (gt_mem_nhds hη))
  refine ⟨m + 1, ?_⟩
  intro j hj
  have h := hm (j - 1) (by omega)
  dsimp only [Set.mem_ofPred_eq] at h
  simpa only [show 1 + (j - 1) = j by omega] using h.le

private theorem constants_exist (B : Base) (ctrl : CovarianceControl B) (A : Parameters B) :
    ∃ K : Constants,
      Real.exp 1 ≤ K.C ∧ 2 ≤ K.mA ∧ A.j₀ ≤ K.mA ∧ |A.CQ| ≤ K.C ∧
      (A.p : ℝ) * A.covPrice ctrl.C * |A.CQ| ≤ K.C ∧
      (∀ j, K.mA ≤ j → ∀ n, K.C * (∑ k ∈ Finset.Ioc j n,
        (ocEpsilon B.q A.Λ (k - 1) ^ A.Q + ocEpsilon B.q A.Λ (k - 1) ^ ocDelta B.α B.q)) ≤ 1) ∧
      (∀ j, K.mA ≤ j → A.CI * ocEpsilon B.q A.Λ (j - 1) ^
        (B.q * min (ocDelta B.α B.q / 4) A.τe) ≤ 1 / 8) ∧
      (∀ j, K.mA ≤ j → A.covPrice ctrl.C * ocEpsilon B.q A.Λ (j - 1) ^ ocDelta B.α B.q ≤ 1) := by
  have hδ := (Scales.admissible_exponent_facts B.alpha_pos B.alpha_lt B.s_pos B.s_lt B.admissible).2.1
  have hβ : 0 < B.q * min (ocDelta B.α B.q / 4) A.τe :=
    mul_pos (zero_lt_one.trans B.admissible.1) (lt_min (div_pos hδ (by norm_num)) A.entry_pos)
  have hprice : 0 ≤ A.covPrice ctrl.C := by
    unfold Parameters.covPrice
    exact div_nonneg (mul_nonneg (mul_nonneg (by norm_num) (zero_le_one.trans ctrl.one_le))
      (sq_nonneg _)) (sq_nonneg _)
  let C := max (Real.exp 1) (|A.CQ| + (A.p : ℝ) * A.covPrice ctrl.C * |A.CQ|)
  have hC : 0 < C := (Real.exp_pos 1).trans_le (le_max_left _ _)
  have hCq : |A.CQ| ≤ C :=
    (le_add_of_nonneg_right (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hprice) (abs_nonneg _))).trans
      (le_max_right _ _)
  have hCr : (A.p : ℝ) * A.covPrice ctrl.C * |A.CQ| ≤ C :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans (le_max_right _ _)
  obtain ⟨mp, _hmp, hp⟩ := amplitude_scale_error_floor B.admissible.1 A.large A.schedule.1 hδ hC
  obtain ⟨mk, hk⟩ := scaled_power_floor (W := A.CI) B.admissible.1 A.large hβ (by norm_num : (0 : ℝ) < 1 / 8)
  obtain ⟨mc, hc⟩ := scaled_power_floor (W := A.covPrice ctrl.C) B.admissible.1 A.large hδ zero_lt_one
  let mA := max A.j₀ (max 2 (max mp (max (mk + 1) (mc + 1))))
  have hmj : A.j₀ ≤ mA := le_max_left _ _
  have hm2 : 2 ≤ mA := (le_max_left _ _).trans (le_max_right _ _)
  have hmp : mp ≤ mA := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hmk : mk + 1 ≤ mA := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hmc : mc + 1 ≤ mA := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  exact ⟨⟨C, mA, hC⟩, le_max_left _ _, hm2, hmj, hCq, hCr,
    fun j hj n => hp j (hmp.trans hj) n,
    fun j hj => hk (j - 1) (by have hh : mk + 1 ≤ j := hmk.trans hj; omega),
    fun j hj => hc (j - 1) (by have hh : mc + 1 ≤ j := hmc.trans hj; omega)⟩

/-- The uniform plan satisfies simultaneously all numerical conditions of the proof. -/
theorem amplitude_uniform_plan (B : Base) (ctrl : CovarianceControl B) :
    ∃ plan : Plan B, ProductPlanOK plan ∧ ContractionPlanOK plan ∧ StepPlanOK ctrl plan := by
  let choices := fun A : Parameters B => Classical.choose (constants_exist B ctrl A)
  have hchoices := fun A : Parameters B => Classical.choose_spec (constants_exist B ctrl A)
  let plan : Plan B := ⟨ctrl.Λ₀, ctrl.large, choices⟩
  refine ⟨plan, ?_, ?_, ?_⟩
  · intro A
    have h := hchoices A
    exact ⟨h.1, (by norm_num : 1 ≤ 2).trans h.2.1, h.2.2.2.2.2.1⟩
  · intro A
    have h := hchoices A
    exact ⟨(by norm_num : 1 ≤ 2).trans h.2.1, h.2.2.1, h.2.2.2.2.2.2.1⟩
  · refine ⟨le_rfl, ?_⟩
    intro A
    have h := hchoices A
    exact ⟨h.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.2.2⟩

/-- All ingredients of the arbitrary-frame amplitude product, with their numerical
conditions discharged by a coherent data-independent plan. -/
theorem amplitude_product : Assembly.CascadeAmplitudeProductStatement := by
  let controls := fun B : Base => Classical.choice (amplitude_covariance_control B)
  let plans := fun B : Base => Classical.choose (amplitude_uniform_plan B (controls B))
  have hp := fun B : Base => Classical.choose_spec (amplitude_uniform_plan B (controls B))
  exact cascade_amplitude_product_of_ingredients plans
    (fun B => amplitude_base_bound (plans B) (hp B).2.1)
    (fun B => amplitude_one_step_bound (controls B) (plans B) (hp B).2.1 (hp B).2.2)
    (fun B => amplitude_restart B (plans B)) amplitude_finite_recurrence_extension
    (fun B => amplitude_product_bound (plans B) (hp B).1)

end AVRegularity.IterationPassage.Amplitude
end
end
end
