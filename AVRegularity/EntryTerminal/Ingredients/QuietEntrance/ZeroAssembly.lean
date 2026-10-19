-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

import AVRegularity.Applications.Global.CompactRangeMain
import AVRegularity.CycleComparison.Coarse.Defect.Final
public import AVRegularity.EntryTerminal.Assembly.Route.EntryTerminalOfWeak
import AVRegularity.Construction.TerminalLift.Assembly
import AVRegularity.Construction.Preservation.FullLift.ZeroFreshMetricSliceJets
import AVRegularity.Construction.Preservation.FullLift.ActualRetainedReadoutEnergy
import AVRegularity.Proofs.Results.Entry.ScalarPackageTerminal
public import AVRegularity.Construction.Preservation.FullLift.CovarianceTimeMeasurable
import AVRegularity.EntryTerminal.Ingredients.Recon.R2Core.Quiet
import AVRegularity.Proofs.CascadeInvariants.Scales
public import AVRegularity.EntryWeak.FluxProductionArithmetic
import AVRegularity.CycleComparison.Assembly.OcDiagonal
import AVRegularity.CycleComparison.LiftSetting.Main
import AVRegularity.CycleReference.ChartTestTransport
import Mathlib.Algebra.Order.Star.Real
import Mathlib.RingTheory.Etale.Weakly
import Mathlib.RingTheory.TotallySplit

section
section
/-! **Scale fact for the quiet entrance**: the level scale `ε_m` decays faster than any fixed
multiple of itself, `C ε_{M+1} ≤ ε_M` for large `M`. It turns the record length bound `C_L ε_{M+1}` of the weak
stage into the bound `ε_M` required by the lift setting. -/

@[expose] public section

open AVRegularity

namespace AVRegularity.EntryTerminal.QuietEntrance

/-- `C ε_{M+1} ≤ ε_M` for all large `M`. -/
theorem qe_eps_ratio {q : ℝ} {Λ : ℕ} (hq : 1 < q) (hΛ : 128 ≤ Λ) (C : ℝ) :
    ∃ M₀ : ℕ, 1 ≤ M₀ ∧ ∀ M : ℕ, M₀ ≤ M → C * ocEpsilon q Λ (M + 1) ≤ ocEpsilon q Λ M := by
  set r : ℝ := (1 / 2 : ℝ) ^ (q - 1) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos (by norm_num) _
  have hr1 : r < 1 := Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hpos : 0 < 1 / (2 ^ q * (|C| + 1)) := by positivity
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hpos hr1
  refine ⟨max n 1, le_max_right _ _, fun M hM => ?_⟩
  have hM1 : 1 ≤ M := le_trans (le_max_right _ _) hM
  have hMn : n ≤ M := le_trans (le_max_left _ _) hM
  have he := Applications.eps_pos (q := q) (Λ := Λ) (m := M) hq hΛ
  have hs := Applications.ocEpsilon_succ_le (q := q) (Λ := Λ) (m := M) hq hΛ hM1
  have hhalf := Applications.eps_le_half_pow hq hΛ M
  have hpow : (ocEpsilon q Λ M) ^ (q - 1) ≤ r ^ M := by
    calc (ocEpsilon q Λ M) ^ (q - 1) ≤ ((1 / 2 : ℝ) ^ M) ^ (q - 1) :=
          Real.rpow_le_rpow he.le hhalf (by linarith)
      _ = r ^ M := by
          rw [hr, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast,
            ← Real.rpow_mul (by norm_num)]
          congr 1
          ring
  have hrM : r ^ M ≤ r ^ n := pow_le_pow_of_le_one hr0.le hr1.le hMn
  have hq' : ocEpsilon q Λ M ^ q = ocEpsilon q Λ M * ocEpsilon q Λ M ^ (q - 1) := by
    rw [← Real.rpow_one_add' he.le (by linarith)]
    congr 1
    ring
  have hC : C ≤ |C| := le_abs_self C
  have hkey : 2 ^ q * (|C| + 1) * ocEpsilon q Λ M ^ (q - 1) ≤ 1 := by
    have h1 : ocEpsilon q Λ M ^ (q - 1) ≤ 1 / (2 ^ q * (|C| + 1)) := by
      linarith
    have hp : (0 : ℝ) < 2 ^ q * (|C| + 1) := by positivity
    calc 2 ^ q * (|C| + 1) * ocEpsilon q Λ M ^ (q - 1)
        ≤ 2 ^ q * (|C| + 1) * (1 / (2 ^ q * (|C| + 1))) := by gcongr
      _ = 1 := by field_simp
  have hep1 : 0 < ocEpsilon q Λ (M + 1) := Applications.eps_pos hq hΛ
  have h2 : C * ocEpsilon q Λ (M + 1) ≤ |C| * (2 ^ q * ocEpsilon q Λ M ^ q) := by
    calc C * ocEpsilon q Λ (M + 1) ≤ |C| * ocEpsilon q Λ (M + 1) := by gcongr
      _ ≤ |C| * (2 ^ q * ocEpsilon q Λ M ^ q) := by gcongr
  refine h2.trans ?_
  rw [hq']
  have : |C| * (2 ^ q * (ocEpsilon q Λ M * ocEpsilon q Λ M ^ (q - 1))) =
      ocEpsilon q Λ M * (|C| * 2 ^ q * ocEpsilon q Λ M ^ (q - 1)) := by ring
  rw [this]
  have hnn : 0 ≤ |C| * 2 ^ q * ocEpsilon q Λ M ^ (q - 1) := by positivity
  calc ocEpsilon q Λ M * (|C| * 2 ^ q * ocEpsilon q Λ M ^ (q - 1))
      ≤ ocEpsilon q Λ M * 1 := by
        gcongr
        nlinarith [Real.rpow_nonneg he.le (q - 1), Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) q]
    _ = ocEpsilon q Λ M := mul_one _

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! **Value jets of truncations**. The value jet of a truncation is the value
jet of the carrier element, and a classical representative is the value jet. These give the
identification of the difference `trunc g - û(t_p)` with `a - T a` at the quiet anchor from
`entry_terminal_initial_value`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity

namespace AVRegularity.EntryTerminal.QuietEntrance

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E]

/-- The value jet of a truncation is the value jet of the element. -/
theorem qe_value_trunc {K L : ℕ} (hLK : L ≤ K) (f : TorusHk K E) :
    (truncateTorusHk hLK f).toFunction.jet (valueIndex2 L) =ᵐ[volume.restrict AVenhance.unitCube]
      f.toFunction.jet (valueIndex2 K) :=
  KernelEnergy.truncateTorusHk_toFunction_jet_ae hLK f (valueIndex2 L)

/-- The value jet of an element with classical representative `a` (at its own order) is `a`. -/
theorem qe_value_rep {K : ℕ} (W : TorusHk K E) (a : Vec 2 → E) (h : IsClassicalRep W a K) :
    W.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] a := by
  have h0 := h.2.2.2 0 (Nat.zero_le _) Fin.elim0
  have e : torusJetOrder W 0 Fin.elim0 = W.toFunction.jet (valueIndex2 K) := by
    funext x
    simp only [torusJetOrder]
    rfl
  rw [e] at h0
  refine h0.trans ?_
  filter_upwards with x
  simp [orderedDerivative]

/-- The value jet of `trunc g - û` is `a - L` when `a` represents the truncation of `g` and the
value jet of `û` is `L`. -/
theorem qe_delta_jet {K₀ K P : ℕ} (hK₀ : K₀ ≤ K) (hP : P ≤ K) (g : TorusHk K E)
    (a L : Vec 2 → E) (û : TorusHk K₀ E)
    (hrep : IsClassicalRep (truncateTorusHk hP g) a P)
    (hû : û.toFunction.jet (valueIndex2 K₀) =ᵐ[volume.restrict AVenhance.unitCube] L) :
    (truncateTorusHk hK₀ g - û).toFunction.jet (valueIndex2 K₀)
      =ᵐ[volume.restrict AVenhance.unitCube] fun x => a x - L x := by
  filter_upwards [CycleComparison.Coarse.jet_sub_ae (truncateTorusHk hK₀ g) û,
    qe_value_trunc hK₀ g, qe_value_trunc hP g, qe_value_rep _ a hrep, hû] with x h1 h2 h3 h4 h5
  rw [h1 (valueIndex2 K₀), h2, ← h3, h4, h5]

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! **Quiet entrance, the two parts**. `TerminalQuietEntranceStatement` is cut into

* **Part 1** (`QELiftSettingStatement`): the lift setting of every odd slot
  at the terminal slow length, from `terminal_level_lift`
  and the identification of its lift sequence with the given `CcT k` (lift-sequence uniqueness).
  The orders `(K, k, L, K_src)` and the uniform constants `(C_G, C_w)` are chosen before the data
  and bound `S_X, S_Z`;
* **Part 2** (`QEOperatorSmallStatement`): the operator `T - I` of the glued lift at the
  quiet anchor is `C_b E^Q` small from the `(ρ, K̂)` norm of the trace to the `(r_*, k₀)` norm,
  by quiet-gap decay on the trimmed quiet margin and the conversion of the Schur cell jets.

The assembly `terminalQuietEntrance_of` (module `Assembly`) proves `TerminalQuietEntranceStatement`
from the two parts. Degenerate cases: `g = 0` (both sides zero), `Q ≤ 0`, `c_r = 1`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.EntryWeakProofs

namespace AVRegularity.EntryTerminal.QuietEntrance

/-- The orders and uniform constants of the terminal lift setting, chosen before the data
(the arguments `K k L K_src` and the outputs `C_G, C_w` of `terminal_level_lift`). -/
structure QEOrders where
  Ksrc : ℕ
  K : ℕ
  kk : ℕ
  L : ℕ
  CG : ℕ → ℝ
  Cw : ℕ → ℝ
  Cj : ℕ → ℕ → ℝ

/-- Admissible orders for the terminal lift of `A`: the source cap is the order index `D̄₀`; the
floors `K, k, L` are monotone (any larger values are admissible). -/
def QEOrders.Adm {X : TermConstruction} (A : TermArgs X) (O : QEOrders) : Prop :=
  O.Ksrc = A.Dt ∧ A.Dt * (A.dW + 1) * A.NT + A.k₀ ≤ O.K ∧
    A.Dt * (A.dW + 1) * A.NT + A.k₀ ≤ O.kk ∧ A.Dt * (A.dW + 1) * A.NT + A.k₀ ≤ O.L ∧ O.L + 2 ≤ O.kk

/-- **The lift setting of the odd slot `k` at level `M`** with the terminal slow length
`ρ = c_r liftLength D M` (the conclusion of `terminal_level_lift` at `G.level = D.term = M`,
restated for the slot `k`), together with the lift recursion of `CcT k` from its own entrance trace
on the window of the slot. -/
def QESlotSetting {Dt : ℕ} {bw : ℝ} {j₀ : ℕ} (D : OCData) (M : ℕ)
    (Gw : GenStage D ScalarH Dt bw j₀) (law : BirthLaw) (cr Θmax : ℝ) (N H : ℕ) (O : QEOrders)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (k : ℤ) (hk : Odd k) : Prop :=
  ∃ (price : CompIn Gw.comps → CompIn Gw.comps → ℝ) (Θ : ℝ)
    (hKD : O.Ksrc ≤ Dt) (_ : Θ ≤ Θmax) (Cc' : ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root)),
    IsLiftSetting
      (restrictLiftData O.Ksrc hKD
        {familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
            (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)) with
          edge := Construction.Preservation.FullLift.windowEdges
            (D.slotStart M k / D.cellScaleSq M)
            ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M)
            (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
              (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩))).edge})
      (Gw.mass law) (D.slotStart M k / D.cellScaleSq M)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M)
      (D.eps M) (D.kap M) (D.kap (M - 1)) (cr * liftLength D M) (D.eps (M - 1))
      (D.eps M / Real.sqrt (D.kap M))
      (ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)))
      (ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)) / (cr * liftLength D M))
      ((cr * liftLength D M) / D.eps (M - 1)) (pulseParallel k)
      (pulseShearProfile D.α D.q D.Λ M D.ζ (D.kap M) k)
      H N O.K O.kk O.L (O.K + 4 * (H + 1) * (N + O.Ksrc) ^ 2)
      (max O.kk (O.L + 2) + H * O.Ksrc + 2 * N + 2 * O.Ksrc) O.CG O.Cw O.Cj price Θ ∧
    IsLiftSequence
      (restrictLiftData O.Ksrc hKD
        {familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
            (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)) with
          edge := Construction.Preservation.FullLift.windowEdges
            (D.slotStart M k / D.cellScaleSq M)
            ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M)
            (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
              (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩))).edge})
      (O.K + O.Ksrc + 2) (max (O.kk + 1) (O.L + 2))
      (D.slotStart M k / D.cellScaleSq M)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) N H Cc' ∧
    ∀ hh, hh ≤ H → ∀ n m (α : DerivativeWord2 m) t,
      t ∈ Set.Icc (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) →
      ∀ X z v u, CcT k hh n m α t X z v u = Cc' hh n m α t X z v u

/-- **Part 1**: for every odd slot of the weak stage, the lift setting at the terminal
slow length and the lift recursion of the given sequence `CcT k`. -/
def QELiftSettingStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∃ (SX SZ Kfloor : ℕ) (O : QEOrders), O.Adm A ∧ O.K + O.Ksrc + 2 ≤ SX ∧ max (O.kk + 1) (O.L + 2) ≤ SZ ∧
  ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT → ∀ Kout : ℕ, Kfloor ≤ Kout →
  ∀ (nW : ℕ+) (cr cK CL Cχ : ℝ) (kW : InvConsts), 0 < cr → cr ≤ 1 → 0 < cK → kW.c₀ = cK →
    A.k₀ ≤ kW.Ks → kW.G0 ≤ kW.Hprod + 1 →
  ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM →
  ∀ (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root)),
    (∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
        sXT sZT (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) A.NT A.dW (CcT k)) →
  ∀ (k : ℤ) (hk : Odd k), QESlotSetting D M Gw lawW cr (Cχ * D.eps M ^ A.χw) A.NT A.dW O CcT k hk

/-- **Part 2**: the operator `T - I` of the glued lift at the quiet anchor is small.
For a classical field `a` (the representative of the truncated trace `g`) and any element `Δ` of
the Sobolev carrier of order `k₀` whose value is `a - T a` at `t_p`, the `(r_*, k₀)` norm of `Δ` is at
most `C_b E^Q` times the `(ρ, K̂)` norm of `g`. -/
def QEOperatorSmallStatement : Prop :=
  ∀ X : TermConstruction, ∃ Λ₀ : ℕ, 128 ≤ Λ₀ ∧ ∀ A : TermArgs X, Λ₀ ≤ A.Λ → A.Valid →
  ∀ (SX SZ Kfloor : ℕ) (O : QEOrders), O.Adm A → O.K + O.Ksrc + 2 ≤ SX → max (O.kk + 1) (O.L + 2) ≤ SZ →
  ∀ sXT sZT : ℕ, SX ≤ sXT → SZ ≤ sZT → ∀ Kout : ℕ, Kfloor ≤ Kout →
  ∀ (nW : ℕ+) (cr cK CL Cχ : ℝ) (kW : InvConsts), 0 < cr → cr ≤ 1 → 0 < cK → kW.c₀ = cK →
    A.k₀ ≤ kW.Ks → kW.G0 ≤ kW.Hprod + 1 →
  ∀ Q : ℝ, ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ j₀ : ℕ, ∃ M₀ : ℕ, ∀ M : ℕ, M₀ ≤ M →
  ∀ D : OCData, IsTermData X A.Λ M D →
  ∀ (a : ℝ) (lawW : BirthLaw) (PW : ProvParams) (Gw : GenStage D ScalarH A.Dt A.bw j₀) (aM : ℝ),
    IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM →
  ∀ tp : ℝ, aM + ocTauP D.α D.q D.Λ M ≤ tp → tp ≤ a + A.T₀ →
    Set.Icc (tp - ocTauP D.α D.q D.Λ M) (tp + ocTauP D.α D.q D.Λ M) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ M →
  ∀ (g : ∀ v : CompIn Gw.comps, TorusHk (A.Khat Kout) (ScalarH v.1.root))
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root)),
    (∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
        sXT sZT (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) A.NT A.dW (CcT k)) →
    (∀ (k : ℤ) (hk : Odd k), QESlotSetting D M Gw lawW cr (Cχ * D.eps M ^ A.χw) A.NT A.dW O CcT k hk) →
  ∀ (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root),
    (∀ v, IsClassicalRep (truncateTorusHk (Nat.sub_le (A.Khat Kout) (2 * A.pT)) (g v))
      (fun x => aRep tp x v) (A.Khat Kout - 2 * A.pT)) →
  ∀ Δ : ∀ v : CompIn Gw.comps, TorusHk A.k₀ (ScalarH v.1.root),
    (∀ v, (Δ v).toFunction.jet (valueIndex2 A.k₀) =ᵐ[volume.restrict AVenhance.unitCube]
      fun x => aRep tp x v - termLiftedRep Gw M A.NT A.dW cr CcT aRep tp x v) →
    weightedNorm (D.termRStar cK M) (Gw.mass lawW) (fun _ => 1) Δ ≤
      Cb * D.eps (M - 1) ^ Q * weightedNorm (D.termRho cr M) (Gw.mass lawW) (fun _ => 1) g

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! **Quiet entrance, part 1**: the lift setting of every odd slot of the weak stage at the terminal
slow length, from `terminal_level_lift` with the source envelope of
`stage_native_lift_source_exists_envelope`, and the identification of the given `CcT k` with the
lift sequence of the setting by uniqueness of lift sequences on the window. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Preservation.FullLift

namespace AVRegularity.EntryTerminal.QuietEntrance

/-- The terminal count `N_T` is positive. -/
theorem qe_one_le_NT {X : TermConstruction} (A : TermArgs X) (hV : A.Valid) : 1 ≤ A.NT := by
  by_contra h
  have h0 : A.NT = 0 := by omega
  obtain ⟨-, -, -, -, hPT, hS, -⟩ := hV
  obtain ⟨-, hQ, -, hζN, -⟩ := hS
  have hq1 : 1 < X.q := X.hq.1
  have hpow : 0 ≤ X.q ^ (A.Jw + 1) := by positivity
  have hs0 := X.hs₀
  rw [h0] at hζN
  simp only [Nat.cast_zero, mul_zero] at hζN
  nlinarith [mul_nonneg hpow (by linarith : (0 : ℝ) ≤ 1 + X.s)]


/-- The reserve of a root component is nonnegative under the premise `G₀ ≤ H_prod + 1`. -/
theorem qe_compReserve_bounds (kW : InvConsts) (hG0 : kW.G0 ≤ kW.Hprod + 1) (c : Comp)
    (hc : c.births = []) : 0 ≤ compReserve kW c ∧ compReserve kW c ≤ 2 := by
  unfold compReserve compGrade
  rw [hc, List.length_nil, add_zero]
  have hpos : (0 : ℝ) < (kW.Hprod : ℝ) + 1 := by positivity
  have h1 : ((kW.G0 : ℕ) : ℝ) / ((kW.Hprod : ℝ) + 1) ≤ 1 := by
    rw [div_le_one hpos]; exact_mod_cast hG0
  have h2 : 0 ≤ ((kW.G0 : ℕ) : ℝ) / ((kW.Hprod : ℝ) + 1) := by positivity
  constructor <;> linarith

/-- **Quiet entrance, part 1**: the lift setting of every odd slot at the terminal slow length
and the window identification of the given `CcT k`. -/
theorem qe_liftSetting : QELiftSettingStatement := by
  intro X
  obtain ⟨Λa, hΛa, hsc⟩ := band_enhanced_lift_scale_bounds X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.hq X.hζ
  refine ⟨max Λa 128, le_max_right _ _, fun A hΛ hV => ?_⟩
  have hΛA : Λa ≤ A.Λ := le_trans (le_max_left _ _) hΛ
  have hΛ128 : 128 ≤ A.Λ := le_trans (le_max_right _ _) hΛ
  have hN : 1 ≤ A.NT := qe_one_le_NT A hV
  have hDt : 2 ≤ A.Dt := le_max_left _ _
  have hbw : 0 < A.bw := hV.2.2.1.1
  obtain ⟨CG, Cw, m₀, hCG, hCw, hm₀, hmain⟩ := Construction.TerminalLift.terminal_level_lift
    X.α X.s X.hα₀ X.hα₁ X.hs₀ X.hs₁ X.q X.hq A.Λ hΛ128 X.ζ X.hζ A.dW A.NT (A.Dt * (A.dW + 1) * A.NT + A.k₀) ((A.Dt * (A.dW + 1) * A.NT + A.k₀) + 2) (A.Dt * (A.dW + 1) * A.NT + A.k₀) A.Dt
    hN hDt
  obtain ⟨B, hB, hsrc⟩ := stage_native_lift_source_exists_envelope A.bw hbw
    ((A.Dt * (A.dW + 1) * A.NT + A.k₀) + 4 * (A.dW + 1) * (A.NT + A.Dt) ^ 2)
    (max ((A.Dt * (A.dW + 1) * A.NT + A.k₀) + 2) ((A.Dt * (A.dW + 1) * A.NT + A.k₀) + 2) + A.dW * A.Dt + 2 * A.NT + 2 * A.Dt)
  let O : QEOrders := ⟨A.Dt, (A.Dt * (A.dW + 1) * A.NT + A.k₀), (A.Dt * (A.dW + 1) * A.NT + A.k₀) + 2, (A.Dt * (A.dW + 1) * A.NT + A.k₀), CG, Cw, fun r q => (Fintype.card (Finset.Icc 2 A.Dt) : ℝ) * B (r + q)⟩
  refine ⟨O.K + O.Ksrc + 2, max (O.kk + 1) (O.L + 2), 0, O, ⟨rfl, le_rfl, Nat.le_add_right _ _, le_rfl, le_rfl⟩,
    le_rfl, le_rfl, ?_⟩
  intro sXT sZT hX hZ Kout hK nW cr cK CL Cχ kW hcr hcr1 hcK hkc hks hG0 j₀
  obtain ⟨m₁, hm₁, hscale⟩ := hsc A.Λ hΛA cr hcr
  obtain ⟨M₂, hM₂, hratio⟩ := qe_eps_ratio (q := X.q) (Λ := A.Λ) X.hq.1 hΛ128 CL
  refine ⟨max (max m₀ m₁) (max j₀ M₂), fun M hM D hD a lawW PW Gw aM hW CcT hCcT k hk => ?_⟩
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, hband, hterm⟩ := hD
  obtain ⟨-, -, hlev, hdepth, hroot, -, hid, -, -, hinv⟩ := hW
  have hm₀M : m₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hM
  have hm₁M : m₁ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hM
  have hjM : j₀ ≤ M := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hM
  have hM₂M : M₂ ≤ M := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hM
  have hΛD : 128 ≤ D.Λ := hDΛ ▸ hΛ128
  have hqD : 1 < D.q := hDq ▸ X.hq.1
  have hbandD : IsOCBandChain X.α X.q A.Λ X.ζ D.term D.κ := hterm ▸ hband
  -- the scale bounds at the terminal slow length
  have hscl := hscale D.term D.κ hbandD M hm₁M (le_of_eq hterm.symm)
  have hprev : M - 1 ≤ D.term := le_trans (Nat.sub_le M 1) (le_of_eq hterm.symm)
  have key : 0 < cr * liftLength D M ∧
      ocDStar D.q D.Λ M (D.kap M) (D.kap (M - 1)) / (cr * liftLength D M) ≤ 1 ∧
      (cr * liftLength D M) / D.eps (M - 1) ≤ 1 := by
    simpa only [liftLength, OCData.kap, Nat.min_eq_left (le_of_eq hterm.symm),
      Nat.min_eq_left hprev, OCData.eps, hDα, hDq, hDΛ, hDζ] using hscl.2
  rw [← hlev] at key
  obtain ⟨hρ, hcell, hlam⟩ := key
  -- reserves
  have hres : ∀ v : CompIn Gw.comps, 0 ≤ compReserve kW v.1 :=
    fun v => (qe_compReserve_bounds kW hG0 v.1 (hroot v)).1
  have hres2 : ∀ v : CompIn Gw.comps, compReserve kW v.1 ≤ 2 :=
    fun v => (qe_compReserve_bounds kW hG0 v.1 (hroot v)).2
  -- record lengths
  have hlen : ∀ v u γ, 1 ≤ (Gw.fam.identity v u γ).record.birthExcess →
      (Gw.fam.identity v u γ).record.length ≤ D.eps Gw.level := by
    intro v u γ _
    have hE : D.eps Gw.level = D.eps M := congrArg D.eps hlev
    rw [hE]
    have h1 := (hid v u γ).2.2.1
    have h2 := hratio M hM₂M
    have h3 : D.eps (M + 1) = ocEpsilon X.q A.Λ (M + 1) := by
      simp only [OCData.eps, hDq, hDΛ]
    have h4 : D.eps M = ocEpsilon X.q A.Λ M := by simp only [OCData.eps, hDq, hDΛ]
    rw [h3] at h1
    rw [h4]
    exact h1.trans h2
  have hinv0 := hinv
  obtain ⟨hnat, -, -, -, hpar, hcert, -, -⟩ := hinv
  have hπ : ∀ v : CompIn Gw.comps, 0 < Gw.mass lawW v :=
    fun v => Construction.Preservation.Buffer.birth_compMass_pos hqD hΛD lawW v.1
  have hεpos : 0 ≤ D.eps (Gw.level - 1) :=
    le_of_lt (Construction.Stream.ocEpsilon_pos (q := D.q) (Λ := D.Λ) (by omega))
  have hsrc' := hsrc ScalarH D A.Dt j₀ Gw lawW PW _ _ A.φ₀ A.hφ₀ (M + A.Jw) kW aM (a + A.T₀) _ _
    hinv0 (by omega) (by omega) (Construction.Stream.ocEpsilon_pos (by omega)) hqD hΛD
    (hDζ ▸ X.hζ) (by rw [hDα, hDq, hDΛ, hDζ]; exact hbandD) hres hres2 hlen ⟨k, hk⟩
    ((cr * liftLength D Gw.level) / D.eps (Gw.level - 1)) (div_nonneg hρ.le hεpos)
    (fun _ => 1) (Or.inl rfl)
  simp only [one_pow, div_one] at hsrc'
  have hz : ∀ v u (d : Finset.Icc 2 A.Dt), A.Dt < d.1 →
      (familyLiftData D Gw.level k (nativeChain Gw.level k) (cr * liftLength D Gw.level)
        (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩))).edge v u d = [] := by
    intro v u d hd
    exact False.elim (Nat.not_lt_of_ge (Finset.mem_Icc.mp d.2).2 hd)
  have hset := hmain ScalarH D hDα hDq hDΛ hDζ hseq
    (by rw [hDα, hDq, hDΛ, hDζ]; exact hbandD) A.Dt j₀ (M + A.Jw) A.bw Gw kW hbw hcert hpar hnat
    (by omega) (by omega) (by omega) hdepth hres hres2 ⟨k, hk⟩ (cr * liftLength D Gw.level) hρ
    hcell hlam (Gw.mass lawW) hπ le_rfl
    (fun r q => (Fintype.card (Finset.Icc 2 A.Dt) : ℝ) * B (r + q))
    (recordMajorant (Gw.mass lawW) Gw.fam) (Cχ * D.eps M ^ A.χw) hz hsrc'
  obtain ⟨hsetting, Cc, hrestr, hamb⟩ := hset
  have hC' := hCcT k hk
  rw [← hlev] at hC'
  have heq := effective_liftSequence_coefficients_unique hsetting sXT sZT
    ((A.Dt * (A.dW + 1) * A.NT + A.k₀) + A.Dt + 2) (max ((A.Dt * (A.dW + 1) * A.NT + A.k₀) + 2 + 1) ((A.Dt * (A.dW + 1) * A.NT + A.k₀) + 2)) (CcT k) Cc hC' hamb
  rw [← hlev]
  exact ⟨_, Cχ * D.eps M ^ A.χw, le_rfl, by rw [hlev], Cc, hsetting, hrestr, heq⟩

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! **Quiet entrance from its two parts**: `TerminalQuietEntranceStatement` follows from
`QELiftSettingStatement` (Part 1) and `QEOperatorSmallStatement` (Part 2). The identification of
`û(t_p)` with the lift of the classical representative of `g` is proved here from
`entry_terminal_initial_value`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance
open AVRegularity.EntryTerminal.Route

namespace AVRegularity.EntryTerminal.QuietEntrance

theorem terminalQuietEntrance_of (h1 : QELiftSettingStatement) (h2 : QEOperatorSmallStatement) :
    TerminalQuietEntranceStatement := by
  intro X
  obtain ⟨Λ₁, h128, h1X⟩ := h1 X
  obtain ⟨Λ₂, -, h2X⟩ := h2 X
  refine ⟨max Λ₁ Λ₂, le_trans h128 (le_max_left _ _), fun A hΛ hV => ?_⟩
  obtain ⟨SX, SZ, Kfloor, O, hAdm, hSX, hSZ, hP1⟩ := h1X A (le_trans (le_max_left _ _) hΛ) hV
  refine ⟨SX, SZ, Kfloor, fun sXT sZT hX hZ Kout hK nW cr cK CL Cχ kW hcr hcr1 hcK hkc hks hG0 Q
    => ?_⟩
  obtain ⟨Cb, hCb, hP2⟩ := h2X A (le_trans (le_max_right _ _) hΛ) hV SX SZ Kfloor O hAdm hSX hSZ sXT sZT
    hX hZ Kout hK nW cr cK CL Cχ kW hcr hcr1 hcK hkc hks hG0 Q
  refine ⟨Cb, hCb, fun j₀ => ?_⟩
  obtain ⟨M₁, hM1⟩ := hP1 sXT sZT hX hZ Kout hK nW cr cK CL Cχ kW hcr hcr1 hcK hkc hks hG0 j₀
  obtain ⟨M₂, hM2⟩ := hP2 j₀
  refine ⟨max M₁ M₂, fun M hM D hD a lawW PW Gw aM hW tp haM htp hcol Gt hsub g Z₀ Z htr hZ CcT PZ
    aRep û hlift => ?_⟩
  have hset := hM1 M (le_trans (le_max_left _ _) hM) D hD a lawW PW Gw aM hW CcT hlift.1
  -- step 1: the order-zero truncation of `û` is a terminal lifted field
  have hlift0 : IsTerminalLiftedField Gw Gt M A.pT (A.Khat Kout) A.NT A.dW sXT sZT A.η₀ tp
      (a + A.T₀) cr Z CcT PZ aRep
      (fun v t => truncateTorusHk (Nat.zero_le A.k₀) (û v t)) := by
    refine ⟨hlift.1, hlift.2.1, fun v t ht => ?_⟩
    exact (qe_value_trunc (Nat.zero_le A.k₀) (û v t)).trans (hlift.2.2 v t ht)
  have hroot : ∀ v : CompIn Gw.comps, v.1.births = [] := hW.2.2.2.2.1
  obtain ⟨-, hrep, -, -⟩ := Providers.entry_terminal_initial_value Gw Gt M A.pT (A.Khat Kout) A.NT
    A.dW sXT sZT A.η₀ tp (a + A.T₀) cr htp hroot hsub g Z₀ Z htr hZ CcT PZ aRep _ hlift0
  have hk0 : A.k₀ ≤ A.Khat Kout :=
    le_trans (by omega : A.k₀ ≤ 2 * A.k₀ + 2) (le_trans (le_max_left _ _) (le_max_right Kout _))
  refine hM2 M (le_trans (le_max_right _ _) hM) D hD a lawW PW Gw aM hW tp haM htp hcol g CcT
    hlift.1 hset aRep hrep _ (fun v => ?_)
  exact qe_delta_jet hk0 (Nat.sub_le _ _) (g v) (fun x => aRep tp x v)
    (fun x => termLiftedRep Gw M A.NT A.dW cr CcT aRep tp x v) (û v tp) (hrep v)
    (hlift.2.2 v tp ⟨le_rfl, htp⟩)

end AVRegularity.EntryTerminal.QuietEntrance
end
end
end

section
section
/-! # The quiet entrance, exact zero: the time geometry and the quietness of the slot lift data

The slot of an observed pulse with `ϖ_k(t_p) ≠ 0` has its window start inside the quiet margin of
`t_p` (`qz_geometry`), and the restricted windowed lift data of the slot are quiet there
(`qz_slot_isQuietOn`). Both are the content of the corresponding lemmas of the quiet decay route,
restated here under their own names so that this route does not import the decay modules. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.EntryWeakProofs
open AVRegularity.Construction.Preservation.FullLift AVRegularity.CycleComparison

namespace AVRegularity.EntryTerminal.QuietEntrance

open AVRegularity

/-- `ocL ≥ 5` once `ε_{m-1} > 0`. -/
theorem qz_ocL_ge_five (α q : ℝ) (Λ m : ℕ) (hΛ : 1 ≤ Λ) : 5 ≤ ocL α q Λ m := by
  unfold ocL
  have hpos : 0 < ocEpsilon q Λ (m - 1) ^ (-ocDelta α q) :=
    Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ) _
  have : 1 ≤ ⌈ocEpsilon q Λ (m - 1) ^ (-ocDelta α q)⌉₊ := Nat.one_le_iff_ne_zero.2
    (Nat.ceil_pos.2 hpos).ne'
  omega

/-- `τ'_m = L_m τ_m`. -/
theorem qz_ocTauP_eq (α q : ℝ) (Λ m : ℕ) (hΛ : 1 ≤ Λ) :
    ocTauP α q Λ m = (ocL α q Λ m : ℝ) * ocTau α q Λ m := by
  have h5 : (0 : ℝ) < ocL α q Λ m := by
    have := qz_ocL_ge_five α q Λ m hΛ
    exact_mod_cast (by omega : 0 < ocL α q Λ m)
  unfold ocTauP ocTau
  field_simp

/-- A nonvanishing cutoff confines the time to `|t - kτ| < 5τ/4`. -/
theorem qz_cutoff_ne_zero {α q : ℝ} {Λ m : ℕ} {k : ℤ} {t : ℝ}
    (hτ : 0 < ocTau α q Λ m) (h : ocCutoff α q Λ m k t ≠ 0) :
    |t - (k : ℝ) * ocTau α q Λ m| < 5 / 4 * ocTau α q Λ m := by
  by_contra hc
  have hc := not_lt.1 hc
  apply h
  unfold ocCutoff
  apply Real.smoothTransition.zero_of_nonpos
  have h1 : 5 / 2 ≤ 2 * |t - (k : ℝ) * ocTau α q Λ m| / ocTau α q Λ m := by
    rw [le_div_iff₀ hτ]; linarith
  linarith

/-- The quiet margin geometry: for `t` between the slot start and `t_p`, the `τ/24`-neighbourhood of `t`
lies in the quiet margin, `t ≥ a_M`, and `t_p - slotStart ≥ τ/48`. -/
theorem qz_geometry {τ L tp kr aM : ℝ} (hτ : 0 < τ) (hL : 5 ≤ L)
    (hcut : |tp - kr * τ| < 5 / 4 * τ) (haM : aM + L * τ ≤ tp) :
    (kr - 61 / 48) * τ ≤ tp ∧ τ / 48 ≤ tp - (kr - 61 / 48) * τ ∧ aM ≤ (kr - 61 / 48) * τ ∧
    ∀ t ∈ Set.Icc ((kr - 61 / 48) * τ) tp,
      Set.Icc (t - τ / 24) (t + τ / 24) ⊆ Set.Icc (tp - L * τ) (tp + L * τ) := by
  obtain ⟨h1, h2⟩ := abs_lt.1 hcut
  have hLτ : 5 * τ ≤ L * τ := by nlinarith
  refine ⟨by linarith, by linarith, by linarith, ?_⟩
  intro t ht x hx
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hx1, hx2⟩ := hx
  constructor <;> linarith

/-- **The restricted, windowed lift data of an odd slot is quiet on the trimmed quiet margin.** -/
theorem qz_slot_isQuietOn {ι : Type*} {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
    [∀ i, NormedSpace ℝ (h i)] {Dm : ℕ} {Pc : Type*} {Ctx : Pc → Type*}
    (Dd : OCData) (m : ℕ) {k : ℤ} (hk : Odd k) (hΛ : 1 ≤ Dd.Λ) (hζ : IsFastProfile Dd.ζ)
    (hκ : 0 < Dd.kap m) (A : RealChain) (ρ : ℝ) (F : ChartedFamily ι h Dm Pc Ctx) (p : Pc)
    (ctx : Ctx p) {W : Set ℝ}
    (hquiet : F.IsFastIndependentOn (ocTrimmedQuietTimes Dd.α Dd.q Dd.Λ Dd.ζ m ∩ W))
    (K : ℕ) (hKD : K ≤ Dm) (a b : ℝ) {S : Set ℝ}
    (hS : ∀ s ∈ S, s ∈ Set.Icc a b ∧ Dd.cellScaleSq m * s ∈
      ocTrimmedQuietTimes Dd.α Dd.q Dd.Λ Dd.ζ m ∩ W ∩ (F.piece p).output) :
    IsQuietOn
      (restrictLiftData K hKD
        {familyLiftData Dd m k A ρ (F.fiber p ctx) with
          edge := windowEdges a b (familyLiftData Dd m k A ρ (F.fiber p ctx)).edge}).edge
      (fun t z => Real.sqrt (restrictLiftData K hKD
        {familyLiftData Dd m k A ρ (F.fiber p ctx) with
          edge := windowEdges a b (familyLiftData Dd m k A ρ (F.fiber p ctx)).edge}).η •
        (restrictLiftData K hKD
        {familyLiftData Dd m k A ρ (F.fiber p ctx) with
          edge := windowEdges a b (familyLiftData Dd m k A ρ (F.fiber p ctx)).edge}).v t z) S := by
  refine ⟨?_, ?_⟩
  · intro s hs z
    have h0 : ocPulse Dd.α Dd.q Dd.Λ Dd.ζ m k (Dd.cellScaleSq m * s) = 0 :=
      AVRegularity.CycleComparison.Assembly.ocPulse_eq_zero_of_quiet hΛ hζ hk
        (ocTrimmedQuietTimes_subset_quiet hΛ Dd.ζ m (hS s hs).2.1.1)
    have hsq : ocEll Dd.q Dd.Λ m (Dd.kap m) ^ 2 = Dd.cellScaleSq m := by
      rw [CycleReference.ocEll_sq_eq hκ]; rfl
    show Real.sqrt (Dd.kap m / Dd.kap (m - 1)) •
      ((ocEll Dd.q Dd.Λ m (Dd.kap m) ^ 2 / ocEpsilon Dd.q Dd.Λ m) •
        (ocPulse Dd.α Dd.q Dd.Λ Dd.ζ m k (ocEll Dd.q Dd.Λ m (Dd.kap m) ^ 2 * s) •
          ocShearVel Dd.α Dd.q Dd.Λ m k (ocEpsilon Dd.q Dd.Λ m • z))) = 0
    rw [hsq, h0]
    simp only [zero_smul, smul_zero]
  · intro v u d γ hγ w s hs X z z'
    simp only [restrictLiftData, restrictConstituentEdges, familyLiftData, windowEdges] at hγ
    obtain ⟨γ₁, hγ₁, rfl⟩ := List.mem_map.1 hγ
    obtain ⟨γ₀, -, -, hc⟩ := LiftSetting.mem_liftEdges_fiber hγ₁
    have hsab := (hS s hs).1
    have hmax : max a (min b s) = s := by
      rw [min_eq_right hsab.2, max_eq_right hsab.1]
    show γ₁.coeff w (max a (min b s)) X z = γ₁.coeff w (max a (min b s)) X z'
    rw [hmax, hc]
    exact hquiet p ctx v u γ₀ d.1 w (Dd.cellScaleSq m * s) (hS s hs).2
      ((ρ / Dd.eps (m - 1)) • X) z z'

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! # Exact zero: the positive lifts of a quiet stretch vanish

`qe_zero_slot_core`: a lift sequence on a window whose lift data are quiet on `[s, t]` (drift and
edge coefficients fast independent) has all positive lifts zero at `t`. This is `r2c_quietZero_core`
(the generic core of the restart) read off `IsQuietOn`. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.EntryTerminal.QuietEntrance

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, InnerProductSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- **The positive lifts vanish at the end of a quiet stretch.** -/
theorem qe_zero_slot_core (Q : LiftOperatorData ι h D) (sX sZ N H : ℕ) (s t e : ℝ)
    (Cc : ℕ → ℕ → LiftCoeff ι h) (hseq : IsLiftSequence Q sX sZ s e N H Cc) (hst : s ≤ t)
    (hte : t ≤ e) (hsymm : ∀ τ X i j, Q.G τ X i j = Q.G τ X j i)
    (hell : ∀ τ ∈ Set.Icc s e, ∀ X (ξ : Vec 2), (3 / 4) * ∑ i, ξ i ^ 2 ≤ ∑ i, ∑ j, Q.G τ X i j * ξ i * ξ j ∧
      ∑ i, ∑ j, Q.G τ X i j * ξ i * ξ j ≤ (5 / 4) * ∑ i, ξ i ^ 2)
    (hη : 0 < Q.η) (hq : IsQuietOn Q.edge (fun τ z => Real.sqrt Q.η • Q.v τ z) (Set.Icc s t)) :
    ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u, Cc hh n m α t X z v u = 0 := by
  intro hh hhH n hn m α X z v u
  refine AVRegularity.EntryTerminal.Ingredients.Recon.r2c_quietZero_core Q sX sZ N H s t e Cc hseq hst hte hsymm
    ⟨3 / 4, 5 / 4, by norm_num, fun τ hτ => hell τ ⟨hτ.1, hτ.2.trans hte⟩⟩ (fun τ hτ z => ?_)
    (fun τ hτ v u d γ hγ α X z z' => hq.2 v u d γ hγ α τ hτ X z z') hh hhH n hn m α t
    ⟨hst, le_rfl⟩ X z v u
  exact (smul_eq_zero.1 (hq.1 τ hτ z)).resolve_left (Real.sqrt_pos.2 hη).ne'

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! # The quiet entrance, exact zero (step i): the positive lifts of the observed slots vanish
at `t_p`

For an observed slot `k` with `ϖ_k(t_p) ≠ 0`, the interval from the slot start to `t_p` lies in the
trimmed quiet margin and in `[a_M, a + T₀]`; the restricted windowed lift data of the slot are quiet
there (`qz_slot_isQuietOn`), so `qe_zero_slot_core` (the generic core `r2c_quietZero_core`) shows
that the positive lifts of the setting's sequence, hence of `CcT k`, vanish at the cell time of `t_p`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryWeakProofs

namespace AVRegularity.EntryTerminal.QuietEntrance

/-- **Step (i): the positive lifts of an observed slot vanish exactly at the cell time of `t_p`.** -/
theorem qz_cc_vanish {X : TermConstruction} (A : TermArgs X) (hΛ128 : 128 ≤ A.Λ)
    (O : QEOrders) (nW : ℕ+) (cr CL Cχ : ℝ) (kW : InvConsts) {j₀ M : ℕ} (D : OCData)
    (hD : IsTermData X A.Λ M D) {a : ℝ} {lawW : BirthLaw} {PW : ProvParams}
    {Gw : GenStage D ScalarH A.Dt A.bw j₀} {aM : ℝ}
    (hW : IsWeakStage lawW PW A.φ₀ A.hφ₀ M (M + A.Jw) A.Jw A.dW A.DW nW kW a A.T₀ A.σw CL Cχ A.χw
      Gw aM) {tp : ℝ} (haM : aM + ocTauP D.α D.q D.Λ M ≤ tp) (htp : tp ≤ a + A.T₀)
    (hcol : Set.Icc (tp - ocTauP D.α D.q D.Λ M) (tp + ocTauP D.α D.q D.Λ M) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ M)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (hset : ∀ (k : ℤ) (hk : Odd k),
      QESlotSetting D M Gw lawW cr (Cχ * D.eps M ^ A.χw) A.NT A.dW O CcT k hk)
    {k : ℤ} (hkobs : k ∈ ocObsPulses D.α D.q D.Λ M tp tp)
    (hcut : ocCutoff D.α D.q D.Λ M k tp ≠ 0) :
    tp / D.cellScaleSq M ∈ Set.Icc (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) ∧
      ∀ hh ≤ A.dW, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
        CcT k hh n m α (tp / D.cellScaleSq M) X z v u = 0 := by
  classical
  obtain ⟨hDα, hDq, hDΛ, hDζ, hseq, hband, hterm⟩ := hD
  have hΛ1 : 1 ≤ D.Λ := by rw [hDΛ]; omega
  obtain ⟨-, -, hlev, -, -, -, -, -, -, hinv⟩ := hW
  obtain ⟨hnat, -, -, -, -, -, -, -, -, -, -, -, hfast, -⟩ := hinv
  have hfastM : Gw.fam.IsFastIndependentOn
      (ocTrimmedQuietTimes D.α D.q D.Λ D.ζ M ∩ Set.Icc aM (a + A.T₀)) := hlev ▸ hfast
  have hout : ∀ p, (Gw.fam.piece p).output = ocPulseWindow D.α D.q D.Λ M p.1 := fun p =>
    hlev ▸ (hnat.1 p).2.1
  have hτ : 0 < ocTau D.α D.q D.Λ M := Construction.Stream.ocTau_pos hΛ1
  have hLge : (5 : ℝ) ≤ (ocL D.α D.q D.Λ M : ℝ) := by
    exact_mod_cast qz_ocL_ge_five D.α D.q D.Λ M hΛ1
  have hTP := qz_ocTauP_eq D.α D.q D.Λ M hΛ1
  have hcol' : Set.Icc (tp - (ocL D.α D.q D.Λ M : ℝ) * ocTau D.α D.q D.Λ M)
      (tp + (ocL D.α D.q D.Λ M : ℝ) * ocTau D.α D.q D.Λ M) ⊆
      ocQuietTimes D.α D.q D.Λ D.ζ M := by rw [← hTP]; exact hcol
  have haM' : aM + (ocL D.α D.q D.Λ M : ℝ) * ocTau D.α D.q D.Λ M ≤ tp := by
    rw [← hTP]; exact haM
  have hk : Odd k := (Finset.mem_filter.1 hkobs).2.1
  obtain ⟨price, Θ, hKD, hΘ, Cc', hsetL, hseqL, hagree⟩ := hset k hk
  have hcs : 0 < D.cellScaleSq M := div_pos (pow_pos hsetL.e_pos 2) hsetL.ν_pos
  have hgeo := qz_geometry hτ hLge (qz_cutoff_ne_zero hτ hcut) haM'
  obtain ⟨hgeo1, hgeo2, hgeo3, hgeo4⟩ := hgeo
  have hcutR := qz_cutoff_ne_zero hτ hcut
  have hss : D.slotStart M k = ((k : ℝ) - 61 / 48) * ocTau D.α D.q D.Λ M := rfl
  set s : ℝ := D.slotStart M k / D.cellScaleSq M with hs
  set T : ℝ := tp / D.cellScaleSq M - s with hT
  have hsT : s + T = tp / D.cellScaleSq M := by rw [hT]; ring
  have hcsT : D.cellScaleSq M * T = tp - D.slotStart M k := by
    rw [hT, hs]; field_simp
  have hTpos : 0 < T := (mul_pos_iff_of_pos_left hcs).1 (by rw [hcsT, hss]; linarith)
  have hwin : tp ≤ ((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M := by
    have := (abs_lt.1 hcutR).2
    linarith
  have hcss : D.cellScaleSq M * s = D.slotStart M k := by rw [hs]; field_simp
  have hS : ∀ u ∈ Set.Icc s (s + T),
      u ∈ Set.Icc s ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) ∧
      D.cellScaleSq M * u ∈ ocTrimmedQuietTimes D.α D.q D.Λ D.ζ M ∩ Set.Icc aM (a + A.T₀) ∩
        (Gw.fam.piece ⟨k, hk⟩).output := by
    intro u hu
    have hu1 : D.slotStart M k ≤ D.cellScaleSq M * u := by
      rw [← hcss]; exact mul_le_mul_of_nonneg_left hu.1 hcs.le
    have hu2 : D.cellScaleSq M * u ≤ tp := by
      have : u ≤ tp / D.cellScaleSq M := hsT ▸ hu.2
      rw [le_div_iff₀ hcs] at this
      linarith
    refine ⟨⟨hu.1, ?_⟩, ⟨?_, ?_⟩, ?_⟩
    · exact (hsT ▸ hu.2).trans (div_le_div_of_nonneg_right hwin hcs.le)
    · show Set.Icc _ _ ⊆ _
      intro x hx
      exact hcol' (hgeo4 _ ⟨by rw [← hss]; exact hu1, hu2⟩ hx)
    · constructor
      · rw [hss] at hu1; linarith
      · exact hu2.trans htp
    · rw [hout]
      constructor
      · rw [hss] at hu1; exact hu1
      · exact hu2.trans hwin
  have hζ' : IsFastProfile D.ζ := hDζ ▸ X.hζ
  have hquietOn := qz_slot_isQuietOn D M hk hΛ1 hζ' hsetL.ν_pos (nativeChain M k)
    (cr * liftLength D M) Gw.fam ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩) hfastM O.Ksrc hKD s
    ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) hS
  have htend : tp / D.cellScaleSq M ≤
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) :=
    div_le_div_of_nonneg_right hwin hcs.le
  have hη : 0 < (restrictLiftData O.Ksrc hKD
      {familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)) with
        edge := Construction.Preservation.FullLift.windowEdges s
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M)
          (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
            (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩))).edge}).η := by
    rw [hsetL.η_eq]; exact div_pos hsetL.ν_pos hsetL.B_pos
  have hz0 := qe_zero_slot_core _ _ _ _ _ s (tp / D.cellScaleSq M)
    ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) Cc' hseqL
    (by rw [← hsT]; linarith) htend hsetL.G_symm
    (fun τ hτ X ξ => hsetL.G_ellip τ hτ X ξ) hη (by rw [← hsT]; exact hquietOn)
  have htmem : tp / D.cellScaleSq M ∈ Set.Icc s
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) :=
    ⟨by rw [← hsT]; linarith, htend⟩
  refine ⟨htmem, fun hh hhH n hn m α X' z v u => ?_⟩
  rw [hagree hh hhH n m α _ htmem X' z v u]
  exact hz0 hh hhH n hn m α X' z v u

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! # The quiet entrance, exact zero (step ii): the glued lift at `t_p` is the identity

When the positive lifts of every observed slot with `ϖ_k(t_p) ≠ 0` vanish at the cell time of
`t_p`, the physical lift of the slot at `t_p` is the field itself (`C₀^{(0)} = I`, chart ∘ label =
id), and the weights `ϖ_k(t_p)` add up to one. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route AVRegularity.EntryWeakProofs

namespace AVRegularity.EntryTerminal.QuietEntrance

section Pulse

variable {ι : Type*} [Fintype ι] {h : ι → Type*} [∀ i, NormedAddCommGroup (h i)]
  [∀ i, NormedSpace ℝ (h i)] [∀ i, FiniteDimensional ℝ (h i)] {D : ℕ}

/-- Degree `0`, grade `0` lifts are the identity on values. -/
theorem qz_apply_zero_id {Q : LiftOperatorData ι h D} {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) {s : ℝ}
    (hs : s ∈ Set.Icc t₀ t₁) (b : ℝ → Vec 2 → ∀ i, h i) (X z : Vec 2) :
    liftApply 0 (Cc 0 0) b s X z = b s X := by
  have h1 := hC.1 (fun _ => b s X) contDiff_const s hs X z
  have e : liftApply 0 (Cc 0 0) b s X z = liftApply 0 (Cc 0 0) (fun _ => fun _ => b s X) s X z := by
    funext v
    simp [liftApply, orderedDerivative]
  rw [e, h1]

/-- **The physical lift of a pulse is the field itself at a time where its positive lifts vanish.** -/
theorem qz_pulse_eq (Q : LiftOperatorData ι h D) {sX sZ N H : ℕ} {t₀ t₁ : ℝ}
    {Cc : ℕ → ℕ → LiftCoeff ι h} (hC : IsLiftSequence Q sX sZ t₀ t₁ N H Cc) (c ρ e εc t : ℝ)
    (hc : c ≠ 0) (hρ : ρ ≠ 0) (hmem : c⁻¹ * t ∈ Set.Icc t₀ t₁)
    (hz : ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
      Cc hh n m α (c⁻¹ * t) X z v u = 0)
    (chart label : ℝ → Vec 2 → Vec 2) (a : ℝ → Vec 2 → ∀ i, h i) (x : Vec 2)
    (hinv : chart t (label t x) = x) :
    pulsePhysicalLift c ρ e εc N H Cc chart label a t x = a t x := by
  have hzero : ∀ hh ≤ H, ∀ n, (n ≠ 0 ∨ hh ≠ 0) → ∀ (B : ℝ → Vec 2 → ∀ i, h i) X' z',
      liftApply n (Cc hh n) B (c⁻¹ * t) X' z' = 0 := by
    intro hh hhH n hn B X' z'
    funext v
    have hall : ∀ m (α : DerivativeWord2 m) u, Cc hh n m α (c⁻¹ * t) X' z' v u = 0 := by
      intro m α u
      rcases hn with hn | hn
      · exact hz hh hhH n (Nat.one_le_iff_ne_zero.2 hn) m α X' z' v u
      · have hn0 : n = 0 ∨ n ≠ 0 := by omega
        rcases hn0 with rfl | hn0
        · exact hC.2.1 hh (Nat.one_le_iff_ne_zero.2 hn) hhH m α _ X' z' v u
        · exact hz hh hhH n (Nat.one_le_iff_ne_zero.2 hn0) m α X' z' v u
    simp [liftApply, hall]
  unfold pulsePhysicalLift diagSample
  rw [Finset.sum_eq_single 0]
  · beta_reduce
    rw [Finset.sum_eq_single 0]
    · simp only [pow_zero, one_smul]
      rw [qz_apply_zero_id hC hmem]
      simp only [← mul_assoc, mul_inv_cancel₀ hc, one_mul, smul_inv_smul₀ hρ, hinv]
    · intro n _ hn
      rw [hzero 0 (Nat.zero_le _) n (Or.inl hn)]
      exact smul_zero _
    · intro hn; exact absurd (Finset.mem_range.2 (Nat.succ_pos N)) hn
  · intro hh hhm hne
    refine Finset.sum_eq_zero fun n _ => ?_
    rw [hzero hh (Nat.lt_succ_iff.1 (Finset.mem_range.1 hhm)) n (Or.inr hne)]
    exact smul_zero _
  · intro hn; exact absurd (Finset.mem_range.2 (Nat.succ_pos H)) hn

end Pulse

/-- An odd slot with nonvanishing cutoff at `t` is observed at `t`. -/
theorem qz_mem_obs {α q : ℝ} {Λ m : ℕ} (hτ : 0 < ocTau α q Λ m) {k : ℤ} (hk : Odd k) {t : ℝ}
    (hcut : ocCutoff α q Λ m k t ≠ 0) : k ∈ ocObsPulses α q Λ m t t := by
  classical
  have h5 := qz_cutoff_ne_zero hτ hcut
  have hwin : t ∈ ocPulseWindow α q Λ m k := by
    obtain ⟨h1, h2⟩ := abs_lt.1 h5
    unfold ocPulseWindow
    constructor <;> nlinarith
  unfold ocObsPulses
  rw [Finset.mem_filter, Finset.mem_Icc]
  refine ⟨⟨?_, ?_⟩, hk, ⟨t, hwin, le_rfl, le_rfl⟩⟩
  · have h1 : t / ocTau α q Λ m < (k : ℝ) + 5 / 4 := by
      rw [div_lt_iff₀ hτ]; have := (abs_lt.1 h5).2; linarith
    have h2 := Int.floor_le (t / ocTau α q Λ m)
    have h4 : (⌊t / ocTau α q Λ m⌋ : ℝ) - 1 < k + 1 := by linarith
    have h5' : ⌊t / ocTau α q Λ m⌋ - 1 < k + 1 := by exact_mod_cast h4
    omega
  · have h1 : ((k : ℝ) - 5 / 4) < t / ocTau α q Λ m := by
      rw [lt_div_iff₀ hτ]; have := (abs_lt.1 h5).1; linarith
    have h2 := Int.le_ceil (t / ocTau α q Λ m)
    have h4 : (k : ℝ) < ⌈t / ocTau α q Λ m⌉ + 2 := by linarith
    have : k < ⌈t / ocTau α q Λ m⌉ + 2 := by exact_mod_cast h4
    omega

/-- **Step (ii): the glued lift of the field at `t_p` is the field itself** when the positive
lifts of the observed slots with nonvanishing cutoff vanish at the cell time of `t_p`. -/
theorem qz_lifted_rep_eq {Dt : ℕ} {bw : ℝ} {j₀ : ℕ} (D : OCData) (M : ℕ)
    (Gw : GenStage D ScalarH Dt bw j₀) (N H sXT sZT : ℕ) (cr tp : ℝ)
    (CcT : ℤ → ℕ → ℕ → LiftCoeff (CompIn Gw.comps) (fun v => ScalarH v.1.root))
    (aRep : ℝ → Vec 2 → ∀ v : CompIn Gw.comps, ScalarH v.1.root) (x : Vec 2)
    (hτ : 0 < ocTau D.α D.q D.Λ M) (hcs : D.cellScaleSq M ≠ 0) (hρ : cr * liftLength D M ≠ 0)
    (hseq : ∀ (k : ℤ) (hk : Odd k),
      IsLiftSequence (familyLiftData D M k (nativeChain M k) (cr * liftLength D M)
          (Gw.fam.fiber ⟨k, hk⟩ (Gw.actual ⟨k, hk⟩)))
        sXT sZT (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) N H (CcT k))
    (hvan : ∀ k ∈ ocObsPulses D.α D.q D.Λ M tp tp, ocCutoff D.α D.q D.Λ M k tp ≠ 0 →
      tp / D.cellScaleSq M ∈ Set.Icc (D.slotStart M k / D.cellScaleSq M)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ M) / D.cellScaleSq M) ∧
      ∀ hh ≤ H, ∀ n, 1 ≤ n → ∀ m (α : DerivativeWord2 m) X z v u,
        CcT k hh n m α (tp / D.cellScaleSq M) X z v u = 0) :
    termLiftedRep Gw M N H cr CcT aRep tp x = aRep tp x := by
  classical
  unfold termLiftedRep gluedLift
  have hterm : ∀ k ∈ ocObsPulses D.α D.q D.Λ M tp tp,
      ocCutoff D.α D.q D.Λ M k tp • pulsePhysicalLift (D.cellScaleSq M) (cr * liftLength D M)
        (D.eps M) (ocDStar D.q D.Λ M (D.κ M) (D.κ (M - 1)) / (cr * liftLength D M)) N H (CcT k)
        (fun s' y => D.flowOf (M - 1) s' y (D.slotAnchor M k))
        (fun s' y => D.flowOf (M - 1) (D.slotAnchor M k) y s') aRep tp x =
      ocCutoff D.α D.q D.Λ M k tp • aRep tp x := by
    intro k hk
    by_cases hcut : ocCutoff D.α D.q D.Λ M k tp = 0
    · simp [hcut]
    · have hodd : Odd k := (Finset.mem_filter.1 hk).2.1
      obtain ⟨hmem, hz⟩ := hvan k hk hcut
      rw [qz_pulse_eq _ (hseq k hodd) _ _ _ _ _ hcs hρ (by rwa [← div_eq_inv_mul])
        (by simpa only [← div_eq_inv_mul] using hz) _ _ aRep x ?_]
      unfold OCData.flowOf
      rw [CycleComparison.Charts.streamFlow_group_law (D.hΦ (M - 1)),
        CycleComparison.Charts.streamFlow_self (D.hΦ (M - 1))]
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul,
    Providers.CascadeInvariants.sum_ocCutoff_eq_one hτ _ (fun k hk => (Finset.mem_filter.1 hk).2.1) tp
      (fun k hk hne => qz_mem_obs hτ hk hne), one_smul]

end AVRegularity.EntryTerminal.QuietEntrance
end
end

section
/-! # The quiet entrance, exact zero: the assembly

At `t_p` the glued lift of the classical representative `aRep` is `aRep` itself (`qz_lifted_rep_eq`,
from the exact vanishing of the positive lifts `qz_cc_vanish`), so every `Δ` with value
`aRep - T aRep` at `t_p` is zero, and its weighted norm is `0`. This proves `QEOperatorSmallStatement`
with `C_b = 0`, and with the lift setting (part 1) the statement
`TerminalQuietEntranceStatement`. -/

@[expose] public noncomputable section

open MeasureTheory Homogenization AVRegularity.Sobolev AVenhance AVRegularity
open AVRegularity.EntryTerminal.Route

namespace AVRegularity.EntryTerminal.QuietEntrance

section Zero

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [MeasurableSpace E]
  [BorelSpace E] [CompleteSpace E] [FiniteDimensional ℝ E] {K : ℕ}

/-- A `TorusHk` element with almost everywhere vanishing value jet is zero. -/
theorem qz_torusHk_zero_of_value (f : TorusHk K E)
    (h : f.toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube] fun _ => 0) :
    f = 0 := by
  have h0 : (0 : TorusHk K E).toFunction.jet (valueIndex2 K) =ᵐ[volume.restrict AVenhance.unitCube]
      fun _ => 0 := by
    filter_upwards [CycleComparison.Coarse.jet_sub_ae f f] with x hx
    have := hx (valueIndex2 K)
    simp only [sub_self] at this
    exact this
  exact KernelEnergy.torusCarrier_eq_of_value_ae f 0 (h.trans h0.symm)

end Zero

/-- The weighted norm of the zero family is zero. -/
theorem qz_weightedNorm_zero {S : Finset Comp} (K : ℕ) (ρ : ℝ) (π w : CompIn S → ℝ) :
    weightedNorm ρ π w (fun v => (0 : TorusHk K (ScalarH v.1.root))) = 0 := by
  unfold weightedNorm
  rw [show (fun v : CompIn S => (0 : TorusHk K (ScalarH v.1.root)).val) = 0 from rfl,
    CycleJointProofs.massNormSq_zero, Real.sqrt_zero]

/-- **Part 2 of the quiet entrance, as an exact zero**: the operator `T - I` vanishes at the quiet
anchor. -/
theorem qz_operatorSmall : QEOperatorSmallStatement := by
  intro X
  refine ⟨128, le_rfl, fun A hΛ hV SX SZ Kfloor O hAdm hSX hSZ sXT sZT hX hZ Kout hK nW cr cK CL Cχ
    kW hcr hcr1 hcK hkc hks hG0 Q => ⟨0, le_rfl, fun j₀ => ⟨0, fun M _ D hD a lawW PW Gw aM hW tp haM
    htp hcol g CcT hCcT hset aRep hrep Δ hΔ => ?_⟩⟩⟩
  classical
  obtain ⟨price, Θ, hKD, hΘ, Cc', hsetL, -⟩ := hset 1 odd_one
  have hcs : 0 < D.cellScaleSq M := div_pos (pow_pos hsetL.e_pos 2) hsetL.ν_pos
  have hρ : 0 < cr * liftLength D M := hsetL.ρ_pos
  have hΛ1 : 1 ≤ D.Λ := by rw [hD.2.2.1]; omega
  have hτ : 0 < ocTau D.α D.q D.Λ M := Construction.Stream.ocTau_pos hΛ1
  have hvan := fun k hk hcut => qz_cc_vanish A hΛ O nW cr CL Cχ kW D hD hW haM htp hcol CcT hset
    (k := k) hk hcut
  have heq : ∀ x, termLiftedRep Gw M A.NT A.dW cr CcT aRep tp x = aRep tp x := fun x =>
    qz_lifted_rep_eq D M Gw A.NT A.dW sXT sZT cr tp CcT aRep x hτ hcs.ne' hρ.ne' hCcT hvan
  have hΔ0 : Δ = fun v => (0 : TorusHk A.k₀ (ScalarH v.1.root)) := by
    funext v
    refine qz_torusHk_zero_of_value _ ?_
    filter_upwards [hΔ v] with x hx
    rw [hx, heq x]
    simp
  rw [hΔ0, qz_weightedNorm_zero]
  simp

/-- **The quiet entrance**: `TerminalQuietEntranceStatement`, from the lift setting (part 1) and
the exact vanishing of `T - I` at the quiet anchor. -/
theorem terminalQuietEntrance : TerminalQuietEntranceStatement :=
  terminalQuietEntrance_of qe_liftSetting qz_operatorSmall

end AVRegularity.EntryTerminal.QuietEntrance
end
end
end
