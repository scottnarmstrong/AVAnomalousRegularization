-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Jet.CovLetter
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Construction.Stream.NextAdmissible

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the explicit transferred coefficients are generated.** `transferExprAt` is the
explicit expression, at every slot, of a transferred coefficient of order `d ≥ 2` (and `0` below
order two), built from explicit finer family expressions `cfin`. If the finer expressions denote
the finer outputs on the admissible chains and output windows of their slots, the explicit
expressions satisfy `IsExprFor` (`isExprFor_transferExprAt`; `isExprFor_of_transfer` with
the expressions made explicit). -/

open AVRegularity.Providers.GenSem

open scoped Classical in
/-- The scheduled finer slots of a slot, as a finite set (empty if not finite). -/
def finerSlots (D : OCData) (i : ℕ) (pc : ℤ) : Finset ℤ :=
  if h : {k : ℤ | Odd k ∧ IsScheduledIn D i k pc}.Finite then h.toFinset else ∅

open scoped Classical in
/-- **The explicit expression of a transferred coefficient at every slot.** -/
def transferExprAt (D : OCData) (i : ℕ) (lam : ℝ) (Dγ d : ℕ) (I : DerivativeWord2 (d - 1))
    (c : Fin 2)
    (cfin : (p : OddSlot) → (k : ℤ) → (d₁ : ℕ) → DerivativeWord2 (d₁ - 1) → Fin 2 →
      Gen .fam (i + 1) k) (p : OddSlot) : Gen .ctx i p.1 :=
  if 2 ≤ d then
    transferExpr i p.1 ((D.kap i * D.eps i ^ (d - 2))⁻¹ * lam) (finerSlots D i p.1) Dγ d I c
      (cfin p)
  else Gen.time (.const 0)

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

open scoped Classical in
/-- **The explicit transferred coefficients are generated.** -/
theorem isExprFor_transferExprAt (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G' : GenStage D hr Dm b j₀) {𝒮 : SeedExports}
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → G'.exports e)
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u') (d : ℕ) (I : DerivativeWord2 (d - 1))
    (c : Fin 2) (lam : ℝ) (Dγ : ℕ) (fop : FamFluxOp)
    (hflux : 2 ≤ d → ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (t : ℝ) (X z : Vec 2),
      G'.fam.flux p ctx v' u' γ' d I t X z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • X))
        then transferAt D (G'.level + 1) p.1 lam Dγ fop t
          (ctx.1.recenter D (D.eps (G'.level - 1) • X)) z d I
        else 0)
    (cfin : (p : OddSlot) → (k : ℤ) → (d₁ : ℕ) → DerivativeWord2 (d₁ - 1) → Fin 2 →
      Gen .fam (G'.level + 1) k)
    (hcfin : ∀ (p : OddSlot) (k : ℤ), Odd k → IsScheduledIn D G'.level k p.1 →
      ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ, ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        Gen.IsScheduled D (cfin p k d₁ I₁ i₀) ∧ Gen.FromSeed 𝒮 (cfin p k d₁ I₁ i₀) ∧
        ∃ fc : GenSort.Sem .fam, Gen.Denotes D b j₀ (cfin p k d₁ I₁ i₀) fc ∧
          ∀ A, IsAdmissibleChain D b j₀ (G'.level + 1) k A →
            ∀ t ∈ ocPulseWindow D.α D.q D.Λ (G'.level + 1) k,
              fc t A = fluxCoeff (fop k t A) d₁ I₁ 0 i₀) :
    G'.IsExprFor v' u' γ' d I c (transferExprAt D G'.level lam Dγ d I c cfin) := by
  by_cases hd : 2 ≤ d
  swap
  · intro p
    simp only [transferExprAt, hd, ↓reduceIte]
    refine ⟨.timeConst 0, .time _, GenSort.ofTime .ctx (TimeLetter.eval D (.const 0)), .time _,
      fun ctx t _ X z => ?_⟩
    have hz := G'.fam.flux_zero p ctx v' u' γ' d I (fun h => hd h.1)
    rw [hz]
    split_ifs <;> simp [GenSort.ofTime, TimeLetter.eval]
  have hτ : ∀ k, 0 < ocTau D.α D.q D.Λ k := fun _ => Construction.Stream.ocTau_pos hΛ
  intro p
  have hfin := scheduledSlots_finite D G'.level p.1 (hτ _)
  have hS : finerSlots D G'.level p.1 = hfin.toFinset := by
    simp only [finerSlots, hfin, ↓reduceDIte]
  have hrep := ctxRep_transferExpr (D := D) (bw := b) (j₀ := j₀) (𝒮 := 𝒮) hζ G'.level p.1
    (fun t ch _ => IsAdmissibleChain D b j₀ G'.level p.1 ch ∧
      t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1) lam Dγ fop d I c hfin (cfin p)
    (fun k hk hsch d₁ hd₁ I₁ i₀ => by
      obtain ⟨hs, hf, fc, hden, hv⟩ := hcfin p k hk hsch d₁ hd₁ I₁ i₀
      refine ⟨hs, hf, fc, hden, fun t ch z hP hcut => ?_⟩
      exact hv _ (appendChild_admissible D hΛ hζ hb hstart G'.level p.1 ch hP.1 k hk hsch t hcut z)
        t (mem_ocPulseWindow_of_ocCutoff_ne_zero (hτ _) hcut))
  obtain ⟨hs, hf, f, hden, hv⟩ := hrep
  simp only [transferExprAt, hd, ↓reduceIte, hS]
  refine ⟨hs, fromSeed_mono hexp hf, f, hden, fun ctx t ht X z => ?_⟩
  rw [hflux hd p ctx t X z]
  split_ifs with hadm
  · exact (hv t _ z ⟨hadm, ht⟩).symm
  · rfl

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the sizes of the old leaves.** The carrier grows with the reserve (`carrierC_mono`),
so the mode suprema do too (`ctxModeSup_mono`). Hence the weighted mode sum of the profile of an
old leaf, at a reserve `μ'` at most the reserve `μo` of its target component and at an inner rate
`a₀ ≤ 3π b` with any weight `L ≤ Lo`, is at most the certified ledger entry `θ_old` of the old
coefficient (`wsum_oldProfile_le`): the certificate (`GenStage.OldCert`) bounds the full context
size, slot supremum inside each mode, at the reserve of the target and the weight `Lo`. -/

open AVRegularity.Providers.Majorant

theorem carrierC_mono (D : OCData) {b : ℝ} (hb : 0 ≤ b) (hε : ∀ k, 0 ≤ D.eps k) (dd : ChainData)
    (n : ℕ) {mres mres' : ℝ} (hm : mres ≤ mres') :
    carrierC D b dd n mres ⊆ carrierC D b dd n mres' := by
  intro x hx
  obtain ⟨h1, h2, h3⟩ := hx
  refine ⟨h1.trans_le ?_, fun k => ⟨(h2 k).1.trans_le ?_, (h2 k).2.trans_le ?_⟩, h3.trans_le ?_⟩
  · have := hε dd.baseLevel
    gcongr
  · have := hε (dd.baseLevel + 1 + k)
    gcongr
  · gcongr
  · gcongr

theorem ctxModeSup_mono (D : OCData) {b : ℝ} (hb : 0 ≤ b) (hε : ∀ k, 0 ≤ D.eps k) (j₀ i : ℕ)
    (p : ℤ) (F : ChainData → (n : ℕ) → ℝ → ChainParamsC n → ℂ) {mres mres' : ℝ}
    (hm : mres ≤ mres') (h : ℤ) :
    ctxModeSup D b j₀ i p F mres h ≤ ctxModeSup D b j₀ i p F mres' h := by
  unfold ctxModeSup
  refine iSup₂_le fun dd n => iSup_le fun hdd => iSup₂_le fun t ht => iSup₂_le fun x hx =>
    iSup_le fun hre => ?_
  exact le_iSup₂_of_le dd n (le_iSup_of_le hdd (le_iSup₂_of_le t ht (le_iSup₂_of_le x
    (carrierC_mono D hb hε dd n hm hx) (le_iSup_of_le hre le_rfl))))

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
  {G : GenStage D hr Dm b j₀}

/-- The certified ledger entry of an old coefficient. -/
def oldTheta (hcert : G.OldCert 𝒮o μo Lo Co) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ :=
  Classical.choose (hcert v u γ)

theorem oldTheta_spec (hcert : G.OldCert 𝒮o μo Lo Co) (v u : CompIn G.comps) (γ : G.fam.Γ v u) :
    (∀ d α c, 0 ≤ oldTheta hcert v u γ d α c) ∧
      ∀ d, 2 ≤ d → d ≤ (G.fam.identity v u γ).maxOrder →
        (D.eps G.level / (G.fam.identity v u γ).record.length) ^ (d - 2) *
            ∑ α, ∑ c, oldTheta hcert v u γ d α c ≤ Co * (G.fam.identity v u γ).record.size :=
  ⟨(Classical.choose_spec (hcert v u γ)).1, (Classical.choose_spec (hcert v u γ)).2.1⟩

/-- The certified context size of an old coefficient. -/
theorem oldExt_ctxSize (hcert : G.OldCert 𝒮o μo Lo Co) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ctxSize D b j₀ G.level (fun p => oldExt hcert ⟨v, u, γ, d, α, c, p⟩) (μo v.1)
      Lo ≤ ENNReal.ofReal (oldTheta hcert v u γ d α c) :=
  (Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (hcert v u γ)).2.2 d α c))).2

/-- **The size of an old leaf.** -/
theorem wsum_oldProfile_le (hcert : G.OldCert 𝒮o μo Lo Co) (hb : 0 ≤ b)
    (hε : ∀ k, 0 ≤ D.eps k) (x : OldIdx G) {μ' : ℝ} (hμ : μ' ≤ μo x.v.1) {a₀ : ℝ}
    (ha₀ : a₀ ≤ 3 * Real.pi * b) {L : ℕ} (hL : L ≤ Lo) :
    wsum a₀ L (fun h => ctxModeSup D b j₀ G.level x.p.1 (oldExt hcert x) μ' h) ≤
      ENNReal.ofReal (oldTheta hcert x.v x.u x.γ x.d x.α x.c) := by
  refine le_trans ?_ (oldExt_ctxSize hcert x.v x.u x.γ x.d x.α x.c)
  unfold wsum ctxSize
  refine ENNReal.tsum_le_tsum fun h => ?_
  refine mul_le_mul' (modeWeight_mono ha₀ hL h) ?_
  refine (ctxModeSup_mono D hb hε j₀ G.level x.p.1 _ hμ h).trans ?_
  exact le_iSup (f := fun p : {k : ℤ // Odd k} =>
    ctxModeSup D b j₀ G.level p.1 (oldExt hcert ⟨x.v, x.u, x.γ, x.d, x.α, x.c, p⟩)
      (μo x.v.1) h) x.p

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the lift constants depend on the graded context only through `S, K_g, K_d`.**
`constCtx κ S Kg Kd` is a context carrying only these constants; the size constants of the lift
recursion (`liftB`) and of the slow flux (`fluxXc`) over any context with the same three constants
are those of `constCtx` (`liftB_congr`, `fluxXc_congr`). The thresholds of the ledger are stated
with `constCtx`, independently of the data. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- A graded context carrying only the constants `S, K_g, K_d`. -/
def constCtx (κ : MajConsts) (S Kg Kd : ℝ≥0) : GCtx where
  κ := κ
  Δ := 0
  a₀ := 0
  leaf := fun _ => none
  μ₀ := 0
  L₀ := 0
  T := Set.univ
  S := S
  Kg := Kg
  Kd := Kd

/-- Two graded contexts have the same constants. -/
structure SameConsts (X X' : GCtx) : Prop where
  hS : X.S = X'.S
  hKg : X.Kg = X'.Kg
  hKd : X.Kd = X'.Kd

variable {X X' : GCtx}

theorem dGK_congr (h : SameConsts X X') (s : ℝ) : UEnv.dGK X s = UEnv.dGK X' s := by
  simp only [UEnv.dGK, h.hS]

theorem cellB1C_congr (h : SameConsts X X') (η : ℝ) (C : ℝ≥0) :
    UEnv.cellB1C X η C = UEnv.cellB1C X' η C := by
  simp only [UEnv.cellB1C, h.hS, h.hKg, h.hKd]

theorem cellB2C_congr (h : SameConsts X X') (η : ℝ) (C : ℝ≥0) :
    UEnv.cellB2C X η C = UEnv.cellB2C X' η C := by
  simp only [UEnv.cellB2C, h.hS, h.hKg]

theorem edgeWordC_congr (h : SameConsts X X') (Dm : ℕ) :
    UEnv.edgeWordC X Dm = UEnv.edgeWordC X' Dm := by
  simp only [UEnv.edgeWordC, dGK_congr h]

theorem liftAc_congr (h : SameConsts X X') (Dm : ℕ) (β : ℕ → ℕ → ℝ≥0) (hh n : ℕ) :
    UEnv.liftAc X Dm β hh n = UEnv.liftAc X' Dm β hh n := by
  simp only [UEnv.liftAc, cellB1C_congr h, cellB2C_congr h, dGK_congr h, edgeWordC_congr h]

theorem srcCc_congr (h : SameConsts X X') (Dm : ℕ) (β : ℕ → ℕ → ℝ≥0) (hh n : ℕ) :
    UEnv.srcCc X Dm β hh n = UEnv.srcCc X' Dm β hh n := by
  simp only [UEnv.srcCc, liftAc_congr h, h.hS]

theorem liftBfun_congr (h : SameConsts X X') (Dm : ℕ) :
    ∀ r hh n, liftBfun X Dm r hh n = liftBfun X' Dm r hh n := by
  intro r
  induction r with
  | zero => intro hh n; rfl
  | succ r ih =>
    intro hh n
    have hβ : liftBfun X Dm r = liftBfun X' Dm r := funext fun hh => funext fun n => ih hh n
    simp only [liftBfun, hβ, srcCc_congr h]

theorem liftB_congr (h : SameConsts X X') (Dm : ℕ) : liftB X Dm = liftB X' Dm :=
  funext fun hh => funext fun n => liftBfun_congr h Dm (hh + n) hh n

theorem fluxXc_congr (h : SameConsts X X') (Dm hh n : ℕ) :
    UEnv.fluxXc X Dm (liftB X Dm) hh n = UEnv.fluxXc X' Dm (liftB X' Dm) hh n := by
  rw [liftB_congr h Dm]
  simp only [UEnv.fluxXc, h.hS, h.hKg, h.hKd, edgeWordC_congr h]

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: no uncertified solved node.** An expression without any `solved` node
(`Gen.NoSolved`) is `SolvedFree` for every leaf map (`solvedFree_of_noSolved`); letters, the
entries of `J⁻¹` and the Piola factors have none. `SolvedFree` passes through the explicit sums
(`solvedFree_genSumList`), and a wrapped old expression is a certified leaf of `oldLeaf`
(`solvedFree_oldWrap`). Hence the explicit direct transport and the explicit transfer of
`SolvedFree` finer expressions are `SolvedFree` (`solvedFree_directExpr`,
`solvedFree_transferExpr`). -/

open AVRegularity.Providers.GenSem

/-- The expression contains no `solved` node. -/
def _root_.AVRegularity.Gen.NoSolved : {s : GenSort} → {i : ℕ} → {p : ℤ} → Gen s i p → Prop
  | _, _, _, .geo _ _ => True
  | _, _, _, .drift _ => True
  | _, _, _, .time _ => True
  | _, _, _, .add a b => Gen.NoSolved a ∧ Gen.NoSolved b
  | _, _, _, .mul a b => Gen.NoSolved a ∧ Gen.NoSolved b
  | _, _, _, .dOld _ a => Gen.NoSolved a
  | _, _, _, .dPhase a => Gen.NoSolved a
  | _, _, _, .dSlowFam _ a => Gen.NoSolved a
  | _, _, _, .dSlowCell _ a => Gen.NoSolved a
  | _, _, _, .dInternal a => Gen.NoSolved a
  | _, _, _, .restrict a => Gen.NoSolved a
  | _, _, _, .cellInv F _ ι => (∀ k, Gen.NoSolved (F k)) ∧ Gen.NoSolved ι
  | _, _, _, .transPrim a => Gen.NoSolved a
  | _, _, _, .solved .. => False
  | _, _, _, .mean a => Gen.NoSolved a
  | _, _, _, .famCell a => Gen.NoSolved a
  | _, _, _, .evalChild _ a => Gen.NoSolved a

variable (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞))

theorem solvedFree_of_noSolved {s : GenSort} {i : ℕ} {p : ℤ} (e : Gen s i p) :
    Gen.NoSolved e → Gen.SolvedFree leaf e := by
  induction e with
  | geo => intro; trivial
  | drift => intro; trivial
  | time => intro; trivial
  | add a b iha ihb => exact fun h => Or.inr ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb => exact fun h => Or.inr ⟨iha h.1, ihb h.2⟩
  | dOld j a iha => exact fun h => Or.inr (iha h)
  | dPhase a iha => exact fun h => Or.inr (iha h)
  | dSlowFam j a iha => exact fun h => Or.inr (iha h)
  | dSlowCell j a iha => exact fun h => Or.inr (iha h)
  | dInternal a iha => exact fun h => Or.inr (iha h)
  | restrict a iha => exact fun h => Or.inr (iha h)
  | cellInv F t₀ ι ihF ihι => exact fun h => Or.inr ⟨fun k => ihF k (h.1 k), ihι h.2⟩
  | transPrim a iha => exact fun h => Or.inr (iha h)
  | solved => exact fun h => h.elim
  | mean a iha => exact fun h => Or.inr (iha h)
  | famCell a iha => exact fun h => Or.inr (iha h)
  | evalChild k a iha => exact fun h => Or.inr (iha h)

theorem noSolved_kExpr (i : ℕ) (pc k : ℤ) (a b : Fin 2) : Gen.NoSolved (kExpr i pc k a b) := by
  simp [kExpr, Gen.NoSolved]

theorem noSolved_tExpr (i : ℕ) (pc k : ℤ) : ∀ I A, Gen.NoSolved (tExpr i pc k I A)
  | [], [] => trivial
  | [], _ :: _ => trivial
  | _ :: I, [] => ⟨⟨⟨noSolved_kExpr _ _ _ _ _, noSolved_tExpr i pc k I []⟩,
      ⟨noSolved_kExpr _ _ _ _ _, noSolved_tExpr i pc k I []⟩⟩, trivial⟩
  | _ :: I, _ :: A₀ => ⟨⟨⟨noSolved_kExpr _ _ _ _ _, noSolved_tExpr i pc k I _⟩,
      ⟨noSolved_kExpr _ _ _ _ _, noSolved_tExpr i pc k I _⟩⟩,
      ⟨noSolved_kExpr _ _ _ _ _, noSolved_tExpr i pc k I A₀⟩⟩

theorem solvedFree_genSumList {s : GenSort} {i : ℕ} {p : ℤ} (l : List (Gen s i p))
    (h : ∀ e ∈ l, Gen.SolvedFree leaf e) : Gen.SolvedFree leaf (genSumList l) := by
  induction l with
  | nil => trivial
  | cons e es ih =>
    exact Or.inr ⟨h e List.mem_cons_self, ih fun x hx => h x (List.mem_cons_of_mem e hx)⟩

theorem solvedFree_mul {s : GenSort} {i : ℕ} {p : ℤ} {a b : Gen s i p}
    (ha : Gen.SolvedFree leaf a) (hb : Gen.SolvedFree leaf b) :
    Gen.SolvedFree leaf (Gen.mul a b) := Or.inr ⟨ha, hb⟩

/-- **The explicit transfer is free of uncertified solved nodes** if its finer expressions are. -/
theorem solvedFree_transferExpr (i : ℕ) (pc : ℤ) (C : ℝ) (S : Finset ℤ) (Dγ d' : ℕ)
    (β : DerivativeWord2 (d' - 1)) (κ : Fin 2)
    (c : (k : ℤ) → (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → Gen .fam (i + 1) k)
    (hc : ∀ k d I i₀, Gen.SolvedFree leaf (c k d I i₀)) :
    Gen.SolvedFree leaf (transferExpr i pc C S Dγ d' β κ c) := by
  refine solvedFree_mul leaf trivial (solvedFree_genSumList leaf _ fun e he => ?_)
  obtain ⟨k, -, rfl⟩ := List.mem_map.mp he
  refine solvedFree_genSumList leaf _ fun e he => ?_
  obtain ⟨d, -, rfl⟩ := List.mem_map.mp he
  refine solvedFree_genSumList leaf _ fun e he => ?_
  obtain ⟨I, -, rfl⟩ := List.mem_map.mp he
  refine solvedFree_genSumList leaf _ fun e he => ?_
  obtain ⟨i₀, -, rfl⟩ := List.mem_map.mp he
  exact solvedFree_mul leaf (solvedFree_mul leaf (solvedFree_of_noSolved leaf _
    (noSolved_kExpr _ _ _ _ _)) (Or.inr (hc k d I i₀)))
    (solvedFree_of_noSolved leaf _ (noSolved_tExpr _ _ _ _ _))

/-- **The explicit direct transport is free of uncertified solved nodes** if its old expressions
are certified leaves. -/
theorem solvedFree_directExpr (m : ℕ) (k : ℤ) (C : ℝ) {d : ℕ} (I : DerivativeWord2 (d - 1))
    (κ : Fin 2) (oldE : DerivativeWord2 (d - 1) → Fin 2 → Gen .ctx m k)
    (hold : ∀ J c, Gen.SolvedFree leaf (oldE J c)) :
    Gen.SolvedFree leaf (directExpr m k C I κ oldE) := by
  refine solvedFree_mul leaf trivial (solvedFree_genSumList leaf _ fun e he => ?_)
  obtain ⟨σ, -, rfl⟩ := List.mem_map.mp he
  exact Or.inr (Or.inr (hold _ _))

theorem solvedFree_wrapE (n : ℕ) {i : ℕ} {p : ℤ} (e : Gen .ctx i p)
    (h : (leaf (wrapE n e)).isSome) : Gen.SolvedFree leaf (wrapE n e) := by
  unfold wrapE at h ⊢
  exact Or.inl h

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
  {G : GenStage D hr Dm b j₀}

/-- A wrapped old expression is a certified leaf of the old-coefficient leaf map. -/
theorem solvedFree_oldWrap (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) :
    Gen.SolvedFree (oldLeaf hcert) (oldWrap hcert x) := by
  have h : (oldLeaf hcert (oldWrap hcert x)).isSome := by rw [oldLeaf_oldWrap]; rfl
  exact solvedFree_wrapE _ _ _ h

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the constants and the threshold of the ledger.**
* `LedgerConsts`: the real constants of the ledger over finite, decaying carrier constants, at a
  reserve step `Δ` and an outer rate `a ∈ (3π b, 6π b)`; they exist for every `Δ > 0`
  (`exists_ledgerConsts`) and depend on the carrier constants, `b`, `D_m`, `L_*` and `Δ` only.
* `fluxMax`, `covKMax`: the largest lift constants over the finite menu (path lengths up to `r_H`,
  cell degrees up to `n_H`, covariance degrees up to `p`).
* `ledgerThr`: the threshold of the witness constant `C_w`. The requirements of the four path
  sources are of the form `ledgerA · q · u · f · dp ≤ C_w · e` with `q ≤ c_r^{-D_m}`,
  `u ≤ C^{n_H+2p} e`, `f ≤ (covKMax+1)(fluxMax+1)`, `dp ≤ (D_m+1)^{r_H}` (`ledgerThr_ge`).
* the gains of the letters in abstract real form: `mean_gain_le` (a mean letter of cell degree
  `n ≥ 3` gains `(d_*/ρ)^{n-2} ≤ C^{n_H} E^δ`) and `cov_gain_le` (a covariance letter gains
  `(‖𝖧‖/ρ²)^{a+a'} ≤ C^{2p} E^δ`), each against the normalization `E^{-η₀}` and the tag
  `E^{δ-η₀}`; `fresh_Q_le` (the fresh length `c_r ρ` costs `c_r^{-D_m}`); `slow_le` (a slow
  derivative on the scale `ρ ≤ E` costs `C_slow/Δ`). -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- **The real constants of the ledger** over the carrier constants `κc`. -/
structure LedgerConsts (b : ℝ) (Dm Lstar : ℕ) (κc : MajConsts) (a Δ K W Cold Wr : ℝ)
    (S Kg Kd : ℝ≥0) : Prop where
  /-- The outer rate exceeds the rate of the ledger weight. -/
  ha3 : 3 * Real.pi * b < a
  /-- The reserve step is positive. -/
  hΔ : 0 < Δ
  hK0 : 0 ≤ K
  hW0 : 0 ≤ W
  hC0 : 0 ≤ Cold
  hWr0 : 0 ≤ Wr
  /-- The entries of the inverse chart transition. -/
  hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K
  /-- The child profile. -/
  hW : wsum a 0 κc.child ≤ ENNReal.ofReal W
  /-- The Cauchy constant of the old-label derivative. -/
  hCold : κc.Cold ≤ ENNReal.ofReal Cold
  /-- The ledger weight of the pointwise decay. -/
  hWr : wsum (3 * Real.pi * b) Lstar (expProfile 1 a) ≤ ENNReal.ofReal Wr
  /-- The geometric letters on the fast weights up to `L_*`. -/
  hKg : ∀ L, L ≤ Lstar → geoW κc (3 * Real.pi * b) L ≤ Kg
  /-- The drift letters on the fast weights up to `L_*`. -/
  hKd : ∀ (k : Fin 2) (L : ℕ), L ≤ Lstar → wsum (3 * Real.pi * b) L (κc.drift k) ≤ Kd
  /-- The cost of a slow derivative on the unit scale. -/
  hS : κc.Cslow / ENNReal.ofReal Δ ≤ S

/-- **The constants of the ledger exist** for finite, decaying carrier constants. -/
theorem exists_ledgerConsts {bw : ℝ} (hb : 0 < bw) {κ : MajConsts} (hκ : MajOK bw κ)
    (Dm Lstar : ℕ) {Δ : ℝ} (hΔ : 0 < Δ) :
    ∃ (a K W Cold Wr : ℝ) (S Kg Kd : ℝ≥0), LedgerConsts bw Dm Lstar κ a Δ K W Cold Wr S Kg Kd := by
  have hπb : 0 < Real.pi * bw := mul_pos Real.pi_pos hb
  have ha3 : 3 * Real.pi * bw < 9 / 2 * Real.pi * bw := by nlinarith
  have ha6 : 9 / 2 * Real.pi * bw < 6 * Real.pi * bw := by nlinarith
  have h36 : 3 * Real.pi * bw < 6 * Real.pi * bw := by nlinarith
  obtain ⟨K, W, Cold, hK0, hW0, hC0, hK, hW, hCold⟩ := majOK_consts hκ ha6 Dm
  obtain ⟨Wr, hWr0, hWr⟩ := ledgerWeight_le ha3 Lstar
  obtain ⟨C, hg, hd, -, -, hCs⟩ := hκ
  have hXt : wsum (3 * Real.pi * bw) Lstar (expProfile C (6 * Real.pi * bw)) < ⊤ :=
    wsum_expProfile_lt_top h36 Lstar C
  have hSt : κ.Cslow / ENNReal.ofReal Δ ≠ ⊤ :=
    ENNReal.div_ne_top hCs (ENNReal.ofReal_pos.mpr hΔ).ne'
  refine ⟨9 / 2 * Real.pi * bw, K, W, Cold, Wr, (κ.Cslow / ENNReal.ofReal Δ).toNNReal,
    (wsum (3 * Real.pi * bw) Lstar (expProfile C (6 * Real.pi * bw))).toNNReal,
    (wsum (3 * Real.pi * bw) Lstar (expProfile C (6 * Real.pi * bw))).toNNReal,
    ⟨ha3, hΔ, hK0, hW0, hC0, hWr0, hK, hW, hCold, hWr, fun L hL => ?_, fun k L hL => ?_, ?_⟩⟩
  · rw [ENNReal.coe_toNNReal hXt.ne]
    exact iSup₂_le fun fr Lt => (wsum_mono fun h => hg fr Lt h).trans
      (wsum_mono_weight le_rfl hL _)
  · rw [ENNReal.coe_toNNReal hXt.ne]
    exact (wsum_mono fun h => hd k h).trans (wsum_mono_weight le_rfl hL _)
  · rw [ENNReal.coe_toNNReal hSt]

/-- **A slow derivative on the scale `ρ ≤ E`** costs at most `C_slow/Δ`. -/
theorem slow_le {Cs : ℝ≥0∞} {ρ ε Δ : ℝ} (hρ : 0 ≤ ρ) (hρε : ρ ≤ ε) (hε : 0 < ε) :
    ENNReal.ofReal |ρ| * (Cs / ENNReal.ofReal (ε * Δ)) ≤ Cs / ENNReal.ofReal Δ := by
  rw [abs_of_nonneg hρ, ENNReal.ofReal_mul hε.le]
  have hε' : ENNReal.ofReal ε ≠ 0 := (ENNReal.ofReal_pos.mpr hε).ne'
  have h1 : ENNReal.ofReal ρ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal hρε
  calc ENNReal.ofReal ρ * (Cs / (ENNReal.ofReal ε * ENNReal.ofReal Δ))
      ≤ ENNReal.ofReal ε * (Cs / (ENNReal.ofReal ε * ENNReal.ofReal Δ)) := mul_le_mul' h1 le_rfl
    _ = Cs / ENNReal.ofReal Δ := by
        rw [div_eq_mul_inv, div_eq_mul_inv,
          ENNReal.mul_inv (Or.inl hε') (Or.inl ENNReal.ofReal_ne_top), ← mul_assoc, ← mul_assoc,
          mul_comm (ENNReal.ofReal ε) Cs, mul_assoc Cs,
          ENNReal.mul_inv_cancel hε' ENNReal.ofReal_ne_top, mul_one]

/-- **The fresh length `c_r ρ` costs `c_r^{-D_m}`** in the record bound. -/
theorem fresh_Q_le {ε ρ cr : ℝ} (hε : 0 < ε) (hρ : 0 < ρ) (hρε : ρ ≤ ε) (hcr : 0 < cr)
    (hcr1 : cr ≤ 1) {k Dm : ℕ} (hk : k ≤ Dm) (i' : ℕ) :
    (ε / (cr * ρ)) ^ k * (ρ / ε) ^ (k + i') ≤ cr⁻¹ ^ Dm := by
  have h1 : (1 : ℝ) ≤ cr⁻¹ := (one_le_inv₀ hcr).mpr hcr1
  have h2 : ρ / ε ≤ 1 := (div_le_one hε).mpr hρε
  have h3 : 0 ≤ ρ / ε := (div_pos hρ hε).le
  have e : (ε / (cr * ρ)) ^ k * (ρ / ε) ^ k = cr⁻¹ ^ k := by
    rw [← mul_pow]
    congr 1
    field_simp
  calc (ε / (cr * ρ)) ^ k * (ρ / ε) ^ (k + i')
      = cr⁻¹ ^ k * (ρ / ε) ^ i' := by rw [pow_add, ← mul_assoc, e]
    _ ≤ cr⁻¹ ^ k * 1 := mul_le_mul_of_nonneg_left (pow_le_one₀ h3 h2) (by positivity)
    _ = cr⁻¹ ^ k := mul_one _
    _ ≤ cr⁻¹ ^ Dm := pow_le_pow_right₀ h1 hk

theorem rpow_neg_mul_rpow {E : ℝ} (hE0 : 0 < E) (δ η₀ : ℝ) :
    E ^ (-η₀) * E ^ δ = E ^ (δ - η₀) := by
  rw [← Real.rpow_add hE0]
  congr 1
  ring

/-- `(d_*/ρ)^{n-2} ≤ C^{n_H}` for `d_*/ρ ≤ C E^{3δ}`. -/
theorem pow_ratio_le_const {x Cu E δ : ℝ} (hx0 : 0 ≤ x) (hCu : 1 ≤ Cu) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hδ : 0 < δ) (hx : x ≤ Cu * E ^ (3 * δ)) {n nH : ℕ} (hnH : n ≤ nH) :
    x ^ (n - 2) ≤ Cu ^ nH := by
  have hy1 : E ^ (3 * δ) ≤ 1 := Real.rpow_le_one hE0.le hE1 (by positivity)
  have hxC : x ≤ Cu := hx.trans (by
    calc Cu * E ^ (3 * δ) ≤ Cu * 1 := mul_le_mul_of_nonneg_left hy1 (by linarith)
      _ = Cu := mul_one _)
  exact (pow_le_pow_left₀ hx0 hxC _).trans (pow_le_pow_right₀ hCu (by omega))

/-- `(d_*/ρ)^{n-2} ≤ C^{n_H} E^δ` for `n ≥ 3` and `d_*/ρ ≤ C E^{3δ}`. -/
theorem pow_ratio_le {x Cu E δ : ℝ} (hx0 : 0 ≤ x) (hCu : 1 ≤ Cu) (hE0 : 0 < E) (hE1 : E ≤ 1)
    (hδ : 0 < δ) (hx : x ≤ Cu * E ^ (3 * δ)) {n nH : ℕ} (hn : 3 ≤ n) (hnH : n ≤ nH) :
    x ^ (n - 2) ≤ Cu ^ nH * E ^ δ := by
  have hy0 : 0 ≤ E ^ (3 * δ) := Real.rpow_nonneg hE0.le _
  have hy1 : E ^ (3 * δ) ≤ 1 := Real.rpow_le_one hE0.le hE1 (by positivity)
  have hyδ : E ^ (3 * δ) ≤ E ^ δ := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (by linarith)
  have hCu0 : 0 ≤ Cu := by linarith
  calc x ^ (n - 2) ≤ (Cu * E ^ (3 * δ)) ^ (n - 2) := pow_le_pow_left₀ hx0 hx _
    _ = Cu ^ (n - 2) * (E ^ (3 * δ)) ^ (n - 2) := mul_pow _ _ _
    _ ≤ Cu ^ nH * E ^ δ :=
        mul_le_mul (pow_le_pow_right₀ hCu (by omega))
          ((pow_le_of_le_one hy0 hy1 (by omega)).trans hyδ) (pow_nonneg hy0 _)
          (pow_nonneg hCu0 _)

/-- `(C E^δ)^k ≤ C^{k_H} E^δ` for `1 ≤ k ≤ k_H`. -/
theorem pow_cov_le {Cu E δ : ℝ} (hCu : 1 ≤ Cu) (hE0 : 0 < E) (hE1 : E ≤ 1) (hδ : 0 < δ)
    {k kH : ℕ} (hk : 1 ≤ k) (hkH : k ≤ kH) : (Cu * E ^ δ) ^ k ≤ Cu ^ kH * E ^ δ := by
  have hy0 : 0 ≤ E ^ δ := Real.rpow_nonneg hE0.le _
  have hy1 : E ^ δ ≤ 1 := Real.rpow_le_one hE0.le hE1 hδ.le
  have hCu0 : 0 ≤ Cu := by linarith
  calc (Cu * E ^ δ) ^ k = Cu ^ k * (E ^ δ) ^ k := mul_pow _ _ _
    _ ≤ Cu ^ kH * E ^ δ :=
        mul_le_mul (pow_le_pow_right₀ hCu hkH) (pow_le_of_le_one hy0 hy1 (by omega))
          (pow_nonneg hy0 _) (pow_nonneg hCu0 _)

/-- **The gain of a mean letter** of cell degree `n ≥ 3` against its normalization. -/
theorem mean_gain_le {x Cu E δ : ℝ} (η₀ : ℝ) (hx0 : 0 ≤ x) (hCu : 1 ≤ Cu) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hδ : 0 < δ) (hx : x ≤ Cu * E ^ (3 * δ)) {n nH : ℕ} (p : ℕ) (hn : 3 ≤ n)
    (hnH : n ≤ nH) : |E ^ (-η₀)| * x ^ (n - 2) ≤ Cu ^ (nH + 2 * p) * E ^ (δ - η₀) := by
  have hl0 : 0 ≤ E ^ (-η₀) := Real.rpow_nonneg hE0.le _
  have hCu0 : 0 ≤ Cu := by linarith
  rw [abs_of_nonneg hl0]
  calc E ^ (-η₀) * x ^ (n - 2) ≤ E ^ (-η₀) * (Cu ^ nH * E ^ δ) :=
        mul_le_mul_of_nonneg_left (pow_ratio_le hx0 hCu hE0 hE1 hδ hx hn hnH) hl0
    _ = Cu ^ nH * E ^ (δ - η₀) := by rw [← rpow_neg_mul_rpow hE0]; ring
    _ ≤ Cu ^ (nH + 2 * p) * E ^ (δ - η₀) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hCu (by omega)) (Real.rpow_nonneg hE0.le _)

/-- **The gain of a covariance letter** with `a + a' ≥ 1` against its normalization. -/
theorem cov_gain_le {x Cu E δ : ℝ} (η₀ : ℝ) (hx0 : 0 ≤ x) (hCu : 1 ≤ Cu) (hE0 : 0 < E)
    (hE1 : E ≤ 1) (hδ : 0 < δ) (hx : x ≤ Cu * E ^ (3 * δ)) {n nH a a' p : ℕ} (hnH : n ≤ nH)
    (ha : a ≤ p) (ha' : a' ≤ p) (haa : 1 ≤ a + a') :
    |E ^ (-η₀)| * x ^ (n - 2) * (Cu * E ^ δ) ^ (a + a') ≤ Cu ^ (nH + 2 * p) * E ^ (δ - η₀) := by
  have hl0 : 0 ≤ E ^ (-η₀) := Real.rpow_nonneg hE0.le _
  have hCu0 : 0 ≤ Cu := by linarith
  have hy0 : 0 ≤ E ^ δ := Real.rpow_nonneg hE0.le _
  rw [abs_of_nonneg hl0]
  calc E ^ (-η₀) * x ^ (n - 2) * (Cu * E ^ δ) ^ (a + a')
      ≤ E ^ (-η₀) * Cu ^ nH * (Cu ^ (2 * p) * E ^ δ) :=
        mul_le_mul (mul_le_mul_of_nonneg_left (pow_ratio_le_const hx0 hCu hE0 hE1 hδ hx hnH) hl0)
          (pow_cov_le hCu hE0 hE1 hδ haa (by omega)) (pow_nonneg (mul_nonneg hCu0 hy0) _)
          (mul_nonneg hl0 (pow_nonneg hCu0 _))
    _ = Cu ^ (nH + 2 * p) * E ^ (δ - η₀) := by rw [← rpow_neg_mul_rpow hE0, pow_add]; ring

/-! ### The threshold -/

/-- The common prefactor of the requirements on the witness constant. -/
def ledgerA (Dm : ℕ) (K W Cold Wr Δ : ℝ) : ℝ :=
  4 ^ Dm * ((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W)

theorem ledgerA_nonneg {Dm : ℕ} {K W Cold Wr Δ : ℝ} (hK0 : 0 ≤ K) (hW0 : 0 ≤ W)
    (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr) (hΔ : 0 < Δ) : 0 ≤ ledgerA Dm K W Cold Wr Δ := by
  have := tConst_nonneg hK0 hC0 hΔ
  unfold ledgerA
  positivity

/-- The largest slow-flux constant of the lifts over the menu. -/
def fluxMax (κ : MajConsts) (S Kg Kd : ℝ≥0) (Dm rH nH : ℕ) : ℝ≥0 :=
  ∑ h ∈ Finset.range (rH + 1), ∑ n ∈ Finset.range (nH + 1),
    UEnv.fluxXc (constCtx κ S Kg Kd) Dm (liftB (constCtx κ S Kg Kd) Dm) h n

theorem fluxXc_le_fluxMax {X : GCtx} {κ : MajConsts} {S Kg Kd : ℝ≥0}
    (hX : SameConsts X (constCtx κ S Kg Kd)) (Dm : ℕ) {rH nH h n : ℕ} (hh : h ≤ rH)
    (hn : n ≤ nH) : UEnv.fluxXc X Dm (liftB X Dm) h n ≤ fluxMax κ S Kg Kd Dm rH nH := by
  rw [fluxXc_congr hX]
  unfold fluxMax
  exact (Finset.single_le_sum (f := fun n => UEnv.fluxXc (constCtx κ S Kg Kd) Dm
      (liftB (constCtx κ S Kg Kd) Dm) h n) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega))).trans
    (Finset.single_le_sum (f := fun h => ∑ n ∈ Finset.range (nH + 1),
      UEnv.fluxXc (constCtx κ S Kg Kd) Dm (liftB (constCtx κ S Kg Kd) Dm) h n)
      (fun _ _ => zero_le) (Finset.mem_range.mpr (by omega)))

/-- The largest constant of the covariance letters over the menu. -/
def covKMax (S Kg : ℝ≥0) (nH p : ℕ) : ℝ≥0 :=
  ∑ n ∈ Finset.range (nH + 1), ∑ a ∈ Finset.range (p + 1), ∑ a' ∈ Finset.range (p + 1),
    covLetK n a a' S Kg

theorem covLetK_le_covKMax (S Kg : ℝ≥0) {nH p n a a' : ℕ} (hn : n ≤ nH) (ha : a ≤ p)
    (ha' : a' ≤ p) : covLetK n a a' S Kg ≤ covKMax S Kg nH p := by
  unfold covKMax
  exact ((Finset.single_le_sum (f := fun a' => covLetK n a a' S Kg) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega))).trans
    (Finset.single_le_sum (f := fun a => ∑ a' ∈ Finset.range (p + 1), covLetK n a a' S Kg)
      (fun _ _ => zero_le) (Finset.mem_range.mpr (by omega)))).trans
    (Finset.single_le_sum (f := fun n => ∑ a ∈ Finset.range (p + 1),
      ∑ a' ∈ Finset.range (p + 1), covLetK n a a' S Kg) (fun _ _ => zero_le)
      (Finset.mem_range.mpr (by omega)))

/-- **The threshold of the witness constant** for the path sources. -/
def ledgerThr (Dm rH nH p : ℕ) (K W Cold Wr Δ cr Cu : ℝ) (FM KM : ℝ≥0) : ℝ :=
  ledgerA Dm K W Cold Wr Δ * cr⁻¹ ^ Dm * Cu ^ (nH + 2 * p) *
    (((KM + 1) * (FM + 1) : ℝ≥0) : ℝ) * ((Dm : ℝ) + 1) ^ rH

/-- **The requirements of the path sources are below the threshold.** -/
theorem ledgerThr_ge {Dm rH nH p : ℕ} {K W Cold Wr Δ cr Cu : ℝ} {FM KM : ℝ≥0} (hK0 : 0 ≤ K)
    (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr) (hΔ : 0 < Δ) (hCu : 1 ≤ Cu)
    {q u f dp e : ℝ} (hq0 : 0 ≤ q) (hu0 : 0 ≤ u) (hf0 : 0 ≤ f) (hdp0 : 0 ≤ dp) (he : 0 ≤ e)
    (hq : q ≤ cr⁻¹ ^ Dm) (hu : u ≤ Cu ^ (nH + 2 * p) * e)
    (hf : f ≤ (((KM + 1) * (FM + 1) : ℝ≥0) : ℝ)) (hdp : dp ≤ ((Dm : ℝ) + 1) ^ rH) :
    ledgerA Dm K W Cold Wr Δ * q * u * f * dp ≤
      ledgerThr Dm rH nH p K W Cold Wr Δ cr Cu FM KM * e := by
  have hA := ledgerA_nonneg (Dm := Dm) hK0 hW0 hC0 hWr0 hΔ
  have hQ0 : 0 ≤ cr⁻¹ ^ Dm := hq0.trans hq
  have hCP : 0 ≤ Cu ^ (nH + 2 * p) := pow_nonneg (by linarith) _
  have hF0 : 0 ≤ (((KM + 1) * (FM + 1) : ℝ≥0) : ℝ) := NNReal.coe_nonneg _
  have hD0 : 0 ≤ ((Dm : ℝ) + 1) ^ rH := by positivity
  calc ledgerA Dm K W Cold Wr Δ * q * u * f * dp
      ≤ ledgerA Dm K W Cold Wr Δ * cr⁻¹ ^ Dm * (Cu ^ (nH + 2 * p) * e) *
          (((KM + 1) * (FM + 1) : ℝ≥0) : ℝ) * ((Dm : ℝ) + 1) ^ rH := by gcongr
    _ = ledgerThr Dm rH nH p K W Cold Wr Δ cr Cu FM KM * e := by unfold ledgerThr; ring

theorem one_le_crInv_pow {cr : ℝ} (hcr : 0 < cr) (hcr1 : cr ≤ 1) (Dm : ℕ) : 1 ≤ cr⁻¹ ^ Dm :=
  one_le_pow₀ ((one_le_inv₀ hcr).mpr hcr1)

theorem coe_le_KF {FM KM x : ℝ≥0} (hx : x ≤ FM + 1) :
    (x : ℝ) ≤ (((KM + 1) * (FM + 1) : ℝ≥0) : ℝ) :=
  NNReal.coe_le_coe.mpr (hx.trans (le_mul_of_one_le_left zero_le (le_add_of_nonneg_left zero_le)))

theorem one_le_KF (FM KM : ℝ≥0) : (1 : ℝ) ≤ (((KM + 1) * (FM + 1) : ℝ≥0) : ℝ) := by
  have h := coe_le_KF (FM := FM) (KM := KM) (x := 1) (le_add_of_nonneg_left zero_le)
  rwa [NNReal.coe_one] at h

/-- The requirement of a direct transport is below the common prefactor. -/
theorem dirConst_le_ledgerA {Dm : ℕ} {K W Cold Wr Δ : ℝ} (hK0 : 0 ≤ K) (hW0 : 0 ≤ W)
    (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr) (hΔ : 0 < Δ) :
    2 ^ Dm * ((Dm : ℝ) + 1) * Wr * K * W * tConst K Cold Δ ^ Dm ≤ ledgerA Dm K W Cold Wr Δ := by
  have ht := tConst_nonneg hK0 hC0 hΔ
  have h24 : (2 : ℝ) ^ Dm ≤ 4 ^ Dm := pow_le_pow_left₀ (by norm_num) (by norm_num) Dm
  unfold ledgerA
  calc 2 ^ Dm * ((Dm : ℝ) + 1) * Wr * K * W * tConst K Cold Δ ^ Dm
      = 2 ^ Dm * (((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W)) := by ring
    _ ≤ 4 ^ Dm * (((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W)) :=
        mul_le_mul_of_nonneg_right h24 (by positivity)
    _ = 4 ^ Dm * ((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W) := by ring

theorem natCast_pow_le_succ_pow (Dm : ℕ) {h rH : ℕ} (hh : h ≤ rH) :
    (Dm : ℝ) ^ h ≤ ((Dm : ℝ) + 1) ^ rH :=
  (pow_le_pow_left₀ (Nat.cast_nonneg _) (by linarith) h).trans
    (pow_le_pow_right₀ (by have : (0 : ℝ) ≤ Dm := Nat.cast_nonneg _; linarith) hh)

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev MeasureTheory
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the direct transport (`copyDir` sources).** The finer outputs of a direct copy of
the old edge `γ` are the explicit direct-transport expressions of the wrapped certified old
expressions (`cfinCopyDir`, cast from the level of `G` to `G'.level + 1`). They are scheduled,
seed-provenanced, denote the finer outputs on the admissible chains and output windows of their
slots (`hcfin_copyDir`), and are free of uncertified solved nodes (`solvedFree_cfinCopyDir`). -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-- Transport of an expression along an equality of levels. -/
def castLevel {s : GenSort} {i i' : ℕ} {p : ℤ} (h : i = i') (e : Gen s i p) : Gen s i' p := h ▸ e

section Cast

variable {s : GenSort} {i i' : ℕ} {p : ℤ}

theorem isScheduled_castLevel {D : OCData} (h : i = i') {e : Gen s i p} (he : Gen.IsScheduled D e) :
    Gen.IsScheduled D (castLevel h e) := by
  subst h; exact he

theorem fromSeed_castLevel {𝒮 : SeedExports} (h : i = i') {e : Gen s i p}
    (he : Gen.FromSeed 𝒮 e) : Gen.FromSeed 𝒮 (castLevel h e) := by
  subst h; exact he

theorem denotes_castLevel {D : OCData} {b : ℝ} {j₀ : ℕ} (h : i = i') {e : Gen s i p} {f : s.Sem}
    (he : Gen.Denotes D b j₀ e f) : Gen.Denotes D b j₀ (castLevel h e) f := by
  subst h; exact he

theorem solvedFree_castLevel
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) (h : i = i')
    {e : Gen s i p} (he : Gen.SolvedFree leaf e) : Gen.SolvedFree leaf (castLevel h e) := by
  subst h; exact he

theorem genNorm_castLevel (D : OCData) (κc : MajConsts) (Δ a₀ : ℝ)
    (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)) (h : i = i')
    (e : Gen s i p) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ leaf (castLevel h e) a mres L t = genNorm D κc Δ a₀ leaf e a mres L t := by
  subst h; rfl

end Cast

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
  {G : GenStage D hr Dm b j₀}

open scoped Classical in
/-- The flux of an old coefficient is its certified function on the admissible recentered
contexts and zero off them. -/
theorem oldFun_flux (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G)
    (ctx : StageCtx D b j₀ G.level x.p) (t : ℝ) (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level x.p.1)
    (X z : Vec 2) :
    G.fam.flux x.p ctx x.v x.u x.γ x.d x.α t X z x.c =
      if IsAdmissibleChain D b j₀ G.level x.p.1 (ctx.1.recenter D (D.eps (G.level - 1) • X))
      then oldFun hcert x t (ctx.1.recenter D (D.eps (G.level - 1) • X)) z else 0 := by
  have := ((Classical.choose_spec (Classical.choose_spec
    ((Classical.choose_spec (hcert x.v x.u x.γ)).2.2 x.d x.α x.c))).1 x.p).2.2 ctx t ht X z
  exact this

open scoped Classical in
/-- **The finer outputs of a direct copy of the old edge `γ`.** -/
def cfinCopyDir (hcert : G.OldCert 𝒮o μo Lo Co) {i : ℕ} (hlev : G.level = i + 1)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (_p : OddSlot) (k : ℤ) (d₁ : ℕ)
    (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) : Gen .fam (i + 1) k :=
  if hk : Odd k then
    castLevel hlev (directExpr G.level k (directConst D G.level (Finset.Icc 3 Dm) d₁) I₁ i₀
      (fun J c' => oldWrap hcert ⟨v, u, γ, d₁, J, c', ⟨k, hk⟩⟩))
  else Gen.time (.const 0)

theorem solvedFree_cfinCopyDir (hcert : G.OldCert 𝒮o μo Lo Co) {i : ℕ}
    (hlev : G.level = i + 1) {v u : CompIn G.comps} (γ : G.fam.Γ v u) (p : OddSlot) (k : ℤ)
    (d₁ : ℕ) (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) :
    Gen.SolvedFree (oldLeaf hcert) (cfinCopyDir hcert hlev γ p k d₁ I₁ i₀) := by
  unfold cfinCopyDir
  split_ifs with hk
  · exact solvedFree_castLevel _ hlev (solvedFree_directExpr _ _ _ _ _ _ _ fun J c' =>
      solvedFree_oldWrap hcert _)
  · trivial

open scoped Classical in
/-- **The finer outputs of a direct copy are denoted by the explicit expressions.** -/
theorem hcfin_copyDir (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hcert : G.OldCert G.exports μo Lo Co) {i : ℕ} (hlev : G.level = i + 1)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) (ρ s₀ : ℝ) (t' : List WordLetter)
    (Cc : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin ((SuccSource.copyDir t' v u γ).pathLen + 1))
      (fun _ => ℝ)) (p : OddSlot) (k : ℤ) (hk : Odd k) (d₁ : ℕ)
    (hd₁ : 1 ≤ d₁) (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) :
    Gen.IsScheduled D (cfinCopyDir hcert hlev γ p k d₁ I₁ i₀) ∧
      Gen.FromSeed G.exports (cfinCopyDir hcert hlev γ p k d₁ I₁ i₀) ∧
      ∃ fc : GenSort.Sem .fam, Gen.Denotes D b j₀ (cfinCopyDir hcert hlev γ p k d₁ I₁ i₀) fc ∧
        ∀ A, IsAdmissibleChain D b j₀ (i + 1) k A →
          ∀ t ∈ ocPulseWindow D.α D.q D.Λ (i + 1) k,
            fc t A = fluxCoeff ((SuccSource.copyDir t' v u γ).fluxOp ρ s₀ Cc k t A) d₁ I₁ 0 i₀ := by
  have hcont := oldFluxContinuous_of_cert hΛ hζ hb G hcert
  have hrep := famURep_directExpr hζ G ⟨k, hk⟩ γ (Finset.Icc 3 Dm)
    (fun d' hd' => by simp only [Finset.mem_Icc] at hd'; omega) hd₁ I₁ i₀
    (fun J c' => oldWrap hcert ⟨v, u, γ, d₁, J, c', ⟨k, hk⟩⟩)
    (fun J c' => by
      obtain ⟨hs, hf, hden⟩ := oldExpr_spec hcert ⟨v, u, γ, d₁, J, c', ⟨k, hk⟩⟩
      refine ⟨.add (.mul (.timeConst 1) hs) (.mul (.timeConst 0) (.timeConst _)),
        .add (.mul (.time _) hf) (.mul (.time _) (.time _)), _,
        .add (.mul (.time _) hden) (.mul (.time _) (.time _)), fun cc t ht X z => ?_⟩
      rw [oldFun_flux hcert ⟨v, u, γ, d₁, J, c', ⟨k, hk⟩⟩ cc t ht X z]
      split_ifs
      · show _ = TimeLetter.eval D (.const 1) t * _ + TimeLetter.eval D (.const 0) t * _
        simp [TimeLetter.eval]
      · rfl)
    (fun _ cc t ht σ => integrableOn_unitCube_of_continuous
      (hcont ⟨k, hk⟩ cc v u γ d₁ (I₁ ∘ σ) t ht))
  obtain ⟨hs, hf, fc, hden, hv⟩ := hrep
  simp only [cfinCopyDir, hk, ↓reduceDIte]
  refine ⟨isScheduled_castLevel hlev hs, fromSeed_castLevel hlev hf, fc,
    denotes_castLevel hlev hden, fun A hA t ht => ?_⟩
  have hA' : IsAdmissibleChain D b j₀ G.level k A := by rw [hlev]; exact hA
  have ht' : t ∈ ocPulseWindow D.α D.q D.Λ G.level k := by rw [hlev]; exact ht
  have hval : fluxCoeff (directFlux G ⟨k, hk⟩ ⟨A, hA'⟩ γ (Finset.Icc 3 Dm) t) d₁ I₁ 0 i₀ = fc t A :=
    hv (⟨A, hA'⟩, t) ht'
  rw [← hval]
  simp only [SuccSource.fluxOp, hA', hk, and_self, ↓reduceDIte]

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the structural norm of the transferred direct copies.** The old-coefficient leaf
map has no leaf off the context sort and off the level of `G` (`oldLeaf_eq_none_of_ne_ctx`,
`oldLeaf_eq_none_of_level_ne`); a wrapped old coefficient has the weighted sum of its certified
profile (`genNorm_oldWrap_eq`). Hence, at every time:
* the finer output of a direct copy costs `|c_{d₁}| Σ_σ θ_old(d₁, I₁∘σ, i₀)` at a reserve below
  that of the old target component and an inner rate `a₀ ≤ 3π b` (`genNorm_cfinCopyDir_le`);
* the transferred coefficient costs `|C_d|` times the sum over the orders, words and components of
  `K · W_child · (that cost) · T_{d₁-1, d-1}`, uniformly in the slot and the time: the finer slots
  enter as a sub-convex combination of the cutoff weights (`genNorm_transferExprAt_copyDir_le`). -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

theorem finerSlots_odd (D : OCData) (i : ℕ) (pc : ℤ) : ∀ k ∈ finerSlots D i pc, Odd k := by
  classical
  intro k hk
  unfold finerSlots at hk
  split_ifs at hk with h
  · exact (h.mem_toFinset.mp hk).1
  · simp at hk

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {𝒮o : SeedExports} {μo : Comp → ℝ} {Lo : ℕ} {Co : ℝ}
  {G : GenStage D hr Dm b j₀}

theorem oldLeaf_eq_none_of_ne_ctx (hcert : G.OldCert 𝒮o μo Lo Co) {s : GenSort} {i : ℕ}
    {p : ℤ} (e : Gen s i p) (hs : s ≠ .ctx) : oldLeaf hcert e = none := by
  classical
  simp only [oldLeaf]
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    exact absurd (congrArg Sigma.fst hx).symm hs
  · rfl

theorem oldLeaf_eq_none_of_level_ne (hcert : G.OldCert 𝒮o μo Lo Co) {s : GenSort} {i : ℕ}
    {p : ℤ} (e : Gen s i p) (hi : i ≠ G.level) : oldLeaf hcert e = none := by
  classical
  simp only [oldLeaf]
  split_ifs with h
  · obtain ⟨x, hx⟩ := h
    exact absurd (congrArg (fun σ : Σ (s : GenSort) (i : ℕ) (p : ℤ), Gen s i p => σ.2.1) hx).symm hi
  · rfl

variable (κc : MajConsts) (Δ a₀ : ℝ)

/-- The structural norm of a wrapped old coefficient is the weighted sum of its certified
profile. -/
theorem genNorm_oldWrap_eq (hcert : G.OldCert 𝒮o μo Lo Co) (x : OldIdx G) (a mres : ℝ)
    (L : ℕ) (t : ℝ) :
    genNorm D κc Δ a₀ (oldLeaf hcert) (oldWrap hcert x) a mres L t =
      wsum a L (fun h => ctxModeSup D b j₀ G.level x.p.1 (oldExt hcert x) mres h) := by
  have hl := oldLeaf_oldWrap hcert x
  unfold oldWrap wrapE at hl ⊢
  simp only [genNorm, hl, Option.elim]

/-- **The finer output of a direct copy** at a fixed time. -/
theorem genNorm_cfinCopyDir_le (hcert : G.OldCert 𝒮o μo Lo Co) (hb : 0 ≤ b)
    (hε : ∀ k, 0 ≤ D.eps k) {i : ℕ} (hlev : G.level = i + 1) {v u : CompIn G.comps}
    (γ : G.fam.Γ v u) (p : OddSlot) (k : ℤ) (d₁ : ℕ) (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2)
    {mres : ℝ} (hmres : mres ≤ μo v.1) (ha₀ : a₀ ≤ 3 * Real.pi * b) (t : ℝ) :
    genNorm D κc Δ a₀ (oldLeaf hcert) (cfinCopyDir hcert hlev γ p k d₁ I₁ i₀) a₀ mres 0 t ≤
      ENNReal.ofReal |directConst D G.level (Finset.Icc 3 Dm) d₁| *
        ∑ σ : Equiv.Perm (Fin (d₁ - 1)),
          ENNReal.ofReal (oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀) := by
  unfold cfinCopyDir
  split_ifs with hk
  · rw [genNorm_castLevel]
    refine (genNorm_directExpr_le (D := D) κc Δ a₀ (oldLeaf hcert)
      (fun s i p e hs => oldLeaf_eq_none_of_ne_ctx hcert e hs) G.level k _ I₁ i₀ _ a₀ mres 0
      t).trans ?_
    refine mul_le_mul_right (Finset.sum_le_sum fun σ _ => ?_) _
    exact (genNorm_oldWrap_eq κc Δ a₀ hcert _ a₀ mres 0 t).trans_le
      (wsum_oldProfile_le hcert hb hε ⟨v, u, γ, d₁, I₁ ∘ σ, i₀, ⟨k, hk⟩⟩ hmres ha₀
        (Nat.zero_le _))
  · exact (genNorm_const_le (D := D) κc Δ a₀ (oldLeaf hcert) 0
      (oldLeaf_eq_none_of_ne_ctx hcert _ (by intro h; cases h)) a₀ mres 0 t).trans (by simp)

/-- **The transferred direct copy** at a fixed time, uniformly in the slot. -/
theorem genNorm_transferExprAt_copyDir_le (hcert : G.OldCert 𝒮o μo Lo Co) (hb : 0 ≤ b)
    (hε : ∀ k, 0 ≤ D.eps k) {i : ℕ} (hlev : G.level = i + 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (i + 1)) {v u : CompIn G.comps} (γ : G.fam.Γ v u) (lam : ℝ)
    (Dγ d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) (p : OddSlot) (a mres : ℝ) (L : ℕ)
    (t : ℝ) (hmres : mres ≤ μo v.1) (ha₀ : a₀ ≤ 3 * Real.pi * b) :
    genNorm D κc Δ a₀ (oldLeaf hcert)
        (transferExprAt D i lam Dγ d I c (cfinCopyDir hcert hlev γ) p) a mres L t ≤
      ENNReal.ofReal |(D.kap i * D.eps i ^ (d - 2))⁻¹ * lam| *
        ∑ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ, ∑ I₁ : DerivativeWord2 (d₁ - 1), ∑ i₀ : Fin 2,
          kBound κc a L * wsum a L κc.child *
            (ENNReal.ofReal |directConst D G.level (Finset.Icc 3 Dm) d₁| *
              ∑ σ : Equiv.Perm (Fin (d₁ - 1)),
                ENNReal.ofReal (oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀)) *
            tBound D κc Δ a i (d₁ - 1) (d - 1) mres L := by
  have hleaf : ∀ (s : GenSort) (p : ℤ) (e : Gen s i p), oldLeaf hcert e = none :=
    fun s p e => oldLeaf_eq_none_of_level_ne hcert e (by omega)
  unfold transferExprAt
  split_ifs with hd
  · refine genNorm_transferExpr_le D κc Δ a₀ (oldLeaf hcert) hleaf hτ _ _
      (finerSlots_odd D i p.1) Dγ d I c _ a mres L t _ fun k _ => ?_
    refine Finset.sum_le_sum fun d₁ _ => Finset.sum_le_sum fun I₁ _ =>
      Finset.sum_le_sum fun i₀ _ => ?_
    exact mul_le_mul_left (mul_le_mul_right
      (genNorm_cfinCopyDir_le κc Δ a₀ hcert hb hε hlev γ p k d₁ I₁ i₀ hmres ha₀ t) _) _
  · exact (genNorm_const_le (D := D) κc Δ a₀ (oldLeaf hcert) 0 (hleaf _ _ _) a mres L t).trans
      (by simp)

end AVRegularity.Providers.CascadeInvariants
end
