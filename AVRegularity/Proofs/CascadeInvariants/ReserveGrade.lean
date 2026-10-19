-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.PathFiner
public import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Definitions.Finite.FiniteLiftBridge
import AVRegularity.EntryWeak.MolecularHilbertToRawSolution
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the ledger of a transferred finer output of path-mean size.** For a new identity
`γ'` of `G'` whose coefficient is the transfer (normalization `λ`, orders up to `D_γ`) of a finer
output `fop`, every coefficient of which is a graded slot family function over the certified old
coefficients with the size of a path mean of cell degree `n`
(`|c_{n,d₁}| (d₁-1)! · FP`), the witnesses `θ(d, α, c) = W_r · pmBound(d)` satisfy the conclusion
of `successor_ledger` (`pathMean_ledger_case`), as soon as
`4^{D_m}(D_m+1)c^{D_m} · W_r K W Q |λ| (d_*/ρ)^{n-2} · FP` is at most the new record size.
`pathSize_le` converts the product of the edge sizes of a path into the product of its record
sizes (each edge once, with the factor `D_m^h`). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts} {𝒮o : SeedExports} {μo : Comp → ℝ}
  {Lo : ℕ} {Co : ℝ}

/-- The product of the step sizes of a path is at most `D_m^h Co^h` times the product of the
record sizes of its identities. -/
theorem prod_edgeTheta_le {G : GenStage D hr Dm b j₀} (hcert : G.OldCert 𝒮o μo Lo Co) {h : ℕ}
    (π : StagePath G h) (hCo : 0 ≤ Co)
    (hℓ : ∀ j : Fin h, 3 ≤ (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).maxOrder →
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.length ≤
        D.eps G.level) :
    ((∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2 : ℝ≥0) : ℝ) ≤
      (Dm : ℝ) ^ h * (Co ^ h *
        ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size) := by
  have h1 : (∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2 : ℝ≥0) ≤
      ∏ j : Fin h, ((Dm : ℝ≥0) * Real.toNNReal
        (Co * (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size)) :=
    Finset.prod_le_prod fun j _ => edgeTheta_le hcert _ _ _ (hℓ j)
  have h2 := NNReal.coe_le_coe.mpr h1
  refine h2.trans (le_of_eq ?_)
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  push_cast
  congr 1
  rw [Finset.prod_congr rfl fun j _ => Real.coe_toNNReal _
      (mul_nonneg hCo (G.fam.identity _ _ (π.step j).2.2).record.size_nonneg),
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

/-- **The size of a path against the product of its record sizes.** -/
theorem pathSize_le {G : GenStage D hr Dm b j₀} (hcert : G.OldCert 𝒮o μo Lo Co) {h : ℕ}
    (π : StagePath G h) (hCo : 0 ≤ Co)
    (hℓ : ∀ j : Fin h, 3 ≤ (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).maxOrder →
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.length ≤
        D.eps G.level)
    {F : ℝ≥0} {A Cw : ℝ} (hA : 0 ≤ A) (hCw : A * ((F : ℝ) * (Dm : ℝ) ^ h) ≤ Cw) :
    A * ((F * ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2 : ℝ≥0) : ℝ)
      ≤ Cw * (Co ^ h *
        ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size) := by
  have hprod := prod_edgeTheta_le hcert π hCo hℓ
  have hS0 : 0 ≤ Co ^ h * ∏ j : Fin h,
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size :=
    mul_nonneg (pow_nonneg hCo _)
      (Finset.prod_nonneg fun j _ => (G.fam.identity _ _ (π.step j).2.2).record.size_nonneg)
  calc A * ((F * ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2 :
          ℝ≥0) : ℝ)
      = A * ((F : ℝ) * ((∏ j : Fin h,
          edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2 : ℝ≥0) : ℝ)) := by
        rw [NNReal.coe_mul]
    _ ≤ A * ((F : ℝ) * ((Dm : ℝ) ^ h * (Co ^ h * ∏ j : Fin h,
          (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hprod (NNReal.coe_nonneg _)) hA
    _ = A * ((F : ℝ) * (Dm : ℝ) ^ h) * (Co ^ h * ∏ j : Fin h,
          (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size) := by ring
    _ ≤ Cw * (Co ^ h * ∏ j : Fin h,
          (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size) :=
        mul_le_mul_of_nonneg_right hCw hS0

open scoped Classical in
/-- **The ledger entries of a transferred finer output of path-mean size**, at the reserve `μn`
and the fast weight `Ln` of the new component: the expressions of every coefficient and the bound
`W_r · pmBound(d)` of their weighted majorant sum. -/
theorem pathMean_ledger_entry (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hcert : G.OldCert 𝒮o μo Lo Co)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), 𝒮o e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮o e → G'.exports e)
    (hlev : G.level = G'.level + 1) (ρ : ℝ) (n Dγ : ℕ) (lam : ℝ) (fop : FamFluxOp)
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D G.level p.1 lam Dγ fop t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    (hDγ : Dγ ≤ Dm) (κc : MajConsts) {a Δ μ₀ K W Cold Wr : ℝ}
    {S Kg Kd FP : ℝ≥0} {r : ℕ → ℕ} (μn : ℝ) (Ln : ℕ)
    (hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → d₁ ≤ Dγ →
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ 𝒮o G.level k (oldCtx hcert κc Δ μ₀ S Kg Kd)
          (fun t A => fluxCoeff (fop k t A) d₁ I₁ 0 i₀) (r d₁)
          (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) * FP)))
    (hr : ∀ d₁ : ℕ, 2 ≤ d₁ → d₁ ≤ Dγ → μn + (r d₁ : ℝ) * Δ ≤ μ₀)
    (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1))
    (ha3 : 3 * Real.pi * b < a) (hΔ : 0 < Δ) (hresΔ : μn + Dm * Δ ≤ 2)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr)
    (hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) Ln (expProfile 1 a) ≤ ENNReal.ofReal Wr) :
    ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ' : ℝ)
        (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
        G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ' ∧ LeavesCertified D b j₀ leaf ∧
        (∀ p, Gen.SolvedFree leaf (e p)) ∧
        ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) * (1 + |(h : ℝ)|) ^ Ln) *
          ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
            genMode D κc Δ' leaf (e p) μn h t
          ≤ ENNReal.ofReal (Wr * if 2 ≤ d then
              pmBound D G'.level G.level ρ n Dγ K W (tConst K Cold Δ) lam FP d else 0) := by
  have hc1 := one_le_tConst hK0 hC0 hΔ
  have hc0 : 0 ≤ tConst K Cold Δ := by linarith
  have ha0 : 0 ≤ a := by have := mul_pos Real.pi_pos hb; linarith
  have hlevne : G'.level ≠ G.level := by omega
  have hfine' : ∀ (d : ℕ) (k : ℤ), Odd k → ∀ d₁ ∈ Finset.Icc (d - 1 + 1) Dγ,
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ 𝒮o (G'.level + 1) k (oldCtx hcert κc Δ μ₀ S Kg Kd)
          (fun t A => fluxCoeff (fop k t A) d₁ I₁ 0 i₀) (r d₁)
          (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) * FP)) := by
    intro d k hk d₁ hd₁ I₁ i₀
    have h1 := Finset.mem_Icc.mp hd₁
    rw [← hlev]
    exact hfine k hk d₁ (by omega) h1.2 I₁ i₀
  intro d α c
  obtain ⟨e, hE, hSF, hnorm⟩ := exists_transferExpr_of_finer hζ hΛ hb hstart G'
    (𝒮 := 𝒮o) hexp γ' d α c lam Dγ fop
    (fun hd p ctx t Y z => by rw [hflux p ctx d α t Y z hd, hlev])
    (X := oldCtx hcert κc Δ μ₀ S Kg Kd) (fun t => Set.mem_univ t)
    (fun s p e => oldLeaf_eq_none_of_level_ne hcert e hlevne) hτ (hfine' d)
    (mres := μn)
    (fun hd d₁ hd₁ => by
      have h1 := Finset.mem_Icc.mp hd₁
      exact hr d₁ (by omega) h1.2)
  refine ⟨e, Δ, oldLeaf hcert, hE, hΔ, leavesCertified_oldLeaf hΛ hζ hb hstart hexpU hcert,
    hSF, ?_⟩
  refine (ledgerSum_le D κc Δ (3 * Real.pi * b) (oldLeaf hcert) (by positivity) e ha0
    (3 * Real.pi * b) Ln μn
    (ENNReal.ofReal (if 2 ≤ d then
      pmBound D G'.level G.level ρ n Dγ K W (tConst K Cold Δ) lam FP d else 0))
    fun p t _ => ?_).trans ?_
  · refine (hnorm p a 0 t).trans ?_
    split_ifs with hd
    · exact pm_genNorm_le D κc hε0 hε1 hΔ G.level ρ n Dγ Dm hDγ lam FP hK0 hW0 hC0 hK hW
        hCold hresΔ d
    · exact zero_le
  · rw [ENNReal.ofReal_mul hWr0]
    exact mul_le_mul_left hWr _

open scoped Classical in
/-- **The ledger of a transferred finer output of path-mean size.** -/
theorem pathMean_ledger_case (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hcert : G.OldCert 𝒮o μo Lo Co)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), 𝒮o e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')
    (hexp : ∀ {i p} (e : Gen .ctx i p), 𝒮o e → G'.exports e)
    (hlev : G.level = G'.level + 1) (ρ : ℝ) (n Dγ : ℕ) (lam : ℝ) (fop : FamFluxOp)
    {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D G.level p.1 lam Dγ fop t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    (hDγ : Dγ ≤ Dm) (hn : 2 ≤ n) (κc : MajConsts) {a Δ μ₀ K W Cold Wr Q : ℝ}
    {S Kg Kd FP : ℝ≥0} {r : ℕ → ℕ}
    (hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → d₁ ≤ Dγ →
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ 𝒮o G.level k (oldCtx hcert κc Δ μ₀ S Kg Kd)
          (fun t A => fluxCoeff (fop k t A) d₁ I₁ 0 i₀) (r d₁)
          (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) * FP)))
    (hr : ∀ d₁ : ℕ, 2 ≤ d₁ → d₁ ≤ Dγ → compReserve kI v'.1 + (r d₁ : ℝ) * Δ ≤ μ₀)
    (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1)) (hκ : 0 < D.kap G'.level) (hρ : 0 < ρ)
    (hDst0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
    (hDst : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      D.kap G'.level * D.cellScaleSq G.level)
    (ha3 : 3 * Real.pi * b < a) (hΔ : 0 < Δ) (hresΔ : compReserve kI v'.1 + Dm * Δ ≤ 2)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr)
    (hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 a) ≤ ENNReal.ofReal Wr)
    (hQ0 : 0 ≤ Q)
    (hQ : ∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder → ∀ i',
      (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
        (ρ / D.eps G'.level) ^ (d - 2 + i') ≤ Q)
    (hCw : 4 ^ Dm * (Dm + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W * Q * |lam| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2) * FP) ≤
        (G'.fam.identity v' u' γ').record.size) :
    ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
      (∀ d α c, 0 ≤ θ d α c) ∧
      (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
        (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
            ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
      ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
        ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
          (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
          G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
          (∀ p, Gen.SolvedFree leaf (e p)) ∧
          ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
              (1 + |(h : ℝ)|) ^ kI.Lstar) *
            ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
              genMode D κc Δ leaf (e p) (compReserve kI v'.1) h t
            ≤ ENNReal.ofReal (θ d α c) := by
  have hcs := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκb G.level
  have hc1 := one_le_tConst hK0 hC0 hΔ
  have hc0 : 0 ≤ tConst K Cold Δ := by linarith
  refine ⟨fun d _ _ => Wr * pmBound D G'.level G.level ρ n Dγ K W (tConst K Cold Δ) lam FP d,
    fun d α c => mul_nonneg hWr0
      (pmBound_nonneg D _ _ ρ n Dγ lam hK0 hW0 hc0 hε0.le FP.2 d), fun d hd hdD => ?_,
    fun d α c => ?_⟩
  · -- the record bound
    exact (pmBound_record_le D G'.level G.level ρ (n := n) (Dγ := Dγ) hDγ hK0 hW0 hc1 hWr0
      (lam := lam) (FP := (FP : ℝ)) FP.2 hρ hκ hcs hDst hDst0 hε0
      (G'.fam.identity v' u' γ').record.length_pos hn d hd
      (hdD.trans (G'.fam.identity v' u' γ').le_D) hQ0 (hQ d hd hdD)).trans hCw
  · -- the expressions
    obtain ⟨e, Δ', leaf, hE, hΔ', hL, hSF, hsum⟩ := pathMean_ledger_entry hζ hΛ hb hstart G G'
      hcert hexpU hexp hlev ρ n Dγ lam fop γ' hflux hDγ κc (compReserve kI v'.1) kI.Lstar hfine hr
      hε0 hε1 hτ ha3 hΔ hresΔ hK0 hW0 hC0 hWr0 hK hW hCold hWr d α c
    refine ⟨e, Δ', leaf, hE, hΔ', hL, hSF, hsum.trans (ENNReal.ofReal_le_ofReal
      (mul_le_mul_of_nonneg_left ?_ hWr0))⟩
    split_ifs
    · exact le_rfl
    · exact pmBound_nonneg D _ _ ρ n Dγ lam hK0 hW0 hc0 hε0.le FP.2 d
end

/-! **Ledger: the ledger of a mean letter.** For a new identity `γ'` of `G'` whose source is the
path summand of the mean letter `𝖬_{n,h}` along a path `π` of `h` edges of the old stage
(`letterMean`), the witnesses `θ(d, α, c) = W_r · pmBound(d)` (cell degree `n`) satisfy the
conclusion of `successor_ledger` (`letterMean_ledger_case`):
* the finer output is the graded path mean of cell degree `n`, minus, for a path of one edge, the
  all-slow direct part of order `n` of its identity (`slotFamRepP_directFlux`). The direct part
  has the size of the path mean of the same order with the lift constant `1`
  (`directSize_le`: `κ_m ε_m^{n-2} ≤ κ_{m-1} d_*^{n-2}`), and vanishes when `n` exceeds the maximal
  order of the identity (`directFlux_singleton_eq_zero`); so the difference has the size of a path
  mean with the constant `fluxXc(h, n) + 1`;
* the path mean of order `d₁` spends the reserve `(n - d₁)Δ`, which the birth of the letter
  provides (`hgap`: the reserve of the new component is below the reserves of the path by
  `D_m Δ`);
* the record bound holds with the new size `C_w ∏_j size_j` as soon as
  `C_w ≥ 4^{D_m}(D_m+1)c^{D_m} · W_r K W Q |λ| (d_*/ρ)^{n-2} · (fluxXc(h, n) + 1) · D_m^h`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

/-- The constant of the direct part of order `n` is at most the constant of the path mean of
cell degree `n` at the order `n`: `κ_m ε_m^{n-2} ≤ B d_*^{n-2}` with `d_*² = B ℓ_m²`. -/
theorem directConst_abs_le (D : OCData) (m : ℕ) {ρ B : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 2 ≤ n)
    (hcs : 0 < D.cellScaleSq m)
    (hDst : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = B * D.cellScaleSq m)
    (hκ0 : 0 ≤ D.kap m) (hκle : D.kap m ≤ B) (hε0 : 0 ≤ D.eps m)
    (hεd : D.eps m ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) :
    |directConst D m {n} n| ≤ |LiftGenSetup.pathMeanPref D m ρ n n| := by
  have hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) := hε0.trans hεd
  have hB0 : 0 ≤ B := hκ0.trans hκle
  have hfac : (0 : ℝ) ≤ (((n - 1).factorial : ℕ) : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hB : B = ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 * (D.cellScaleSq m)⁻¹ := by
    rw [hDst, mul_inv_cancel_right₀ hcs.ne']
  have h1 : directConst D m {n} n = D.kap m * D.eps m ^ (n - 2) *
      (((n - 1).factorial : ℕ) : ℝ)⁻¹ := by
    simp [directConst]
  have h2 : LiftGenSetup.pathMeanPref D m ρ n n =
      -(B * ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ (n - 2) *
        (((n - 1).factorial : ℕ) : ℝ)⁻¹) := by
    unfold LiftGenSetup.pathMeanPref
    obtain ⟨j, rfl⟩ : ∃ j, n = 2 + j := ⟨n - 2, by omega⟩
    have hρρ : ρ⁻¹ ^ (2 + j) * ρ ^ (2 + j) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ hρ.ne', one_pow]
    rw [hB, show 2 + j - 2 = j by omega, show 2 + j - 1 = j + 1 by omega, div_eq_mul_inv,
      mul_pow]
    linear_combination (-((D.cellScaleSq m)⁻¹ *
      ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ (2 + j) *
        (((j + 1).factorial : ℕ) : ℝ)⁻¹)) * hρρ
  rw [h1, h2, abs_neg,
    abs_of_nonneg (mul_nonneg (mul_nonneg hκ0 (pow_nonneg hε0 _)) hfac),
    abs_of_nonneg (mul_nonneg (mul_nonneg hB0 (pow_nonneg hD0 _)) hfac)]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul hκle (pow_le_pow_left₀ hε0 hεd _) (pow_nonneg hε0 _) hB0) hfac

/-- **The size of the direct part of order `n`** is at most the size of a path mean of cell
degree `n` with the lift constant `1`. -/
theorem directSize_le {G : GenStage D hr Dm b j₀} (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1)
    {v u : CompIn G.comps} (γ : G.fam.Γ v u) {ρ B : ℝ} (hρ : 0 < ρ) {n : ℕ} (hn : 2 ≤ n)
    (hord : n ≤ (G.fam.identity v u γ).maxOrder) (hcs : 0 < D.cellScaleSq G.level)
    (hDst : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      B * D.cellScaleSq G.level)
    (hκ0 : 0 ≤ D.kap G.level) (hκle : D.kap G.level ≤ B) (hε0 : 0 ≤ D.eps G.level)
    (hεd : D.eps G.level ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
    (d₁ : ℕ) (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) :
    Real.toNNReal |directConst D G.level {n} d₁| *
        ∑ σ : Equiv.Perm (Fin (d₁ - 1)), Real.toNNReal (oldTheta hcert v u γ d₁ (I₁ ∘ σ) i₀) ≤
      Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
          edgeTheta hcert v u γ) := by
  by_cases hd : d₁ = n
  · subst hd
    refine mul_le_mul' (Real.toNNReal_le_toNNReal
      (directConst_abs_le D G.level hρ hn hcs hDst hκ0 hκle hε0 hεd)) ?_
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    exact Finset.sum_le_sum fun σ _ =>
      toNNReal_oldTheta_le_edgeTheta hcert v u γ hn hord (I₁ ∘ σ) i₀
  · have h0 : directConst D G.level {n} d₁ = 0 := by
      simp [directConst, hd]
    rw [h0, abs_zero, Real.toNNReal_zero, zero_mul]
    exact zero_le

/-- The direct part of an order outside `2 ≤ n ≤ D_γ` vanishes. -/
theorem directFlux_singleton_eq_zero (G : GenStage D hr Dm b j₀) (p : OddSlot)
    (c : StageCtx D b j₀ G.level p) {v u : CompIn G.comps} (γ : G.fam.Γ v u) {n : ℕ}
    (hn : ¬ (2 ≤ n ∧ n ≤ (G.fam.identity v u γ).maxOrder)) (t : ℝ) :
    directFlux G p c γ {n} t = fun _ _ => 0 := by
  have hz : ∀ α : DerivativeWord2 (n - 1), G.fam.flux p c v u γ n α = fun _ _ _ => 0 :=
    fun α => G.fam.flux_zero p c v u γ n α hn
  funext f y
  simp [directFlux, hz, fieldCellMean]

open scoped Classical in
/-- **The ledger of a mean letter.** -/
theorem letterMean_ledger_case (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (hT : G.IsSlotTransverse)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), G.exports e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')
    (hexp : ∀ {i p} (e : Gen .ctx i p), G.exports e → G'.exports e)
    (hlev : G.level = G'.level + 1) {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ)
    (t₀ : List WordLetter) (n : ℕ)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.letterMean t₀ n h π).pathLen + 1)) (fun _ => ℝ))
    {sX sZ N R : ℕ}
    (hset : ∀ (k : ℤ) (hk : Odd k), CutoffLiftSetup D b j₀ G.exports G.level k ρ
      (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N R)
    (hn : 2 ≤ n) (hnD : n ≤ Dm) (hR : n + Dm + 2 ≤ R) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u') (lam : ℝ) (Dγ : ℕ) (hDγ : Dγ ≤ Dm)
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D G.level p.1 lam Dγ ((SuccSource.letterMean t₀ n h π).fluxOp ρ s₀ Cc) t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    {Cw : ℝ}
    (hsize' : (G'.fam.identity v' u' γ').record.size = Cw *
      ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size)
    (hℓ : ∀ j : Fin h, 3 ≤ (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).maxOrder →
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.length ≤
        D.eps G.level)
    {μ₀ : ℝ} (hμ₀ : ∀ j : Fin h, μ₀ ≤ compReserve kI (π.step j).1.1)
    (hεn : ∀ k, 0 ≤ D.eps k) (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1)) (hκ : 0 < D.kap G'.level)
    (hκ0 : 0 ≤ D.kap G.level) (hκle : D.kap G.level ≤ D.kap G'.level)
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hρ : 0 < ρ)
    (hεd : D.eps G.level ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
    (hDst : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      D.kap G'.level * D.cellScaleSq G.level)
    (κc : MajConsts) {a Δ K W Cold Wr Q : ℝ} {S Kg Kd : ℝ≥0} (ha3 : 3 * Real.pi * b < a)
    (hΔ : 0 < Δ) (hgap : compReserve kI v'.1 + Dm * Δ ≤ μ₀)
    (hXok : (oldCtx hcert κc Δ μ₀ S Kg Kd).Ok)
    (hSl : ENNReal.ofReal |ρ| * (κc.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hL₀ : UEnv.liftWt Dm h N ≤ kI.Lstar) (hLn : UEnv.liftWt Dm h n ≤ kI.Lstar)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr)
    (hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 a) ≤ ENNReal.ofReal Wr)
    (hQ0 : 0 ≤ Q)
    (hQ : ∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder → ∀ i',
      (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
        (ρ / D.eps G'.level) ^ (d - 2 + i') ≤ Q)
    (hCw : 4 ^ Dm * (Dm + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W * Q * |lam| *
        (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2)) *
      (((UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
        (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n + 1 : ℝ≥0) : ℝ) * (Dm : ℝ) ^ h) ≤ Cw) :
    ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
      (∀ d α c, 0 ≤ θ d α c) ∧
      (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
        (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
            ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
      ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
        ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
          (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
          G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
          (∀ p, Gen.SolvedFree leaf (e p)) ∧
          ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
              (1 + |(h : ℝ)|) ^ kI.Lstar) *
            ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
              genMode D κc Δ leaf (e p) (compReserve kI v'.1) h t
            ≤ ENNReal.ofReal (θ d α c) := by
  have hcs := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκb G.level
  have hDst0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) :=
    (hεn G.level).trans hεd
  -- the finer outputs
  have hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → d₁ ≤ Dγ →
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ G.exports G.level k (oldCtx hcert κc Δ μ₀ S Kg Kd)
          (fun t A => fluxCoeff ((SuccSource.letterMean t₀ n h π).fluxOp ρ s₀ Cc k t A)
            d₁ I₁ 0 i₀)
          (n - 1 - (d₁ - 1))
          (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
              ((UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
                (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n + 1) *
              ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2))) := by
    intro k hk d₁ hd₁ _ I₁ i₀
    have hPM := slotFamRepP_pathMean_of_path hΛ hζ hκb hb.le hεn hcert hT π k hk ρ (Cc k)
      (hset k hk) κc hXok hμ₀ hSl hη0 hη1 hL₀ (by omega) hLn hR d₁ I₁ i₀
    have hmono : Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
          (UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
            (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n *
            ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2)) ≤
        Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
          (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
            ((UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
              (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n + 1) *
            ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2)) :=
      mul_le_mul_right (mul_le_mul_right (mul_le_mul_left le_self_add _) _) _
    by_cases hh : h = 1
    · subst hh
      by_cases hord : n ≤ (G.fam.identity _ _ (π.step ⟨0, by omega⟩).2.2).maxOrder
      · have hDF := (slotFamRepP_directFlux hΛ hζ hb hεn hcert (π.step ⟨0, by omega⟩).2.2 {n}
          (fun d' hd' => by simp only [Finset.mem_singleton] at hd'; omega) hk hd₁ I₁ i₀ κc
          (Δ := Δ) S Kg Kd (hμ₀ ⟨0, by omega⟩)).mono hXok (Nat.zero_le (n - 1 - (d₁ - 1)))
          (directSize_le hcert (π.step ⟨0, by omega⟩).2.2 hρ hn hord hcs hDst hκ0 hκle
            (hεn G.level) hεd d₁ I₁ i₀)
        refine ((hPM.sub hXok hDF).mono hXok le_rfl (le_of_eq ?_)).congr fun A hA t _ => ?_
        · have hE : (∏ j : Fin 1, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2) =
              edgeTheta hcert (π.step ⟨0, by omega⟩).1 (π.step ⟨0, by omega⟩).2.1
                (π.step ⟨0, by omega⟩).2.2 := Fin.prod_univ_one _
          rw [hE]
          ring
        · simp only [SuccSource.fluxOp, hA, hk, and_self, ↓reduceDIte,
            pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
          unfold fluxCoeff
          simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
          ring
      · refine (hPM.mono hXok le_rfl hmono).congr fun A hA t _ => ?_
        have hz := directFlux_singleton_eq_zero G ⟨k, hk⟩ ⟨A, hA⟩ (π.step ⟨0, by omega⟩).2.2
          (n := n) (fun h2 => hord h2.2) t
        simp only [SuccSource.fluxOp, hA, hk, and_self, ↓reduceDIte,
          pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA, hz]
        unfold fluxCoeff
        simp
    · refine (hPM.mono hXok le_rfl hmono).congr fun A hA t _ => ?_
      simp only [SuccSource.fluxOp, hA, hk, and_self, ↓reduceDIte, hh,
        pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
      unfold fluxCoeff
      simp
  refine pathMean_ledger_case hζ hΛ hb hκb hstart G G' hcert hexpU hexp hlev ρ n Dγ lam _ γ' hflux
    hDγ hn κc hfine
    (fun d₁ _ _ => by
      have h1 : ((n - 1 - (d₁ - 1) : ℕ) : ℝ) * Δ ≤ Dm * Δ :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (by omega : n - 1 - (d₁ - 1) ≤ Dm)) hΔ.le
      linarith)
    hε0 hε1 hτ hκ hρ hDst0 hDst ha3 hΔ (hgap.trans hXok.hμ) hK0 hW0 hC0 hWr0 hK hW hCold hWr hQ0
    hQ ?_
  rw [hsize']
  have hcoef : 0 ≤ 4 ^ Dm * ((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W * Q * |lam| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2)) := by
    have : 0 ≤ tConst K Cold Δ := by linarith [one_le_tConst hK0 hC0 hΔ]
    have h3 : 0 ≤ (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2) :=
      pow_nonneg (div_nonneg hDst0 hρ.le) _
    positivity
  refine le_trans (le_of_eq ?_) ((pathSize_le hcert π zero_le_one hℓ hcoef hCw).trans_eq (by rw [one_pow, one_mul]))
  ring
end

/-! **Ledger: the ledger of a transferred quadratic conversion.** For a new identity `γ'` of `G'`
whose source is the quadratic conversion of a path `π` of `h` edges of the old stage (`copyQuad`),
the witnesses `θ(d, α, c) = W_r · pmBound(d)` (cell degree `n = 2`, normalization `λ = 1`, maximal
order `2`) satisfy the conclusion of `successor_ledger` (`copyQuad_ledger_case`):
* the finer outputs are the graded path means of cell degree two (`slotFamRepP_pathMean_of_path`),
  with no reserve at the tested order two ("principal quadratic means have `n = d = 2` and spend no
  reserve"), so the conversion may land in the old target component itself;
* the transferred coefficient is bounded through `pathMean_ledger_case`; the scale factors cancel
  exactly (`d_*² = κ_{m-1} ℓ_m²`);
* the record bound holds with the new size `C_w ∏_j size_j` as soon as
  `C_w ≥ 4^{D_m}(D_m+1)c^{D_m} · W_r K W · fluxXc(h, 2) · D_m^h` (`pathSize_le`): each edge of the
  path contributes its record size once. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

open scoped Classical in
/-- **The ledger of a transferred quadratic conversion.** -/
theorem copyQuad_ledger_case (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (hT : G.IsSlotTransverse)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), G.exports e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')
    (hexp : ∀ {i p} (e : Gen .ctx i p), G.exports e → G'.exports e)
    (hlev : G.level = G'.level + 1) {h : ℕ} (π : StagePath G h) (ρ s₀ : ℝ)
    (t₀ : List WordLetter)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.copyQuad t₀ h π).pathLen + 1)) (fun _ => ℝ))
    {sX sZ N R : ℕ}
    (hset : ∀ (k : ℤ) (hk : Odd k), CutoffLiftSetup D b j₀ G.exports G.level k ρ
      (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N R)
    (hR : 2 + Dm + 2 ≤ R) {v' u' : CompIn G'.comps} (γ' : G'.fam.Γ v' u')
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D G.level p.1 1 2 ((SuccSource.copyQuad t₀ h π).fluxOp ρ s₀ Cc) t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    (hmax' : (G'.fam.identity v' u' γ').maxOrder = 2) {Cw : ℝ}
    (hsize' : (G'.fam.identity v' u' γ').record.size = Cw *
      ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size)
    (hℓ : ∀ j : Fin h, 3 ≤ (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).maxOrder →
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.length ≤
        D.eps G.level)
    (hres : ∀ j : Fin h, compReserve kI v'.1 ≤ compReserve kI (π.step j).1.1)
    (hεn : ∀ k, 0 ≤ D.eps k) (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1)) (hκ : 0 < D.kap G'.level)
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hρ : 0 < ρ) (hρE : ρ ≤ D.eps G'.level)
    (hDst0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
    (hDst : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      D.kap G'.level * D.cellScaleSq G.level)
    (κc : MajConsts) {a Δ K W Cold Wr : ℝ} {S Kg Kd : ℝ≥0} (ha3 : 3 * Real.pi * b < a)
    (hΔ : 0 < Δ) (hresΔ : compReserve kI v'.1 + Dm * Δ ≤ 2)
    (hXok : (oldCtx hcert κc Δ (compReserve kI v'.1) S Kg Kd).Ok)
    (hSl : ENNReal.ofReal |ρ| * (κc.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hL₀ : UEnv.liftWt Dm h N ≤ kI.Lstar) (hLn : UEnv.liftWt Dm h 2 ≤ kI.Lstar)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr)
    (hK : ∀ L, L ≤ Dm → kBound κc a L ≤ ENNReal.ofReal K)
    (hW : wsum a 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 a) ≤ ENNReal.ofReal Wr)
    (hCw : 4 ^ Dm * (Dm + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W) *
      ((UEnv.fluxXc (oldCtx hcert κc Δ (compReserve kI v'.1) S Kg Kd) Dm
        (liftB (oldCtx hcert κc Δ (compReserve kI v'.1) S Kg Kd) Dm) h 2 : ℝ≥0) *
        (Dm : ℝ) ^ h) ≤ Cw) :
    ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
      (∀ d α c, 0 ≤ θ d α c) ∧
      (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
        (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
            ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
      ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
        ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
          (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
          G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
          (∀ p, Gen.SolvedFree leaf (e p)) ∧
          ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
              (1 + |(h : ℝ)|) ^ kI.Lstar) *
            ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
              genMode D κc Δ leaf (e p) (compReserve kI v'.1) h t
            ≤ ENNReal.ofReal (θ d α c) := by
  have hDm2 : 2 ≤ Dm := hmax' ▸ (G'.fam.identity v' u' γ').le_D
  have hc1 := one_le_tConst hK0 hC0 hΔ
  -- the finer outputs
  have hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → d₁ ≤ 2 →
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ G.exports G.level k
          (oldCtx hcert κc Δ (compReserve kI v'.1) S Kg Kd)
          (fun t A => fluxCoeff ((SuccSource.copyQuad t₀ h π).fluxOp ρ s₀ Cc k t A) d₁ I₁ 0 i₀)
          (2 - 1 - (d₁ - 1))
          (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ 2 d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
              (UEnv.fluxXc (oldCtx hcert κc Δ (compReserve kI v'.1) S Kg Kd) Dm
                (liftB (oldCtx hcert κc Δ (compReserve kI v'.1) S Kg Kd) Dm) h 2 *
              ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2))) := by
    intro k hk d₁ _ _ I₁ i₀
    refine (slotFamRepP_pathMean_of_path hΛ hζ hκb hb.le hεn hcert hT π k hk ρ (Cc k)
      (hset k hk) κc hXok hres hSl hη0 hη1 hL₀ (by norm_num) hLn hR d₁ I₁ i₀).congr
      fun A hA t _ => ?_
    simp only [SuccSource.fluxOp, hA, hk, and_self, ↓reduceDIte,
      pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
  refine pathMean_ledger_case hζ hΛ hb hκb hstart G G' hcert hexpU hexp hlev ρ 2 2 1 _ γ' hflux
    hDm2 le_rfl κc (Q := 1) hfine
    (fun d₁ h2 h2' => by
      obtain rfl : d₁ = 2 := by omega
      simp)
    hε0 hε1 hτ hκ hρ hDst0 hDst ha3 hΔ hresΔ hK0 hW0 hC0 hWr0 hK hW hCold hWr zero_le_one
    (fun d hd hdD i' => ?_) ?_
  · rw [hmax'] at hdD
    obtain rfl : d = 2 := by omega
    simp only [Nat.sub_self, pow_zero, one_mul, Nat.zero_add]
    exact pow_le_one₀ (div_nonneg hρ.le hε0.le) ((div_le_one hε0).mpr hρE)
  · rw [hsize']
    have hcoef : 0 ≤ 4 ^ Dm * ((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W) := by
      have : 0 ≤ tConst K Cold Δ := by linarith
      positivity
    refine le_trans (le_of_eq ?_) ((pathSize_le hcert π zero_le_one hℓ hcoef hCw).trans_eq (by rw [one_pow, one_mul]))
    simp only [Nat.sub_self, pow_zero, abs_one, mul_one]
    ring
end

/-! **Ledger: the ledger of a covariance letter.** For a new identity `γ'` of `G'` whose source is
the path summand of the covariance letter `𝖵_{n,h,a,a'}` along a path `π` of `h` edges of the old
stage (`letterCov`), the witnesses `θ(d, α, c) = W_r · pmBound(d)` (cell degree `n`) satisfy the
conclusion of `successor_ledger` (`letterCov_ledger_case`):
* the finer output is the covariance letter of the path mean, a graded slot family function of
  the size of a path mean of cell degree `n` at every tested order up to `n + 2(a + a')`, with the
  lift constant `covLetK · c_H^{a+a'} · fluxXc(h, n)` (`slotFamRepP_covLetter_of_path`), where
  `c_H ≥ |𝖧_m|/ρ²` (the price of the mean multiplied by `(‖H_cov‖/r²)^{a+a'}(r/E)^l`, the
  factors `(r/E)^l ≤ 1` being discarded);
* the reserve `covLetR n a a' · Δ` is provided by the birth of the letter (`hgap`);
* the record bound holds with the new size `C_w ∏_j size_j` as soon as
  `C_w ≥ 4^{D_m}(D_m+1)c^{D_m} · W_r K W Q |λ| (d_*/ρ)^{n-2} · covLetK c_H^{a+a'} fluxXc(h, n) · D_m^h`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

/-- The size of the path mean at the tested order `d`: `|c_{n,d}| (d-1)! = pmC ρ^{d-1}`. -/
theorem toNNReal_pathMeanPref_mul_card (D : OCData) (m : ℕ) {ρ : ℝ} (hc : 0 < D.cellScaleSq m)
    (hρ : 0 < ρ) (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) (n d : ℕ) :
    Real.toNNReal |LiftGenSetup.pathMeanPref D m ρ n d| *
        ((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) =
      Real.toNNReal (LiftGenSetup.pmC D m ρ n) * Real.toNNReal ρ ^ (d - 1) := by
  have hc0 : 0 ≤ LiftGenSetup.pmC D m ρ n := by
    unfold LiftGenSetup.pmC
    positivity
  have hf : (0 : ℝ) < (((d - 1).factorial : ℕ) : ℝ) := by exact_mod_cast Nat.factorial_pos (d - 1)
  have e : LiftGenSetup.pathMeanPref D m ρ n d =
      -(LiftGenSetup.pmC D m ρ n * ρ ^ (d - 1) * (((d - 1).factorial : ℕ) : ℝ)⁻¹) := by
    unfold LiftGenSetup.pathMeanPref LiftGenSetup.pmC
    ring
  rw [e, abs_neg, abs_of_nonneg (mul_nonneg (mul_nonneg hc0 (pow_nonneg hρ.le _))
    (inv_nonneg.mpr hf.le)), Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    Real.toNNReal_mul (mul_nonneg hc0 (pow_nonneg hρ.le _)), Real.toNNReal_mul hc0,
    Real.toNNReal_pow hρ.le, Real.toNNReal_inv, Real.toNNReal_natCast, mul_assoc,
    inv_mul_cancel₀ (by exact_mod_cast (Nat.factorial_pos (d - 1)).ne'), mul_one]

/-- **The covariance letter of a path of the old stage is a graded slot family function.** -/
theorem slotFamRepP_covLetter_of_path {G : GenStage D hr Dm b j₀} (hΛ : 1 ≤ D.Λ)
    (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 ≤ b)
    (hεn : ∀ k, 0 ≤ D.eps k) (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (hT : G.IsSlotTransverse) {h : ℕ}
    (π : StagePath G h) (k : ℤ) (hk : Odd k) (ρ : ℝ)
    (Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)) {sX sZ N R : ℕ}
    (hset : CutoffLiftSetup D b j₀ G.exports G.level k ρ (pathEdgesAt G π ⟨k, hk⟩) Cc sX sZ N R)
    (κ : MajConsts) {Δ μ₀ : ℝ} {S Kg Kd : ℝ≥0} (hXok : (oldCtx hcert κ Δ μ₀ S Kg Kd).Ok)
    (hμ : ∀ j : Fin h, μ₀ ≤ compReserve kI (π.step j).1.1)
    (hSl : ENNReal.ofReal |ρ| * (κ.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hL₀ : UEnv.liftWt Dm h N ≤ kI.Lstar)
    {n : ℕ} (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ kI.Lstar) (hnR : n + Dm + 2 ≤ R)
    (a a' : ℕ) (haR : 2 * a + Dm + 2 ≤ R) (hκκ : D.kap G.level = D.κ G.level)
    (hκκ' : D.kap (G.level - 1) = D.κ (G.level - 1)) (hρ : 0 < ρ)
    (hD0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1))) {cH : ℝ≥0}
    (hH : ∀ t i j, |covMat D G.level 0 t i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ' : Fin 2) :
    SlotFamRepP D b j₀ G.exports G.level k (oldCtx hcert κ Δ μ₀ S Kg Kd) (fun t A =>
      fluxCoeff (covLetterFlux D G.level ρ 0
        (familyLiftData D G.level k A ρ (pathEdgesAt G π ⟨k, hk⟩ A)) (Cc A) n a a' t A) d I 0 κ')
      (covLetR n a a')
      (covLetK n a a' S Kg * (cH ^ (a + a') *
        (Real.toNNReal (LiftGenSetup.pmC D G.level ρ n) *
          (UEnv.fluxXc (oldCtx hcert κ Δ μ₀ S Kg Kd) Dm
            (liftB (oldCtx hcert κ Δ μ₀ S Kg Kd) Dm) h n *
            ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2))) *
        Real.toNNReal ρ ^ (d - 1)) := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ G.level
  have hε : D.eps (G.level - 1) ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  have h1 := CutoffLiftSetup.slotFamRep_covLetterP hset hζ hc hXok hSl hη0 hη1
    (Θ := pathTheta hcert π)
    (fun U hU v u d α c => edgeURepP_of_certified hb hεn hcert hT π ⟨k, hk⟩ rfl rfl hε _ U _ _
      (fun A hA => hA) (fun A hA Y hY => hU A hA hY)
      (fun τ hτ => cellScaleSq_mul_mem_ocPulseWindow hc hτ) κ hXok hμ v u d α c)
    hL₀ hn1 hLn hnR a a' haR hκκ hκκ' hρ hD0 (fun t _ i j => hH t i j) d I κ'
  rwa [pathW_pathTheta] at h1

open scoped Classical in
/-- **The ledger of a covariance letter.** -/
theorem letterCov_ledger_case (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hb : 0 < b)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (G G' : GenStage D hr Dm b j₀) (hcert : G.OldCert G.exports (compReserve kI) kI.Lstar 1) (hT : G.IsSlotTransverse)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), G.exports e → ∀ f f', Gen.Denotes D b j₀ e f →
      Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f')
    (hexp : ∀ {i p} (e : Gen .ctx i p), G.exports e → G'.exports e)
    (hlev : G.level = G'.level + 1) {h : ℕ} (π : StagePath G h) (ρ : ℝ)
    (t₀ : List WordLetter) (n a a' : ℕ)
    (Cc : ℤ → RealChain → ℕ → ℕ →
      LiftCoeff (Fin ((SuccSource.letterCov t₀ n h a a' π).pathLen + 1)) (fun _ => ℝ))
    {sX sZ N R : ℕ}
    (hset : ∀ (k : ℤ) (hk : Odd k), CutoffLiftSetup D b j₀ G.exports G.level k ρ
      (pathEdgesAt G π ⟨k, hk⟩) (Cc k) sX sZ N R)
    (hn : 2 ≤ n) (hR : n + Dm + 2 ≤ R) (haR : 2 * a + Dm + 2 ≤ R) {v' u' : CompIn G'.comps}
    (γ' : G'.fam.Γ v' u') (lam : ℝ) (Dγ : ℕ) (hDγ : Dγ ≤ Dm)
    (hflux : ∀ (p : OddSlot) (ctx : StageCtx D b j₀ G'.level p) (d : ℕ)
      (I : DerivativeWord2 (d - 1)) (t : ℝ) (Y z : Vec 2), 2 ≤ d →
      G'.fam.flux p ctx v' u' γ' d I t Y z =
        if IsAdmissibleChain D b j₀ G'.level p.1 (ctx.1.recenter D (D.eps (G'.level - 1) • Y))
        then transferAt D G.level p.1 lam Dγ
          ((SuccSource.letterCov t₀ n h a a' π).fluxOp ρ 0 Cc) t
          (ctx.1.recenter D (D.eps (G'.level - 1) • Y)) z d I
        else 0)
    {Cw : ℝ}
    (hsize' : (G'.fam.identity v' u' γ').record.size = Cw *
      ∏ j : Fin h, (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.size)
    (hℓ : ∀ j : Fin h, 3 ≤ (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).maxOrder →
      (G.fam.identity (π.step j).1 (π.step j).2.1 (π.step j).2.2).record.length ≤
        D.eps G.level)
    {μ₀ : ℝ} (hμ₀ : ∀ j : Fin h, μ₀ ≤ compReserve kI (π.step j).1.1)
    (hεn : ∀ k, 0 ≤ D.eps k) (hε0 : 0 < D.eps G'.level) (hε1 : D.eps G'.level ≤ 1)
    (hτ : 0 < ocTau D.α D.q D.Λ (G'.level + 1)) (hκ : 0 < D.kap G'.level)
    (hκκ : D.kap G.level = D.κ G.level) (hκκ' : D.kap (G.level - 1) = D.κ (G.level - 1))
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1) (hρ : 0 < ρ)
    (hDst0 : 0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)))
    (hDst : ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      D.kap G'.level * D.cellScaleSq G.level)
    (κc : MajConsts) {ar Δ K W Cold Wr Q : ℝ} {S Kg Kd cH : ℝ≥0} (ha3 : 3 * Real.pi * b < ar)
    (hΔ : 0 < Δ) (hgap : compReserve kI v'.1 + (covLetR n a a' : ℝ) * Δ ≤ μ₀)
    (hresΔ : compReserve kI v'.1 + Dm * Δ ≤ 2)
    (hXok : (oldCtx hcert κc Δ μ₀ S Kg Kd).Ok)
    (hSl : ENNReal.ofReal |ρ| * (κc.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hL₀ : UEnv.liftWt Dm h N ≤ kI.Lstar) (hLn : UEnv.liftWt Dm h n ≤ kI.Lstar)
    (hK0 : 0 ≤ K) (hW0 : 0 ≤ W) (hC0 : 0 ≤ Cold) (hWr0 : 0 ≤ Wr)
    (hK : ∀ L, L ≤ Dm → kBound κc ar L ≤ ENNReal.ofReal K)
    (hW : wsum ar 0 κc.child ≤ ENNReal.ofReal W) (hCold : κc.Cold ≤ ENNReal.ofReal Cold)
    (hWr : wsum (3 * Real.pi * b) kI.Lstar (expProfile 1 ar) ≤ ENNReal.ofReal Wr)
    (hH : ∀ t i j, |covMat D G.level 0 t i j| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    (hQ0 : 0 ≤ Q)
    (hQ : ∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder → ∀ i',
      (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
        (ρ / D.eps G'.level) ^ (d - 2 + i') ≤ Q)
    (hCw : 4 ^ Dm * (Dm + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W * Q * |lam| *
        (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2)) *
      (((covLetK n a a' S Kg * cH ^ (a + a') *
        UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
          (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n : ℝ≥0) : ℝ) * (Dm : ℝ) ^ h) ≤ Cw) :
    ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
      (∀ d α c, 0 ≤ θ d α c) ∧
      (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
        (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
            ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
      ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
        ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
          (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
          G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
          (∀ p, Gen.SolvedFree leaf (e p)) ∧
          ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
              (1 + |(h : ℝ)|) ^ kI.Lstar) *
            ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
              genMode D κc Δ leaf (e p) (compReserve kI v'.1) h t
            ≤ ENNReal.ofReal (θ d α c) := by
  have hcs := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκb G.level
  -- the finer outputs
  have hfine : ∀ k : ℤ, Odd k → ∀ d₁ : ℕ, 1 ≤ d₁ → d₁ ≤ Dγ →
      ∀ (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2),
        SlotFamRepP D b j₀ G.exports G.level k (oldCtx hcert κc Δ μ₀ S Kg Kd)
          (fun t A => fluxCoeff ((SuccSource.letterCov t₀ n h a a' π).fluxOp ρ 0 Cc k t A)
            d₁ I₁ 0 i₀)
          (covLetR n a a')
          (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁| *
            (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
              (covLetK n a a' S Kg * cH ^ (a + a') *
                UEnv.fluxXc (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm
                  (liftB (oldCtx hcert κc Δ μ₀ S Kg Kd) Dm) h n *
              ∏ j : Fin h, edgeTheta hcert (π.step j).1 (π.step j).2.1 (π.step j).2.2))) := by
    intro k hk d₁ _ _ I₁ i₀
    have hCov := slotFamRepP_covLetter_of_path hΛ hζ hκb hb.le hεn hcert hT π k hk ρ (Cc k)
      (hset k hk) κc hXok hμ₀ hSl hη0 hη1 hL₀ (by omega) hLn hR a a' haR hκκ hκκ' hρ hDst0 hH
      d₁ I₁ i₀
    refine (hCov.mono hXok le_rfl (le_of_eq ?_)).congr fun A hA t _ => ?_
    · rw [← mul_assoc (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level ρ n d₁|),
        toNNReal_pathMeanPref_mul_card D G.level hcs hρ hDst0 n d₁]
      ring
    · simp only [SuccSource.fluxOp, hA, hk, and_self, ↓reduceDIte,
        pathEdgesAt_of_admissible G π ⟨k, hk⟩ hA]
      rfl
  refine pathMean_ledger_case hζ hΛ hb hκb hstart G G' hcert hexpU hexp hlev ρ n Dγ lam _ γ' hflux
    hDγ hn κc (a := ar) hfine (fun d₁ _ _ => hgap)
    hε0 hε1 hτ hκ hρ hDst0 hDst ha3 hΔ hresΔ hK0 hW0 hC0 hWr0 hK hW hCold hWr hQ0 hQ ?_
  rw [hsize']
  have hcoef : 0 ≤ 4 ^ Dm * ((Dm : ℝ) + 1) * tConst K Cold Δ ^ Dm * (Wr * K * W * Q * |lam| *
      (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2)) := by
    have : 0 ≤ tConst K Cold Δ := by linarith [one_le_tConst hK0 hC0 hΔ]
    have h3 : 0 ≤ (ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) / ρ) ^ (n - 2) :=
      pow_nonneg (div_nonneg hDst0 hρ.le) _
    positivity
  refine le_trans (le_of_eq ?_) ((pathSize_le hcert π zero_le_one hℓ hcoef hCw).trans_eq (by rw [one_pow, one_mul]))
  ring
end

/-! **Ledger: the standing facts of one passage of the ledger.**
* `LedgerConcl kI κc G' v' u' γ'`: the conclusion of `successor_ledger` for one identity of the
  next family.
* `StepFacts kI G G' P C`: what every case of the ledger uses of the passage from `G` to `G'`:
  the ambient facts, the certified, generated, slotwise transverse old stage with unique exports,
  the tags, the grade monotonicity of the edges, the lengths of the higher identities and the
  scale facts `PassScales` of the level of `G`; with the derived scale facts in the form of the
  case lemmas.
* the reserves of the components: `compReserve ≤ 1`, antitone in the grade
  (`compReserve_anti`), and a letter-born component is exactly one grade step below its old
  component (`compReserve_succComp_append`).
* the letters of the successor alphabet: `mean_mem_succAlphabet`, `cov_mem_succAlphabet`. -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ} {kI : InvConsts}

/-- **The conclusion of the ledger for one identity of the next family.** -/
def LedgerConcl (kI : InvConsts) (κc : MajConsts) (G' : GenStage D hr Dm b j₀)
    (v' u' : CompIn G'.comps) (γ' : G'.fam.Γ v' u') : Prop :=
  ∃ θ : (d : ℕ) → DerivativeWord2 (d - 1) → Fin 2 → ℝ,
    (∀ d α c, 0 ≤ θ d α c) ∧
    (∀ d, 2 ≤ d → d ≤ (G'.fam.identity v' u' γ').maxOrder →
      (D.eps G'.level / (G'.fam.identity v' u' γ').record.length) ^ (d - 2) *
          ∑ α, ∑ c, θ d α c ≤ (G'.fam.identity v' u' γ').record.size) ∧
    ∀ (d : ℕ) (α : DerivativeWord2 (d - 1)) (c : Fin 2),
      ∃ (e : (p : OddSlot) → Gen .ctx G'.level p.1) (Δ : ℝ)
        (leaf : ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞)),
        G'.IsExprFor v' u' γ' d α c e ∧ 0 < Δ ∧ LeavesCertified D b j₀ leaf ∧
        (∀ p, Gen.SolvedFree leaf (e p)) ∧
        ∑' h : ℤ, ENNReal.ofReal (Real.exp (3 * Real.pi * b * |(h : ℝ)|) *
            (1 + |(h : ℝ)|) ^ kI.Lstar) *
          ⨆ p : OddSlot, ⨆ t ∈ ocPulseWindow D.α D.q D.Λ G'.level p.1,
            genMode D κc Δ leaf (e p) (compReserve kI v'.1) h t
          ≤ ENNReal.ofReal (θ d α c)

/-! ### Reserves -/

theorem compReserve_le_one (k : InvConsts) (c : Comp) : compReserve k c ≤ 1 := by
  unfold compReserve
  have h1 : (0 : ℝ) ≤ ((k.G0 + compGrade c : ℕ) : ℝ) := Nat.cast_nonneg _
  have h2 : (0 : ℝ) < (k.Hprod : ℝ) + 1 := by positivity
  have := div_nonneg h1 h2.le
  linarith

/-- The reserve decreases with the grade. -/
theorem compReserve_anti (k : InvConsts) {c c' : Comp} (h : compGrade c ≤ compGrade c') :
    compReserve k c' ≤ compReserve k c := by
  unfold compReserve
  have h1 : ((k.G0 + compGrade c : ℕ) : ℝ) ≤ ((k.G0 + compGrade c' : ℕ) : ℝ) := by
    exact_mod_cast (by omega)
  have h2 : (0 : ℝ) < (k.Hprod : ℝ) + 1 := by positivity
  have := div_le_div_of_nonneg_right h1 h2.le
  linarith

/-- **A letter-born component is one grade step below its old component.** -/
theorem compReserve_succComp_append (k : InvConsts) (m : ℕ) (c : Comp) (t : List WordLetter)
    (l : WordLetter) :
    compReserve k (succComp m c (t ++ [l])) + 1 / ((k.Hprod : ℝ) + 1) = compReserve k c := by
  unfold compReserve
  rw [compGrade_succComp_ne m c (by simp)]
  push_cast
  ring

/-! ### The letters of the successor alphabet -/

theorem mean_mem_succAlphabet {nMax hMax p npad n h : ℕ}
    (hm : WordLetter.mean n h ∈ succAlphabet nMax hMax p npad) :
    3 ≤ n ∧ n ≤ nMax ∧ 1 ≤ h ∧ h ≤ hMax := by
  simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range, reduceCtorEq,
    false_or, or_false, and_false, exists_false, WordLetter.mean.injEq, Prod.exists] at hm
  obtain ⟨n', h', ⟨⟨hn3, hnM⟩, hh1, hhM⟩, rfl, rfl⟩ := hm
  exact ⟨hn3, hnM, hh1, hhM⟩

theorem cov_mem_succAlphabet {nMax hMax p npad n h a a' : ℕ}
    (hm : WordLetter.covariance n h a a' ∈ succAlphabet nMax hMax p npad) :
    2 ≤ n ∧ n ≤ nMax ∧ 1 ≤ h ∧ h ≤ hMax ∧ a ≤ p ∧ a' ≤ p ∧ 1 ≤ a + a' := by
  simp only [succAlphabet, Finset.mem_union, Finset.mem_singleton, Finset.mem_image,
    Finset.mem_product, Finset.mem_Icc, Finset.mem_filter, Finset.mem_range, reduceCtorEq,
    false_or, or_false, and_false, exists_false, WordLetter.covariance.injEq, Prod.exists] at hm
  obtain ⟨n', h', a₁, a₂, ⟨⟨⟨⟨hn2, hnM⟩, hh1, hhM⟩, ha₁, ha₂⟩, haa⟩, rfl, rfl, rfl, rfl⟩ := hm
  exact ⟨hn2, hnM, hh1, hhM, by omega, by omega, haa⟩

/-! ### The standing facts of a passage -/

/-- **The standing facts of the passage from `G` to `G'`** used by every case of the ledger. -/
structure StepFacts (kI : InvConsts) (G G' : GenStage D hr Dm b j₀) (P : ProvParams)
    (Cu : ℝ) : Prop where
  hζ : IsFastProfile D.ζ
  hΛ : 128 ≤ D.Λ
  hq : 1 < D.q
  hb : 0 < b
  hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ
  hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
    2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2))
  hcert : G.IsContextCertified kI
  hT : G.IsSlotTransverse
  hGen : G.IsGenerated
  hexpU : ∀ {i p} (e : Gen .ctx i p), G.exports e → ∀ f f', Gen.Denotes D b j₀ e f →
    Gen.Denotes D b j₀ e f' → AgreeOn D b j₀ i p .ctx f f'
  hexp : ∀ {i p} (e : Gen .ctx i p), G.exports e → G'.exports e
  hlev : G.level = G'.level + 1
  hGT : G.HasTags P
  hGT' : G'.HasTags P
  /-- The edges of the old stage do not lower the grade. -/
  hgrade : ∀ (v u : CompIn G.comps), Nonempty (G.fam.Γ v u) → compGrade u.1 ≤ compGrade v.1
  /-- The higher identities of the old stage have lengths at most its wavelength. -/
  hlen : ∀ v u (γ : G.fam.Γ v u), 1 ≤ (G.fam.identity v u γ).record.birthExcess →
    (G.fam.identity v u γ).record.length ≤ D.eps G.level
  hsc : PassScales D G.level Cu
  hCu : 1 ≤ Cu
  hδ : 0 < ocDelta D.α D.q

namespace StepFacts

variable {G G' : GenStage D hr Dm b j₀} {P : ProvParams} {Cu : ℝ}

theorem hΛ1 (hF : StepFacts kI G G' P Cu) : 1 ≤ D.Λ := by
  have := hF.hΛ
  omega

theorem e1 (hF : StepFacts kI G G' P Cu) : G.level - 1 = G'.level := by
  have := hF.hlev
  omega

theorem hεn (hF : StepFacts kI G G' P Cu) : ∀ k, 0 ≤ D.eps k :=
  fun _ => (Construction.Stream.ocEpsilon_pos hF.hΛ1).le

theorem hεpos (hF : StepFacts kI G G' P Cu) (k : ℕ) : 0 < D.eps k :=
  Construction.Stream.ocEpsilon_pos hF.hΛ1

theorem hεle (hF : StepFacts kI G G' P Cu) (k : ℕ) : D.eps k ≤ 1 :=
  ocEpsilon_le_one hF.hΛ1 k

theorem heps_le (hF : StepFacts kI G G' P Cu) : D.eps G.level ≤ D.eps G'.level := by
  rw [hF.hlev]
  exact eps_succ_le hF.hq hF.hΛ _

theorem hτ (hF : StepFacts kI G G' P Cu) : 0 < ocTau D.α D.q D.Λ (G'.level + 1) :=
  Construction.Stream.ocTau_pos hF.hΛ1

theorem hκ' (hF : StepFacts kI G G' P Cu) : 0 < D.kap G'.level := by
  rw [← hF.e1]
  exact hF.hsc.hκ1

theorem hκκ (hF : StepFacts kI G G' P Cu) : D.kap G.level ≤ D.kap G'.level := by
  rw [← hF.e1]
  exact hF.hsc.hκle

theorem hη0 (hF : StepFacts kI G G' P Cu) : 0 ≤ D.kap G.level / D.kap (G.level - 1) :=
  div_nonneg hF.hsc.hκ0.le hF.hsc.hκ1.le

theorem hη1 (hF : StepFacts kI G G' P Cu) : D.kap G.level / D.kap (G.level - 1) ≤ 1 :=
  (div_le_one hF.hsc.hκ1).mpr hF.hsc.hκle

theorem hρE (hF : StepFacts kI G G' P Cu) : liftLength D G.level ≤ D.eps G'.level := by
  rw [← hF.e1]
  exact hF.hsc.hρE

theorem hDst0 (hF : StepFacts kI G G' P Cu) :
    0 ≤ ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) :=
  (hF.hεn _).trans hF.hsc.hεd

theorem hDst (hF : StepFacts kI G G' P Cu) :
    ocDStar D.q D.Λ G.level (D.kap G.level) (D.kap (G.level - 1)) ^ 2 =
      D.kap G'.level * D.cellScaleSq G.level := by
  rw [hF.hsc.hDst, hF.e1]

/-- The cost of a slow derivative on the lift length. -/
theorem hSl (hF : StepFacts kI G G' P Cu) {κc : MajConsts} {Δ : ℝ} {S : ℝ≥0}
    (hS : κc.Cslow / ENNReal.ofReal Δ ≤ S) :
    ENNReal.ofReal |liftLength D G.level| *
      (κc.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S :=
  (slow_le hF.hsc.hρ0.le hF.hsc.hρE (hF.hεpos _)).trans hS

/-- The identities of order at least three of the old stage have lengths at most its
wavelength. -/
theorem hℓ (hF : StepFacts kI G G' P Cu) (v u : CompIn G.comps) (γ : G.fam.Γ v u)
    (h3 : 3 ≤ (G.fam.identity v u γ).maxOrder) :
    (G.fam.identity v u γ).record.length ≤ D.eps G.level :=
  hF.hlen v u γ (by have := (G.fam.identity v u γ).le_birth; omega)

/-- The targets of the steps of a path have at least the reserve of its target. -/
theorem hres_path (hF : StepFacts kI G G' P Cu) {h : ℕ} (π : StagePath G h) (j : Fin h) :
    compReserve kI π.tgt ≤ compReserve kI (π.step j).1.1 :=
  compReserve_anti kI (stagePath_grade_step_le_tgt hF.hgrade π j)

end StepFacts
end

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger: the grades of the cascade and the reserves of the next family.**
* `grade_le_of_cascade`: every component of a stage of the cascade has grade at most `H` (the seed
  components have no births; the retained components have birth grade at most `H`);
* `grade_le_of_succ`: every component of an actual successor has grade at most `H + 1`;
* `compReserve_nonneg_of_succ`: with `H_prod = G₀ + H + 1`, every component of an actual successor
  has a nonnegative producer reserve;
* `one_le_succSchedD`: `D_H ≥ 1` for `H ≥ 1`. -/

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The components of a stage of the cascade have grade at most `H`.** -/
theorem grade_le_of_cascade {P : ProvParams} {Mn : SuccMenu} {seed : GenStage D hr Dm b j₀}
    (hseedB : ∀ v : CompIn seed.comps, v.1.births = []) {G : GenStage D hr Dm b j₀}
    (hG : IsCascadeStage D P Mn seed G) : ∀ v : CompIn G.comps, compGrade v.1 ≤ Mn.H := by
  induction hG with
  | seed =>
    intro v
    simp [compGrade, hseedB v]
  | @step G G' _ _ _ =>
    intro v
    exact (Finset.mem_filter.mp v.2).2.1

/-- **The components of an actual successor have grade at most `H + 1`.** -/
theorem grade_le_of_succ {P : ProvParams} {Mn : SuccMenu} {G G' : GenStage D hr Dm b j₀}
    (hG : ∀ v : CompIn G.comps, compGrade v.1 ≤ Mn.H) (hS : IsActualSuccessor D P Mn G G') :
    ∀ v : CompIn G'.comps, compGrade v.1 ≤ Mn.H + 1 := by
  obtain ⟨-, -, hc, -⟩ := hS
  rintro ⟨c, hv⟩
  rw [hc] at hv
  show compGrade c ≤ Mn.H + 1
  rcases Finset.mem_union.mp hv with h | h
  · exact (hG ⟨c, h⟩).trans (Nat.le_succ _)
  · obtain ⟨⟨x, t⟩, hx, he⟩ := Finset.mem_image.mp h
    rw [← he]
    have hxG := hG ⟨x, (Finset.mem_product.mp hx).1⟩
    by_cases ht : t = []
    · subst ht
      rw [compGrade_succComp_nil]
      dsimp only at hxG ⊢
      omega
    · rw [compGrade_succComp_ne _ _ ht]
      dsimp only at hxG ⊢
      omega

/-- **The components of an actual successor have a nonnegative producer reserve.** -/
theorem compReserve_nonneg_of_succ (kI : InvConsts) {H : ℕ} (hH : kI.Hprod = kI.G0 + H + 1)
    {c : Comp} (hc : compGrade c ≤ H + 1) : 0 ≤ compReserve kI c := by
  unfold compReserve
  have h1 : ((kI.G0 + compGrade c : ℕ) : ℝ) ≤ (kI.Hprod : ℝ) + 1 := by
    rw [hH]
    push_cast
    have : (compGrade c : ℝ) ≤ (H : ℝ) + 1 := by exact_mod_cast hc
    linarith
  have h2 : (0 : ℝ) < (kI.Hprod : ℝ) + 1 := by positivity
  have := (div_le_one h2).mpr h1
  linarith

/-- `D_H ≥ 1` for `H ≥ 1`. -/
theorem one_le_succSchedD (D₀ N p : ℕ) {H : ℕ} (hH : 1 ≤ H) : 1 ≤ succSchedD D₀ N p H := by
  obtain ⟨h, rfl⟩ : ∃ h, H = h + 1 := ⟨H - 1, by omega⟩
  simp only [succSchedD]
  omega

end AVRegularity.Providers.CascadeInvariants
end
