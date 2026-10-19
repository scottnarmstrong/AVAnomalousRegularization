-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.WeakGen.EddyEntry
import AVRegularity.Proofs.QuietAtlas.SummedTransition
import AVRegularity.Proofs.GenSem.LiftOn.Omega
public import AVRegularity.Proofs.QuietAtlas.FirstSourceRenewal
public import AVRegularity.Proofs.QuietAtlas.PiolaGeom
import AVRegularity.Applications.Global.CompactRangeMain

section
section
/-! **Weak entry, the entries of the eddy sources** (`weakEddyLedger`). An
identity of the outgoing stage whose source is the eddy letter of degree `n` has the record size
`ε_{i-1}^{-η₀} Pe_i²`, the length `ε_i` and the order `n` (`WeakPassageAt.eddy_record`). Its
coefficient is the transfer, with the normalization `λ = ε_{i-1}^{-η₀}`, of the eddy flux, whose
finer coefficients are graded slot family functions of size `|c_{n,d}| (d-1)! · π Pe_i ·
(Pe_i / C_pe) · B` in the eddy context (`eddySlotFam`). The ledger's transfer over that context
(`transferEntryGen`) and the leaf monotonicity (`genMode_le_of_leaf_dominates`) give the entry with
no leaf; the arithmetic is that of the ledger's tagged size with `d_* = ε_i`, `ρ = ε_{i-1}`, which gives
`Keddy · ε_{i-1}^{-η₀} Pe_i² (ε_i/ε_{i-1})^{n-2}`, `Keddy` depending on the request only. -/

@[expose] public noncomputable section

open Homogenization AVRegularity AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly
open scoped ENNReal NNReal

namespace AVRegularity.Providers.WeakGen

open GenSem CascadeInvariants Majorant

/-- The ledger's tagged size of a transferred path mean at `ℓ' = ρ = ε_i`, with any normalization. -/
theorem pm_le_lam (D : OCData) {i m n N : ℕ} {ρ K W c Wr lam FP : ℝ} (hnN : n ≤ N) (hK : 0 ≤ K)
    (hW : 0 ≤ W) (hc : 1 ≤ c) (hWr : 0 ≤ Wr) (hF : 0 ≤ FP) (hρ : 0 < ρ) (hκ : 0 < D.kap i)
    (hL : 0 < D.cellScaleSq m)
    (hD : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap i * D.cellScaleSq m)
    (hDst : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) (hρE : D.eps i = ρ) (hn : 2 ≤ n)
    {d : ℕ} (hd : 2 ≤ d) (hdN : d ≤ N) :
    Wr * pmBound D i m ρ n n K W c lam FP d ≤
      4 ^ N * ((N : ℝ) + 1) * c ^ N *
        (Wr * K * W * |lam| * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ (n - 2) * FP) := by
  have hE : 0 < D.eps i := hρE ▸ hρ
  have hR := pmBound_record_le D i m ρ (n := n) (Dγ := n) (Dm := N) hnN hK hW hc hWr hF hρ hκ
    hL hD hDst hE hρ hn d hd hdN (lam := lam) (Q := 1) zero_le_one
    (fun i' => by rw [hρE, div_self hρ.ne', one_pow, one_pow, one_mul])
  rw [hρE, div_self hρ.ne', one_pow, one_mul] at hR
  simp only [mul_one] at hR
  have h0 : 0 ≤ Wr * pmBound D i m ρ n n K W c lam FP d :=
    mul_nonneg hWr (pmBound_nonneg D i m ρ n n lam hK hW (by linarith) hE.le hF d)
  refine le_trans ?_ hR
  refine (Finset.single_le_sum (f := fun _ : Fin 2 => Wr * pmBound D i m ρ n n K W c lam FP d)
    (fun _ _ => h0) (Finset.mem_univ 0)).trans ?_
  exact Finset.single_le_sum (f := fun _ : DerivativeWord2 (d - 1) =>
      ∑ _c : Fin 2, Wr * pmBound D i m ρ n n K W c lam FP d)
    (fun _ _ => Finset.sum_nonneg fun _ _ => h0) (Finset.mem_univ (fun _ => 0))

/-- **The bound of one coefficient of an eddy identity**, abstractly. -/
theorem eddy_coeff_bound (D : OCData) {i m n N : ℕ} {ρ K W c Wr lam FP Kc Sz : ℝ} (hnN : n ≤ N)
    (hK : 0 ≤ K) (hW : 0 ≤ W) (hc : 1 ≤ c) (hWr : 0 ≤ Wr) (hF : 0 ≤ FP) (hρ : 0 < ρ)
    (hκ : 0 < D.kap i) (hL : 0 < D.cellScaleSq m)
    (hDst : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) = D.eps m)
    (hD : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 = D.kap i * D.cellScaleSq m)
    (hρE : D.eps i = ρ) (hn : 2 ≤ n) (hεm : 0 ≤ D.eps m)
    (hKS : 4 ^ N * ((N : ℝ) + 1) * c ^ N * (Wr * K * W) * (|lam| * FP) ≤ Kc * Sz)
    (hKS0 : 0 ≤ Kc * Sz) (d : ℕ) :
    Wr * (if 2 ≤ d then pmBound D i m ρ n n K W c lam FP d else 0) ≤
      Kc * Sz * (D.eps m / D.eps i) ^ (n - 2) := by
  have hE : 0 < D.eps i := hρE ▸ hρ
  have hratio : 0 ≤ (D.eps m / D.eps i) ^ (n - 2) := pow_nonneg (div_nonneg hεm hE.le) _
  have hRHS := mul_nonneg hKS0 hratio
  split_ifs with hd2
  swap
  · rw [mul_zero]; exact hRHS
  by_cases hdN : d ≤ N
  swap
  · rw [pmBound_eq_zero_of_lt _ _ _ _ _ _ _ _ _ _ (by omega), mul_zero]; exact hRHS
  refine (pm_le_lam D hnN hK hW hc hWr hF hρ hκ hL hD (by rw [hDst]; exact hεm) hρE hn hd2
    hdN).trans ?_
  rw [hDst, ← hρE]
  have hr0 : 0 ≤ (D.eps m / D.eps i) ^ (n - 2) := hratio
  calc 4 ^ N * ((N : ℝ) + 1) * c ^ N *
        (Wr * K * W * |lam| * (D.eps m / D.eps i) ^ (n - 2) * FP)
      = 4 ^ N * ((N : ℝ) + 1) * c ^ N * (Wr * K * W) * (|lam| * FP) *
          (D.eps m / D.eps i) ^ (n - 2) := by ring
    _ ≤ Kc * Sz * (D.eps m / D.eps i) ^ (n - 2) := mul_le_mul_of_nonneg_right hKS hr0

variable {plan : WeakCoefficientPlan}

/-- At a weak level the drift constant of the passage is the Péclet number. -/
theorem weakCd_eq_weakPe (x : WeakCoefficientInstance plan) {i : ℕ} (hi : x.M < i) :
    weakCd x i = x.D.weakPe i := by
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.hΛ]; have := case_Lambda_ge x; omega
  have hζ : IsFastProfile x.D.ζ := by rw [x.hζ]; exact x.base.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.hα, x.hq, x.hΛ, x.hζ, x.term]; exact x.band
  have hκ : 0 < x.D.kap i := EntryWeakProofs.weakData_kap_pos x.D hΛ1 hζ hband i
  have hkap : ∀ j, x.M ≤ j → x.D.kap j = x.D.κ x.M := fun j hj => by
    rw [EntryWeakProofs.weakData_kap_terminal x.D j (by rw [x.term]; exact hj), x.term]
  unfold weakCd OCData.weakPe
  rw [hkap (i - 1) (by omega), ← hkap i hi.le, Real.sqrt_mul_self hκ.le]

/-- **The record of an eddy identity**: the size `ε_{i-1}^{-η₀} Pe_i²`, the length `ε_i`, the
order `n`. -/
theorem WeakPassageAt.eddy_record (x : WeakPassageAt plan) (w : CaseWitness x)
    (v' u' : CompIn (x.stage (x.i - 1)).comps) (γ' : (x.stage (x.i - 1)).fam.Γ v' u')
    {v₀ : CompIn (x.stage x.i).comps} {wd : List WordLetter} {n : ℕ}
    (hs : (w.e v' u' γ').1 = .eddy v₀ wd n) :
    ((x.stage (x.i - 1)).fam.identity v' u' γ').record.size =
        x.inst.D.eps ((x.stage x.i).level - 1) ^ (-x.inst.physical.η₀) *
          x.inst.D.weakPe (x.stage x.i).level ^ 2 ∧
      ((x.stage (x.i - 1)).fam.identity v' u' γ').record.length =
        x.inst.D.eps (x.stage x.i).level ∧
      ((x.stage (x.i - 1)).fam.identity v' u' γ').maxOrder = n := by
  have ht := x.passage.2 v' u' γ'
  rw [w.prov v' u' γ', hs] at ht
  obtain ⟨⟨hsz, -, -, hlen, -, -⟩, hord⟩ := ht
  exact ⟨hsz, hlen, hord⟩

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- The sum of the grade-zero lift constants at the uniform constants, over the degrees
`≤ N₀`. -/
def eddyLB (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) : ℝ :=
  ∑ n' ∈ Finset.range (1 + A.Jw * A.Nw + 1),
    (liftB (constCtx (inhKappa B A) (inhData plan R).S (inhData plan R).Kg (inhData plan R).Kd)
      (1 + A.Jw * A.Nw) 0 n' : ℝ)

/-- **The constant map of the eddy ledger** (independent of the incoming constant: the eddy
letters do not read the incoming coefficients). -/
def Keddy (plan : WeakCoefficientPlan) : WeakConstFn := fun {B} {A} R _ =>
  4 ^ (1 + A.Jw * A.Nw) * (((1 + A.Jw * A.Nw : ℕ) : ℝ) + 1) *
    tConst (inhData plan R).K (inhData plan R).Cold (inhDelta A) ^ (1 + A.Jw * A.Nw) *
    ((inhData plan R).Wr * (inhData plan R).K * (inhData plan R).W) *
    (Real.pi / weakPeBound B * eddyLB plan R)

theorem Keddy_nonneg (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) (C : ℝ) :
    0 ≤ Keddy plan R C := by
  have h := (inhData plan R).h
  have hc := tConst_nonneg h.hK0 h.hC0 h.hΔ
  have hpe : 0 ≤ Real.pi / weakPeBound B :=
    div_nonneg Real.pi_pos.le (zero_le_one.trans (one_le_weakPeBound B))
  have hlb : 0 ≤ eddyLB plan R := Finset.sum_nonneg fun _ _ => NNReal.coe_nonneg _
  have hW := h.hWr0
  have hK := h.hK0
  have hW' := h.hW0
  unfold Keddy
  positivity

section Fine

/-- The edge-free lift data restricted to a smaller cap are the edge-free lift data of that cap. -/
theorem familyLiftData_empty_restrict {Dm N : ℕ} (hND : N ≤ Dm) (D : OCData) (m : ℕ) (k : ℤ)
    (A : RealChain) (ρ : ℝ) :
    restrictData hND (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A ρ
      (fun _ _ _ => [])) =
      familyLiftData (Dm := N) (hv := fun _ : Fin 1 => ℝ) D m k A ρ (fun _ _ _ => []) := by
  unfold restrictData familyLiftData
  congr 1


variable {D : OCData} {Dm : ℕ} {bw : ℝ} {j₀ : ℕ}
  {κ₁ : MajConsts} {Δ a₀ μ₀ : ℝ} {L₀ : ℕ} {S Kg Kd : ℝ≥0}

/-- **The finer outputs of an eddy source of a weak passage**, from lifts of a high reserve that
agree with the lifts of the passage at the grade `0`. -/
theorem eddyFineOfLifts (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκb : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) {G : GenStage D ScalarH Dm bw j₀}
    (v₀ : CompIn G.comps) (wd : List WordLetter) (n : ℕ)
    (CcI : ∀ s : WeakSource G, ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin (s.pathLen + 1)) (fun _ => ℝ))
    (Cc0 Cc0' : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) {N₀ R Nl : ℕ}
    (hND : N₀ ≤ Dm) (hNl : Nl ≤ N₀) (hNR : Nl + N₀ + 2 ≤ R)
    (hL0 : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D bw j₀ G.level k A →
      IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A
          (D.eps (G.level - 1)) (fun _ _ _ => []))
        R R (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Nl 0
        (Cc0' k A))
    (hAg : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D bw j₀ G.level k A →
      ∀ τ ∈ liftWindowOf D G.level k, ∀ n' m' (α : DerivativeWord2 m') X z v u,
        Cc0' k A 0 n' m' α τ X z v u = Cc0 k A 0 n' m' α τ X z v u)
    (hX₁ : (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd).Ok)
    (hSl : ENNReal.ofReal |D.eps (G.level - 1)| *
      (κ₁.Cslow / ENNReal.ofReal (D.eps (G.level - 1) * Δ)) ≤ S)
    (hη0 : 0 ≤ D.kap G.level / D.kap (G.level - 1))
    (hη1 : D.kap G.level / D.kap (G.level - 1) ≤ 1)
    (hL₀ : UEnv.liftWt N₀ 0 Nl ≤ L₀) (hn : 2 ≤ n) (hLn : n - 1 ≤ L₀) (ha₀ : 0 ≤ a₀)
    {κ : MajConsts} {Dd lam : ℝ≥0} (hl0 : (lam : ℝ≥0∞) ≠ 0) (hl1 : (lam : ℝ≥0∞) ≤ 1)
    (hd : ∀ c h, κ.drift c h ≤ lam * κ₁.drift c h)
    (hg : ∀ L h, κ.geo .own L h ≤ κ₁.geo .own L h) (hg0 : ∀ L h, h ≠ 0 → κ.geo .own L h = 0)
    (hCold : κ.Cold ≤ κ₁.Cold) (hCslow : κ.Cslow ≤ κ₁.Cslow)
    (hDd : ∀ c h, κ.drift c h ≤ if h = 0 then 0 else (Dd : ℝ≥0∞))
    (k : ℤ) (hk : Odd k) (d₁ : ℕ) (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) :
    SlotFamRepP D bw j₀ (fun {_ _} _ => False) G.level k
      (eddyCtx D (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) κ G.level)
      (fun t A => fluxCoeff ((WeakSource.eddy v₀ wd n).fluxOp (D.eps (G.level - 1))
        (CcI (.eddy v₀ wd n)) Cc0 k t A) d₁ I₁ 0 i₀)
      (n - 1 - (d₁ - 1))
      (Real.toNNReal |LiftGenSetup.pathMeanPref D G.level (D.eps (G.level - 1)) n d₁| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d₁ - 1)))).card : ℝ≥0) *
          (Dd * lam * liftB (topCtx κ₁ Δ a₀ μ₀ L₀ S Kg Kd) N₀ 0 (n - 1)))) := by
  have hc := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκb G.level
  have hlift : ∀ A, IsAdmissibleChain D bw j₀ G.level k A →
      IsLiftSequence (familyLiftData (Dm := N₀) (hv := fun _ : Fin 1 => ℝ) D G.level k A
          (D.eps (G.level - 1)) (fun _ _ _ => []))
        R R (D.slotStart G.level k / D.cellScaleSq G.level)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) Nl 0
        (Cc0' k A) := fun A hA => by
    rw [← familyLiftData_empty_restrict hND]
    exact isLiftSequence_restrict hND (fun _ _ _ _ => rfl) (Cc0' k A) hNl (hL0 k A hk hA)
  refine (eddySlotFam hΛ hζ hκb G.level k hk (Cc0' k) hNR hlift hX₁ hSl hη0 hη1 hL₀ hn hLn ha₀ hl0
    hl1 hd hg hg0 hCold hCslow hDd d₁ I₁ i₀).congr fun A hA t ht => ?_
  have hτ := inv_mul_mem_liftWindowOf hc ht
  have hcross : weakEddyFlux D G.level (D.eps (G.level - 1))
      (familyLiftData (Dm := N₀) (hv := fun _ : Fin 1 => ℝ) D G.level k A (D.eps (G.level - 1))
        (fun _ _ _ => [])) (Cc0' k A) n t =
      weakEddyFlux D G.level (D.eps (G.level - 1))
      (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A (D.eps (G.level - 1))
        (fun _ _ _ => [])) (Cc0' k A) n t := rfl
  have hfo : (WeakSource.eddy v₀ wd n).fluxOp (D.eps (G.level - 1)) (CcI (.eddy v₀ wd n)) Cc0 k t A =
      weakEddyFlux D G.level (D.eps (G.level - 1))
        (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D G.level k A (D.eps (G.level - 1))
          (fun _ _ _ => [])) (Cc0 k A) n t := by
    unfold WeakSource.fluxOp
    rw [dite_eq_left ⟨hA, hk⟩]
  rw [hcross, hfo]
  unfold fluxCoeff
  rw [weakEddyFlux_congr0 D G.level _ rfl rfl n t
    (fun m' α z => funext fun v => funext fun u => hAg k A hk hA _ hτ (n - 1) m' α 0 z v u)]

end Fine

section Consts

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- The context of the uniform constants is admissible. -/
theorem topCtx_inh_ok (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) {μ : ℝ} {L : ℕ}
    (hμ : μ ≤ 2) (hL : L ≤ inhLmax plan R) :
    (topCtx (inhKappa B A) (inhDelta A) (3 * Real.pi * A.bw) μ L (inhData plan R).S
      (inhData plan R).Kg (inhData plan R).Kd).Ok where
  hΔ := (inhDelta_pos A).le
  hμ := hμ
  hleaf := fun s i p e hs => by
    cases e with
    | geo fr L => exact absurd rfl hs
    | evalChild => exact absurd rfl hs
    | _ => rfl
  hgeo := fun _ _ _ => rfl
  hKg := fun L' hL' => (inhData plan R).h.hKg L' (hL'.trans hL)
  hKd := fun k L' hL' => (inhData plan R).h.hKd k L' (hL'.trans hL)
  hT := fun t => Set.mem_univ t

variable {plan : WeakCoefficientPlan}

theorem weakCd_pos (x : WeakCoefficientInstance plan) (i : ℕ) : 0 < weakCd x i := by
  have hΛ1 : 1 ≤ x.D.Λ := by rw [x.hΛ]; have := case_Lambda_ge x; omega
  have hζ : IsFastProfile x.D.ζ := by rw [x.hζ]; exact x.base.hζ
  have hband : IsOCBandChain x.D.α x.D.q x.D.Λ x.D.ζ x.D.term x.D.κ := by
    rw [x.hα, x.hq, x.hΛ, x.hζ, x.term]; exact x.band
  have hk := EntryWeakProofs.weakData_kap_pos x.D hΛ1 hζ hband
  unfold weakCd
  exact div_pos (Real.rpow_pos_of_pos (Construction.Stream.ocEpsilon_pos hΛ1) _)
    (Real.sqrt_pos.mpr (mul_pos (hk i) (hk (i - 1))))

/-- **The drift profiles of a weak passage are `λ = Pe/C_pe` times the uniform ones.** -/
theorem weakKappa_drift_scale (x : WeakCoefficientInstance plan) (i : ℕ) (c : Fin 2) (h : ℤ) :
    (weakKappa x i).drift c h ≤
      (Real.toNNReal (weakCd x i / weakPeBound x.base) : ℝ≥0∞) *
        (inhKappa x.base x.physical).drift c h := by
  have hC : 0 < weakPeBound x.base := zero_lt_one.trans_le (one_le_weakPeBound _)
  have hP := weakCd_pos x i
  simp only [weakKappa, inhKappa, ComplexContext.complexContextKappa]
  split_ifs
  · change ENNReal.ofReal _ ≤ ENNReal.ofReal _ * ENNReal.ofReal _
    rw [← ENNReal.ofReal_mul (div_nonneg hP.le hC.le)]
    refine ENNReal.ofReal_le_ofReal (le_of_eq ?_)
    rw [div_mul_eq_mul_div, eq_div_iff hC.ne']
    ring
  · exact zero_le

theorem weakKappa_drift_le (x : WeakCoefficientInstance plan) (i : ℕ) (c : Fin 2) (h : ℤ) :
    (weakKappa x i).drift c h ≤
      if h = 0 then 0 else (Real.toNNReal (Real.pi * weakCd x i) : ℝ≥0∞) := by
  simp only [weakKappa, ComplexContext.complexContextKappa]
  split_ifs with h1 h2
  · omega
  · exact le_of_eq (by rw [ENNReal.ofReal])
  · exact zero_le
  · exact zero_le

theorem weakKappa_geo_own (x : WeakCoefficientInstance plan) (i : ℕ) (L : GeoLetter) (h : ℤ) :
    (weakKappa x i).geo .own L h = (inhKappa x.base x.physical).geo .own L h := rfl

theorem weakKappa_geo_own_zero (x : WeakCoefficientInstance plan) (i : ℕ) (L : GeoLetter) {h : ℤ}
    (hh : h ≠ 0) : (weakKappa x i).geo .own L h = 0 := by
  simp only [weakKappa, ComplexContext.complexContextKappa]
  cases L <;> simp [hh]

end Consts

section Entry

/-- The means of another level are not leaves. -/
theorem leafMeanAt_of_ne (D : OCData) (κ : MajConsts) (Δ : ℝ) {m i : ℕ} (hne : i ≠ m)
    {s : GenSort} {p : ℤ} (e : Gen s i p) : leafMeanAt D κ Δ m e = none := by
  cases e <;> simp [leafMeanAt, hne]

/-- The algebra of the eddy constant: `λ π Pe (Pe/C_pe) B ≤ (π/C_pe) B' λ Pe²`. -/
theorem eddy_KS_le {Z E P P' Cpe LB : ℝ} {lb : ℝ≥0} (hZ : 0 ≤ Z) (hE : 0 ≤ E) (hP : 0 ≤ P)
    (hC : 0 < Cpe) (hPP : P = P') (hLb : (lb : ℝ) ≤ LB) :
    Z * (|E| * ((Real.toNNReal (Real.pi * P) * Real.toNNReal (P / Cpe) * lb : ℝ≥0) : ℝ)) ≤
      Z * (Real.pi / Cpe * LB) * (E * P' ^ 2) := by
  subst hPP
  rw [abs_of_nonneg hE, NNReal.coe_mul, NNReal.coe_mul,
    Real.coe_toNNReal _ (mul_nonneg Real.pi_pos.le hP), Real.coe_toNNReal _ (div_nonneg hP hC.le)]
  have h1 : Real.pi / Cpe * lb ≤ Real.pi / Cpe * LB :=
    mul_le_mul_of_nonneg_left hLb (div_nonneg Real.pi_pos.le hC.le)
  calc Z * (E * (Real.pi * P * (P / Cpe) * lb)) = Z * (Real.pi / Cpe * lb) * (E * P ^ 2) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hZ)
        (mul_nonneg hE (sq_nonneg P))

variable {B : WeakCoefficientBase} {A : WeakCoefficientPhysical B}

/-- The lift constant of the uniform context is one term of `eddyLB`. -/
theorem liftB_top_le_eddyLB (plan : WeakCoefficientPlan) (R : WeakCoefficientRequest A) {μ : ℝ}
    {L n : ℕ} (hn : n ≤ 1 + A.Jw * A.Nw) :
    (liftB (topCtx (inhKappa B A) (inhDelta A) (3 * Real.pi * A.bw) μ L (inhData plan R).S
      (inhData plan R).Kg (inhData plan R).Kd) (1 + A.Jw * A.Nw) 0 n : ℝ) ≤ eddyLB plan R := by
  have h : liftB (topCtx (inhKappa B A) (inhDelta A) (3 * Real.pi * A.bw) μ L (inhData plan R).S
      (inhData plan R).Kg (inhData plan R).Kd) (1 + A.Jw * A.Nw) =
      liftB (constCtx (inhKappa B A) (inhData plan R).S (inhData plan R).Kg (inhData plan R).Kd)
        (1 + A.Jw * A.Nw) :=
    liftB_congr (X := topCtx (inhKappa B A) (inhDelta A) (3 * Real.pi * A.bw) μ L
      (inhData plan R).S (inhData plan R).Kg (inhData plan R).Kd)
      (X' := constCtx (inhKappa B A) (inhData plan R).S (inhData plan R).Kg (inhData plan R).Kd)
      ⟨rfl, rfl, rfl⟩ _
  rw [h]
  exact Finset.single_le_sum (f := fun n' => (liftB (constCtx (inhKappa B A) (inhData plan R).S
      (inhData plan R).Kg (inhData plan R).Kd) (1 + A.Jw * A.Nw) 0 n' : ℝ))
    (fun _ _ => NNReal.coe_nonneg _) (Finset.mem_range.mpr (by omega))

variable {plan : WeakCoefficientPlan}

/-- **The ledger entry of an eddy identity.** -/
theorem weakEddy_entry (hplan : WeakComplexContextPlanOK plan) (hLw : WeakInhPlanOK plan)
    (hHR : WeakHighReserveLiftsStatement plan) (x : WeakPassageAt plan) {C : ℝ}
    (hW : WeakCertified C (weakReserve x.inst x.i) (weakWeight x.inst x.i) (x.stage x.i))
    (w : CaseWitness x) (v' u' : CompIn (x.stage (x.i - 1)).comps)
    (γ' : (x.stage (x.i - 1)).fam.Γ v' u') {v₀ : CompIn (x.stage x.i).comps}
    {wd : List WordLetter} {n : ℕ} (hs : (w.e v' u' γ').1 = .eddy v₀ wd n) :
    WeakLedgerEntry x (Keddy plan x.inst.request C) (weakReserve x.inst (x.i - 1))
      (weakWeight x.inst (x.i - 1)) v' u' γ' := by
  intro d I kk
  -- standing facts
  have hΛ : 128 ≤ x.inst.D.Λ := by rw [x.inst.hΛ]; exact case_Lambda_ge x.inst
  have hΛ1 : 1 ≤ x.inst.D.Λ := by omega
  have hζ : IsFastProfile x.inst.D.ζ := by rw [x.inst.hζ]; exact x.inst.base.hζ
  have hq : 1 < x.inst.D.q := by rw [x.inst.hq]; exact x.inst.base.hq.1
  have hκb : IsOCBandChain x.inst.D.α x.inst.D.q x.inst.D.Λ x.inst.D.ζ x.inst.D.term
      x.inst.D.κ := by
    rw [x.inst.hα, x.inst.hq, x.inst.hΛ, x.inst.hζ, x.inst.term]; exact x.inst.band
  have hb := x.inst.physical.bw_pos
  have hstart := (case_complexContextBase hplan x.inst 0).hstart
  have hεpos : ∀ k, 0 < x.inst.D.eps k := fun k => Construction.Stream.ocEpsilon_pos hΛ1
  have hεn : ∀ k, 0 ≤ x.inst.D.eps k := fun k => (hεpos k).le
  have hi := x.hi
  have hiJ := x.hiJ
  have hlevi : (x.stage x.i).level = x.i := x.pc.level x.i (by omega) hiJ
  have hlev' : (x.stage (x.i - 1)).level = x.i - 1 := x.pc.level (x.i - 1) le_rfl (by omega)
  have hκM : 0 < x.inst.D.κ x.inst.M := by
    have := EntryWeakProofs.weakData_kap_pos x.inst.D hΛ1 hζ hκb x.inst.M
    rwa [EntryWeakProofs.weakData_kap_terminal x.inst.D x.inst.M (by rw [x.inst.term]),
      x.inst.term] at this
  have hkap : ∀ j, x.inst.M ≤ j → x.inst.D.kap j = x.inst.D.κ x.inst.M := fun j hj => by
    rw [EntryWeakProofs.weakData_kap_terminal x.inst.D j (by rw [x.inst.term]; exact hj),
      x.inst.term]
  have hkapi : x.inst.D.kap (x.stage x.i).level = x.inst.D.κ x.inst.M := hkap _ (by omega)
  have hkapi' : x.inst.D.kap ((x.stage x.i).level - 1) = x.inst.D.κ x.inst.M :=
    hkap _ (by omega)
  have hkap' : x.inst.D.kap (x.stage (x.i - 1)).level = x.inst.D.κ x.inst.M := hkap _ (by omega)
  -- the source
  have hV := (w.e v' u' γ').2.1
  rw [hs] at hV
  obtain ⟨-, -, hn2, -⟩ := hV
  have hrec := x.eddy_record w v' u' γ' hs
  have hnN : n ≤ weakCap x.inst := by
    have := x.outgoing_maxOrder_le w v' u' γ'
    rwa [hrec.2.2] at this
  have hND : weakCap x.inst ≤ x.inst.Dm := x.inst.order
  have hN' := x.outgoing_maxOrder_le w
  -- the lifts of a high reserve
  obtain ⟨_, Cc0', _, hL0', _, hAg0⟩ := hHR x hW.weakHolGen w (2 * weakCap x.inst + 2)
  -- the constants
  have hLC : LedgerConsts x.inst.physical.bw (weakCap x.inst) (inhLmax plan x.inst.request)
      (weakKappa x.inst x.i) (inhData plan x.inst.request).a (inhDelta x.inst.physical)
      (inhData plan x.inst.request).K (inhData plan x.inst.request).W
      (inhData plan x.inst.request).Cold (inhData plan x.inst.request).Wr
      (inhData plan x.inst.request).S (inhData plan x.inst.request).Kg
      (inhData plan x.inst.request).Kd :=
    ledgerConsts_drift_mono (weakCd_le x.inst hi) (inhData plan x.inst.request).h
  have hJ : (0 : ℝ) < x.inst.physical.Jw := by exact_mod_cast x.inst.physical.Jw_pos
  have hres := weakReserve_mem x.inst hiJ
  have hres' := weakReserve_mem x.inst (i := x.i - 1) (by omega)
  have hstep : weakReserve x.inst x.i =
      weakReserve x.inst (x.i - 1) + 1 / x.inst.physical.Jw := by
    unfold weakReserve
    rw [show x.i - x.inst.M = (x.i - 1 - x.inst.M) + 1 by omega]
    push_cast
    ring
  have hNΔ : (weakCap x.inst : ℝ) * inhDelta x.inst.physical = 1 / x.inst.physical.Jw := by
    unfold inhDelta
    field_simp
  have hLo : weakWeight x.inst x.i ≤ inhLmax plan x.inst.request := by
    unfold weakWeight inhLmax
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hLn : weakWeight x.inst (x.i - 1) ≤ inhLmax plan x.inst.request := by
    unfold weakWeight inhLmax
    exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (by omega)) _
  have hLs : (plan.constants x.inst.request).kW.Lstar ≤ weakWeight x.inst x.i :=
    Nat.le_add_right _ _
  have hlw : UEnv.liftWt (weakCap x.inst) (x.inst.physical.Jw * x.inst.physical.Rw)
      (weakCap x.inst) ≤ weakWeight x.inst x.i := (hLw x.inst.request).trans hLs
  have hNw : x.inst.physical.Nw ≤ weakCap x.inst := by
    have := Nat.le_mul_of_pos_left x.inst.physical.Nw x.inst.physical.Jw_pos
    unfold weakCap; omega
  have hρpos := hεpos ((x.stage x.i).level - 1)
  have hη : x.inst.D.kap (x.stage x.i).level / x.inst.D.kap ((x.stage x.i).level - 1) = 1 := by
    rw [hkapi, hkapi', div_self hκM.ne']
  have hC : 0 < weakPeBound x.inst.base := zero_lt_one.trans_le (one_le_weakPeBound _)
  have hP := weakCd_pos x.inst x.i
  have hX₁ := topCtx_inh_ok plan x.inst.request hres.2 hLo
  -- the finer outputs
  have hfine := fun (k : ℤ) (hk : Odd k) (d₁ : ℕ) (_ : 1 ≤ d₁) (_ : d₁ ≤ n)
      (I₁ : DerivativeWord2 (d₁ - 1)) (i₀ : Fin 2) =>
    eddyFineOfLifts hΛ1 hζ hκb (G := x.stage x.i) v₀ wd n w.Cc w.Cc0 Cc0' hND hNw (by omega)
      hL0' hAg0 hX₁ ((slow_le hρpos.le le_rfl hρpos).trans (inhData plan x.inst.request).h.hS)
      (by rw [hη]; exact zero_le_one) (by rw [hη])
      ((GenSem.UEnv.liftWt_mono _ (Nat.zero_le _) hNw).trans hlw) hn2
      (le_trans (le_trans (Nat.sub_le n 1) (le_trans hnN (Nat.le_add_right _ _))) hlw)
      (mul_pos (mul_pos (by norm_num) Real.pi_pos) hb).le (κ := weakKappa x.inst x.i)
      (ENNReal.coe_ne_zero.mpr (Real.toNNReal_pos.mpr (div_pos hP hC)).ne')
      (ENNReal.coe_le_one_iff.mpr (Real.toNNReal_le_one.mpr
        ((div_le_one₀ hC).mpr (weakCd_le x.inst hi))))
      (weakKappa_drift_scale x.inst x.i) (fun L h => le_of_eq (weakKappa_geo_own x.inst x.i L h))
      (fun L _ hh => weakKappa_geo_own_zero x.inst x.i L hh) le_rfl le_rfl
      (weakKappa_drift_le x.inst x.i) k hk d₁ I₁ i₀
  -- the coefficient of the identity
  have hfl := w.flux v' u' γ'
  rw [hs] at hfl
  obtain ⟨e, hE, -, hsum⟩ := transferEntryGen hζ hΛ1 hb hstart
    ((x.stage (x.i - 1)).recap (weakCap x.inst) hN' noExports) (𝒮o := noExports)
    (fun _ he => False.elim he)
    (show (x.stage x.i).level = (x.stage (x.i - 1)).level + 1 by omega)
    (x.inst.D.eps ((x.stage x.i).level - 1)) n n
    (x.inst.D.eps ((x.stage x.i).level - 1) ^ (-x.inst.physical.η₀))
    ((WeakSource.eddy v₀ wd n).fluxOp (x.inst.D.eps ((x.stage x.i).level - 1))
      (w.Cc (.eddy v₀ wd n)) w.Cc0) γ'
    (fun p ctx d I t Y z hd => hfl p ctx d I t Y z hd) hnN
    (X := eddyCtx x.inst.D (topCtx (inhKappa x.inst.base x.inst.physical)
      (inhDelta x.inst.physical) (3 * Real.pi * x.inst.physical.bw) (weakReserve x.inst x.i)
      (weakWeight x.inst x.i) (inhData plan x.inst.request).S (inhData plan x.inst.request).Kg
      (inhData plan x.inst.request).Kd) (weakKappa x.inst x.i) (x.stage x.i).level)
    (fun t => Set.mem_univ t)
    (fun _ _ e => leafMeanAt_of_ne _ _ _
      (show (x.stage (x.i - 1)).level ≠ (x.stage x.i).level by omega) e)
    rfl (r := fun d₁ => n - 1 - (d₁ - 1)) (weakReserve x.inst (x.i - 1))
    (weakWeight x.inst (x.i - 1)) hfine
    (fun d₁ _ _ => by
      show weakReserve x.inst (x.i - 1) + ((n - 1 - (d₁ - 1) : ℕ) : ℝ) *
        inhDelta x.inst.physical ≤ weakReserve x.inst x.i
      have h1 : ((n - 1 - (d₁ - 1) : ℕ) : ℝ) * inhDelta x.inst.physical ≤
          (weakCap x.inst : ℝ) * inhDelta x.inst.physical :=
        mul_le_mul_of_nonneg_right
          (by exact_mod_cast (by omega : n - 1 - (d₁ - 1) ≤ weakCap x.inst)) (inhDelta_pos _).le
      linarith)
    (hεpos _) (Applications.eps_le_one hq hΛ) (Construction.Stream.ocTau_pos hΛ1) hLC.ha3 hLC.hΔ
    (by
      show weakReserve x.inst (x.i - 1) + (weakCap x.inst : ℝ) * inhDelta x.inst.physical ≤ 2
      linarith)
    hLC.hK0 hLC.hW0 hLC.hC0 hLC.hWr0 hLC.hK hLC.hW hLC.hCold
    ((wsum_mono_weight le_rfl hLn _).trans hLC.hWr) d I kk
  refine ⟨e, inhDelta x.inst.physical, leafNone, fun p => ⟨(hE p).1, (hE p).2.1⟩,
    ⟨fun p => Classical.choose (hE p).2.2, fun p => (Classical.choose_spec (hE p).2.2).1,
      fun p ctx t ht X z => (Classical.choose_spec (hE p).2.2).2 ctx t ht X z⟩,
    inhDelta_pos _, ⟨fun _ _ _ _ _ => rfl, fun _ _ _ _ hB => by simp at hB⟩,
    fun p => Gen.FromSeed.solvedFree_noExports leafNone (hE p).2.1,
    fun p => driftIn_ctx leafNone (e p)
      (by show x.i ≤ (x.stage (x.i - 1)).level + 1; rw [hlev']; omega), ?_⟩
  refine le_trans (ENNReal.tsum_le_tsum fun h => mul_le_mul' le_rfl
    (iSup_mono fun p => iSup₂_mono fun t _ =>
      genMode_le_of_leaf_dominates (D := x.inst.D) (Δ := inhDelta x.inst.physical)
        (weakKappa x.inst x.i)
        (leafMeanAt x.inst.D (weakKappa x.inst x.i) (inhDelta x.inst.physical) (x.stage x.i).level)
        (fun e B hB mres h t => leafMeanAt_dominates _ _ _ _ e B hB mres h t) (e p) _ h t))
    (hsum.trans (ENNReal.ofReal_le_ofReal ?_))
  -- the bound
  rw [hrec.1, hrec.2.1, hrec.2.2]
  have hρE : x.inst.D.eps (x.stage (x.i - 1)).level =
      x.inst.D.eps ((x.stage x.i).level - 1) := by rw [hlev', hlevi]
  have hDst : ocDStar x.inst.D.q x.inst.D.Λ (x.stage x.i).level
      (x.inst.D.kap (x.stage x.i).level) (x.inst.D.kap ((x.stage x.i).level - 1)) =
      x.inst.D.eps (x.stage x.i).level := by
    unfold ocDStar
    rw [hkapi, hkapi', div_self hκM.ne', Real.sqrt_one, mul_one]
    rfl
  have hD : ocDStar x.inst.D.q x.inst.D.Λ (x.stage x.i).level
      (x.inst.D.kap (x.stage x.i).level) (x.inst.D.kap ((x.stage x.i).level - 1)) ^ 2 =
      x.inst.D.kap (x.stage (x.i - 1)).level * x.inst.D.cellScaleSq (x.stage x.i).level := by
    rw [hDst, hkap']
    unfold OCData.cellScaleSq
    rw [hkapi]
    field_simp
  have hc := tConst_nonneg hLC.hK0 hLC.hC0 hLC.hΔ
  have hKS := eddy_KS_le (E := x.inst.D.eps ((x.stage x.i).level - 1) ^ (-x.inst.physical.η₀))
    (Z := 4 ^ weakCap x.inst * (((weakCap x.inst : ℕ) : ℝ) + 1) *
      tConst (inhData plan x.inst.request).K (inhData plan x.inst.request).Cold
        (inhDelta x.inst.physical) ^ weakCap x.inst *
      ((inhData plan x.inst.request).Wr * (inhData plan x.inst.request).K *
        (inhData plan x.inst.request).W))
    (mul_nonneg (mul_nonneg (mul_nonneg (by positivity) (by positivity)) (pow_nonneg hc _))
      (mul_nonneg (mul_nonneg hLC.hWr0 hLC.hK0) hLC.hW0))
    (Real.rpow_nonneg (hεn _) _) hP.le hC
    (P' := x.inst.D.weakPe (x.stage x.i).level) (by rw [weakCd_eq_weakPe x.inst hi, hlevi])
    (liftB_top_le_eddyLB plan x.inst.request (μ := weakReserve x.inst x.i)
      (L := weakWeight x.inst x.i) (n := n - 1) (by unfold weakCap at hnN; omega))
  exact eddy_coeff_bound x.inst.D hnN hLC.hK0 hLC.hW0 (one_le_tConst hLC.hK0 hLC.hC0 hLC.hΔ)
    hLC.hWr0 (NNReal.coe_nonneg _) hρpos
    (by show 0 < x.inst.D.kap (x.stage (x.i - 1)).level; rw [hkap']; exact hκM)
    (EntryWeakProofs.weakData_cellScaleSq_pos x.inst.D hΛ1 hζ hκb (x.stage x.i).level) hDst hD
    hρE hn2 (hεn _) hKS
    (mul_nonneg (Keddy_nonneg plan x.inst.request C)
      (mul_nonneg (Real.rpow_nonneg (hεn _) _) (sq_nonneg _))) d

/-- **The eddy ledger: the entries of the eddy sources**, with the constant map `Keddy`. -/
theorem weakEddyLedger (hplan : WeakComplexContextPlanOK plan) (hLw : WeakInhPlanOK plan)
    (hHR : WeakHighReserveLiftsStatement plan) : WeakEddyLedgerStatement plan (Keddy plan) := by
  intro x C _ hW
  refine ⟨Keddy_nonneg plan x.inst.request C, fun w v' u' γ' hne => ?_⟩
  generalize hs : (w.e v' u' γ').1 = s at hne
  cases s with
  | inherited => exact False.elim (hne trivial)
  | eddy v₀ wd n => exact weakEddy_entry hplan hLw hHR x hW w v' u' γ' hs

/-- **The weak ledger of one passage**, with the constant map `max Kinh Keddy`. -/
theorem weakPassageLedger (hplan : WeakComplexContextPlanOK plan) (hLw : WeakInhPlanOK plan)
    (hHR : WeakHighReserveLiftsStatement plan) :
    WeakPassageLedgerStatement plan (fun R C => max (Kinh plan R C) (Keddy plan R C)) :=
  weakPassageLedger_of_ingredients (Kinh plan) (Keddy plan) (weakInheritedLedger hplan hLw hHR)
    (weakEddyLedger hplan hLw hHR)

end Entry

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The data of the weak finer outputs read only the history** (the carried quiet invariant of
the weak passage, first part).
* `weakPassagePresentation`: the outgoing stage of a weak passage presented by transfers of its
  sources (`WeakPassageWitness.flux`).
* `FluxRecenterCovariant`: the flux at a label is the flux at the label `0` of the recentered
  context. Every presented stage has it (`fluxRecenterCovariant_of_presentation`).
* `flux_eq_of_histEq`: for a covariant stage with the carried history invariant, two contexts
  with the same history geometry give the same flux at every label where both recentered
  contexts are admissible.
* `familyLiftData_G_eq_of_histEq`: two families with the same history geometry have the same
  lift metric at every slow offset and at every time of their history. -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev Filter Topology

namespace AVRegularity.Providers.WeakGen

open QuietAtlas

variable {hr : ℕ → Type} [∀ r, NormedAddCommGroup (hr r)] [∀ r, InnerProductSpace ℝ (hr r)]
  {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- The flux at a label is the flux at the label `0` of the recentered context. -/
def FluxRecenterCovariant (G : GenStage D hr Dm b j₀) : Prop :=
  ∀ (p : OddSlot) (c : StageCtx D b j₀ G.level p) v u (γ : G.fam.Γ v u) d
    (I : DerivativeWord2 (d - 1)) t (Y z : Vec 2)
    (hadm : IsAdmissibleChain D b j₀ G.level p.1 (c.1.recenter D (D.eps (G.level - 1) • Y))),
    G.fam.flux p c v u γ d I t Y z = G.fam.flux p ⟨_, hadm⟩ v u γ d I t 0 z

theorem fluxRecenterCovariant_of_presentation (hζ : IsFastProfile D.ζ)
    (G : GenStage D hr Dm b j₀) (P : QuietPresentation G) : FluxRecenterCovariant G := by
  intro p c v u γ d I t Y z hadm
  by_cases hd : 2 ≤ d
  · rw [P.represents p c v u γ d I t Y z hd, P.represents p ⟨_, hadm⟩ v u γ d I t 0 z hd]
    have h0 : (c.1.recenter D (D.eps (G.level - 1) • Y)).recenter D (D.eps (G.level - 1) • 0) =
        c.1.recenter D (D.eps (G.level - 1) • Y) := by
      rw [smul_zero, GenSem.recenter_zero D hζ]
    have hadm' : IsAdmissibleChain D b j₀ G.level p.1
        ((c.1.recenter D (D.eps (G.level - 1) • Y)).recenter D (D.eps (G.level - 1) • 0)) := by
      rw [h0]; exact hadm
    rw [ite_eq_left_of_eq_true _ _ (eq_true hadm), ite_eq_left_of_eq_true _ _ (eq_true hadm'), h0]
  · rw [G.fam.flux_zero p c v u γ d I (fun h => hd h.1),
      G.fam.flux_zero p ⟨_, hadm⟩ v u γ d I (fun h => hd h.1)]

/-- A stage without identities is covariant. -/
theorem fluxRecenterCovariant_of_isEmpty (G : GenStage D hr Dm b j₀)
    (h : ∀ v u, IsEmpty (G.fam.Γ v u)) : FluxRecenterCovariant G :=
  fun _ _ v u γ => (h v u).elim γ

/-- A stage without identities has the carried history invariant. -/
theorem stageHistoryInvariant_of_isEmpty (G : GenStage D hr Dm b j₀) (Mtop : ℕ)
    (h : ∀ v u, IsEmpty (G.fam.Γ v u)) : StageHistoryInvariant G Mtop :=
  fun _ _ _ _ _ _ v u γ => (h v u).elim γ

/-- **Equal history geometry gives equal fluxes** wherever both recentered contexts are
admissible. -/
theorem flux_eq_of_histEq (hζ : IsFastProfile D.ζ) {G : GenStage D hr Dm b j₀} {Mtop : ℕ}
    (hcov : FluxRecenterCovariant G) (hinv : StageHistoryInvariant G Mtop) (p : OddSlot)
    {A A' : RealChain} (hA : IsAdmissibleChain D b j₀ G.level p.1 A)
    (hA' : IsAdmissibleChain D b j₀ G.level p.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level p.1)) {t : ℝ}
    (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1) (v u : CompIn G.comps)
    (γ : G.fam.Γ v u) (d : ℕ) (I : DerivativeWord2 (d - 1)) {Y : Vec 2}
    (hY : IsAdmissibleChain D b j₀ G.level p.1 (A.recenter D (D.eps (G.level - 1) • Y)))
    (hY' : IsAdmissibleChain D b j₀ G.level p.1 (A'.recenter D (D.eps (G.level - 1) • Y)))
    (z : Vec 2) :
    G.fam.flux p ⟨A, hA⟩ v u γ d I t Y z = G.fam.flux p ⟨A', hA'⟩ v u γ d I t Y z := by
  rw [hcov p ⟨A, hA⟩ v u γ d I t Y z hY, hcov p ⟨A', hA'⟩ v u γ d I t Y z hY']
  have hl : A.WellSlotted := hA.2.2.1
  have hl' : A'.WellSlotted := hA'.2.2.1
  have hrh := histEq_recenter D hζ hl hl' hh (D.eps (G.level - 1) • Y)
  have hsame := (histEq_iff_sameHistory D _ _ hrh.1).mp hrh
  exact (hinv p ⟨_, hY⟩ ⟨_, hY'⟩ hsame t ht v u γ d I z).eq_of_nhds

/-- **Equal history geometry gives the same lift metric.** -/
theorem familyLiftData_G_eq_of_histEq (hζ : IsFastProfile D.ζ) {A A' : RealChain}
    (hl : A.WellSlotted) (hl' : A'.WellSlotted) {I : Set ℝ}
    (hh : HistEq (A.geom D) (A'.geom D) I) {ι : Type*} {hv : ι → Type*}
    [∀ i, NormedAddCommGroup (hv i)] [∀ i, NormedSpace ℝ (hv i)] (m : ℕ) (k : ℤ) (ρ : ℝ)
    (edge edge' : ConstituentEdges Dm hv) {s : ℝ} (hs : D.cellScaleSq m * s ∈ I) (X : Vec 2) :
    (familyLiftData (ι := ι) D m k A' ρ edge').G s X =
      (familyLiftData (ι := ι) D m k A ρ edge).G s X := by
  have hrh := histEq_recenter D hζ hl hl' hh (ρ • X)
  funext a c
  simp only [familyLiftData, RealChain.famMetric, famJac_eq_of_histEq D hrh hs]

/-- **The presentation of the outgoing stage of a weak passage.** -/
def weakPassagePresentation {P : ProvParams} {Mn : WeakMenu} {rW : ℝ} {Din : ℕ}
    {G G' : GenStage D ScalarH Dm b j₀} (w : WeakPassageWitness P Mn rW Din G G')
    (hlev : G.level = G'.level + 1) : QuietPresentation G' where
  source v' u' γ' := .transfer ((w.e v' u' γ').1.lam G.level Mn.η0) (w.e v' u' γ').1.degree
    ((w.e v' u' γ').1.fluxOp (D.eps (G.level - 1)) (w.Cc (w.e v' u' γ').1) w.Cc0)
  represents p c v' u' γ' d I t Y z hd := by
    rw [w.flux v' u' γ' p c d I t Y z hd]
    simp only [QuietSource.array]
    have e : transferAt D G.level = transferAt D (G'.level + 1) := by rw [hlev]
    rw [e]

theorem weakPassagePresentation_allTransfer {P : ProvParams} {Mn : WeakMenu} {rW : ℝ}
    {Din : ℕ} {G G' : GenStage D ScalarH Dm b j₀} (w : WeakPassageWitness P Mn rW Din G G')
    (hlev : G.level = G'.level + 1) : (weakPassagePresentation w hlev).AllTransfer :=
  fun _ _ _ => ⟨_, _, _, rfl⟩

/-! ### The finer outputs -/

section Flux

variable {ι : Type*} [Fintype ι] {hv : ι → Type*} [∀ i, NormedAddCommGroup (hv i)]
  [∀ i, NormedSpace ℝ (hv i)]

/-- The slow flux reads the data only through its fields at the point. -/
theorem liftFluxX_data_point_congr (Q Q' : LiftOperatorData ι hv Dm) (hη : Q.η = Q'.η)
    (hvv : Q.v = Q'.v) (he : Q.edge = Q'.edge) (Cc : ℕ → ℕ → LiftCoeff ι hv)
    (f : ℝ → Vec 2 → ∀ i, hv i) (hh n : ℕ) (t : ℝ) (X : Vec 2) (hG : Q.G t X = Q'.G t X)
    (z : Vec 2) (k : Fin 2) :
    liftFluxX Q Cc f hh n t X z k = liftFluxX Q' Cc f hh n t X z k := by
  simp only [liftFluxX, hη, hvv, he, hG]

end Flux

/-- The slow offsets of both lift carriers. -/
theorem isOpen_ladderOmega (b : ℝ) (j₀ m : ℕ) (k : ℤ) (A : RealChain) (ρ : ℝ) :
    IsOpen (ladderOmega D b j₀ m k A ρ) :=
  (GenSem.isOpen_admissible_recenter D b j₀ m k A).preimage (continuous_const_smul ρ)

theorem zero_mem_ladderOmega (hζ : IsFastProfile D.ζ) {b : ℝ} {j₀ m : ℕ} {k : ℤ}
    {A : RealChain} (hA : IsAdmissibleChain D b j₀ m k A) (ρ : ℝ) :
    (0 : Vec 2) ∈ ladderOmega D b j₀ m k A ρ := by
  show IsAdmissibleChain D b j₀ m k (A.recenter D (ρ • 0))
  rw [smul_zero, GenSem.recenter_zero D hζ]
  exact hA

/-- **The lifted path edges agree on both carriers.** -/
theorem pathEdges_slowOpenEdgeEq (hζ : IsFastProfile D.ζ) {G : GenStage D ScalarH Dm b j₀}
    {Mtop : ℕ} (hcov : FluxRecenterCovariant G) (hinv : StageHistoryInvariant G Mtop)
    (k : OddSlot) {A A' : RealChain} (hA : IsAdmissibleChain D b j₀ G.level k.1 A)
    (hA' : IsAdmissibleChain D b j₀ G.level k.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level k.1)) {h : ℕ}
    (π : StagePath G h) {ρ : ℝ} (hε : D.eps (G.level - 1) ≠ 0) {U : Set (Vec 2)}
    (hU : U ⊆ ladderOmega D b j₀ G.level k.1 A ρ ∩ ladderOmega D b j₀ G.level k.1 A' ρ)
    {s : ℝ} (hs : D.cellScaleSq G.level * s ∈ ocPulseWindow D.α D.q D.Λ G.level k.1) :
    EntryWeakProofs.SlowOpenEdgeEq U s
      (liftEdges (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) (pathEdges G π k ⟨A', hA'⟩))
      (liftEdges (D.cellScaleSq G.level) (ρ / D.eps (G.level - 1)) (pathEdges G π k ⟨A, hA⟩)) := by
  intro v u d
  have hsc : ∀ X : Vec 2, D.eps (G.level - 1) • ((ρ / D.eps (G.level - 1)) • X) = ρ • X :=
    fun X => by rw [smul_smul, mul_div_cancel₀ _ hε]
  unfold liftEdges pathEdges
  split_ifs with hvu hd
  · simp only [List.map_cons, List.map_nil, List.forall₂_cons, List.forall₂_nil_left_iff,
      and_true]
    refine ⟨trivial, fun α X hX z => ?_⟩
    obtain ⟨hXA, hXA'⟩ := hU hX
    have hY : IsAdmissibleChain D b j₀ G.level k.1
        (A.recenter D (D.eps (G.level - 1) • ((ρ / D.eps (G.level - 1)) • X))) := by
      rw [hsc]; exact hXA
    have hY' : IsAdmissibleChain D b j₀ G.level k.1
        (A'.recenter D (D.eps (G.level - 1) • ((ρ / D.eps (G.level - 1)) • X))) := by
      rw [hsc]; exact hXA'
    exact (flux_eq_of_histEq hζ hcov hinv k hA hA' hh hs _ _ _ d.1 α hY hY' z).symm
  · exact List.Forall₂.nil
  · exact List.Forall₂.nil

theorem _root_.AVRegularity.Providers.QuietAtlas.HistEq.symm {g g' : ChainGeom} {I : Set ℝ}
    (h : HistEq g g' I) : HistEq g' g I :=
  ⟨h.1.symm, fun s hs w => (h.2 s hs w).symm⟩

/-- The times of the lift window are the times of the pulse window. -/
theorem mul_mem_ocPulseWindow {m : ℕ} {k : ℤ} (hc : 0 < D.cellScaleSq m) {s : ℝ}
    (hs : s ∈ liftWindowOf D m k) : D.cellScaleSq m * s ∈ ocPulseWindow D.α D.q D.Λ m k := by
  obtain ⟨h1, h2⟩ := hs
  rw [div_le_iff₀ hc] at h1
  rw [le_div_iff₀ hc] at h2
  exact ⟨by unfold OCData.slotStart at h1; linarith, by linarith⟩

/-- **The path-mean fluxes of two families with the same history agree as germs.** -/
theorem pathMeanFlux_germ_of_histEq (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    {G : GenStage D ScalarH Dm b j₀} (hc2 : 0 < D.cellScaleSq G.level) {Mtop : ℕ}
    (hcov : FluxRecenterCovariant G) (hinv : StageHistoryInvariant G Mtop) (k : OddSlot)
    {A A' : RealChain} (hA : IsAdmissibleChain D b j₀ G.level k.1 A)
    (hA' : IsAdmissibleChain D b j₀ G.level k.1 A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop G.level k.1)) {h : ℕ}
    (π : StagePath G h) (sX sZ sX' sZ' N : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ))
    (hc : IsLiftSequenceOn (ladderOmega D b j₀ G.level k.1 A (D.eps (G.level - 1)))
      (familyLiftData D G.level k.1 A (D.eps (G.level - 1)) (pathEdges G π k ⟨A, hA⟩)) sX sZ
      (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Cc)
    (hd : IsLiftSequenceOn (ladderOmega D b j₀ G.level k.1 A' (D.eps (G.level - 1)))
      (familyLiftData D G.level k.1 A' (D.eps (G.level - 1)) (pathEdges G π k ⟨A', hA'⟩)) sX'
      sZ' (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) N h Dc)
    (n : ℕ) (hn : 2 ≤ n) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1)
    (f : Vec 2 → ℝ) :
    pathMeanFlux D G.level (D.eps (G.level - 1))
        (familyLiftData D G.level k.1 A (D.eps (G.level - 1)) (pathEdges G π k ⟨A, hA⟩)) Cc n t f
      =ᶠ[𝓝 0] pathMeanFlux D G.level (D.eps (G.level - 1))
        (familyLiftData D G.level k.1 A' (D.eps (G.level - 1)) (pathEdges G π k ⟨A', hA'⟩)) Dc n
          t f := by
  set ρ := D.eps (G.level - 1) with hρ
  have hε : ρ ≠ 0 := (Construction.Stream.ocEpsilon_pos hΛ).ne'
  set U := ladderOmega D b j₀ G.level k.1 A ρ ∩ ladderOmega D b j₀ G.level k.1 A' ρ
  have hU : IsOpen U := (isOpen_ladderOmega b j₀ _ _ _ _).inter (isOpen_ladderOmega b j₀ _ _ _ _)
  have h0U : (0 : Vec 2) ∈ U := ⟨zero_mem_ladderOmega hζ hA ρ, zero_mem_ladderOmega hζ hA' ρ⟩
  have hl : A.WellSlotted := hA.2.2.1
  have hl' : A'.WellSlotted := hA'.2.2.1
  have hwin : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      D.cellScaleSq G.level * s ∈ ocPulseWindow D.α D.q D.Λ G.level k.1 :=
    fun s hs => mul_mem_ocPulseWindow hc2 hs
  have hav := ocPulseWindow_subset_availInterval D Mtop G.level k.1
  have hG : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level), ∀ X ∈ U,
      (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).G s X =
        (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)).G s X :=
    fun s hs X _ => familyLiftData_G_eq_of_histEq hζ hl hl' hh G.level k.1 ρ _ _ (hav (hwin s hs)) X
  have hE : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      EntryWeakProofs.SlowOpenEdgeEq U s
        (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).edge
        (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)).edge :=
    fun s hs => pathEdges_slowOpenEdgeEq hζ hcov hinv k hA hA' hh π hε le_rfl (hwin s hs)
  have hE' : ∀ s ∈ Set.Icc (D.slotStart G.level k.1 / D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level),
      EntryWeakProofs.SlowOpenEdgeEq U s
        (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)).edge
        (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).edge :=
    fun s hs => pathEdges_slowOpenEdgeEq hζ hcov hinv k hA' hA hh.symm π hε
      (fun X hX => ⟨hX.2, hX.1⟩) (hwin s hs)
  have hts : (D.cellScaleSq G.level)⁻¹ * t ∈ Set.Icc (D.slotStart G.level k.1 /
      D.cellScaleSq G.level)
      ((((k.1 : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ G.level) / D.cellScaleSq G.level) :=
    inv_mul_mem_liftWindowOf hc2 ht
  have hab := hts.1.trans hts.2
  have hcoef := familyLift_cross_unique D hζ G.level k.1 k.2 A A' ρ _ _ hU
    Set.inter_subset_left Set.inter_subset_right _ _ hab N h sX sZ sX' sZ' Cc Dc hc hd hG hE
  have hev : ∀ᶠ y in 𝓝 (0 : Vec 2), ρ⁻¹ • y ∈ U := by
    have htend : Filter.Tendsto (fun y : Vec 2 => ρ⁻¹ • y) (𝓝 0) (𝓝 0) := by
      simpa using (continuous_const_smul ρ⁻¹).tendsto (0 : Vec 2)
    exact htend (hU.mem_nhds h0U)
  filter_upwards [hev] with y hy
  have hz : ∀ z k', liftFluxX (familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩)) Cc
        (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
        ((D.cellScaleSq G.level)⁻¹ * t) (ρ⁻¹ • y) z k' =
      liftFluxX (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)) Dc
        (fun _ X => Pi.single (0 : Fin (h + 1)) (f (ρ • X))) h n
        ((D.cellScaleSq G.level)⁻¹ * t) (ρ⁻¹ • y) z k' := by
    intro z k'
    refine (EntryWeakProofs.liftFluxX_slow_open_congr_predecessors hU _ Cc Dc _ h n hn _
      (fun p q hpq m _ α X hX z v u => hcoef p (by omega) q m α _ hts X hX z v u) _ hy z
        k').trans ?_
    refine (EntryWeakProofs.liftFluxX_edge_slow_open_congr hU _ _ Dc _ h n _ (hE' _ hts) k' _
      hy z).trans ?_
    exact liftFluxX_data_point_congr
      (Q := {familyLiftData D G.level k.1 A ρ (pathEdges G π k ⟨A, hA⟩) with
        edge := (familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)).edge})
      (Q' := familyLiftData D G.level k.1 A' ρ (pathEdges G π k ⟨A', hA'⟩)) rfl rfl rfl Dc _ h n
      _ _ (hG _ hts _ hy).symm z k'
  unfold pathMeanFlux
  simp only [hz]

/-- **The eddy fluxes of two families with the same history agree as germs.** -/
theorem weakEddyFlux_germ_of_histEq (hζ : IsFastProfile D.ζ) {m : ℕ}
    (hc2 : 0 < D.cellScaleSq m) {Mtop : ℕ} {k : ℤ} (hk : Odd k) {A A' : RealChain}
    (hA : IsAdmissibleChain D b j₀ m k A) (hA' : IsAdmissibleChain D b j₀ m k A')
    (hh : HistEq (A.geom D) (A'.geom D) (availInterval D Mtop m k)) (sX sZ sX' sZ' N : ℕ)
    (Cc Dc : ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hc : IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A
        (D.eps (m - 1)) (fun _ _ _ => [])) sX sZ (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N 0 Cc)
    (hd : IsLiftSequence (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k A'
        (D.eps (m - 1)) (fun _ _ _ => [])) sX' sZ' (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) N 0 Dc)
    (n : ℕ) {t : ℝ} (ht : t ∈ ocPulseWindow D.α D.q D.Λ m k) (f : Vec 2 → ℝ) :
    weakEddyFlux D m (D.eps (m - 1)) (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m k
        A (D.eps (m - 1)) (fun _ _ _ => [])) Cc n t f =ᶠ[𝓝 0]
      weakEddyFlux D m (D.eps (m - 1)) (familyLiftData (Dm := Dm) (hv := fun _ : Fin 1 => ℝ) D m
        k A' (D.eps (m - 1)) (fun _ _ _ => [])) Dc n t f := by
  set ρ := D.eps (m - 1)
  have hl : A.WellSlotted := hA.2.2.1
  have hl' : A'.WellSlotted := hA'.2.2.1
  have hav := ocPulseWindow_subset_availInterval D Mtop m k
  have hts : (D.cellScaleSq m)⁻¹ * t ∈ Set.Icc (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m) :=
    inv_mul_mem_liftWindowOf hc2 ht
  have hcoef := familyLift_cross_unique D hζ m k hk A A' ρ (fun _ _ _ => [])
    (fun _ _ _ => []) isOpen_univ (Set.subset_univ _) (Set.subset_univ _) _ _
    (hts.1.trans hts.2) N 0 sX sZ sX' sZ' Cc Dc
    (WeakEntryProofs.liftSequenceOn_of_global Set.univ _ sX sZ _ _ N 0 Cc hc)
    (WeakEntryProofs.liftSequenceOn_of_global Set.univ _ sX' sZ' _ _ N 0 Dc hd)
    (fun s hs X _ => familyLiftData_G_eq_of_histEq hζ hl hl' hh m k ρ _ _
      (hav (mul_mem_ocPulseWindow hc2 hs)) X)
    (fun s _ v u d => by simp [familyLiftData, liftEdges])
  refine Filter.Eventually.of_forall fun y => ?_
  have ha : ∀ z, liftApply (n - 1) (Cc 0 (n - 1))
        (fun _ X => Pi.single (0 : Fin 1) (f (ρ • X))) ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z =
      liftApply (n - 1) (Dc 0 (n - 1))
        (fun _ X => Pi.single (0 : Fin 1) (f (ρ • X))) ((D.cellScaleSq m)⁻¹ * t) (ρ⁻¹ • y) z := by
    intro z
    funext v
    simp only [liftApply]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun α _ =>
      Finset.sum_congr rfl fun u _ => ?_
    rw [hcoef 0 le_rfl (n - 1) l α _ hts _ (Set.mem_univ _) z v u]
  unfold weakEddyFlux
  simp only [ha]
  rfl

/-- **The carried finer-operator invariant of a weak passage**, from the carried invariant and the
covariance of the incoming stage: the finer outputs are path means and eddy means of unique
lifts, whose data read only the history. -/
theorem weakPassage_finerHistory (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) {P : ProvParams}
    {Mn : WeakMenu} {rW : ℝ} {Din : ℕ} {G G' : GenStage D ScalarH Dm b j₀}
    (w : WeakPassageWitness P Mn rW Din G G') (hlev : G.level = G'.level + 1)
    (hc2 : 0 < D.cellScaleSq G.level) {Mtop : ℕ} (hcov : FluxRecenterCovariant G)
    (hinv : StageHistoryInvariant G Mtop) :
    FinerHistoryInvariant G' (weakPassagePresentation w hlev) Mtop := by
  intro v' u' γ' n _ k ch ch' hsame t ht f
  obtain ⟨hV, -, -⟩ := (w.e v' u' γ').2
  simp only [weakPassagePresentation, QuietSource.finer]
  have hA : IsAdmissibleChain D b j₀ G.level k.1 ch.1 := by rw [hlev]; exact ch.2
  have hA' : IsAdmissibleChain D b j₀ G.level k.1 ch'.1 := by rw [hlev]; exact ch'.2
  have ht' : t ∈ ocPulseWindow D.α D.q D.Λ G.level k.1 := by rw [hlev]; exact ht
  have hanc : (ch.1.geom D).2.2 = (ch'.1.geom D).2.2 := by
    rw [geom_anchor D ch.1 ch.2.2.2.1, geom_anchor D ch'.1 ch'.2.2.2.1, ch.2.1, ch.2.2.2.2.1,
      ch'.2.1, ch'.2.2.2.2.1]
  have hh : HistEq (ch.1.geom D) (ch'.1.geom D) (availInterval D Mtop G.level k.1) := by
    rw [hlev]
    exact (histEq_iff_sameHistory D _ _ hanc).mpr hsame
  generalize (w.e v' u' γ').1 = s at hV ⊢
  cases s with
  | inherited wd h π n' =>
    obtain ⟨-, -, hn2, -⟩ := hV
    unfold WeakSource.fluxOp
    rw [dite_eq_left ⟨hA, k.2⟩, dite_eq_left ⟨hA', k.2⟩]
    exact pathMeanFlux_germ_of_histEq hζ hΛ hc2 hcov hinv k hA hA' hh π Mn.sX Mn.sZ Mn.sX Mn.sZ
      Mn.N _ _ ((w.lifts (.inherited wd h π n')) k.1 ch.1 ⟨hA, k.2⟩)
      ((w.lifts (.inherited wd h π n')) k.1 ch'.1 ⟨hA', k.2⟩) n' hn2 ht' f
  | eddy v₀ wd n' =>
    unfold WeakSource.fluxOp
    rw [dite_eq_left ⟨hA, k.2⟩, dite_eq_left ⟨hA', k.2⟩]
    exact weakEddyFlux_germ_of_histEq hζ hc2 k.2 hA hA' hh Mn.sX Mn.sZ Mn.sX Mn.sZ Mn.N _ _
      (w.lifts0 k.1 ch.1 k.2 hA) (w.lifts0 k.1 ch'.1 k.2 hA') n' ht' f

end AVRegularity.Providers.WeakGen
end
end
end

section
section
/-! **The quiet atlas of the weak stage** (weak entry:
`WeakStageQuietAtlasStatement` for the root encodings).
* `weakConstruction_history`: down a weak construction, every stage has the carried history
  invariant and the recentering covariance. The root has no identity. Each passage passes the
  invariant to its finer outputs (`weakPassage_finerHistory`), and the transfer stage keeps it
  (`quietHistoryPreservation_of_allTransfer_core`).
* The passage into the stage `M` presents it by transfers, with the carried finer invariant.
  The presentation and the finer invariant pass to the relabeled and scaled root encoding, whose
  identities and fluxes are those of the stage `M`, reindexed.
* `weakStageQuietAtlas`: the atlas clauses follow (`quietAtlas_of_allTransfer`). The plan
  condition is that of the carrier calculus (`WeakComplexContextPlanOK`: `j₀ + 2 ≤ M`, `1 ≤ CH`, `Υ ≥ 100`). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev AVRegularity.WeakEntryProofs.Assembly

namespace AVRegularity.Providers.WeakGen

open QuietAtlas WeakEntryProofs

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-! ### Down the construction -/

/-- **Every stage of a weak construction carries the history invariant and the covariance.** -/
theorem weakConstruction_history (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (hcell : ∀ m, 0 < D.cellScaleSq m) {P : ProvParams} {Mn : WeakMenu} {M J : ℕ} {rW : ℝ}
    {r : ℕ} {stage : ℕ → GenStage D ScalarH Dm b j₀}
    (hc : IsWeakConstruction D P Mn M J rW r stage) :
    ∀ n, n ≤ J → StageHistoryInvariant (stage (M + J - n)) (M + J) ∧
      FluxRecenterCovariant (stage (M + J - n))
  | 0, _ => by
    have hr := hc.2.1
    simp only [Nat.sub_zero]
    exact ⟨stageHistoryInvariant_of_isEmpty _ _ hr.2.2.1,
      fluxRecenterCovariant_of_isEmpty _ hr.2.2.1⟩
  | n + 1, hn => by
    obtain ⟨ihinv, ihcov⟩ := weakConstruction_history hΛ hζ hb hstart hcell hc n (by omega)
    have hi : M < M + J - n := by omega
    have hit : M + J - n ≤ M + J := by omega
    have hpass := (hc.2.2 (M + J - n) hi hit).1
    rw [show M + J - (n + 1) = M + J - n - 1 by omega]
    obtain ⟨w⟩ := IsWeakPassage.witness hpass
    have hlv := EntryWeakProofs.weakConstruction_level P Mn M J r rW stage hc
    have hlev : (stage (M + J - n)).level = (stage (M + J - n - 1)).level + 1 := by
      rw [hlv _ hi.le hit, hlv _ (by omega) (by omega)]
      omega
    have hfiner := weakPassage_finerHistory hζ hΛ w hlev (hcell _) ihcov ihinv
    have hlt : (stage (M + J - n - 1)).level < M + J := by
      rw [hlv _ (by omega) (by omega)]
      omega
    exact ⟨quietHistoryPreservation_of_allTransfer_core hΛ hζ hb hstart _
      (weakPassagePresentation w hlev) (M + J) hlt (weakPassagePresentation_allTransfer w hlev)
      hfiner, fluxRecenterCovariant_of_presentation hζ _ (weakPassagePresentation w hlev)⟩

/-- **The stage `M` is presented by transfers, with the carried finer invariant.** -/
theorem weakConstruction_stage_presentation (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hb : 0 < b)
    (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
      2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ b / (64 * (8 * Real.pi ^ 2)))
    (hcell : ∀ m, 0 < D.cellScaleSq m) {P : ProvParams} {Mn : WeakMenu} {M J : ℕ} {rW : ℝ}
    {r : ℕ} {stage : ℕ → GenStage D ScalarH Dm b j₀}
    (hc : IsWeakConstruction D P Mn M J rW r stage) (hJ : 1 ≤ J) :
    ∃ Q : QuietPresentation (stage M), Q.AllTransfer ∧
      FinerHistoryInvariant (stage M) Q (M + J) := by
  obtain ⟨ihinv, ihcov⟩ := weakConstruction_history hΛ hζ hb hstart hcell hc (J - 1) (by omega)
  rw [show M + J - (J - 1) = M + 1 by omega] at ihinv ihcov
  have hpass := (hc.2.2 (M + 1) (by omega) (by omega)).1
  obtain ⟨w⟩ := IsWeakPassage.witness hpass
  have hlv := EntryWeakProofs.weakConstruction_level P Mn M J r rW stage hc
  have hlev : (stage (M + 1)).level = (stage (M + 1 - 1)).level + 1 := by
    rw [hlv _ (by omega) (by omega), hlv _ (by omega) (by omega)]
    omega
  exact ⟨weakPassagePresentation w hlev, weakPassagePresentation_allTransfer w hlev,
    weakPassage_finerHistory hζ hΛ w hlev (hcell _) ihcov ihinv⟩

/-! ### The root encoding -/

/-- **The quiet atlas of the weak stage** for the root encodings. -/
theorem weakStageQuietAtlas {plan : WeakCoefficientPlan} (hplan : WeakComplexContextPlanOK plan)
    (Cθ : WeakCoefficientCase plan → ℝ) (hCθ : ∀ c, 1 ≤ Cθ c)
    (exports : WeakCoefficientCase plan → SeedExports) :
    WeakStageQuietAtlasStatement plan (weakRootEncodingChoice plan Cθ hCθ exports) := by
  intro c w
  dsimp only
  -- standing facts
  have hΛ' : 128 ≤ c.inst.D.Λ := by rw [c.inst.hΛ]; exact case_Lambda_ge c.inst
  have hΛ : 1 ≤ c.inst.D.Λ := by omega
  have hζ : IsFastProfile c.inst.D.ζ := by rw [c.inst.hζ]; exact c.inst.base.hζ
  have hκb : IsOCBandChain c.inst.D.α c.inst.D.q c.inst.D.Λ c.inst.D.ζ c.inst.D.term
      c.inst.D.κ := by
    rw [c.inst.hα, c.inst.hq, c.inst.hΛ, c.inst.hζ, c.inst.term]; exact c.inst.band
  have hb := c.inst.physical.bw_pos
  have hcarrier : IsCarrierStart c.inst.D.α c.inst.D.q c.inst.D.Λ c.inst.physical.bw
      (plan.constants c.inst.request).CH (plan.constants c.inst.request).Υ c.inst.j₀ := by
    rw [c.inst.hα, c.inst.hq, c.inst.hΛ]; exact c.inst.carrier
  have hok := hplan.1 c.inst.request
  have hCH : 1 ≤ (plan.constants c.inst.request).CH := hok.1
  have hΥ : 1 ≤ (plan.constants c.inst.request).Υ :=
    le_trans (by norm_num) ((le_max_left _ _).trans hok.2)
  have hstart := GenSem.startBound_of_carrierStart hΛ hCH hΥ hcarrier
  have hcell : ∀ m, 0 < c.inst.D.cellScaleSq m :=
    fun m => EntryWeakProofs.weakData_cellScaleSq_pos c.inst.D hΛ hζ hκb m
  have hJ : 1 ≤ c.inst.physical.Jw := c.inst.physical.Jw_pos
  have hlvl := (hplan.2 c.inst.request c.inst.j₀).trans c.inst.level_large
  have hc := c.construction
  -- the stage `M`
  obtain ⟨Q, hall, hF⟩ := weakConstruction_stage_presentation hΛ hζ hb hstart hcell hc hJ
  have hlv := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ hc c.inst.M le_rfl
    (by omega)
  have hpass := (hc.2.2 (c.inst.M + 1) (by omega) (by omega)).1
  have hnatM : (c.stage c.inst.M).IsNatural (c.inst.M + c.inst.physical.Jw) := by
    have h := hpass.2.2.2.2.1
    rwa [hc.1] at h
  -- the root encoding
  set S := weakRootComps (c.stage c.inst.M).comps
  set e := weakRootEquiv (c.stage c.inst.M).comps
  let Qe : QuietPresentation (weakRootEncodingChoice plan Cθ hCθ exports c).stage :=
    ⟨fun v u γ => Q.source (e.symm v) (e.symm u) γ,
      fun p ch v u γ d I t Y z hd => Q.represents p ch (e.symm v) (e.symm u) γ d I t Y z hd⟩
  have halle : Qe.AllTransfer := fun v u γ => hall (e.symm v) (e.symm u) γ
  have hFe : FinerHistoryInvariant (weakRootEncodingChoice plan Cθ hCθ exports c).stage Qe
      (c.inst.M + c.inst.physical.Jw) :=
    fun v u γ n hn k ch ch' hs t ht f => hF (e.symm v) (e.symm u) γ n hn k ch ch' hs t ht f
  have hnate : (weakRootEncodingChoice plan Cθ hCθ exports c).stage.IsNatural
      (c.inst.M + c.inst.physical.Jw) :=
    (weakConstruction_scaledRootLaws _ _ _ _ _ _ _ hc hJ (Cθ c) (hCθ c)).1 hnatM
  have hlve : (weakRootEncodingChoice plan Cθ hCθ exports c).stage.level = c.inst.M := hlv
  exact quietAtlas_of_allTransfer hb hΛ hζ _ Qe halle _ _ (by rw [hlve]; omega)
    (by rw [hlve]; omega) _ _ hCH hcarrier hnate hFe

/-- **The independence clause of the weak stage** (on the trimmed quiet times) for the
root encodings: transversality on the enlarged pulses and fast independence, from the quiet
matching of the transfer stage at the history-quiet set `ocTrimmedQuietTimes`. The slot
transversality of the bottom stage is the input `hT`. -/
theorem weakStageIndependence {plan : WeakCoefficientPlan} (hplan : WeakComplexContextPlanOK plan)
    (Cθ : WeakCoefficientCase plan → ℝ) (hCθ : ∀ c, 1 ≤ Cθ c)
    (exports : WeakCoefficientCase plan → SeedExports)
    (hT : ∀ c : WeakCoefficientCase plan, (c.stage c.inst.M).IsSlotTransverse) :
    WeakStageIndependenceStatement plan (weakRootEncodingChoice plan Cθ hCθ exports) := by
  intro c w
  dsimp only
  -- standing facts
  have hΛ' : 128 ≤ c.inst.D.Λ := by rw [c.inst.hΛ]; exact case_Lambda_ge c.inst
  have hΛ : 1 ≤ c.inst.D.Λ := by omega
  have hζ : IsFastProfile c.inst.D.ζ := by rw [c.inst.hζ]; exact c.inst.base.hζ
  have hκb : IsOCBandChain c.inst.D.α c.inst.D.q c.inst.D.Λ c.inst.D.ζ c.inst.D.term
      c.inst.D.κ := by
    rw [c.inst.hα, c.inst.hq, c.inst.hΛ, c.inst.hζ, c.inst.term]; exact c.inst.band
  have hb := c.inst.physical.bw_pos
  have hcarrier : IsCarrierStart c.inst.D.α c.inst.D.q c.inst.D.Λ c.inst.physical.bw
      (plan.constants c.inst.request).CH (plan.constants c.inst.request).Υ c.inst.j₀ := by
    rw [c.inst.hα, c.inst.hq, c.inst.hΛ]; exact c.inst.carrier
  have hok := hplan.1 c.inst.request
  have hCH : 1 ≤ (plan.constants c.inst.request).CH := hok.1
  have hΥ : 1 ≤ (plan.constants c.inst.request).Υ :=
    le_trans (by norm_num) ((le_max_left _ _).trans hok.2)
  have hstart := GenSem.startBound_of_carrierStart hΛ hCH hΥ hcarrier
  have hcell : ∀ m, 0 < c.inst.D.cellScaleSq m :=
    fun m => EntryWeakProofs.weakData_cellScaleSq_pos c.inst.D hΛ hζ hκb m
  have hJ : 1 ≤ c.inst.physical.Jw := c.inst.physical.Jw_pos
  have hlvl := (hplan.2 c.inst.request c.inst.j₀).trans c.inst.level_large
  have hc := c.construction
  -- the stage `M`
  obtain ⟨Q, hall, hF⟩ := weakConstruction_stage_presentation hΛ hζ hb hstart hcell hc hJ
  have hlv := EntryWeakProofs.weakConstruction_level _ _ _ _ _ _ _ hc c.inst.M le_rfl
    (by omega)
  have hpass := (hc.2.2 (c.inst.M + 1) (by omega) (by omega)).1
  have hnatM : (c.stage c.inst.M).IsNatural (c.inst.M + c.inst.physical.Jw) := by
    have h := hpass.2.2.2.2.1
    rwa [hc.1] at h
  -- the root encoding
  set e := weakRootEquiv (c.stage c.inst.M).comps
  let Qe : QuietPresentation (weakRootEncodingChoice plan Cθ hCθ exports c).stage :=
    ⟨fun v u γ => Q.source (e.symm v) (e.symm u) γ,
      fun p ch v u γ d I t Y z hd => Q.represents p ch (e.symm v) (e.symm u) γ d I t Y z hd⟩
  have halle : Qe.AllTransfer := fun v u γ => hall (e.symm v) (e.symm u) γ
  have hFe : FinerHistoryInvariant (weakRootEncodingChoice plan Cθ hCθ exports c).stage Qe
      (c.inst.M + c.inst.physical.Jw) :=
    fun v u γ n hn k ch ch' hs t ht f => hF (e.symm v) (e.symm u) γ n hn k ch ch' hs t ht f
  have htrans := (weak_encoding_transport plan Cθ hCθ exports c).2.2.2.2 (hT c)
  have hnate : (weakRootEncodingChoice plan Cθ hCθ exports c).stage.IsNatural
      (c.inst.M + c.inst.physical.Jw) :=
    (weakConstruction_scaledRootLaws _ _ _ _ _ _ _ hc hJ (Cθ c) (hCθ c)).1 hnatM
  have hlve : (weakRootEncodingChoice plan Cθ hCθ exports c).stage.level = c.inst.M := hlv
  have hS := isHistoryQuiet_ocTrimmedQuiet hΛ hCH hcarrier (c.inst.M + c.inst.physical.Jw)
    (weakRootEncodingChoice plan Cθ hCθ exports c).stage.level (by rw [hlve]; omega)
  exact (quietMatching_of_allTransfer hb hΛ hζ _ Qe halle _ _ _ (by rw [hlve]; omega)
    (by rw [hlve]; omega) _ _ hCH hcarrier hnate hS hFe htrans).2

end AVRegularity.Providers.WeakGen
end
end

section
/-! **The carried history invariant of the weak stage `Gw`** (the parent input of the terminal
successor's quiet matching).
* `stageHistoryInvariant_of_weakEncoding`: the invariant passes along a weak encoding. The
  encoded fluxes are those of the stage `M`, reindexed by the bijections `ι` and `e`, at the same
  contexts.
* `weakStage_stageHistory`: the stage `M` of a weak construction carries the invariant at the
  finest level `M + J` (`weakConstruction_history`), hence so does its encoding `Gw`. The
  hypotheses are the data facts and a carrier start, all available wherever the construction
  and the encoding are (for instance in `entry_terminal`'s output, which carries both). -/

@[expose] public noncomputable section

open Homogenization AVRegularity.Sobolev

namespace AVRegularity.Providers.WeakGen

open QuietAtlas

variable {D : OCData} {Dm : ℕ} {b : ℝ} {j₀ : ℕ}

/-- **The history invariant passes along a weak encoding.** -/
theorem stageHistoryInvariant_of_weakEncoding {N J : ℕ} {η₀ : ℝ} {rootM rootR : ℕ → ℝ}
    {G Gw : GenStage D ScalarH Dm b j₀} {ι : CompIn G.comps ≃ CompIn Gw.comps}
    (henc : IsWeakEncoding N J η₀ rootM rootR G Gw ι) {Mtop : ℕ}
    (h : StageHistoryInvariant G Mtop) : StageHistoryInvariant Gw Mtop := by
  obtain ⟨hlev, -, -, -, -, -, Cθ, e, idx, -, -, hid⟩ := henc
  let hctx : ∀ {p : OddSlot}, StageCtx D b j₀ Gw.level p → StageCtx D b j₀ G.level p :=
    fun {p} c => ⟨c.1, by rw [← hlev]; exact c.2⟩
  intro p ch ch' hs t ht v' u' γ' d I z
  obtain ⟨v, rfl⟩ := ι.surjective v'
  obtain ⟨u, rfl⟩ := ι.surjective u'
  obtain ⟨γ, rfl⟩ := (e v u).surjective γ'
  have hflux := fun (c : StageCtx D b j₀ Gw.level p) =>
    (hid v u γ).2.2.2.2.2.2.2.2.2 p c (hctx c) rfl d I t
  have hs' : SameHistoryGeometry D Mtop G.level p.1 ch.1 ch'.1 := by
    rw [← hlev]; exact hs
  have ht' : t ∈ ocPulseWindow D.α D.q D.Λ G.level p.1 := by rw [← hlev]; exact ht
  have hG := h p (hctx ch) (hctx ch') hs' t ht' v u γ d I z
  simp only [hflux]
  exact hG

/-- **The weak stage carries the history invariant at the finest weak level.** The stage `M` of
a weak construction has it (`weakConstruction_history`), and the encoding transports it. -/
theorem weakStage_stageHistory (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) (hb : 0 < b) {CH Υ : ℝ} (hCH : 1 ≤ CH)
    (hΥ : 1 ≤ Υ) (hcar : IsCarrierStart D.α D.q D.Λ b CH Υ j₀) {P : ProvParams}
    {Mn : WeakMenu} {M J : ℕ} {rW : ℝ} {r : ℕ} {stage : ℕ → GenStage D ScalarH Dm b j₀}
    (hc : IsWeakConstruction D P Mn M J rW r stage) {N J' : ℕ} {η₀ : ℝ} {rootM rootR : ℕ → ℝ}
    {Gw : GenStage D ScalarH Dm b j₀} {ι : CompIn (stage M).comps ≃ CompIn Gw.comps}
    (henc : IsWeakEncoding N J' η₀ rootM rootR (stage M) Gw ι) :
    StageHistoryInvariant Gw (M + J) := by
  have hstart := GenSem.startBound_of_carrierStart hΛ hCH hΥ hcar
  have hcell : ∀ m, 0 < D.cellScaleSq m :=
    fun m => EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ m
  have hM := (weakConstruction_history hΛ hζ hb hstart hcell hc J le_rfl).1
  rw [Nat.add_sub_cancel] at hM
  exact stageHistoryInvariant_of_weakEncoding henc hM

end AVRegularity.Providers.WeakGen
end
end
end
