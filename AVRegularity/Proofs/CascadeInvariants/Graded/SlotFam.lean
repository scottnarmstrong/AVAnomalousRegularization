-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Graded.LiftMain
public import AVRegularity.Proofs.GenSem.SuccessorGeneration.Setup
import AVRegularity.Proofs.GenSem.SuccessorGeneration.GermCov

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.GenSem

/-! **Ledger: the graded path mean.** The quantitative form of
`LiftGenSetup.pathMeanFlux_famRep'`: the coefficient of tested order `d` of the path mean flux of
cell degree `n` of a path of `h` edges is a graded family function with
* reserve cost `(n - 1) - (d - 1)` (its coefficient of tested order `d - 1` is bounded at the
  reserve `𝗆 - (n - d)Δ`);
* size `|c_{n,d}| · (d-1)! · fluxXc · pathW Θ h`, where
  `c_{n,d} = -(ℓ_m²)⁻¹ (d_*/ρ)^n ρ · ρ^{d-1}/(d-1)!` is the dimensional prefactor
  (`pathMeanPref`) and `pathW Θ h` (last, first) is the product of the edge sizes of the
  path. -/

section
open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

namespace LiftGenSetup

section General

variable {ι : Type} [Fintype ι] [DecidableEq ι] {Dm : ℕ} {D : OCData} {bw : ℝ} {j₀ : ℕ}
  {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain} {ρ : ℝ}
  {edge : RealChain → ConstituentEdges Dm (fun _ : ι => ℝ)} {U : RealChain → Set (Vec 2)}
  {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ} {Cc : RealChain → ℕ → ℕ → LiftCoeff ι (fun _ => ℝ)}

/-- The metric of the lift data is a graded letter. -/
theorem metric_repP (_hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) {X : GCtx}
    (hX : X.Ok) (a b : Fin 2) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X
      (fun l Y _ => (familyLiftData D m k l.1 ρ (edge l.1)).G l.2 Y a b) 0 0 X.Kg :=
  (UEnv.isURepP_metric hX (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) a b).congr fun _ _ _ _ _ => rfl

/-- The normalized drift of the lift data is a graded letter. -/
theorem drift_repP (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc) {X : GCtx}
    (hX : X.Ok) (c : Fin 2) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X
      (fun l _ z => Real.sqrt (D.kap m / D.kap (m - 1)) *
        (familyLiftData D m k l.1 ρ (edge l.1)).v l.2 z c) 0 0 X.Kd :=
  (UEnv.isURepP_drift hX (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) (fun l => l.2) (fun _ => rfl)
    hS.hc.ne' c).congr fun _ _ _ _ _ => rfl

end General

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {𝒜 : Set RealChain}
  {ρ : ℝ} {h Dm : ℕ} {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {U : RealChain → Set (Vec 2)} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N H : ℕ}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)}

/-- The dimensional prefactor of the coefficient of tested order `d` of the mean of cell degree
`n`. -/
def pathMeanPref (D : OCData) (m : ℕ) (ρ : ℝ) (n d : ℕ) : ℝ :=
  -((D.cellScaleSq m)⁻¹ * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ n * ρ) *
    ρ ^ (d - 1) * ((d - 1).factorial : ℝ)⁻¹

/-- **The coefficient array of the path mean flux is a graded family function** (every degree
`n ≥ 1`: the means beyond the lift cutoff use the truncated lifts and have the same profile). -/
theorem pathMeanFlux_famRepP (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ edge U sX sZ t₀ t₁ N H Cc)
    {X : GCtx} (hX : X.Ok) (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁) X ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).IsURepP X (fun l Y z =>
        (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm H N ≤ X.L₀) (h0 : ∀ A ∈ 𝒜, (0 : Vec 2) ∈ U A) (hhH : h ≤ H) {n : ℕ}
    (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hregn : ∀ A ∈ 𝒜, ∀ τ ∈ Set.Icc t₀ t₁,
      LiftRegular (familyLiftData D m k A ρ (edge A)) (Cc A) 0 τ h n (n + Dm + 2))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁).FamURepP X (fun l =>
      fluxCoeff (pathMeanFlux D m ρ (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) n
        (D.cellScaleSq m * l.2)) d I 0 κ) (n - 1 - (d - 1))
      (Real.toNNReal |pathMeanPref D m ρ n d| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
          (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0))) := by
  set V := liftEnv D bw j₀ 𝒮 m k ρ 𝒜 U t₀ t₁ with hV
  have hok : V.Ok := hS.ok
  have hbelow : V.CoeffRepBelowP X Dm Cc (pathW Θ) (liftB X Dm) h n :=
    fun hh' k' h1 _ m'' α' v' u' =>
      hS.coeffRepP hX hSl hη0 hη1 hed hL₀ (h1.trans hhH) k' m'' α' v' u'
  have hrep := UEnv.URepArrP.fluxXArr hX hok hSl (fun A => familyLiftData D m k A ρ (edge A)) Cc
    0 hn1 (η := D.kap m / D.kap (m - 1)) (fun _ _ => rfl) hη0 hη1 (hS.metric_repP hX)
    (hS.drift_repP hX) hed (fun hh v w hh1 => pathW_succ Θ hh v w hh1) hbelow
    (fun l hl => hregn l.1 hl.1 l.2 hl.2) (Fin.last h) κ
  have hsum : V.IsURepP X (fun l Y z => ∑ σ : Equiv.Perm (Fin (d - 1)),
      GenSem.fluxXArr (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) 0 h n l.2 (Fin.last h) κ
        (d - 1) (I ∘ σ) Y z) (n - 1 - (d - 1)) (UEnv.liftWt Dm h n)
      (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
        (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0)) :=
    UEnv.IsURepP.sum_le hX _ fun σ _ => hrep (d - 1) (I ∘ σ)
  have hm := hsum.mean0 hX hS.hζ hLn (fun l hl => h0 l.1 hl.1)
  have hc := hm.smul hX (pathMeanPref D m ρ n d)
  refine hc.congr fun l hl => ?_
  have hreg : LiftRegular (familyLiftData D m k l.1 ρ (edge l.1)) (Cc l.1) (0 : Fin (h + 1))
      ((D.cellScaleSq m)⁻¹ * (D.cellScaleSq m * l.2)) h n (Dm + 2) := by
    rw [← mul_assoc, inv_mul_cancel₀ hS.hc.ne', one_mul]
    exact (hregn l.1 hl.1 l.2 hl.2).mono le_rfl le_rfl (by omega)
  rw [fluxCoeff_pathMeanFlux D m _ _ n _ hreg d I κ, ← mul_assoc, inv_mul_cancel₀ hS.hc.ne']
  unfold pathMeanPref
  ring_nf

end LiftGenSetup
end

/-! **Ledger: graded slot family representations.** `SlotFamRepP … X ψ r C`: `ψ` is denoted
on the admissible families over the slot and the pulse window by one scheduled, seed-provenanced
family expression (`SlotFamRep`) without uncertified solved node, whose structural norm at
the inner rate and fast weight zero is at most `C` whenever `r` reserve steps are available: the
finer output fed to the explicit transfer (`transferExprAt`, `genNorm_transferExpr_le`).

`CutoffLiftSetup.slotFamRep_pathMeanP`: the path means are graded slot family functions. The setup
represents the cut-off data; the graded source edges of the true data transfer to the cut-off
edges on the offsets, and the germ of the output at `0` transfers back to the true data (as in
`CutoffLiftSetup.slotFamRep_pathMean`). -/

section
open AVRegularity.Providers.CascadeInvariants AVRegularity.Providers.Majorant

/-- **Graded slot family representation** with the reserve cost `r` and the size `C`. -/
def SlotFamRepP (D : OCData) (b : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (m : ℕ) (k : ℤ) (X : GCtx)
    (ψ : ℝ → RealChain → ℝ) (r : ℕ) (C : ℝ≥0) : Prop :=
  ∃ c : Gen .fam m k, Gen.IsScheduled D c ∧ Gen.FromSeed 𝒮 c ∧
    (∃ fc : GenSort.Sem .fam, Gen.Denotes D b j₀ c fc ∧
      ∀ A, IsAdmissibleChain D b j₀ m k A → ∀ t ∈ ocPulseWindow D.α D.q D.Λ m k,
        fc t A = ψ t A) ∧
    Gen.SolvedFree X.leaf c ∧
    ∀ t ∈ X.T, ∀ mres, mres + r * X.Δ ≤ X.μ₀ → genNorm D X.κ X.Δ X.a₀ X.leaf c X.a₀ mres 0 t ≤ C

namespace SlotFamRepP

variable {D : OCData} {b : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {X : GCtx}

theorem congr {ψ ψ' : ℝ → RealChain → ℝ} {r : ℕ} {C : ℝ≥0}
    (h : SlotFamRepP D b j₀ 𝒮 m k X ψ r C)
    (hψ : ∀ A, IsAdmissibleChain D b j₀ m k A → ∀ t ∈ ocPulseWindow D.α D.q D.Λ m k,
      ψ t A = ψ' t A) : SlotFamRepP D b j₀ 𝒮 m k X ψ' r C := by
  obtain ⟨c, hs, hf, ⟨fc, hd, hv⟩, hsf, hn⟩ := h
  exact ⟨c, hs, hf, ⟨fc, hd, fun A hA t ht => (hv A hA t ht).trans (hψ A hA t ht)⟩, hsf, hn⟩

theorem mono (hX : X.Ok) {ψ : ℝ → RealChain → ℝ} {r r' : ℕ} {C C' : ℝ≥0}
    (h : SlotFamRepP D b j₀ 𝒮 m k X ψ r C) (hr : r ≤ r') (hC : C ≤ C') :
    SlotFamRepP D b j₀ 𝒮 m k X ψ r' C' := by
  obtain ⟨c, hs, hf, hv, hsf, hn⟩ := h
  refine ⟨c, hs, hf, hv, hsf, fun t ht mres hm =>
    (hn t ht mres ?_).trans (ENNReal.coe_le_coe.mpr hC)⟩
  have hrr : (r : ℝ) * X.Δ ≤ r' * X.Δ :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hr) hX.hΔ
  linarith

/-- The difference of two graded slot family functions. -/
theorem sub (hX : X.Ok) {ψ φ : ℝ → RealChain → ℝ} {r : ℕ} {C₁ C₂ : ℝ≥0}
    (hψ : SlotFamRepP D b j₀ 𝒮 m k X ψ r C₁) (hφ : SlotFamRepP D b j₀ 𝒮 m k X φ r C₂) :
    SlotFamRepP D b j₀ 𝒮 m k X (fun t A => ψ t A - φ t A) r (C₁ + C₂) := by
  obtain ⟨a, sa, fa, ⟨f, hf, hva⟩, hsa, hna⟩ := hψ
  obtain ⟨c, sc, fcs, ⟨g, hg, hvc⟩, hsc, hnc⟩ := hφ
  refine ⟨Gen.add a (Gen.mul (Gen.time (.const (-1))) c),
    .add sa (.mul (.timeConst (-1)) sc), .add fa (.mul (.time _) fcs),
    ⟨GenSort.add .fam f (GenSort.mul .fam (GenSort.ofTime .fam (TimeLetter.eval D (.const (-1))))
      g), .add hf (.mul (.time _) hg), fun A hA t ht => ?_⟩,
    Or.inr ⟨hsa, Or.inr ⟨trivial, hsc⟩⟩, fun t ht mres hm => ?_⟩
  · show f t A + TimeLetter.eval D (.const (-1)) t * g t A = _
    rw [hva A hA t ht, hvc A hA t ht]
    simp only [TimeLetter.eval]
    ring
  · rw [genNorm_add_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx),
      genNorm_mul_eq _ _ _ _ _ (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx),
      genNorm_const_eq _ _ _ _ _ (-1) (hX.hleaf _ _ _ _ GCtx.fam_ne_ctx), ENNReal.coe_add]
    refine add_le_add (hna t ht mres hm) ?_
    have h1 : ENNReal.ofReal |(-1 : ℝ)| = 1 := by simp
    rw [h1, one_mul]
    exact hnc t ht mres hm

/-- **From a graded family representation over the lift window.** -/
theorem of_famURepP (hc : 0 < D.cellScaleSq m) {ρ : ℝ} {U : RealChain → Set (Vec 2)}
    {φ : RealChain × ℝ → ℝ} {r : ℕ} {C : ℝ≥0}
    (h : (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
      (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).FamURepP X φ r C) :
    SlotFamRepP D b j₀ 𝒮 m k X (fun t A => φ (A, (D.cellScaleSq m)⁻¹ * t)) r C := by
  obtain ⟨c, ⟨hs, hf, fc, hd, hv⟩, hsf, hn⟩ := h
  refine ⟨c, hs, hf, ⟨fc, hd, fun A hA t ht => ?_⟩, hsf, hn⟩
  have hmem : (A, (D.cellScaleSq m)⁻¹ * t) ∈ (liftEnv D b j₀ 𝒮 m k ρ
      {A | IsAdmissibleChain D b j₀ m k A} U (D.slotStart m k / D.cellScaleSq m)
      ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).W := by
    refine ⟨hA, ?_, ?_⟩
    · rw [div_eq_inv_mul]
      refine mul_le_mul_of_nonneg_left ?_ (inv_nonneg.mpr hc.le)
      exact ht.1
    · rw [div_eq_inv_mul]
      exact mul_le_mul_of_nonneg_left ht.2 (inv_nonneg.mpr hc.le)
  have := hv _ hmem
  simp only [liftEnv] at this
  show fc t A = φ (A, (D.cellScaleSq m)⁻¹ * t)
  rw [this, ← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]

end SlotFamRepP

variable {h Dm : ℕ} {D : OCData} {b : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {m : ℕ} {k : ℤ} {ρ : ℝ}
  {edge : RealChain → ConstituentEdges Dm (fun _ : Fin (h + 1) => ℝ)}
  {Cc : RealChain → ℕ → ℕ → LiftCoeff (Fin (h + 1)) (fun _ => ℝ)} {sX sZ N R : ℕ}

/-- **The path means are graded slot family functions.** -/
theorem CutoffLiftSetup.slotFamRep_pathMeanP
    (hset : CutoffLiftSetup D b j₀ 𝒮 m k ρ edge Cc sX sZ N R) (hc : 0 < D.cellScaleSq m)
    {X : GCtx} (hX : X.Ok)
    (hSl : ENNReal.ofReal |ρ| * (X.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X.Δ)) ≤ X.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    {Θ : Fin (h + 1) → Fin (h + 1) → ℝ≥0}
    (hed : ∀ U : RealChain → Set (Vec 2),
      (∀ A, IsAdmissibleChain D b j₀ m k A → U A ⊆ ladderOmega D b j₀ m k A ρ) →
      ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
        (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
          (D.slotStart m k / D.cellScaleSq m)
          ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).IsURepP X
          (fun l Y z => (((familyLiftData D m k l.1 ρ (edge l.1)).edge v u d).map
            fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u))
    (hL₀ : UEnv.liftWt Dm h N ≤ X.L₀) {n : ℕ} (hn1 : 1 ≤ n) (hLn : UEnv.liftWt Dm h n ≤ X.L₀)
    (hnR : n + Dm + 2 ≤ R) (d : ℕ) (I : DerivativeWord2 (d - 1)) (κ : Fin 2) :
    SlotFamRepP D b j₀ 𝒮 m k X (fun t A =>
      fluxCoeff (pathMeanFlux D m ρ (familyLiftData D m k A ρ (edge A)) (Cc A) n t) d I 0 κ)
      (n - 1 - (d - 1))
      (Real.toNNReal |LiftGenSetup.pathMeanPref D m ρ n d| *
        (((Finset.univ : Finset (Equiv.Perm (Fin (d - 1)))).card : ℝ≥0) *
          (UEnv.fluxXc X Dm (liftB X Dm) h n * pathW Θ h (Fin.last h) 0))) := by
  obtain ⟨edge', Cc', U, hS, hU⟩ := hset
  have hed' : ∀ (v u : Fin (h + 1)) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1))
      (c : Fin 2), (liftEnv D b j₀ 𝒮 m k ρ {A | IsAdmissibleChain D b j₀ m k A} U
        (D.slotStart m k / D.cellScaleSq m)
        ((((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m)).IsURepP X
        (fun l Y z => (((familyLiftData D m k l.1 ρ (edge' l.1)).edge v u d).map
          fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0 (Θ v u) := fun v u d α c =>
    (hed U (fun A hA => (hU A hA).2.2.1) v u d α c).congr fun l hl Y hY z =>
      (Uniqueness.list_sum_map_forall₂ ((hU l.1 hl.1).2.2.2.1.edge v u d) fun γ γ' hγ => by
        rw [hγ.1, hγ.2 α l.2 Y hY z]).symm
  have hfam := hS.pathMeanFlux_famRepP hX hSl hη0 hη1 hed' hL₀ (fun A hA => (hU A hA).2.1) le_rfl
    hn1 hLn (fun A hA τ hτ => (hU A hA).2.2.2.2.2 h le_rfl n _ hnR τ hτ 0) d I κ
  refine (SlotFamRepP.of_famURepP hc hfam).congr fun A hA t _ => ?_
  obtain ⟨hO, h0, -, hag, hCeq, -⟩ := hU A hA
  simp only
  rw [← mul_assoc, mul_inv_cancel₀ hc.ne', one_mul]
  rw [Uniqueness.fluxCoeff_pathMeanFlux_agree D m ρ hag (Cc A) (Cc' A) n t hO h0
    (fun hh' _ n' m' α Y hY => (hCeq hh' n' m' α _ Y hY).symm) d I]
end

end AVRegularity.Providers.GenSem
end
