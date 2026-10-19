-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.CascadeInvariants.Diag.FirstQ
public import AVRegularity.Proofs.CascadeInvariants.CopyDirNorm
import AVRegularity.Proofs.GenSem.SuccessorGeneration.Terminal
import AVRegularity.Proofs.CascadeInvariants.Scales
import AVRegularity.Proofs.GenSem.First.Child
import AVRegularity.Proofs.GenSem.First.RepMain
import AVRegularity.Proofs.GenSem.Jet.Chart

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the sized mean arrays of the appended children.**
* `CCtx.Ok.toG`: the graded family context of a context calculus is admissible;
* `ctxAlgQ_sumEvalChild`, `jetRepGQ_sumEvalChildQ`: the sum over the finer slots of the
  evaluations at the appended children of sized family jets of size `C` is a sized context jet of
  size `W_c C` — the partition weights add up to at most one at each time
  (`sum_ocCutoff_mul_le`), so the number of finer slots does not enter;
* `arrJetGQ_diagChildQ`: the push-forward arrays of the grade-zero label fluxes of cell degree `n`
  are sized family arrays (`arrJetGQ_pmArr`, `arrJetGQ_push`), with the constant `childK`;
* `arrJetGQ_dmArrQ`: the assembled mean arrays `K_n` are sized context arrays. -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop} {X : CCtx} {σ : ℝ≥0}

/-- The graded family context of an admissible context calculus is admissible. -/
theorem CCtx.Ok.toG (hX : X.Ok) {S Kg Kd : ℝ≥0}
    (hKg : ∀ L, L ≤ X.L₀ → geoW X.κ X.a₀ L ≤ Kg)
    (hKd : ∀ (k : Fin 2) (L : ℕ), L ≤ X.L₀ → wsum X.a₀ L (X.κ.drift k) ≤ Kd) :
    (X.toG S Kg Kd).Ok :=
  ⟨hX.hΔ, hX.hμ, hX.hctx, fun _ _ _ => hX.hshape _ id, hKg, hKd, fun _ => Set.mem_univ _⟩

/-! ### Explicit sums -/

theorem noMark_genSumList : ∀ (l : List (Gen .ctx i pc)), NoMark (genSumList l)
  | [] => by trivial
  | _ :: _ => noMark_add _ _

/-- The structural norm of an explicit sum is at most the sum of the norms. -/
theorem genNorm_genSumList_leQ (hX : X.Ok) (a mres : ℝ) (L : ℕ) (t : ℝ) :
    ∀ l : List (Gen .ctx i pc), genNorm D X.κ X.Δ X.a₀ X.leaf (genSumList l) a mres L t ≤
      (l.map fun e => genNorm D X.κ X.Δ X.a₀ X.leaf e a mres L t).sum
  | [] => by
      simpa [genSumList] using genNorm_const_le X.κ X.Δ X.a₀ X.leaf (D := D) (s := .ctx) (i := i)
        (p := pc) 0 (hX.hshape _ (not_isMarkShape_time _)) a mres L t
  | e :: es => by
      simp only [genSumList, List.map_cons, List.sum_cons]
      rw [genNorm_add_eq _ _ _ _ _ (hX.hshape _ (not_isMarkShape_add _ (noMark_genSumList es)))]
      exact add_le_add le_rfl (genNorm_genSumList_leQ hX a mres L t es)

/-! ### Sums of evaluations at the appended children -/

/-- **The sum over the finer slots of the evaluations at the appended children.** -/
theorem ctxAlgQ_sumEvalChild (hX : X.Ok) (S Kg Kd : ℝ≥0) (T : Finset ℤ)
    (hT : ∀ k ∈ T, Odd k ∧ IsScheduledIn D i k pc) (hτ : 0 < ocTau D.α D.q D.Λ (i + 1))
    {Wc : ℝ≥0} (hW : ∀ L, L ≤ X.L₀ → wsum X.a L X.κ.child ≤ Wc) (r : ℕ)
    {G : ℤ → ℝ → RealChain → ℝ} {C : ℝ≥0}
    (hG : ∀ k ∈ T, famAlgQ D bw j₀ 𝒮 (i + 1) k (childW D i k P) (X.toG S Kg Kd)
      (fun q => G k q.1.1 q.1.2) r C) :
    ctxAlgQ D bw j₀ 𝒮 i pc P X (fun l => ∑ k ∈ T,
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 * G k l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2))
      r (Wc * C) := by
  classical
  have hc : ∀ k, ∃ c : Gen .fam (i + 1) k, k ∈ T → Gen.IsScheduled D c ∧ Gen.FromSeed 𝒮 c ∧
      (∃ fc : GenSort.Sem .fam, Gen.Denotes D bw j₀ c fc ∧
        ∀ q : childW D i k P, G k q.1.1 q.1.2 = fc q.1.1 q.1.2) ∧
      Gen.SolvedFree X.leaf c ∧ ∀ (t mres : ℝ), mres + r * X.Δ ≤ X.μ₀ →
        genNorm D X.κ X.Δ X.a₀ X.leaf c X.a₀ mres 0 t ≤ C := by
    intro k
    by_cases hk : k ∈ T
    · obtain ⟨c, hs, hf, hv, hsf, hn⟩ := hG k hk
      exact ⟨c, fun _ => ⟨hs, hf, hv, hsf, fun t mres hm => hn t (Set.mem_univ t) mres hm⟩⟩
    · exact ⟨Gen.time (.const 0), fun h => absurd h hk⟩
  choose c hc using hc
  refine ⟨fun t ch z => ∑ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k t * G k t (ch.appendChild D k t z),
    genSumList (T.toList.map fun k => Gen.evalChild (i := i) (p := pc) k (c k)), fun _ => rfl,
    ?_, ?_, noMark_genSumList _, fun t _ mres L _ hm hL => ?_⟩
  · refine CtxRep.genSumFinset T _ _ fun k hk => ?_
    obtain ⟨hs, hf, ⟨fc, hd, hv⟩, -, -⟩ := hc k hk
    exact ctxRep_evalChild P k (hT k hk) hs hf hd fun t ch z hP hcut =>
      (hv ⟨(t, ch.appendChild D k t z), ⟨t, ch, z, hP, hcut, rfl⟩⟩).symm
  · refine solvedFree_genSumList X.leaf _ fun e he => ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp he
    exact Or.inr (hc k (Finset.mem_toList.mp hk)).2.2.2.1
  · refine (genNorm_genSumList_leQ hX X.a mres L t _).trans ?_
    rw [List.map_map, Finset.sum_map_toList]
    have hterm : ∀ k ∈ T, genNorm D X.κ X.Δ X.a₀ X.leaf
        (Gen.evalChild (i := i) (p := pc) k (c k)) X.a mres L t ≤
        ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) k t) * ((Wc * C : ℝ≥0) : ℝ≥0∞) := by
      intro k hk
      rw [genNorm_evalChild_eq _ _ _ _ _ (hX.hshape _ id), mul_assoc, ENNReal.coe_mul]
      exact mul_le_mul' le_rfl (mul_le_mul' (hW L (by omega)) ((hc k hk).2.2.2.2 t mres hm))
    calc ∑ k ∈ T, ((fun e => genNorm D X.κ X.Δ X.a₀ X.leaf e X.a mres L t) ∘
          fun k => Gen.evalChild (i := i) (p := pc) k (c k)) k
        ≤ ∑ k ∈ T, ENNReal.ofReal (ocCutoff D.α D.q D.Λ (i + 1) k t) *
            ((Wc * C : ℝ≥0) : ℝ≥0∞) := Finset.sum_le_sum hterm
      _ ≤ ((Wc * C : ℝ≥0) : ℝ≥0∞) :=
          sum_ocCutoff_mul_le hτ T (fun k hk => (hT k hk).1) t _ fun _ _ => le_rfl

/-- The sums of evaluations at the appended children are as smooth as the family functions. -/
theorem contDiff_sumEvalChild (T : Finset ℤ) {n : ℕ} {G : ℤ → ℝ → RealChain → Vec 2 → ℝ}
    (hGs : ∀ k ∈ T, ∀ q : childW D i k P, ContDiff ℝ n (G k q.1.1 q.1.2)) (l : CtxIdx P) :
    ContDiff ℝ n (fun x => ∑ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 *
      G k l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2) x) := by
  refine ContDiff.sum fun k hk => ?_
  by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
  · simp only [h0, zero_mul]
    exact contDiff_const
  · exact contDiff_const.mul (hGs k hk ⟨(l.1.1, l.1.2.1.appendChild D k l.1.1 l.1.2.2),
      ⟨l.1.1, l.1.2.1, l.1.2.2, l.2, h0, rfl⟩⟩)

/-- **Sized jets of sums of evaluations at the appended children.** -/
theorem jetRepGQ_sumEvalChildQ (hX : X.Ok) (S Kg Kd : ℝ≥0) (T : Finset ℤ)
    (hT : ∀ k ∈ T, Odd k ∧ IsScheduledIn D i k pc) (hτ : 0 < ocTau D.α D.q D.Λ (i + 1))
    {Wc : ℝ≥0} (hW : ∀ L, L ≤ X.L₀ → wsum X.a L X.κ.child ≤ Wc) :
    ∀ (n r : ℕ) {G : ℤ → ℝ → RealChain → Vec 2 → ℝ} {C : ℝ≥0},
      (∀ k ∈ T, JetRepGQ (famAlgQ D bw j₀ 𝒮 (i + 1) k (childW D i k P) (X.toG S Kg Kd)) σ n
        (fun q y => G k q.1.1 q.1.2 y) r C) →
      (∀ k ∈ T, ∀ q : childW D i k P, ContDiff ℝ n (G k q.1.1 q.1.2)) →
      JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ n (fun l x => ∑ k ∈ T,
        ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 * G k l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2) x)
        r (Wc * C) := by
  intro n
  induction n with
  | zero =>
    intro r G C hG _
    exact ctxAlgQ_sumEvalChild hX S Kg Kd T hT hτ hW r (G := fun k t B => G k t B 0)
      fun k hk => hG k hk
  | succ n ih =>
    intro r G C hG hGs
    refine ⟨ctxAlgQ_sumEvalChild hX S Kg Kd T hT hτ hW r (G := fun k t B => G k t B 0)
      fun k hk => (hG k hk).1, fun j => ?_⟩
    have h := ih (r + 1) (G := fun k t B y => fderiv ℝ (G k t B) y (basisVec j))
      (fun k hk => (hG k hk).2 j) (fun k hk q => contDiff_dirDeriv_nat (hGs k hk q) j)
    rw [mul_left_comm]
    refine h.congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
    simp only [dLabelG]
    have hd : ∀ k ∈ T, DifferentiableAt ℝ (fun x => ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 *
        G k l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2) x) x := by
      intro k hk
      by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
      · simp only [h0, zero_mul]
        exact differentiableAt_const _
      · exact ((hGs k hk ⟨(l.1.1, l.1.2.1.appendChild D k l.1.1 l.1.2.2),
          ⟨l.1.1, l.1.2.1, l.1.2.2, l.2, h0, rfl⟩⟩).differentiable (by simp) x).const_mul _
    rw [fderiv_fun_sum hd, _root_.sum_apply]
    exact Finset.sum_congr rfl fun k _ => (fderiv_const_mul_apply' _ _ _ _).symm

/-! ### The push-forward arrays of the grade-zero label fluxes -/

/-- The constant of the push-forward arrays of cell degree `n` at the jet order `r'`. -/
def childK (D : OCData) (X' : GCtx) (Dm m : ℕ) (ρ : ℝ) (n r' : ℕ) (s : ℝ≥0) : ℝ≥0 :=
  chartK r' n (invP X'.Kg r') (s + 2 ^ (r' + n) * X'.Kg) *
    (compC (invP X'.Kg r') r' * X'.Kg *
      (Real.toNNReal (LiftGenSetup.pmC D m ρ n) * UEnv.fluxXc X' Dm (liftB X' Dm) 0 n))

/-- **The push-forward arrays of the grade-zero label fluxes are sized family arrays.** -/
theorem arrJetGQ_diagChildQ {m : ℕ} {k : ℤ} {𝒜 : Set RealChain} {ρ : ℝ} {Dm sX sZ N : ℕ}
    {t₀ t₁ : ℝ} {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hS : LiftGenSetup D bw j₀ 𝒮 m k 𝒜 ρ
      (fun _ => (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ))) (fun _ => Set.univ)
      sX sZ t₀ t₁ N 0 (Cc0 k))
    {X' : GCtx} (hX' : X'.Ok)
    (hSl : UEnv.slowC (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 (fun _ => Set.univ) t₀ t₁) X' ≤ X'.S)
    (hη0 : 0 ≤ D.kap m / D.kap (m - 1)) (hη1 : D.kap m / D.kap (m - 1) ≤ 1)
    (hL₀ : UEnv.liftWt Dm 0 N ≤ X'.L₀) {n : ℕ} (hn1 : 1 ≤ n)
    (hLn : UEnv.liftWt Dm 0 n ≤ X'.L₀) (r' : ℕ)
    (hreg : ∀ A ∈ 𝒜, ∀ τ ∈ Set.Icc t₀ t₁,
      LiftRegular (diagQ D Dm m k A ρ) (Cc0 k A) 0 τ 0 n (max r' n + Dm + 2))
    {s : ℝ≥0} (hσ : X'.κ.Cslow / ENNReal.ofReal (D.eps (m - 1) * X'.Δ) ≤ σ) (hρ : 0 < ρ)
    (hσw : σ * Real.toNNReal ρ ≤ s) (hD0 : 0 ≤ ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)))
    {W' : Set (ℝ × RealChain)} (hW' : W' ⊆ liftFamW D m 𝒜 t₀ t₁) (c : Fin 2) :
    ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W' X') σ (Real.toNNReal ρ) r'
      (fun q => diagChildArr D Dm m ρ Cc0 k n q.1.1 q.1.2 c) (n - 1 + n)
      (childK D X' Dm m ρ n r' s) := by
  set W := liftFamW D m 𝒜 t₀ t₁ with hWdef
  have hR := repAlgQ_famAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := m) (p := k) (W := W)
    hX'
  have hWS : ∀ q ∈ W, q.2.WellSlotted := fun q hq => (hS.hA q.2 hq.1).1
  have hw : Real.toNNReal ρ ≠ 0 := (Real.toNNReal_pos.mpr hρ).ne'
  have hed : ∀ (v u : Fin 1) (d : Finset.Icc 2 Dm) (α : DerivativeWord2 (d.1 - 1)) (c : Fin 2),
      (liftEnv D bw j₀ 𝒮 m k ρ 𝒜 (fun _ => Set.univ) t₀ t₁).IsURepP X' (fun l Y z =>
        (((familyLiftData D m k l.1 ρ
          ((fun _ => (fun _ _ _ => [] : ConstituentEdges Dm (fun _ : Fin 1 => ℝ))) l.1)).edge
            v u d).map fun γ => γ.map 1 * γ.coeff α l.2 Y z c).sum) 0 0
        ((0 : Fin 1 → Fin 1 → ℝ≥0) v u) := fun v u d α c =>
    (UEnv.isURepP_zero hX' _ 0 0).congr fun l _ Y _ z => by simp [familyLiftData, liftEdges]
  have hP : ∀ κ, ArrJetGQ (famAlgQ D bw j₀ 𝒮 m k W X') σ (Real.toNNReal ρ) r' (fun q : W =>
      pmArr D m ρ (diagQ D Dm m k q.1.2 ρ) (Cc0 k q.1.2) n q.1.1 κ) (n - 1)
      (Real.toNNReal (LiftGenSetup.pmC D m ρ n) * UEnv.fluxXc X' Dm (liftB X' Dm) 0 n) := by
    intro κ
    have h := hS.arrJetGQ_pmArr hX' hSl hη0 hη1 hed hL₀ (fun _ _ => Set.mem_univ _) le_rfl hn1
      hLn (fun A hA τ hτ => (hreg A hA τ hτ).mono le_rfl le_rfl (by omega)) hσ hρ hD0 r'
      (fun A hA τ hτ => (hreg A hA τ hτ).mono le_rfl le_rfl (by omega)) κ
    simpa only [pathW_zero, Fin.last_zero, ite_true, mul_one] using h
  have hΨ : ∀ b j, JetRepGQ (famAlgQ D bw j₀ 𝒮 m k W X') σ (r' + n)
      (dLabelG j (fun (q : W) y => q.1.2.famMap D q.1.1 y b)) (n - 1) X'.Kg := fun b j =>
    (jetRepGQ_dLabel_famMap hX' hS.hζ hσ hWS (r' + n) b j).mono hR le_rfl (Nat.zero_le _) le_rfl
  have hI : ∀ b j, JetRepGQ (famAlgQ D bw j₀ 𝒮 m k W X') σ r'
      (dLabelG j (fun (q : W) x => q.1.2.famMapInv D q.1.1 x b)) (n - 1) (invP X'.Kg r') :=
    fun b j => (jetRepGQ_dLabel_famMapInv hX' hS.hζ hσ hWS r' b j).mono hR le_rfl
      (Nat.zero_le _) le_rfl
  have hB := arrJetGQ_push hR hw hσw (fun q : W => contDiff_famMap q.1.2 q.1.1) hΨ le_rfl
    (fun q : W => contDiff_famMapInv q.1.2 q.1.1) (fun q : W => famMapInv_zero hS.hζ q.1.2 q.1.1)
    hI hP c
  exact ArrJetGQ.comap (fun q' : W' => (⟨q'.1, hW' q'.2⟩ : W))
    (fun F r C hF => famAlgQ_restrict hW' hF) hB

/-! ### The assembled mean arrays -/

/-- **The assembled mean arrays `K_n` are sized context arrays.** -/
theorem arrJetGQ_dmArrQ (hX : X.Ok) (S Kg Kd : ℝ≥0) (T : Finset ℤ)
    (hT : ∀ k ∈ T, Odd k ∧ IsScheduledIn D i k pc) (hτ : 0 < ocTau D.α D.q D.Λ (i + 1))
    {Wc : ℝ≥0} (hW : ∀ L, L ≤ X.L₀ → wsum X.a L X.κ.child ≤ Wc)
    (hadm : ∀ l : CtxIdx P, ∀ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2))
    {Dm : ℕ} {ρ : ℝ} {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (n nj rc : ℕ) (c : Fin 2) {w cC : ℝ≥0}
    (hchild : ∀ k ∈ T, ArrJetGQ (famAlgQ D bw j₀ 𝒮 (i + 1) k (childW D i k P) (X.toG S Kg Kd))
      σ w nj (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c) rc cC) :
    ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ w nj
      (fun l => dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 n c) rc (Wc * cC) := by
  classical
  have e : ∀ l : CtxIdx P, dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 n c =
      ∑ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 •
        diagChildArr D Dm (i + 1) ρ Cc0 k n l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2) c := by
    intro l
    unfold dmArr
    refine Finset.sum_congr rfl fun k hkT => ?_
    split_ifs with h
    · rfl
    · by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
      · rw [h0, zero_smul]
      · exact absurd (hadm l k hkT h0) h
  intro m α
  have hG := jetRepGQ_sumEvalChildQ hX S Kg Kd T hT hτ hW nj rc
    (G := fun k t B y => diagChildArr D Dm (i + 1) ρ Cc0 k n t B c m α y 0) (C := cC * w ^ m)
    (fun k hk => (hchild k hk m α).1) (fun k hk q => (hchild k hk m α).2 q)
  refine ⟨?_, fun l => ?_⟩
  · rw [mul_assoc]
    refine hG.congr_germ fun l => Filter.Eventually.of_forall fun y => ?_
    simp only [e l, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  · have h := contDiff_sumEvalChild T
      (G := fun k t B y => diagChildArr D Dm (i + 1) ρ Cc0 k n t B c m α y 0)
      (fun k hk q => (hchild k hk m α).2 q) l
    simpa only [e l, Finset.sum_apply, Pi.smul_apply, smul_eq_mul] using h

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology Set
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the bridge arrays are sized through the certified leaves.** Over the
contexts `P` of the slot `pc` (times of the pulse window), the bridge arrays
`K_2 − 𝖩_m ∇ = ∑_k ϖ_k · bridgeChild_k` (`bridgeArr_eq`) have entries of order one only
(`ChildLift.bridgeChild_ne_one`), and the ordered derivative of the word `β` at the label `0` of
the entry `(c, γ)` is the bridge leaf `leafSem c (γ 0) β` (`orderedDerivative_entry`).
When every bridge leaf is a marked leaf of the calculus with the profile
`leafProf |β| (σ^{|β|} K_B)`, the bridge arrays are sized context arrays of the constant `c_B`,
`W_l K_B ≤ c_B w` (`arrJetGQ_bridgeQ`); with the mean arrays of the degrees `3, …, N + 1`
(`arrJetGQ_dmArrQ`) this sizes the assembled mean arrays `dfArr` (`arrJetGQ_dfArrQ`). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant

/-! ### Ordered derivatives of finite combinations -/

/-- Ordered derivatives commute with constant factors, without differentiability. -/
theorem orderedDerivative_const_mul' (c : ℝ) : ∀ {m : ℕ} (β : DerivativeWord2 m) (g : Vec 2 → ℝ),
    AVRegularity.orderedDerivative β (fun x => c * g x) =
      fun x => c * AVRegularity.orderedDerivative β g x
  | 0, β, g => by
      have : β = Fin.elim0 := Subsingleton.elim _ _
      subst this
      simp [orderedDerivative_zero_word]
  | m + 1, β, g => by
      rw [GenSem.orderedDerivative_succ, GenSem.orderedDerivative_succ]
      have h1 : (fun x => fderiv ℝ (fun x => c * g x) x (basisVec (β 0))) =
          fun x => c * fderiv ℝ g x (basisVec (β 0)) :=
        funext fun x => fderiv_const_mul_apply' c g x _
      rw [h1]
      exact orderedDerivative_const_mul' c (fun i => β i.succ) _

/-- Ordered derivatives commute with finite sums of functions of the class of the word. -/
theorem orderedDerivative_finsetSum' {ι : Type*} (T : Finset ι) :
    ∀ {m : ℕ} (β : DerivativeWord2 m) (f : ι → Vec 2 → ℝ), (∀ k ∈ T, ContDiff ℝ m (f k)) →
      AVRegularity.orderedDerivative β (fun x => ∑ k ∈ T, f k x) =
        fun x => ∑ k ∈ T, AVRegularity.orderedDerivative β (f k) x
  | 0, β, f, _ => by
      have : β = Fin.elim0 := Subsingleton.elim _ _
      subst this
      simp [orderedDerivative_zero_word]
  | m + 1, β, f, hf => by
      rw [GenSem.orderedDerivative_succ]
      have h1 : (fun x => fderiv ℝ (fun x => ∑ k ∈ T, f k x) x (basisVec (β 0))) =
          fun x => ∑ k ∈ T, fderiv ℝ (f k) x (basisVec (β 0)) := by
        funext x
        rw [fderiv_fun_sum fun k hk => ((hf k hk).differentiable (by simp) x), _root_.sum_apply]
      rw [h1, orderedDerivative_finsetSum' T (fun i => β i.succ) _
        fun k hk => contDiff_dirDeriv_nat (hf k hk) _]
      funext x
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [GenSem.orderedDerivative_succ]

/-! ### The orders of the bridge arrays of an appended child -/

namespace ChildLift

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {Dm m : ℕ} {k : ℤ}
  {𝒜 : Set RealChain} {ρ : ℝ} {sX sZ : ℕ} {t₀ t₁ : ℝ} {N : ℕ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- The bridge arrays of an appended child have no entry of an order other than one. -/
theorem bridgeChild_ne_one (L : ChildLift D bw j₀ 𝒮 Dm m k 𝒜 ρ sX sZ t₀ t₁ N Cc0) {A : RealChain}
    (hA : A ∈ 𝒜) {t : ℝ} (ht : (D.cellScaleSq m)⁻¹ * t ∈ Icc t₀ t₁) (c : Fin 2) {m' : ℕ}
    (hm : m' ≠ 1) (γ : DerivativeWord2 m') (x : Vec 2) :
    bridgeChild D Dm m ρ Cc0 k t A c m' γ x 0 = 0 := by
  show chartCoef (fun x => jacMatrix (A.famMap D t) (A.famMapInv D t x)) (A.famMapInv D t)
    (A.famMap D t) 2 (bridgeLab D Dm m ρ Cc0 k t A) c m' γ x = 0
  unfold chartCoef
  refine Finset.sum_eq_zero fun κ _ => ?_
  rw [Finset.sum_eq_zero fun r _ => Finset.sum_eq_zero fun α _ => ?_, mul_zero]
  by_cases hr : r = 1
  · subst hr
    rw [fdbArr_one_ne _ α hm γ, mul_zero]
  · rw [L.bridgeLab_ne_one hA ht κ hr α _, zero_mul]

end ChildLift

/-! ### The bridge arrays over the contexts -/

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop} {X : CCtx} {σ : ℝ≥0} {Dm : ℕ} {ρ : ℝ} {sX sZ N : ℕ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- The standing facts of the bridge arrays over the contexts `P`. -/
structure BridgeCtx (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (pc : ℤ)
    (P : ℝ → RealChain → Vec 2 → Prop) (Dm : ℕ) (ρ : ℝ) (sX sZ N : ℕ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (T : Finset ℤ)
    (𝒜 : ℤ → Set RealChain) (t₀ t₁ : ℤ → ℝ) : Prop where
  hζ : IsFastProfile D.ζ
  hτ : 0 < ocTau D.α D.q D.Λ (i + 1)
  hT : ∀ k, k ∈ T ↔ Odd k ∧ IsScheduledIn D i k pc
  hPw : ∀ l : CtxIdx P, l.1.1 ∈ ocPulseWindow D.α D.q D.Λ i pc
  hadm : ∀ l : CtxIdx P, ∀ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
    IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2)
  L : ∀ k ∈ T, ChildLift D bw j₀ 𝒮 Dm (i + 1) k (𝒜 k) ρ sX sZ (t₀ k) (t₁ k) N Cc0
  hgood : ∀ l : CtxIdx P, ∀ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
    (D.cellScaleSq (i + 1))⁻¹ * l.1.1 ∈ Icc (t₀ k) (t₁ k) ∧
      l.1.2.1.appendChild D k l.1.1 l.1.2.2 ∈ 𝒜 k

namespace BridgeCtx

variable {T : Finset ℤ} {𝒜 : ℤ → Set RealChain} {t₀ t₁ : ℤ → ℝ}
  (B : BridgeCtx D bw j₀ 𝒮 i pc P Dm ρ sX sZ N Cc0 T 𝒜 t₀ t₁)
include B

/-- The bridge arrays at a context are the cutoff-weighted bridge arrays of the children. -/
theorem bridge_eq (l : CtxIdx P) (c : Fin 2) :
    dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
        matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c =
      ∑ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 •
        bridgeChild D Dm (i + 1) ρ Cc0 k l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2) c :=
  bridgeArr_eq B.hζ B.hτ T (fun k hk => ((B.hT k).1 hk).1) l.1.1 l.1.2.1 l.1.2.2
    (fun k hk hcut => (B.hT k).2 ⟨hk, ⟨l.1.1, Function.mem_support.mpr hcut, B.hPw l⟩⟩)
    (B.hadm l) c

/-- The entries of order one of the bridge arrays at a context. -/
theorem entry_one (l : CtxIdx P) (c : Fin 2) (γ : DerivativeWord2 1) (y : Vec 2) :
    (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
        matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c) 1 γ y 0 =
      ∑ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 *
        hSem D (i + 1) k c (γ 0) l.1.1 ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).recenter D
          ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).famMapInv D l.1.1 y)) := by
  rw [B.bridge_eq l c]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_congr rfl fun k hk => ?_
  by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
  · rw [h0, zero_mul, zero_mul]
  · obtain ⟨ht, hA⟩ := B.hgood l k hk h0
    rw [(B.L k hk).bridgeChild_eq_hSem hA ht c γ y]

/-- The entries of an order other than one of the bridge arrays at a context vanish. -/
theorem entry_ne_one (l : CtxIdx P) (c : Fin 2) {m' : ℕ} (hm : m' ≠ 1) (γ : DerivativeWord2 m')
    (y : Vec 2) :
    (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
        matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c) m' γ y 0 =
      0 := by
  rw [B.bridge_eq l c]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  refine Finset.sum_eq_zero fun k hk => ?_
  by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
  · rw [h0, zero_mul]
  · obtain ⟨ht, hA⟩ := B.hgood l k hk h0
    rw [(B.L k hk).bridgeChild_ne_one hA ht c hm γ y, mul_zero]

/-- The weighted push-forward tensors are of the class of the lifts. -/
theorem contDiff_term (l : CtxIdx P) (c g : Fin 2) {r : ℕ} (hRX : r + Dm + 2 ≤ sX)
    (hRZ : r + Dm + 2 ≤ sZ) (k : ℤ) (hk : k ∈ T) :
    ContDiff ℝ r (fun y => ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 *
      hSem D (i + 1) k c g l.1.1 ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).recenter D
        ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).famMapInv D l.1.1 y))) := by
  by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
  · simp only [h0, zero_mul]
    exact contDiff_const
  · obtain ⟨ht, hA⟩ := B.hgood l k hk h0
    exact contDiff_const.mul (((B.L k hk).contDiff_hSem_recenter hA ht hRX hRZ c g).comp
      ((contDiff_famMapInv _ _).of_le (by exact_mod_cast le_top)))

/-- **The ordered derivatives at `0` of the entries of order one of the bridge arrays are the
bridge leaves.** -/
theorem orderedDerivative_entry (l : CtxIdx P) (c : Fin 2) (γ : DerivativeWord2 1) {r : ℕ}
    (hRX : r + Dm + 2 ≤ sX) (hRZ : r + Dm + 2 ≤ sZ) (β : DerivativeWord2 r) :
    AVRegularity.orderedDerivative β (fun y =>
      (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
        matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c) 1 γ y 0) 0 =
      leafSem D i T c (γ 0) β l.1.1 l.1.2.1 l.1.2.2 := by
  have e : (fun y => (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
        matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c) 1 γ y 0) =
      fun y => ∑ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 *
        hSem D (i + 1) k c (γ 0) l.1.1 ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).recenter D
          ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).famMapInv D l.1.1 y)) :=
    funext fun y => B.entry_one l c γ y
  rw [e, orderedDerivative_finsetSum' T β _ fun k hk => B.contDiff_term l c (γ 0) hRX hRZ k hk]
  simp only [orderedDerivative_const_mul']
  rfl

end BridgeCtx

/-! ### The sized bridge arrays -/

/-- **The bridge arrays are sized context arrays** through the certified bridge leaves. -/
theorem arrJetGQ_bridgeQ (hX : X.Ok) {T : Finset ℤ} {𝒜 : ℤ → Set RealChain} {t₀ t₁ : ℤ → ℝ}
    (B : BridgeCtx D bw j₀ 𝒮 i pc P Dm ρ sX sZ N Cc0 T 𝒜 t₀ t₁) (nJ : ℕ)
    (hRX : nJ + Dm + 2 ≤ sX) (hRZ : nJ + Dm + 2 ≤ sZ) {KB Wl cB w : ℝ≥0}
    (hWl : ∀ L, L ≤ X.L₀ →
      wsum X.a L (fun h => ENNReal.ofReal (Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ≤ Wl)
    (hcB : Wl * KB ≤ cB * w) (c : Fin 2)
    (hleaf : ∀ (g : Fin 2) (r : ℕ) (β : DerivativeWord2 r), r ≤ nJ →
      ∃ (e : Gen .ctx i pc) (code : ℤ), CtxRep D bw j₀ 𝒮 P (leafSem D i T c g β) e ∧
        X.leaf (markE code e) = some (leafProf bw X.Δ X.μ₀ r (σ ^ r * KB))) :
    ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ w nJ
      (fun l => dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
        matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c) 0 cB := by
  have hR := repAlgQ_ctxAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hX
  have hzero : ∀ {m' : ℕ} (hm : m' ≠ 1) (γ : DerivativeWord2 m'),
      JetRepGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ nJ (fun l y =>
        (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
          matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c)
          m' γ y 0) 0 (cB * w ^ m') ∧
      ∀ l : CtxIdx P, ContDiff ℝ nJ (fun y =>
        (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
          matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c)
          m' γ y 0) := by
    intro m' hm γ
    have e : ∀ l : CtxIdx P, (fun y =>
        (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
          matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c)
          m' γ y 0) = fun _ => 0 := fun l => funext fun y => B.entry_ne_one l c hm γ y
    refine ⟨((jetRepGQ_zero hR nJ 0).mono hR le_rfl le_rfl zero_le).congr_germ fun l =>
      Filter.Eventually.of_forall fun y => (congrFun (e l) y).symm, fun l => ?_⟩
    rw [e l]
    exact contDiff_const
  intro m' γ
  match m' with
  | 0 => exact hzero (by omega) γ
  | m' + 2 => exact hzero (by omega) γ
  | 1 =>
    refine ⟨JetRepGQ.of_ordered hR fun m hm β => ?_, fun l => ?_⟩
    · obtain ⟨e, code, he, hl⟩ := hleaf (γ 0) m β hm
      have h := ctxAlgQ_mark code he hl (r := m) (C := σ ^ m * (cB * w ^ 1))
        fun mres L hm0 hmres hL => by
          have e1 : leafProf bw X.Δ X.μ₀ m (σ ^ m * KB) mres = fun h : ℤ =>
              ENNReal.ofReal (Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|))) *
                ((σ ^ m * KB : ℝ≥0) : ℝ≥0∞) := by
            funext h
            simp only [leafProf, hm0, hmres, and_self, ↓reduceIte]
          rw [e1, wsum_mul_const]
          calc wsum X.a L (fun h => ENNReal.ofReal (Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) *
                ((σ ^ m * KB : ℝ≥0) : ℝ≥0∞) ≤ (Wl : ℝ≥0∞) * ((σ ^ m * KB : ℝ≥0) : ℝ≥0∞) :=
                mul_le_mul' (hWl L (by omega)) le_rfl
            _ = ((σ ^ m * (Wl * KB) : ℝ≥0) : ℝ≥0∞) := by push_cast; ring
            _ ≤ ((σ ^ m * (cB * w ^ 1) : ℝ≥0) : ℝ≥0∞) := by
                rw [pow_one]
                exact_mod_cast mul_le_mul' le_rfl hcB
      have ef : (fun l : CtxIdx P => AVRegularity.orderedDerivative β (fun y =>
          (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
            matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c)
            1 γ y 0) 0) = fun l => leafSem D i T c (γ 0) β l.1.1 l.1.2.1 l.1.2.2 :=
        funext fun l => B.orderedDerivative_entry l c γ (by omega) (by omega) β
      rw [ef]
      exact hR.mono h (by omega) le_rfl
    · have e : (fun y => (dmArr D bw j₀ Dm (i + 1) ρ Cc0 T l.1.1 l.1.2.1 l.1.2.2 2 c -
          matGradArr (fun _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1) c)
            1 γ y 0) =
          fun y => ∑ k ∈ T, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 *
            hSem D (i + 1) k c (γ 0) l.1.1 ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).recenter D
              ((l.1.2.1.appendChild D k l.1.1 l.1.2.2).famMapInv D l.1.1 y)) :=
        funext fun y => B.entry_one l c γ y
      rw [e]
      exact ContDiff.sum fun k hk => B.contDiff_term l c (γ 0) hRX hRZ k hk

/-- **The assembled mean arrays `𝓕_A = dfArr` are sized context arrays**: the bridge arrays
(constant `c_B`, through the leaves) and the mean arrays of the degrees `3, …, N + 1`
(constants `W_c c_n`). -/
theorem arrJetGQ_dfArrQ (hX : X.Ok) {T : Finset ℤ} {𝒜 : ℤ → Set RealChain} {t₀ t₁ : ℤ → ℝ}
    (B : BridgeCtx D bw j₀ 𝒮 i pc P Dm ρ sX sZ N Cc0 T 𝒜 t₀ t₁) (nJ : ℕ)
    (hRX : nJ + Dm + 2 ≤ sX) (hRZ : nJ + Dm + 2 ≤ sZ) {KB Wl cB w : ℝ≥0}
    (hWl : ∀ L, L ≤ X.L₀ →
      wsum X.a L (fun h => ENNReal.ofReal (Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ≤ Wl)
    (hcB : Wl * KB ≤ cB * w) (c : Fin 2)
    (hleaf : ∀ (g : Fin 2) (r : ℕ) (β : DerivativeWord2 r), r ≤ nJ →
      ∃ (e : Gen .ctx i pc) (code : ℤ), CtxRep D bw j₀ 𝒮 P (leafSem D i T c g β) e ∧
        X.leaf (markE code e) = some (leafProf bw X.Δ X.μ₀ r (σ ^ r * KB)))
    (S Kg Kd : ℝ≥0) {Wc : ℝ≥0} (hW : ∀ L, L ≤ X.L₀ → wsum X.a L X.κ.child ≤ Wc)
    (cC : ℕ → ℝ≥0)
    (hchild : ∀ n, 3 ≤ n → n ≤ N + 1 → ∀ k ∈ T,
      ArrJetGQ (famAlgQ D bw j₀ 𝒮 (i + 1) k (childW D i k P) (X.toG S Kg Kd)) σ w nJ
        (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c) (n - 1 + n) (cC n)) :
    ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc P X) σ w nJ
      (fun l => dfArr D bw j₀ Dm (i + 1) ρ N Cc0 T l.1.1 l.1.2.1 l.1.2.2 c) (2 * N + 1)
      (cB + ∑ n ∈ Finset.Icc 3 (N + 1), Wc * cC n) := by
  have hR := repAlgQ_ctxAlgQ (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (i := i) (pc := pc)
    (P := P) hX
  exact ArrJetGQ.add hR ((arrJetGQ_bridgeQ hX B nJ hRX hRZ hWl hcB c hleaf).mono hR le_rfl
    (Nat.zero_le _) le_rfl) (ArrJetGQ.sum hR _ fun n hn => by
      have hn' := Finset.mem_Icc.mp hn
      exact (arrJetGQ_dmArrQ hX S Kg Kd T (fun k hk => (B.hT k).1 hk) B.hτ hW B.hadm n nJ
        (n - 1 + n) c (hchild n hn'.1 hn'.2)).mono hR le_rfl (by omega) le_rfl)
end

/-! **Ledger, first source: the leaf map of the bridge leaves.** Over the slots `pc` of the level
`i` (contexts `slotCtx`: admissible chains at the times of the pulse window, finer slots
`schedSlots`):
* `bridgeCtx_of`: the grade-zero lifts (`IsDiagLifts` at the level `i + 1`) give the standing facts
  of the bridge arrays (`BridgeCtx`), as in the generation statement (`diagLiftGenSetup`, `appendChild_admissible`);
* `exists_leafRep`: every bridge leaf `leafSem c g β` is the denotation of a scheduled context
  expression with seed provenance — the ordered derivative of the jets of the bridge arrays
  (`arrJetG_dmArr`, `ctxAlg_refFlux`), identified by `BridgeCtx.orderedDerivative_entry`;
* `bleaf`: the leaf map of the marked expressions `markE (code x) (E x)` of the bridge leaves
  `x = (pc, c, g, β)`, `|β| ≤ n_J`, with the profiles `leafProf |β| (σ^{|β|} K_B)`;
* `bleaf_leaf`: the leaves of a slot, as the sized bridge arrays use them;
* `leavesCertified_bleaf`: the leaf map is certified (`leafSem_cert`), every denotation of a marked
  leaf agreeing with the bridge leaf on the output domain (`denotes_agreeOn_of_exports`). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext
  AVRegularity.Providers.ComplexFlow

/-! ### Slots, contexts and the standing facts -/

open scoped Classical in
/-- The finer slots scheduled in the slot `pc` of the level `i`. -/
def schedSlots (D : OCData) (i : ℕ) (pc : ℤ) : Finset ℤ :=
  if h : {k : ℤ | Odd k ∧ IsScheduledIn D i k pc}.Finite then h.toFinset else ∅

theorem mem_schedSlots {D : OCData} {i : ℕ} {pc : ℤ} (hτ : 0 < ocTau D.α D.q D.Λ (i + 1))
    (k : ℤ) : k ∈ schedSlots D i pc ↔ Odd k ∧ IsScheduledIn D i k pc := by
  classical
  unfold schedSlots
  rw [dite_eq_left_of_eq_true (eq_true (scheduledSlots_finite D i pc hτ)), Set.Finite.mem_toFinset]
  rfl

/-- The contexts of the slot `pc` of the level `i`: admissible chains at the output times. -/
def slotCtx (D : OCData) (bw : ℝ) (j₀ i : ℕ) (pc : ℤ) : ℝ → RealChain → Vec 2 → Prop :=
  fun t ch _ => IsAdmissibleChain D bw j₀ i pc ch ∧ t ∈ ocPulseWindow D.α D.q D.Λ i pc

/-- The lift windows of the finer slots. -/
def liftT0 (D : OCData) (m : ℕ) (k : ℤ) : ℝ := D.slotStart m k / D.cellScaleSq m

/-- The lift windows of the finer slots. -/
def liftT1 (D : OCData) (m : ℕ) (k : ℤ) : ℝ :=
  (((k : ℝ) + 61 / 48) * ocTau D.α D.q D.Λ m) / D.cellScaleSq m

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {i : ℕ}

section Facts

variable (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ) (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ)
  (hb : 0 < bw)
  (hstart : ∀ k : ℕ, j₀ ≤ k + 1 →
    2 * ocA D.α D.q D.Λ k * ocTauPP D.α D.q D.Λ (k + 1) ≤ bw / (64 * (8 * Real.pi ^ 2)))
  (𝒮 : SeedExports) {ρ : ℝ} (hρ : ρ ≠ 0) {N : ℕ} (hN : 1 ≤ N) {Dm sX sZ R : ℕ}
  (hRX : R ≤ sX) (hRZ : R ≤ sZ) (hNR : N + Dm + 2 ≤ R)
  (hDst : ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)) ^ 2 =
    D.kap (i + 1 - 1) * D.cellScaleSq (i + 1))
  (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
  (hDL : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D bw j₀ (i + 1) k A →
    IsLiftSequence (diagQ D Dm (i + 1) k A ρ) sX sZ (liftT0 D (i + 1) k) (liftT1 D (i + 1) k)
      N 0 (Cc0 k A))
include hΛ hζ hκ hb hstart hρ hN hRX hRZ hNR hDst hDL

/-- **The standing facts of the bridge arrays** over the contexts of a slot. -/
theorem bridgeCtx_of (pc : ℤ) :
    BridgeCtx D bw j₀ 𝒮 i pc (slotCtx D bw j₀ i pc) Dm ρ sX sZ N Cc0 (schedSlots D i pc)
      (fun k => {A | IsAdmissibleChain D bw j₀ (i + 1) k A}) (liftT0 D (i + 1)) (liftT1 D (i + 1)) := by
  have hτ : 0 < ocTau D.α D.q D.Λ (i + 1) := Construction.Stream.ocTau_pos hΛ
  have hc : 0 < D.cellScaleSq (i + 1) := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ hζ hκ _
  have hT := mem_schedSlots (D := D) (pc := pc) hτ
  have hadm : ∀ l : CtxIdx (slotCtx D bw j₀ i pc), ∀ k ∈ schedSlots D i pc,
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) :=
    fun l k hk hcut => appendChild_admissible D hΛ hζ hb hstart i pc l.1.2.1 l.2.1 k
      ((hT k).1 hk).1 ((hT k).1 hk).2 l.1.1 hcut l.1.2.2
  exact
    { hζ := hζ
      hτ := hτ
      hT := hT
      hPw := fun l => l.2.2
      hadm := hadm
      L := fun k hk =>
        { hS := diagLiftGenSetup D hΛ hζ hκ bw j₀ 𝒮 (i + 1) k ((hT k).1 hk).1 ρ hρ (Cc0 k) hRX hRZ
            hNR fun A hA => hDL k A ((hT k).1 hk).1 hA
          hk := ((hT k).1 hk).1
          hΛ := hΛ
          hζ := hζ
          hκ := EntryWeakProofs.weakData_kap_pos D hΛ hζ hκ
          hN := hN
          hρ := hρ
          hDst := hDst
          hseq := fun A hA => hDL k A ((hT k).1 hk).1 hA }
      hgood := fun l k hk hcut =>
        ⟨mem_liftWindow_of_mem_ocPulseWindow hc (mem_ocPulseWindow_of_ocCutoff_ne_zero hτ hcut),
          hadm l k hk hcut⟩ }

/-- **Every bridge leaf is a context expression** (generation). -/
theorem exists_leafRep (hκm : D.kap (i + 1) = D.κ (i + 1)) (pc : ℤ) (c g : Fin 2) {r : ℕ}
    (hr : r + Dm + 2 ≤ R) (hR2 : 2 + Dm + 2 ≤ R) (β : DerivativeWord2 r) :
    ∃ e : Gen .ctx i pc, CtxRep D bw j₀ 𝒮 (slotCtx D bw j₀ i pc)
      (leafSem D i (schedSlots D i pc) c g β) e := by
  classical
  have B := bridgeCtx_of hΛ hζ hκ hb hstart 𝒮 hρ hN hRX hRZ hNR hDst Cc0 hDL pc
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc (slotCtx D bw j₀ i pc)
  have hk : ∀ k ∈ schedSlots D i pc, Odd k ∧ IsScheduledIn D i k pc := fun k hk => (B.hT k).1 hk
  have hchild : ∀ k ∈ schedSlots D i pc,
      ArrJetG (famAlg D bw j₀ 𝒮 (i + 1) k (childW D i k (slotCtx D bw j₀ i pc))) r
        (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k 2 q.1.1 q.1.2 c) := by
    intro k hkT
    have hkodd := (hk k hkT).1
    refine (B.L k hkT).hS.arrJetG_diagChild (fun _ _ => trivial) (by norm_num : 1 ≤ 2) r
      (fun A hA τ hτ' => liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ
        (hDL k A hkodd hA) (R := max r 2 + Dm + 2) (by omega) (by omega) 0 le_rfl 2 τ hτ' 0)
      ?_ c
    rintro ⟨t, A⟩ ⟨t', ch, z, hPz, hcut, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨(B.hgood ⟨(t, ch, z), hPz⟩ k hkT hcut).2, (B.hgood ⟨(t, ch, z), hPz⟩ k hkT hcut).1⟩
  have hB := ArrJetG.sub hR (arrJetG_dmArr (schedSlots D i pc) hk B.hadm 2 r c hchild)
    (arrJetG_matGradArr hR (M := fun l (_ : Vec 2) =>
        ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) (l : CtxIdx (slotCtx D bw j₀ i pc)).1.1)
      (fun a b => jetRepG_labelConst hR (ctxAlg_refFlux hκm a b) r)
      (fun _ _ _ => contDiff_const) c)
  obtain ⟨φ, hφ, e, he⟩ := JetRepG.orderedDerivative (hB 1 (fun _ => g)).1 (m := r) le_rfl β
  refine ⟨e, he.congr fun t ch z hPz => ?_⟩
  have h1 := hφ ⟨(t, ch, z), hPz⟩
  have h2 := B.orderedDerivative_entry ⟨(t, ch, z), hPz⟩ c (fun _ => g) (by omega) (by omega) β
  exact (h2.symm.trans h1).symm

end Facts

/-! ### The leaf map -/

/-- The index of the bridge leaves: the slot, the entry `(c, g)` and a jet word of length at most
`n_J`. -/
abbrev BLeafIdx (nJ : ℕ) : Type := OddSlot × Fin 2 × Fin 2 × (Σ r : Fin (nJ + 1), DerivativeWord2 r.1)

/-- The length of the jet word of a bridge leaf. -/
def BLeafIdx.len {nJ : ℕ} (x : BLeafIdx nJ) : ℕ := x.2.2.2.1.1

open scoped Classical in
/-- The expression of a bridge leaf (a representation `CtxRep`, `0` if there is none). -/
def bleafExpr (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i nJ : ℕ) (x : BLeafIdx nJ) :
    Gen .ctx i x.1.1 :=
  if h : ∃ e : Gen .ctx i x.1.1, CtxRep D bw j₀ 𝒮 (slotCtx D bw j₀ i x.1.1)
      (leafSem D i (schedSlots D i x.1.1) x.2.1 x.2.2.1 x.2.2.2.2) e then Classical.choose h
  else Gen.time (.const 0)

theorem bleafExpr_spec {𝒮 : SeedExports} {nJ : ℕ} (x : BLeafIdx nJ)
    (h : ∃ e : Gen .ctx i x.1.1, CtxRep D bw j₀ 𝒮 (slotCtx D bw j₀ i x.1.1)
      (leafSem D i (schedSlots D i x.1.1) x.2.1 x.2.2.1 x.2.2.2.2) e) :
    CtxRep D bw j₀ 𝒮 (slotCtx D bw j₀ i x.1.1)
      (leafSem D i (schedSlots D i x.1.1) x.2.1 x.2.2.1 x.2.2.2.2) (bleafExpr D bw j₀ 𝒮 i nJ x) := by
  classical
  unfold bleafExpr
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact Classical.choose_spec h

/-- An injective code of the bridge leaves. -/
def bleafCode (nJ : ℕ) : BLeafIdx nJ → ℤ :=
  fun x => ((Classical.choose (Countable.exists_injective_nat (BLeafIdx nJ)) x : ℕ) : ℤ)

theorem bleafCode_injective (nJ : ℕ) : Function.Injective (bleafCode nJ) := fun x y h =>
  Classical.choose_spec (Countable.exists_injective_nat (BLeafIdx nJ)) (by
    simpa only [bleafCode, Nat.cast_inj] using h)

/-- **The leaf map of the bridge leaves.** -/
def bleaf (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i nJ : ℕ) (Δ μ₀ : ℝ) (σ KB : ℝ≥0) :
    ∀ {s : GenSort} {i : ℕ} {p : ℤ}, Gen s i p → Option (ℝ → ℤ → ℝ≥0∞) :=
  markLeaf i (fun x : BLeafIdx nJ => x.1.1) (bleafCode nJ) (bleafExpr D bw j₀ 𝒮 i nJ)
    (fun x => leafProf bw Δ μ₀ x.len (σ ^ x.len * KB))

variable {𝒮 : SeedExports} {nJ : ℕ} {Δ μ₀ : ℝ} {σ KB : ℝ≥0}

theorem bleaf_shape {s : GenSort} {i' : ℕ} {p : ℤ} (e : Gen s i' p) (he : ¬ isMarkShape e) :
    bleaf D bw j₀ 𝒮 i nJ Δ μ₀ σ KB e = none :=
  markLeaf_eq_none he

theorem bleaf_ctx (s : GenSort) (i' : ℕ) (p : ℤ) (e : Gen s i' p) (hs : s ≠ .ctx) :
    bleaf D bw j₀ 𝒮 i nJ Δ μ₀ σ KB e = none :=
  markLeaf_eq_none_of_ne e hs

/-- **The leaves of a slot**, in the form of the sized bridge arrays. -/
theorem bleaf_leaf (pc : OddSlot) (c : Fin 2)
    (hex : ∀ (g : Fin 2) (r : ℕ) (β : DerivativeWord2 r), r ≤ nJ →
      ∃ e : Gen .ctx i pc.1, CtxRep D bw j₀ 𝒮 (slotCtx D bw j₀ i pc.1)
        (leafSem D i (schedSlots D i pc.1) c g β) e)
    (g : Fin 2) (r : ℕ) (β : DerivativeWord2 r) (hr : r ≤ nJ) :
    ∃ (e : Gen .ctx i pc.1) (code : ℤ), CtxRep D bw j₀ 𝒮 (slotCtx D bw j₀ i pc.1)
        (leafSem D i (schedSlots D i pc.1) c g β) e ∧
      bleaf D bw j₀ 𝒮 i nJ Δ μ₀ σ KB (markE code e) = some (leafProf bw Δ μ₀ r (σ ^ r * KB)) := by
  set x : BLeafIdx nJ := (pc, c, g, ⟨⟨r, Nat.lt_succ_of_le hr⟩, β⟩) with hx
  exact ⟨bleafExpr D bw j₀ 𝒮 i nJ x, bleafCode nJ x, bleafExpr_spec x (hex g r β hr),
    markLeaf_markE (bleafCode_injective nJ) x⟩

/-- **The leaf map of the bridge leaves is certified.** -/
theorem leavesCertified_bleaf {CH Υ : ℝ} (env : ChainEnv D bw CH Υ j₀) (hij : j₀ ≤ i)
    (hexpU : ∀ {i p} (e : Gen .ctx i p), 𝒮 e → ∀ f f', Gen.Denotes D bw j₀ e f →
      Gen.Denotes D bw j₀ e f' → AgreeOn D bw j₀ i p .ctx f f')
    (hm : ownSize D (i + 1) ≤ 1 / 100)
    {Cd : ℝ} (hCd : D.eps (i + 1) ^ (1 + D.α) ≤ Cd * Real.sqrt (D.kap (i + 1) * D.kap i))
    (hc : 0 < D.cellScaleSq (i + 1)) (hκm : D.kap (i + 1) = D.κ (i + 1))
    (hκle : D.kap (i + 1) ≤ D.kap i) (hΔ : 0 < Δ) (hμ : μ₀ ≤ 2)
    (hσ : ENNReal.ofReal (12 / bw) / ENNReal.ofReal (D.eps i * Δ) ≤ σ)
    {Dm sX sZ N : ℕ} {ρ : ℝ} {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}
    (hRX : nJ + Dm + 2 ≤ sX) (hRZ : nJ + Dm + 2 ≤ sZ)
    (𝒜 : ℤ → Set RealChain) (t₀ t₁ : ℤ → ℝ)
    (B : ∀ pc : OddSlot, BridgeCtx D bw j₀ 𝒮 i pc.1 (slotCtx D bw j₀ i pc.1) Dm ρ sX sZ N Cc0
      (schedSlots D i pc.1) 𝒜 t₀ t₁)
    (hex : ∀ x : BLeafIdx nJ, ∃ e : Gen .ctx i x.1.1, CtxRep D bw j₀ 𝒮 (slotCtx D bw j₀ i x.1.1)
      (leafSem D i (schedSlots D i x.1.1) x.2.1 x.2.2.1 x.2.2.2.2) e) :
    LeavesCertified D bw j₀
      (bleaf D bw j₀ 𝒮 i nJ Δ μ₀ σ (compC (invP 2 nJ) nJ * (16 * sizeS D (i + 1) Cd))) := by
  refine ⟨fun s i' p e hs => bleaf_ctx s i' p e hs, fun i' p e Bx hB f hf => ?_⟩
  obtain ⟨x, hx, rfl⟩ := markLeaf_eq_some hB
  cases hx
  obtain ⟨hs, hfs, f₀, hd₀, hv₀⟩ := bleafExpr_spec x (hex x)
  have Bx := B x.1
  obtain ⟨F, hF, hmode⟩ := leafSem_cert env hij hm hCd hc hκm hκle hΔ hμ hσ hRX hRZ 𝒜 t₀ t₁
    (schedSlots D i x.1.1) (fun k hk => (Bx.hT k).1 hk) Bx.L
    (fun k hk t ht ch hch ζ hcut => Bx.hgood ⟨(t, ch, ζ), ⟨hch, ht⟩⟩ k hk hcut)
    x.2.1 x.2.2.1 (Nat.lt_succ_iff.mp x.2.2.2.1.2) x.2.2.2.2
  refine ⟨F, ⟨hF.1, hF.2.1, fun ch t ht ζ hA => ?_⟩, hmode⟩
  unfold markE at hf
  cases hf with
  | @add _ _ _ _ _ fx fz hx hz =>
    cases hx with
    | @mul _ _ _ _ _ fa fb hc' hd' =>
      cases hc'
      cases hz with
      | mul hc0 hcn =>
        cases hc0
        cases hcn
        have hag := denotes_agreeOn_of_exports env.hΛ1 env.hζ env.hb0
          (startBound_of_carrierStart env.hΛ1 env.hCH env.hΥ env.hcs) hexpU hd' hfs hs hd₀
        rw [hF.2.2 ch t ht ζ hA]
        show ((leafSem D i (schedSlots D i x.1.1) x.2.1 x.2.2.1 x.2.2.2.2 t ch ζ : ℝ) : ℂ) =
          ((1 * fb t ch ζ + 0 * _ : ℝ) : ℂ)
        rw [one_mul, zero_mul, add_zero, hag t ht ch hA ζ, hv₀ t ch ζ ⟨hA, ht⟩]
end

/-! **Ledger, first source: the coefficients over a slot.** The context calculus of the first
source at the level `i` (`diagX`: carrier constants `κc`, reserve step `Δ`, outer and inner rates
`a, a₀`, budgets `2` and `L₀`, the leaf map `bleaf` of the bridge leaves of the jet order `2p`).
Over every slot `pc` of the level `i`, the coefficient of tested order `d` of the first source of
the level `i + 1` is a sized context function of cost `fsR N p (2N + 1)` and size
`fsK · ρ^{d-1}` (`slot_firstSource_ctxAlgQ`), with
* `c_J = jhK (4p) W_g a_i c_H ρ` for the commutator arrays (`|𝖧| ≤ c_H ρ²`);
* `c_F = c_B + ∑_{n=3}^{N+1} W_c childK n` for the assembled mean arrays: the bridge leaves
  (`W_l K_B ≤ c_B ρ`, `K_B = compC (invP 2 (2p)) (2p) · 16 C_Ŝ`) and the means of the degrees
  `n ≥ 3` (`arrJetGQ_diagChildQ`). -/

section
open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext
  AVRegularity.Providers.ComplexFlow

/-- The context calculus of the first source at the level `i`. -/
def diagX (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i nJ : ℕ) (κc : MajConsts)
    (Δ a a₀ : ℝ) (L₀ : ℕ) (σ KB : ℝ≥0) : CCtx :=
  ⟨κc, Δ, a, a₀, 2, L₀, bleaf D bw j₀ 𝒮 i nJ Δ 2 σ KB⟩

theorem diagX_ok {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i nJ : ℕ} {κc : MajConsts}
    {Δ a a₀ : ℝ} {L₀ : ℕ} {σ KB : ℝ≥0} (hΔ : 0 ≤ Δ) :
    (diagX D bw j₀ 𝒮 i nJ κc Δ a a₀ L₀ σ KB).Ok :=
  ⟨hΔ, le_rfl, fun e he => bleaf_shape e he, fun s i p e hs => bleaf_ctx s i p e hs⟩

/-- The constant of the bridge leaves of the jet order `2p`. -/
def bleafK (D : OCData) (i p : ℕ) (Cd : ℝ) : ℝ≥0 :=
  compC (invP 2 (2 * p)) (2 * p) * (16 * sizeS D (i + 1) Cd)

/-- The constant of the assembled mean arrays. -/
def dfK (D : OCData) (X' : GCtx) (Dm i : ℕ) (ρ : ℝ) (N p : ℕ) (s cB Wc : ℝ≥0) : ℝ≥0 :=
  cB + ∑ n ∈ Finset.Icc 3 (N + 1), Wc * childK D X' Dm (i + 1) ρ n (2 * p) s

variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ}

/-- **The coefficients of the first source over a slot are sized context functions.** -/
theorem slot_firstSource_ctxAlgQ {CH Υ : ℝ} (env : ChainEnv D bw CH Υ j₀)
    (hκ : IsOCBandChain D.α D.q D.Λ D.ζ D.term D.κ) {ρ : ℝ} (hρ : 0 < ρ) {N p Dm sX sZ R : ℕ}
    (hN : 1 ≤ N) (hRX : R ≤ sX) (hRZ : R ≤ sZ) (hR1 : N + 1 + Dm + 2 ≤ R)
    (hR2 : 2 * p + Dm + 2 ≤ R)
    (hDst : ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)) ^ 2 =
      D.kap (i + 1 - 1) * D.cellScaleSq (i + 1))
    (hκm : D.kap (i + 1) = D.κ (i + 1)) (hκi : D.kap i = D.κ i)
    (hκle : D.kap (i + 1) ≤ D.kap i)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ))
    (hDL : ∀ (k : ℤ) (A : RealChain), Odd k → IsAdmissibleChain D bw j₀ (i + 1) k A →
      IsLiftSequence (diagQ D Dm (i + 1) k A ρ) sX sZ (liftT0 D (i + 1) k) (liftT1 D (i + 1) k)
        N 0 (Cc0 k A))
    (κc : MajConsts) {Δ a a₀ : ℝ} (hΔ : 0 < Δ) {L₀ : ℕ} (hLN : N + 1 ≤ L₀) {σ s : ℝ≥0}
    (hσc : κc.Cold / ENNReal.ofReal (D.eps i * Δ) + ENNReal.ofReal (2 * Real.pi / D.eps i) ≤ σ)
    (hσf : κc.Cslow / ENNReal.ofReal (D.eps i * Δ) ≤ σ)
    (hσw : σ * Real.toNNReal ρ ≤ s) {Wg Wc Wl Kg Kd S : ℝ≥0}
    (hWg : ∀ L, L ≤ L₀ → geoW κc a L ≤ Wg) (hWc : ∀ L, L ≤ L₀ → wsum a L κc.child ≤ Wc)
    (hWl : ∀ L, L ≤ L₀ →
      wsum a L (fun h => ENNReal.ofReal (Real.exp (-(6 * Real.pi * bw * |(h : ℝ)|)))) ≤ Wl)
    (hKg : ∀ L, L ≤ L₀ → geoW κc a₀ L ≤ Kg)
    (hKd : ∀ (k : Fin 2) (L : ℕ), L ≤ L₀ → wsum a₀ L (κc.drift k) ≤ Kd)
    (hSl : ENNReal.ofReal |ρ| * (κc.Cslow / ENNReal.ofReal (D.eps i * Δ)) ≤ S)
    {cH : ℝ≥0} (hcov : ∀ t a b, |covMat D (i + 1) 0 t a b| ≤ ((cH * Real.toNNReal ρ ^ 2 : ℝ≥0) : ℝ))
    {Cd : ℝ} {cB : ℝ≥0} (hcB : Wl * bleafK D i p Cd ≤ cB * Real.toNNReal ρ)
    (pc : OddSlot) (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ctxAlgQ D bw j₀ 𝒮 i pc.1 (slotCtx D bw j₀ i pc.1)
      (diagX D bw j₀ 𝒮 i (2 * p) κc Δ a a₀ L₀ σ (bleafK D i p Cd))
      (fun l => fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p 0 Cc0 l.1.1 l.1.2.1 l.1.2.2)
        d I 0 c)
      (fsR N p (2 * N + 1))
      (fsK N p s Wg cH (jhK (4 * p) Wg (Real.toNNReal (ocA D.α D.q D.Λ i)) cH (Real.toNNReal ρ))
        (dfK D ((diagX D bw j₀ 𝒮 i (2 * p) κc Δ a a₀ L₀ σ (bleafK D i p Cd)).toG S Kg Kd) Dm i ρ
          N p s cB Wc) * Real.toNNReal ρ ^ (d - 1)) := by
  set X := diagX D bw j₀ 𝒮 i (2 * p) κc Δ a a₀ L₀ σ (bleafK D i p Cd) with hXdef
  have hX : X.Ok := diagX_ok hΔ.le
  set P := slotCtx D bw j₀ i pc.1 with hPdef
  set T := schedSlots D i pc.1 with hTdef
  have hΛ := env.hΛ1
  have hτ : 0 < ocTau D.α D.q D.Λ (i + 1) := Construction.Stream.ocTau_pos hΛ
  have hc : 0 < D.cellScaleSq (i + 1) := EntryWeakProofs.weakData_cellScaleSq_pos D hΛ env.hζ hκ _
  have hkap : ∀ k, 0 < D.kap k := EntryWeakProofs.weakData_kap_pos D hΛ env.hζ hκ
  have hstart := startBound_of_carrierStart env.hΛ1 env.hCH env.hΥ env.hcs
  have hNR : N + Dm + 2 ≤ R := by omega
  have B := bridgeCtx_of hΛ env.hζ hκ env.hb0 hstart 𝒮 hρ.ne' hN hRX hRZ hNR hDst Cc0 hDL pc.1
  have hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc.1 :=
    fun l => ⟨l.2.1.2.2.1, l.2.1.1, l.2.1.2.2.2.1⟩
  obtain ⟨p', hp'⟩ := exists_isScheduledIn hΛ i pc.1
  -- the strain field and the lifts
  have htop : ∀ r : ℕ, ((r : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) := fun r => by
    exact_mod_cast le_top
  have hSreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
      contextStrain D i pc.1 l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c) :=
    fun l a c => (contDiff_contextStrain_recenter D env.hζ i pc.1 l.1.1 l.1.2.1 (hP l).1 l.1.2.2 a
      c).of_le (htop (4 * p))
  have hreg : ∀ l : CtxIdx P, ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ T,
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) →
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      LiftRegular (diagQ D Dm (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) ρ)
        (Cc0 k (l.1.2.1.appendChild D k l.1.1 l.1.2.2)) (0 : Fin 1)
        ((D.cellScaleSq (i + 1))⁻¹ * l.1.1) 0 n (2 * p + Dm + 2) :=
    fun l n _ _ k hk hA hcut => liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ
      (hDL k _ ((B.hT k).1 hk).1 hA) (R := 2 * p + Dm + 2) (by omega) (by omega) 0 le_rfl n _
      (B.hgood l k hk hcut).1 0
  have hH : ∀ a b, ctxAlgQ D bw j₀ 𝒮 i pc.1 P X (fun l => covMat D (i + 1) 0 l.1.1 a b) 0
      (cH * Real.toNNReal ρ ^ 2) :=
    ctxAlgQ_covMat hX hκm hκi fun t _ a b => hcov t a b
  -- the family calculus of the appended children
  have hX' : (X.toG S Kg Kd).Ok := hX.toG hKg hKd
  have hη0 : 0 ≤ D.kap (i + 1) / D.kap (i + 1 - 1) := (div_pos (hkap _) (hkap _)).le
  have hη1 : D.kap (i + 1) / D.kap (i + 1 - 1) ≤ 1 := by
    rw [div_le_one (hkap _)]
    exact hκle
  have hD0 : 0 ≤ ocDStar D.q D.Λ (i + 1) (D.kap (i + 1)) (D.kap (i + 1 - 1)) :=
    mul_nonneg (Construction.Stream.ocEpsilon_pos hΛ).le (Real.sqrt_nonneg _)
  have hchild : ∀ c', ∀ n, 3 ≤ n → n ≤ N + 1 → ∀ k ∈ T,
      ArrJetGQ (famAlgQ D bw j₀ 𝒮 (i + 1) k (childW D i k P) (X.toG S Kg Kd)) σ (Real.toNNReal ρ)
        (2 * p) (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c') (n - 1 + n)
        (childK D (X.toG S Kg Kd) Dm (i + 1) ρ n (2 * p) s) := by
    intro c' n h3 hn k hk
    have hkodd := ((B.hT k).1 hk).1
    refine arrJetGQ_diagChildQ (B.L k hk).hS hX' hSl hη0 hη1
      (by simp only [UEnv.liftWt, zero_mul, add_zero]; show N ≤ L₀; omega) (by omega)
      (by simp only [UEnv.liftWt, zero_mul, add_zero]; show n ≤ L₀; omega) (2 * p)
      (fun A hA τ hτ' => liftRegular_of_isLiftSequence D (i + 1) k hA.2.2.1 ρ (hDL k A hkodd hA)
        (R := max (2 * p) n + Dm + 2) (by omega) (by omega) 0 le_rfl n τ hτ' 0)
      hσf hρ hσw hD0 ?_ c'
    rintro ⟨t, A⟩ ⟨t', ch, z, hPz, hcut, heq⟩
    simp only [Prod.mk.injEq] at heq
    obtain ⟨rfl, rfl⟩ := heq
    exact ⟨(B.hgood ⟨(t, ch, z), hPz⟩ k hk hcut).2, (B.hgood ⟨(t, ch, z), hPz⟩ k hk hcut).1⟩
  -- the assembled mean arrays
  have hdf : ∀ c', ArrJetGQ (ctxAlgQ D bw j₀ 𝒮 i pc.1 P X) σ (Real.toNNReal ρ) (2 * p)
      (fun l => dfArr D bw j₀ Dm (i + 1) ρ N Cc0 T l.1.1 l.1.2.1 l.1.2.2 c') (2 * N + 1)
      (dfK D (X.toG S Kg Kd) Dm i ρ N p s cB Wc) := fun c' =>
    arrJetGQ_dfArrQ hX B (2 * p) (by omega) (by omega) hWl hcB c'
      (bleaf_leaf pc c' fun g r β hr => exists_leafRep hΛ env.hζ hκ env.hb0 hstart 𝒮 hρ.ne' hN
        hRX hRZ hNR hDst Cc0 hDL hκm pc.1 c' g (by omega) (by omega) β) S Kg Kd hWc _
      (hchild c')
  exact firstSource_ctxAlgQ hX env.hζ hσc hWg hΛ hρ hσw hN T B.hT hp' hP hSreg hreg hH hdf d I c
end

end AVRegularity.Providers.CascadeInvariants
end

section
open Homogenization AVRegularity AVRegularity.Sobolev
open scoped ENNReal NNReal
namespace AVRegularity.Providers.CascadeInvariants

/-! **Ledger, first source: the size algebra.**
* `fsK_eq`: the constant of the first-source arrays is linear in the constants `(c_J, c_F)` of the
  commutator and of the assembled mean arrays, `fsK = fC (c_J wE + c_F wP)`;
* `childK_congr`: the constant of the child arrays depends on the graded context only through
  `S, K_g, K_d` (`fluxXc_congr`);
* the unit bounds, against the unit `κ_i E^δ` of the first source at the length `ρ`:
  `jhK_mul_le` (the commutator, from `|𝖧| ≤ c_H ρ²`, `ρ² = κ_i τ''` and `a_i τ'' ≤ C E^δ`),
  `bleafK_le` (the bridge leaves, from `ownSize ≤ C E^δ`), `pmC_mul_le` (the means of the degrees
  `n ≥ 3`, from `d_*² = κ_i ℓ²` and `d_*/ρ ≤ C_u E^{3δ}`). -/

open AVRegularity.Providers.GenSem AVRegularity.Providers.Majorant AVRegularity.Providers.ComplexContext
  AVRegularity.Providers.ComplexFlow

/-! ### Linearity of the first-source constant -/

/-- The part of `wArr` proportional to the commutator constant. -/
def wE (p : ℕ) (s cH : ℝ≥0) : ℝ≥0 :=
  ∑ l ∈ Finset.Icc 1 p, Real.toNNReal |((l.factorial : ℝ)⁻¹)| *
    ∑ a ∈ Finset.range l, eK p s cH 1 l a

/-- The part of `wArr` proportional to the mean-array constant. -/
def wP (N p : ℕ) (s cH : ℝ≥0) : ℝ≥0 := compK (N + 1) (2 * p) s * polyK p wPcoef (2 * p + (N + 1)) s cH

/-- The prefactor of the first-source constant. -/
def fC (N p : ℕ) (s Wg cH : ℝ≥0) : ℝ≥0 :=
  chartK 0 (2 * p + (N + 1 + 2 * p)) Wg
      (s + 2 ^ (0 + (2 * p + (N + 1 + 2 * p))) * invP Wg (2 * p + (N + 1 + 2 * p))) *
    (Wg * (compK (2 * p) 0 s * polyK p wQcoef 0 s cH))

theorem eK_lin (p : ℕ) (s cH cJ : ℝ≥0) (l a : ℕ) : eK p s cH cJ l a = cJ * eK p s cH 1 l a := by
  unfold eK
  ring

theorem wK_eq (N p : ℕ) (s cH cJ cF : ℝ≥0) :
    wK N p s cH cJ cF = cJ * wE p s cH + cF * wP N p s cH := by
  unfold wK wE wP
  congr 1
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [eK_lin p s cH cJ l a]
    ring
  · ring

theorem fsK_eq (N p : ℕ) (s Wg cH cJ cF : ℝ≥0) :
    fsK N p s Wg cH cJ cF = fC N p s Wg cH * (cJ * wE p s cH + cF * wP N p s cH) := by
  unfold fsK fC
  rw [wK_eq]
  ring

/-- **The first-source constant at the length `w`** is at most `fC (K_J wE + K_F wP) u` when the
commutator and mean-array constants are at most `K_J u / w` and `K_F u / w`. -/
theorem fsK_mul_le {N p : ℕ} {s Wg cH cJ cF w KJ KF u : ℝ≥0} (hJ : cJ * w ≤ KJ * u)
    (hF : cF * w ≤ KF * u) :
    fsK N p s Wg cH cJ cF * w ≤ fC N p s Wg cH * (KJ * wE p s cH + KF * wP N p s cH) * u := by
  rw [fsK_eq]
  calc fC N p s Wg cH * (cJ * wE p s cH + cF * wP N p s cH) * w
      = fC N p s Wg cH * (cJ * w * wE p s cH + cF * w * wP N p s cH) := by ring
    _ ≤ fC N p s Wg cH * (KJ * u * wE p s cH + KF * u * wP N p s cH) := by gcongr
    _ = fC N p s Wg cH * (KJ * wE p s cH + KF * wP N p s cH) * u := by ring

/-! ### The constant of the child arrays depends only on `S, K_g, K_d` -/

theorem childK_congr {X Y : GCtx} (h : SameConsts X Y) (D : OCData) (Dm m : ℕ) (ρ : ℝ)
    (n r' : ℕ) (s : ℝ≥0) : childK D X Dm m ρ n r' s = childK D Y Dm m ρ n r' s := by
  simp only [childK, fluxXc_congr h, h.hKg]

/-! ### The unit bounds -/

/-- **The commutator constant at the length `ρ`.** -/
theorem jhK_mul_le (n : ℕ) (Wg cH : ℝ≥0) {A ρ κ τ C E δ : ℝ} (hA : 0 ≤ A) (hρ : 0 ≤ ρ)
    (hρ2 : ρ ^ 2 = κ * τ) (hκ : 0 ≤ κ) (hC : 0 ≤ C) (hE : 0 ≤ E ^ δ) (hAτ : A * τ ≤ C * E ^ δ) :
    jhK n Wg (Real.toNNReal A) cH (Real.toNNReal ρ) * Real.toNNReal ρ ≤
      4 * 2 ^ n * compC (invP Wg n) n * Wg * cH * Real.toNNReal C *
        Real.toNNReal (κ * E ^ δ) := by
  rw [← NNReal.coe_le_coe]
  unfold jhK
  simp only [NNReal.coe_mul, NNReal.coe_pow, NNReal.coe_ofNat, Real.coe_toNNReal _ hA,
    Real.coe_toNNReal _ hρ, Real.coe_toNNReal _ hC, Real.coe_toNNReal _ (mul_nonneg hκ hE)]
  set K : ℝ := 4 * 2 ^ n * (compC (invP Wg n) n : ℝ) * (Wg : ℝ) * (cH : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  have h1 : A * ρ ^ 2 ≤ κ * (C * E ^ δ) := by
    rw [hρ2, show A * (κ * τ) = κ * (A * τ) by ring]
    exact mul_le_mul_of_nonneg_left hAτ hκ
  calc 4 * 2 ^ n * ((compC (invP Wg n) n : ℝ) * (A * (Wg : ℝ))) * (cH : ℝ) * ρ * ρ
      = K * (A * ρ ^ 2) := by rw [hK]; ring
    _ ≤ K * (κ * (C * E ^ δ)) := mul_le_mul_of_nonneg_left h1 hK0
    _ = 4 * 2 ^ n * (compC (invP Wg n) n : ℝ) * (Wg : ℝ) * (cH : ℝ) * C * (κ * E ^ δ) := by
        rw [hK]; ring

/-- **The constant of the bridge leaves.** -/
theorem bleafK_le (D : OCData) (i p : ℕ) (Cd : ℝ) {C E δ : ℝ} (hown : ownSize D (i + 1) ≤ C * E ^ δ)
    (hκ : 0 ≤ D.kap i) (hC : 0 ≤ C) :
    bleafK D i p Cd ≤ compC (invP 2 (2 * p)) (2 * p) * 16 * Real.toNNReal (14 * (Cd ^ 2 + 1)) *
      Real.toNNReal C * Real.toNNReal (D.kap i * E ^ δ) := by
  unfold bleafK sizeS
  have h14 : 0 ≤ 14 * (Cd ^ 2 + 1) := by positivity
  have hs : Real.toNNReal (14 * (Cd ^ 2 + 1) * D.kap (i + 1 - 1) * ownSize D (i + 1)) ≤
      Real.toNNReal (14 * (Cd ^ 2 + 1)) * Real.toNNReal C * Real.toNNReal (D.kap i * E ^ δ) := by
    rw [← Real.toNNReal_mul h14, ← Real.toNNReal_mul (mul_nonneg h14 hC)]
    refine Real.toNNReal_le_toNNReal ?_
    rw [Nat.add_sub_cancel]
    calc 14 * (Cd ^ 2 + 1) * D.kap i * ownSize D (i + 1)
        ≤ 14 * (Cd ^ 2 + 1) * D.kap i * (C * E ^ δ) :=
          mul_le_mul_of_nonneg_left hown (mul_nonneg h14 hκ)
      _ = 14 * (Cd ^ 2 + 1) * C * (D.kap i * E ^ δ) := by ring
  calc compC (invP 2 (2 * p)) (2 * p) *
        (16 * Real.toNNReal (14 * (Cd ^ 2 + 1) * D.kap (i + 1 - 1) * ownSize D (i + 1)))
      ≤ compC (invP 2 (2 * p)) (2 * p) * (16 * (Real.toNNReal (14 * (Cd ^ 2 + 1)) *
          Real.toNNReal C * Real.toNNReal (D.kap i * E ^ δ))) := by gcongr
    _ = _ := by ring

/-- The prefactor of the path mean array at the length `ρ`: `pmC ρ = κ (d_*/ρ)^{n-2}`. -/
theorem pmC_mul_eq (D : OCData) (m : ℕ) {ρ : ℝ} (hρ : ρ ≠ 0) (hc : D.cellScaleSq m ≠ 0) {n : ℕ}
    (hn : 2 ≤ n) (hDst : ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) ^ 2 =
      D.kap (m - 1) * D.cellScaleSq m) :
    LiftGenSetup.pmC D m ρ n * ρ =
      D.kap (m - 1) * (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1)) / ρ) ^ (n - 2) := by
  unfold LiftGenSetup.pmC
  obtain ⟨j, rfl⟩ : ∃ j, n = j + 2 := ⟨n - 2, by omega⟩
  rw [Nat.add_sub_cancel, pow_add, div_pow (ocDStar D.q D.Λ m (D.kap m) (D.kap (m - 1))) ρ 2,
    hDst]
  field_simp

/-- **The prefactor of the path mean arrays of the degrees `n ≥ 3` at the length `ρ`.** -/
theorem pmC_mul_le {Cu E δ q κ : ℝ} {n : ℕ} (hn : 3 ≤ n) (hq0 : 0 ≤ q) (hqE : q ≤ Cu * E ^ (3 * δ))
    (hCu : 1 ≤ Cu) (hE0 : 0 < E) (hE1 : E ≤ 1) (hδ : 0 ≤ δ) (hκ : 0 ≤ κ) :
    κ * q ^ (n - 2) ≤ Cu ^ (n - 2) * (κ * E ^ δ) := by
  have h3 : 0 ≤ E ^ (3 * δ) := Real.rpow_nonneg hE0.le _
  have h31 : E ^ (3 * δ) ≤ 1 := Real.rpow_le_one hE0.le hE1 (by positivity)
  have h3d : E ^ (3 * δ) ≤ E ^ δ := Real.rpow_le_rpow_of_exponent_ge hE0 hE1 (by linarith)
  have hpow : (E ^ (3 * δ)) ^ (n - 2) ≤ E ^ (3 * δ) := pow_le_of_le_one h3 h31 (by omega)
  calc κ * q ^ (n - 2) ≤ κ * (Cu * E ^ (3 * δ)) ^ (n - 2) :=
        mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hq0 hqE _) hκ
    _ = Cu ^ (n - 2) * (κ * (E ^ (3 * δ)) ^ (n - 2)) := by rw [mul_pow]; ring
    _ ≤ Cu ^ (n - 2) * (κ * E ^ δ) := by
        gcongr
        exact hpow.trans h3d

end AVRegularity.Providers.CascadeInvariants
end
