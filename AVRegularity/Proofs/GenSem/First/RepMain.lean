-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.Jet.CtxChart
import AVRegularity.Proofs.GenSem.Strain.Main
import AVRegularity.Proofs.GenSem.LiftOn.Omega
public import AVRegularity.Proofs.GenSem.First.Identity
import AVRegularity.Construction.Stream.NextAdmissible
import AVRegularity.Proofs.GenSem.Jet.Chart
import AVRegularity.Proofs.GenSem.Op.FamChart

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.GenSem

/-! **The first source is a context expression.** Every coefficient
`fluxCoeff (firstSourceFlux … t ch z) d I 0 c` is, on the contexts `P` of level `i` over the slot
`pc`, the denotation of one scheduled context expression with seed provenance
(`firstSource_ctxRep`).

The arrays `fsArr` of `firstSourceFlux_applyArr` carry represented context jets (`ArrJetG` over
the context algebra `ctxAlg P`):
* the context strain at the recentered contexts is the strain letter of an appended child
  (`contextStrain_eq_childStrain`), covariant under `dOld`; composed with the inverse chart;
* the covariance and reference matrices are the time letters `covPrimitive`, `refFlux`;
* the assembled mean flux reads the push-forward arrays of the appended children (family jets,
  hypothesis `hchild`), evaluated at the child (`jetRepG_evalChild`);
* the pullback by the chart pair of the context family (`jetRepG_ctx_famMap`,
  `jetRepG_ctx_famMapInv`, inverse Jacobians through `jacInv`).

Hypotheses beyond the identity: the contexts are well slotted at level `i` over `pc`; some finer
slot `p'` is scheduled in `pc`; the anchor is `0`; `kap = κ` at `i`, `i + 1`; the appended children
with a nonzero weight are admissible; the strain is `C^{4p}` in the recentering offset; the child
push-forward arrays have represented family jets of order `2p`. -/

section
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop}

/-! ### Time letters at the context level -/

theorem ctxAlg_covMat_zero (hκ : D.kap (i + 1) = D.κ (i + 1)) (hκ' : D.kap i = D.κ i)
    (a b : Fin 2) :
    ctxAlg D bw j₀ 𝒮 i pc P (fun l => covMat D (i + 1) 0 l.1.1 a b) :=
  ⟨fun t _ _ => covMat D (i + 1) 0 t a b, fun _ => rfl,
    Gen.time (.covPrimitive (i + 1) 0 a b), .timeCov _ _ _, .time _, _, .time _,
    fun t ch z _ => by
      simp only [covMat, GenSort.ofTime, TimeLetter.eval, hκ, Nat.add_sub_cancel, hκ']⟩

/-- The covariance at any anchor `s₀`: the time letter at the anchor `0` minus the time constant
at `s₀` (`ocCovariance_anchor`). -/
theorem ctxAlg_covMat {s₀ : ℝ} (hΛ : 1 ≤ D.Λ) (hζ : IsFastProfile D.ζ)
    (hν : 0 < D.κ (i + 1)) (hκ : D.kap (i + 1) = D.κ (i + 1)) (hκ' : D.kap i = D.κ i)
    (a b : Fin 2) :
    ctxAlg D bw j₀ 𝒮 i pc P (fun l => covMat D (i + 1) s₀ l.1.1 a b) := by
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc P
  have h := hR.add (ctxAlg_covMat_zero (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (pc := pc) (P := P) hκ hκ'
    a b) (hR.const (-covMat D (i + 1) 0 s₀ a b))
  have heq : (fun l : CtxIdx P => covMat D (i + 1) s₀ l.1.1 a b) =
      fun l : CtxIdx P => covMat D (i + 1) 0 l.1.1 a b + -covMat D (i + 1) 0 s₀ a b :=
    funext fun l =>
      (ocCovariance_anchor D hΛ hζ (i + 1) hν _ s₀ l.1.1 a b).trans (sub_eq_add_neg _ _)
  rw [heq]
  exact h

theorem ctxAlg_refFlux (hκ : D.kap (i + 1) = D.κ (i + 1)) (a b : Fin 2) :
    ctxAlg D bw j₀ 𝒮 i pc P (fun l => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) l.1.1 a b) :=
  ⟨fun t _ _ => ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) t a b, fun _ => rfl,
    Gen.time (.refFlux (i + 1) a b), .timeRef _ _ _, .time _, _, .time _,
    fun t ch z _ => by simp only [GenSort.ofTime, TimeLetter.eval, hκ]⟩

/-! ### The strain field -/

/-- **Context jets of the strain field** `x ↦ S_c(x)`. -/
theorem jetRepG_strainAt (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    {p' : ℤ} (hp' : IsScheduledIn D i p' pc) (r : ℕ)
    (hreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ (r : WithTop ℕ∞) (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (a c : Fin 2) :
    JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r (fun l x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c) := by
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc P
  have key : ∀ (t : ℝ) (ch' : RealChain) (ζ' : Vec 2), ch'.WellSlotted → ch'.ctxLevel = i →
      ch'.slot = pc → contextStrain D i pc t ch' ζ' = (ch'.appendChild D p' t ζ').famStrain D t := by
    intro t ch' ζ' hw h1 h2
    rw [← h1, ← h2]
    exact contextStrain_eq_childStrain D hζ hΛ ch' hw p' t ζ'
  -- the child strain is the normalized letter times its strain rate `a_i`
  have hA : ocA D.α D.q D.Λ i ≠ 0 :=
    (Real.rpow_pos_of_pos (AVRegularity.Construction.Stream.ocEpsilon_pos hΛ) _).ne'
  have hG : JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r (fun l y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c) :=
    jetRepG_covariant_ctx hζ r (a := Gen.mul (Gen.time (.const (ocA D.α D.q D.Λ i)))
        (Gen.geo (i := i) (p := pc) (.child p') (.strain a c)))
      (U := fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.mem_univ _)
      (.mul (.timeConst _) (.geoChild p' _ hp')) (.mul (.time _) (.geo _ _))
      (.mul (.time _) (.geo _ _)) fun l w _ => by
        obtain ⟨hws, hlev, hslot⟩ := hP l
        have hw := recenter_wellSlotted D _ hws w
        have hlev' : (l.1.2.1.recenter D w).ctxLevel = i := by rw [recenter_ctxLevel]; exact hlev
        rw [key _ _ _ hw.1 hlev' (by rw [hw.2]; exact hslot)]
        have hll : ((l.1.2.1.recenter D w).appendChild D p' l.1.1
            (l.1.2.2 + (D.eps i)⁻¹ • w)).lastLevel = i := by
          rw [← hlev']
          simp only [RealChain.appendChild, RealChain.lastLevel, RealChain.ctxLevel,
            List.length_append, List.length_singleton]
          omega
        simp only [GenSort.mul, GenSort.ofTime, TimeLetter.eval, GeoLetter.eval,
          GeoLetter.isStrain, true_or, ite_true, GeoLetter.evalAt, hll]
        field_simp
  have hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted := fun l => (hP l).1
  have hcomp := JetRepG.comp hR (r := r)
    (g := fun l y => contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c)
    (Ψ := fun l x => l.1.2.1.famMapInv D l.1.1 x) (fun l => famMapInv_zero hζ _ _)
    (fun l => hreg l a c) (fun l => (contDiff_famMapInv _ _).of_le (by exact_mod_cast le_top)) hG
    (fun b => jetRepG_ctx_famMapInv hζ hW r b)
  refine hcomp.congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
  simp only [strainAt, Nat.add_sub_cancel, (hP l).2.2]

/-! ### The commutator arrays -/

theorem arrJetG_jhArr (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) {s₀ : ℝ} (hν : 0 < D.κ (i + 1))
    (hκ : D.kap (i + 1) = D.κ (i + 1)) (hκ' : D.kap i = D.κ i)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    {p' : ℤ} (hp' : IsScheduledIn D i p' pc) (r : ℕ)
    (hreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ (r : WithTop ℕ∞) (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (hstr : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ (r : WithTop ℕ∞)
      (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c)) (c : Fin 2) :
    ArrJetG (ctxAlg D bw j₀ 𝒮 i pc P) r
      (fun l => jhArr D (i + 1) s₀ l.1.1 l.1.2.1 l.1.2.2 c) := by
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc P
  have hS := jetRepG_strainAt (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) hζ hΛ hP hp' r hreg
  have hH : ∀ a b, JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r (fun l (_ : Vec 2) => covMat D (i + 1) s₀ l.1.1 a b) :=
    fun a b => jetRepG_labelConst hR (ctxAlg_covMat hΛ hζ hν hκ hκ' a b) r
  have hMj : ∀ a b, JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r
      (fun l x => jhMat D (i + 1) s₀ l.1.1 l.1.2.1 l.1.2.2 x a b) := by
    intro a b
    have h1 := JetRepG.finsetSum hR (r := r) Finset.univ
      (F := fun j l x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a j * covMat D (i + 1) s₀ l.1.1 j b)
      (fun j _ l => (hstr l a j).mul contDiff_const)
      (fun j _ => JetRepG.mul hR (fun l => hstr l a j) (fun _ => contDiff_const) (hS a j) (hH j b))
    have h2 := JetRepG.finsetSum hR (r := r) Finset.univ
      (F := fun j l x => covMat D (i + 1) s₀ l.1.1 a j * strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x b j)
      (fun j _ l => contDiff_const.mul (hstr l b j))
      (fun j _ => JetRepG.mul hR (fun _ => contDiff_const) (fun l => hstr l b j) (hH a j) (hS b j))
    refine (JetRepG.add hR (fun l => ContDiff.sum fun j _ => (hstr l a j).mul contDiff_const)
      (fun l => ContDiff.sum fun j _ => contDiff_const.mul (hstr l b j)) h1 h2).congr_germ
      fun l => Filter.Eventually.of_forall fun x => ?_
    simp [jhMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
  have hMs : ∀ a b l, ContDiff ℝ (r : WithTop ℕ∞)
      (fun x => jhMat D (i + 1) s₀ (l : CtxIdx P).1.1 l.1.2.1 l.1.2.2 x a b) := by
    intro a b l
    simp only [jhMat, Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply]
    exact (ContDiff.sum fun j _ => (hstr l a j).mul contDiff_const).add
      (ContDiff.sum fun j _ => contDiff_const.mul (hstr l b j))
  exact ArrJetG.smul' hR (hR.const (-1)) (arrJetG_matGradArr hR hMj hMs c)
end

/-! **D6c: the first source is a context expression** (`firstSource_ctxRep`). See `First/Rep`
for the strain and commutator jets; here the assembled mean arrays, the combination `wArr`, the
pullback and the extraction. -/

section
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop} {Dm : ℕ} {ρ : ℝ} {N p : ℕ} {s₀ : ℝ}
  {Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)}

/-- **Jets of the assembled mean arrays** at the contexts, from family jets of the push-forward
arrays of the appended children. -/
theorem arrJetG_dmArr (S : Finset ℤ) (hk : ∀ k ∈ S, Odd k ∧ IsScheduledIn D i k pc)
    (hadm : ∀ l : CtxIdx P, ∀ k ∈ S, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2))
    (n r : ℕ) (c : Fin 2)
    (hchild : ∀ k ∈ S, ArrJetG (famAlg D bw j₀ 𝒮 (i + 1) k (childW D i k P)) r
      (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c)) :
    ArrJetG (ctxAlg D bw j₀ 𝒮 i pc P) r
      (fun l => dmArr D bw j₀ Dm (i + 1) ρ Cc0 S l.1.1 l.1.2.1 l.1.2.2 n c) := by
  classical
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc P
  have e : (fun l : CtxIdx P => dmArr D bw j₀ Dm (i + 1) ρ Cc0 S l.1.1 l.1.2.1 l.1.2.2 n c) =
      fun l => ∑ k ∈ S, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 •
        diagChildArr D Dm (i + 1) ρ Cc0 k n l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2) c := by
    funext l
    unfold dmArr
    refine Finset.sum_congr rfl fun k hkS => ?_
    split_ifs with h
    · rfl
    · by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
      · rw [h0, zero_smul]
      · exact absurd (hadm l k hkS h0) h
  rw [e]
  refine ArrJetG.sum hR S fun k hkS => fun m α => ⟨?_, fun l => ?_⟩
  · exact (jetRepG_evalChild k (hk k hkS) r
      (G := fun t B y => diagChildArr D Dm (i + 1) ρ Cc0 k n t B c m α y 0)
      ((hchild k hkS) m α).1).congr_germ fun _ => Filter.Eventually.of_forall fun _ => rfl
  · by_cases h0 : ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 = 0
    · simp only [h0, zero_smul]
      exact contDiff_const
    · exact contDiff_const.mul (((hchild k hkS) m α).2
        ⟨(l.1.1, l.1.2.1.appendChild D k l.1.1 l.1.2.2), ⟨l.1.1, l.1.2.1, l.1.2.2, l.2, h0, rfl⟩⟩)

theorem arrJetG_dfArr (hκ : D.kap (i + 1) = D.κ (i + 1)) (S : Finset ℤ)
    (hk : ∀ k ∈ S, Odd k ∧ IsScheduledIn D i k pc)
    (hadm : ∀ l : CtxIdx P, ∀ k ∈ S, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2))
    (r : ℕ) (c : Fin 2)
    (hchild : ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ S,
      ArrJetG (famAlg D bw j₀ 𝒮 (i + 1) k (childW D i k P)) r
        (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c)) (hN : 1 ≤ N) :
    ArrJetG (ctxAlg D bw j₀ 𝒮 i pc P) r
      (fun l => dfArr D bw j₀ Dm (i + 1) ρ N Cc0 S l.1.1 l.1.2.1 l.1.2.2 c) := by
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc P
  unfold dfArr
  refine ArrJetG.add hR (ArrJetG.sub hR (arrJetG_dmArr S hk hadm 2 r c (hchild 2 le_rfl (by omega)))
    (arrJetG_matGradArr hR (M := fun l (_ : Vec 2) =>
        ocRefFlux D.α D.q D.Λ D.ζ (i + 1) (D.κ (i + 1)) (l : CtxIdx P).1.1)
      (fun a b => jetRepG_labelConst hR (ctxAlg_refFlux hκ a b) r) (fun _ _ _ => contDiff_const) c))
    (ArrJetG.sum hR _ fun n hn => ?_)
  have hn' := Finset.mem_Icc.mp hn
  exact arrJetG_dmArr S hk hadm n r c (hchild n (by omega) hn'.2)

theorem arrJetG_wArr (hζ : IsFastProfile D.ζ) (hΛ : 1 ≤ D.Λ) (hν : 0 < D.κ (i + 1))
    (hκ : D.kap (i + 1) = D.κ (i + 1)) (hκ' : D.kap i = D.κ i)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    {p' : ℤ} (hp' : IsScheduledIn D i p' pc) (S : Finset ℤ)
    (hk : ∀ k ∈ S, Odd k ∧ IsScheduledIn D i k pc)
    (hadm : ∀ l : CtxIdx P, ∀ k ∈ S, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2))
    (r : ℕ)
    (hreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ ((r + 2 * p : ℕ) : WithTop ℕ∞) (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (hstr : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ ((r + 2 * p : ℕ) : WithTop ℕ∞)
      (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c))
    (hchild : ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ S, ∀ c,
      ArrJetG (famAlg D bw j₀ 𝒮 (i + 1) k (childW D i k P)) r
        (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c)) (hN : 1 ≤ N) (c : Fin 2) :
    ArrJetG (ctxAlg D bw j₀ 𝒮 i pc P) r
      (fun l => wArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 S l.1.1 l.1.2.1 l.1.2.2 c) := by
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc P
  have hH : ∀ a b, ctxAlg D bw j₀ 𝒮 i pc P (fun l => covMat D (i + 1) s₀ l.1.1 a b) :=
    ctxAlg_covMat hΛ hζ hν hκ hκ'
  have hjh := fun c' => arrJetG_jhArr (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) (s₀ := s₀) hζ hΛ hν hκ hκ'
    hP hp' (r + 2 * p) hreg hstr c'
  unfold wArr
  refine ArrJetG.add hR (ArrJetG.neg hR (ArrJetG.sum hR _ fun l hl =>
    ArrJetG.smul' hR (hR.const _) (ArrJetG.sum hR _ fun a ha => ?_)))
    (arrJetG_compArr hR (N + 1) (arrJetG_dfArr hκ S hk hadm r c (fun n h1 h2 k hk' =>
      hchild n h1 h2 k hk' c) hN) (arrJetG_polyArr hR hH p wPcoef (r + (N + 1))))
  have hlp := Finset.mem_Icc.mp hl
  have hal := Finset.mem_range.mp ha
  exact arrJetG_compArr hR (2 * a) (arrJetG_covArrPow hR hH a r)
    (arrJetG_compArr hR 1 ((hjh c).mono (by omega)) (arrJetG_covArrPow hR hH _ (r + 2 * a + 1)))

theorem arrSupp_fsArr (D : OCData) (b : ℝ) (j₀ Dm m : ℕ) (ρ : ℝ) (N p : ℕ) (s₀ : ℝ)
    (Cc0 : ℤ → RealChain → ℕ → ℕ → LiftCoeff (Fin 1) (fun _ => ℝ)) (S : Finset ℤ) (t : ℝ)
    (ch : RealChain) (ζ : Vec 2) (c : Fin 2) :
    ArrSupp (2 * p + (N + 1 + 2 * p)) (fsArr D b j₀ Dm m ρ N p s₀ Cc0 S t ch ζ c) :=
  arrSupp_chartArr _ _ _ _ _ c

/-- **The first source is a context expression.** -/
theorem firstSource_ctxRep (hζ : IsFastProfile D.ζ) (hρ : ρ ≠ 0) (hΛ : 1 ≤ D.Λ) (hN : 1 ≤ N)
    (hν : 0 < D.κ (i + 1)) (hκ : D.kap (i + 1) = D.κ (i + 1)) (hκ' : D.kap i = D.κ i)
    (S : Finset ℤ)
    (hS : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D i k pc) {p' : ℤ} (hp' : IsScheduledIn D i p' pc)
    (hP : ∀ l : CtxIdx P, l.1.2.1.WellSlotted ∧ l.1.2.1.ctxLevel = i ∧ l.1.2.1.slot = pc)
    (hadm : ∀ l : CtxIdx P, ∀ k ∈ S, ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2))
    (hSreg : ∀ l : CtxIdx P, ∀ a c, ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞) (fun y =>
      contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c))
    (hreg : ∀ l : CtxIdx P, ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ S,
      IsAdmissibleChain D bw j₀ (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) →
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 ≠ 0 →
      LiftRegular (diagQ D Dm (i + 1) k (l.1.2.1.appendChild D k l.1.1 l.1.2.2) ρ)
        (Cc0 k (l.1.2.1.appendChild D k l.1.1 l.1.2.2)) (0 : Fin 1)
        ((D.cellScaleSq (i + 1))⁻¹ * l.1.1) 0 n (2 * p + Dm + 2))
    (hchild : ∀ n, 2 ≤ n → n ≤ N + 1 → ∀ k ∈ S, ∀ c,
      ArrJetG (famAlg D bw j₀ 𝒮 (i + 1) k (childW D i k P)) (2 * p)
        (fun q => diagChildArr D Dm (i + 1) ρ Cc0 k n q.1.1 q.1.2 c))
    (d : ℕ) (I : DerivativeWord2 (d - 1)) (c : Fin 2) :
    ∃ e : Gen .ctx i pc, CtxRep D bw j₀ 𝒮 P (fun t ch z =>
      fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 t ch z) d I 0 c) e := by
  have hR := repAlg_ctxAlg D bw j₀ 𝒮 i pc P
  have hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted := fun l => (hP l).1
  have hk : ∀ k ∈ S, Odd k ∧ IsScheduledIn D i k pc := fun k hkS => (hS k).1 hkS
  have hH : ∀ a b, ctxAlg D bw j₀ 𝒮 i pc P (fun l => covMat D (i + 1) s₀ l.1.1 a b) :=
    ctxAlg_covMat hΛ hζ hν hκ hκ'
  -- the strain field in the label variable
  have hstr : ∀ l : CtxIdx P, ∀ a c', ContDiff ℝ ((4 * p : ℕ) : WithTop ℕ∞)
      (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c') := by
    intro l a c'
    have e : (fun x => strainAt D (i + 1) l.1.1 l.1.2.1 l.1.2.2 x a c') =
        (fun y => contextStrain D i pc l.1.1 (l.1.2.1.recenter D y) (l.1.2.2 + (D.eps i)⁻¹ • y) a c')
          ∘ l.1.2.1.famMapInv D l.1.1 := by
      funext x
      simp only [strainAt, Function.comp_apply, Nat.add_sub_cancel, (hP l).2.2]
    have htopV : ∀ (r : ℕ) {g : Vec 2 → Vec 2}, ContDiff ℝ (⊤ : ℕ∞) g →
        ContDiff ℝ (r : WithTop ℕ∞) g := fun r _ hg => hg.of_le (by exact_mod_cast le_top)
    rw [e]
    exact (hSreg l a c').comp (htopV (4 * p) (contDiff_famMapInv _ _))
  -- the jets of the arrays
  set K := 2 * p + (N + 1 + 2 * p) with hK
  have hq : ∀ k, ArrJetG (ctxAlg D bw j₀ 𝒮 i pc P) 0 (fun l => compArr (2 * p)
      (polyArr (covMat D (i + 1) s₀ l.1.1) p wQcoef)
      (wArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 S l.1.1 l.1.2.1 l.1.2.2 k) 0) := fun k =>
    arrJetG_compArr hR (2 * p) (arrJetG_polyArr hR hH p wQcoef 0)
      (by
        rw [zero_add]
        exact arrJetG_wArr hζ hΛ hν hκ hκ' hP hp' S hk hadm (2 * p)
          (by rw [show 2 * p + 2 * p = 4 * p by ring]; exact hSreg)
          (by rw [show 2 * p + 2 * p = 4 * p by ring]; exact hstr) hchild hN k)
  have hMinv : ∀ c' k', JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) 0
      (fun l x => ((jacMatrix (l.1.2.1.famMap D l.1.1) x)⁻¹) c' k') := by
    intro c' k'
    have h0 := jetRepG_covariant_ctx (D := D) (bw := bw) (j₀ := j₀) (𝒮 := 𝒮) hζ 0
      (P := P) (a := Gen.geo (i := i) (p := pc) .own (.jacInv c' k')) (U := fun _ => Set.univ)
      (fun _ => isOpen_univ) (fun _ => Set.mem_univ _) (.geoOwn _) (.geo _ _) (.geo _ _)
      (g := fun l w => ((l.1.2.1.recenter D w).famJac D l.1.1)⁻¹ c' k') fun l w _ => rfl
    refine h0.congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
    simp only
    rw [jacMatrix_famMap hζ l.1.2.1 (hW l) l.1.1 x]
  have hF : ∀ c', ArrJetG (ctxAlg D bw j₀ 𝒮 i pc P) 0
      (fun l => fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 S l.1.1 l.1.2.1 l.1.2.2 c') := fun c' =>
    arrJetG_pull hR (K := K) (fun l => famMap_zero _ _)
      (fun l => (contDiff_famMap _ _).of_le (by exact_mod_cast le_top))
      (fun b => jetRepG_ctx_famMap hζ hW 0 b) (fun l => contDiff_famMapInv _ _)
      (fun b => jetRepG_ctx_famMapInv hζ hW (0 + K) b) hMinv
      (fun c'' k' l => by
        have e : (fun x => ((jacMatrix (l.1.2.1.famMap D l.1.1) x)⁻¹) c'' k') =
            fun x => ((l.1.2.1.recenter D x).famJac D l.1.1)⁻¹ c'' k' := by
          funext x; rw [jacMatrix_famMap hζ l.1.2.1 (hW l) l.1.1 x]
        rw [e]
        exact (contDiff_famJacInv hζ l.1.2.1 (hW l) l.1.1 c'' k').of_le
          (by exact_mod_cast le_top)) hq c'
  -- the extraction
  set K' := max K (d - 1) with hK'
  obtain ⟨φ, hφ, e, he⟩ := rep_fluxCoeff_applyArr hR (K := K')
    (A := fun l k => fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 S l.1.1 l.1.2.1 l.1.2.2 k) d I
    (le_max_right _ _) c (fun m α => (hF c m α).1.value)
  refine ⟨e, he.congr fun t ch z hPz => ?_⟩
  have hl := hP ⟨(t, ch, z), hPz⟩
  have hmono : ContDiff ℝ (⊤ : ℕ∞) (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) :=
    (contDiff_mono (0 : Vec 2) I).of_le le_top
  have hS' : ∀ k, k ∈ S ↔ Odd k ∧ IsScheduledIn D (i + 1 - 1) k ch.slot := by
    intro k; rw [Nat.add_sub_cancel, hl.2.2]; exact hS k
  have hvec : firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 t ch z
      (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 =
      fun k => applyArr K' (fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 S t ch z k)
        (fun Y : Vec 2 => ∏ j, (Y - 0) (I j)) 0 0 := by
    refine funext fun k => ?_
    rw [firstSourceFlux_applyArr hζ hρ hN t ch z S hS' (hstr ⟨(t, ch, z), hPz⟩)
      (hreg ⟨(t, ch, z), hPz⟩) hmono 0 k,
      applyArr_eq_of_supp (le_max_left K (d - 1)) (arrSupp_fsArr _ _ _ _ _ _ _ _ _ _ _ _ _ _ k)]
  have key : fluxCoeff (fun g y k => applyArr K' (fsArr D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 S t ch z k)
      g y 0) d I 0 c = fluxCoeff (firstSourceFlux D bw j₀ Dm (i + 1) ρ N p s₀ Cc0 t ch z) d I 0 c := by
    unfold fluxCoeff
    rw [hvec]
  exact (hφ ⟨(t, ch, z), hPz⟩).symm.trans key
end

end AVRegularity.Providers.GenSem
end
