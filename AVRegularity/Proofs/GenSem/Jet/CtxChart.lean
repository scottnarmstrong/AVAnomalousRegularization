-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.Proofs.GenSem.Jet.JetRepG
public import AVRegularity.Proofs.GenSem.Transfer.Assemble
import AVRegularity.Proofs.GenSem.Jet.Chart

@[expose] public noncomputable section

section
open Homogenization AVRegularity AVRegularity.Sobolev Filter Topology
namespace AVRegularity.Providers.GenSem

/-! **D6a: the context instance of the jet calculus.** `ctxAlg P`: scalar functions of the context
index `(t, ch, ζ)` (subject to the condition `P`) that agree with a represented context function
(`CtxRep`). Covariant context functions — the value at the label `w` is a context function at the
recentered context `(ch^{[w]}, ζ + ε_i⁻¹ w)` — have represented jets of every order, by iterated
old-label derivatives `dOld` (K3)(a). The evaluation at an appended child turns represented family
values into context values (`ctxAlg_evalChild`). -/

section
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}

/-- The context index under the condition `P`. -/
abbrev CtxIdx (P : ℝ → RealChain → Vec 2 → Prop) : Type :=
  {x : ℝ × RealChain × Vec 2 // P x.1 x.2.1 x.2.2}

/-- The context algebra: functions of the index agreeing with a represented context function. -/
def ctxAlg (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (pc : ℤ)
    (P : ℝ → RealChain → Vec 2 → Prop) : (CtxIdx P → ℝ) → Prop :=
  fun F => ∃ φ : ℝ → RealChain → Vec 2 → ℝ, (∀ l : CtxIdx P, F l = φ l.1.1 l.1.2.1 l.1.2.2) ∧
    ∃ e : Gen .ctx i pc, CtxRep D bw j₀ 𝒮 P φ e

theorem repAlg_ctxAlg (D : OCData) (bw : ℝ) (j₀ : ℕ) (𝒮 : SeedExports) (i : ℕ) (pc : ℤ)
    (P : ℝ → RealChain → Vec 2 → Prop) : RepAlg (ctxAlg D bw j₀ 𝒮 i pc P) where
  const c := ⟨fun _ _ _ => c, fun _ => rfl, _, CtxRep.const c⟩
  add := by
    rintro F G ⟨F', hF, a, ha⟩ ⟨G', hG, b, hb⟩
    exact ⟨_, fun l => by show F l + G l = _; rw [hF, hG], _, ha.add hb⟩
  mul := by
    rintro F G ⟨F', hF, a, ha⟩ ⟨G', hG, b, hb⟩
    exact ⟨_, fun l => by show F l * G l = _; rw [hF, hG], _, ha.mul hb⟩

/-- **Covariant context jets** (open neighbourhood version). -/
theorem jetRepG_covariant_ctx (hζ : IsFastProfile D.ζ) {P : ℝ → RealChain → Vec 2 → Prop} :
    ∀ (r : ℕ) {g : CtxIdx P → Vec 2 → ℝ} {a : Gen .ctx i pc} {fa : GenSort.Sem .ctx}
      {U : CtxIdx P → Set (Vec 2)}, (∀ l, IsOpen (U l)) → (∀ l, (0 : Vec 2) ∈ U l) →
      Gen.IsScheduled D a → Gen.FromSeed 𝒮 a → Gen.Denotes D bw j₀ a fa →
      (∀ l, ∀ w ∈ U l, g l w =
        fa l.1.1 (l.1.2.1.recenter D w) (l.1.2.2 + (D.eps i)⁻¹ • w)) →
      JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r g := by
  intro r
  induction r with
  | zero =>
    intro g a fa U _ h0 hs hf hd hg
    refine ⟨fun t ch z => fa t ch z, fun l => ?_, a, hs, hf, fa, hd, fun _ _ _ _ => rfl⟩
    show g l 0 = fa _ _ _
    rw [hg l 0 (h0 l), recenter_zero D hζ, smul_zero, add_zero]
  | succ r ih =>
    intro g a fa U hU h0 hs hf hd hg
    refine ⟨⟨fun t ch z => fa t ch z, fun l => ?_, a, hs, hf, fa, hd, fun _ _ _ _ => rfl⟩,
      fun j => ?_⟩
    · show g l 0 = fa _ _ _
      rw [hg l 0 (h0 l), recenter_zero D hζ, smul_zero, add_zero]
    refine ih (a := Gen.dOld j a) (U := U) hU h0 (.dOld j hs) (.dOld j hf) (.dOld j hd)
      fun l w hw => ?_
    have hev : g l =ᶠ[𝓝 w] fun w' =>
        fa l.1.1 (l.1.2.1.recenter D w') (l.1.2.2 + (D.eps i)⁻¹ • w') := by
      filter_upwards [(hU l).mem_nhds hw] with w' hw'
      exact hg l w' hw'
    simp only [dLabelG]
    rw [hev.fderiv_eq]
    exact (dOld_along hζ i fa l.1.1 l.1.2.1 l.1.2.2 w j).symm

/-- **Evaluation at the appended child**: represented family values give context values. -/
theorem ctxAlg_evalChild {P : ℝ → RealChain → Vec 2 → Prop} (k : ℤ)
    (hk : Odd k ∧ IsScheduledIn D i k pc) {c : Gen .fam (i + 1) k} {G : ℝ → RealChain → ℝ}
    (hs : Gen.IsScheduled D c) (hf : Gen.FromSeed 𝒮 c) {fc : GenSort.Sem .fam}
    (hd : Gen.Denotes D bw j₀ c fc)
    (hv : ∀ t ch z, P t ch z → ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 →
      fc t (ch.appendChild D k t z) = G t (ch.appendChild D k t z)) :
    ctxAlg D bw j₀ 𝒮 i pc P (fun l =>
      ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 * G l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2)) :=
  ⟨_, fun _ => rfl, _, ctxRep_evalChild P k hk hs hf hd hv⟩
end

/-! **D6c groundwork: chart jets at the context level, and jets at appended children.**
* `jetRepG_ctx_famMap`, `jetRepG_ctx_famMapInv`: the centered chart map of the context family
  and its inverse have represented context jets of every order (`dOld` of the own-frame letters
  `jac`, `jacInv`; the chart maps do not depend on the final phase).
* `jetRepG_evalChild`: represented family jets on the appended children of the contexts give
  represented context jets of the label functions evaluated at the appended child, times the
  partition weight. -/

section
variable {D : OCData} {bw : ℝ} {j₀ : ℕ} {𝒮 : SeedExports} {i : ℕ} {pc : ℤ}
  {P : ℝ → RealChain → Vec 2 → Prop}

/-- `c * g` differentiates to `c * Dg`, without differentiability. -/
theorem fderiv_const_mul_apply' (c : ℝ) (g : Vec 2 → ℝ) (x v : Vec 2) :
    fderiv ℝ (fun y => c * g y) x v = c * fderiv ℝ g x v := by
  have h := fderiv_const_smul_field (𝕜 := ℝ) (f := g) c
  have e : (fun y => c * g y) = c • g := rfl
  rw [e, h]
  rfl

theorem ctxAlg_famMap_zero (b : Fin 2) :
    ctxAlg D bw j₀ 𝒮 i pc P (fun l => l.1.2.1.famMap D l.1.1 0 b) := by
  have e : (fun l : CtxIdx P => l.1.2.1.famMap D l.1.1 0 b) = fun _ => 0 :=
    funext fun l => by simp [famMap_zero]
  rw [e]
  exact (repAlg_ctxAlg D bw j₀ 𝒮 i pc P).const 0

theorem ctxAlg_famMapInv_zero (hζ : IsFastProfile D.ζ) (b : Fin 2) :
    ctxAlg D bw j₀ 𝒮 i pc P (fun l => l.1.2.1.famMapInv D l.1.1 0 b) := by
  have e : (fun l : CtxIdx P => l.1.2.1.famMapInv D l.1.1 0 b) = fun _ => 0 :=
    funext fun l => by simp [famMapInv_zero hζ]
  rw [e]
  exact (repAlg_ctxAlg D bw j₀ 𝒮 i pc P).const 0

/-- **Context jets of the centered chart map.** -/
theorem jetRepG_ctx_famMap (hζ : IsFastProfile D.ζ) (hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted) :
    ∀ (r : ℕ) (b : Fin 2), JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r
      (fun l x => l.1.2.1.famMap D l.1.1 x b)
  | 0, b => ctxAlg_famMap_zero b
  | r + 1, b => ⟨ctxAlg_famMap_zero b, fun j =>
      jetRepG_covariant_ctx hζ r (a := Gen.geo (i := i) (p := pc) .own (.jac b j))
        (U := fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.mem_univ _) (.geoOwn _)
        (.geo _ _) (.geo _ _) fun l w _ => by
          simp only [dLabelG]
          rw [dLabel_famMap hζ l.1.2.1 (hW l) l.1.1 b j w]
          rfl⟩

/-- **Context jets of the inverse centered chart map.** -/
theorem jetRepG_ctx_famMapInv (hζ : IsFastProfile D.ζ) (hW : ∀ l : CtxIdx P, l.1.2.1.WellSlotted) :
    ∀ (r : ℕ) (b : Fin 2), JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r
      (fun l x => l.1.2.1.famMapInv D l.1.1 x b)
  | 0, b => ctxAlg_famMapInv_zero hζ b
  | r + 1, b => ⟨ctxAlg_famMapInv_zero hζ b, fun j => by
      have hG : JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r
          (fun l w => ((l.1.2.1.recenter D w).famJac D l.1.1)⁻¹ b j) :=
        jetRepG_covariant_ctx hζ r (a := Gen.geo (i := i) (p := pc) .own (.jacInv b j))
          (U := fun _ => Set.univ) (fun _ => isOpen_univ) (fun _ => Set.mem_univ _) (.geoOwn _)
          (.geo _ _) (.geo _ _) fun l w _ => rfl
      have hcomp := JetRepG.comp (repAlg_ctxAlg D bw j₀ 𝒮 i pc P) (r := r)
        (g := fun l w => ((l.1.2.1.recenter D w).famJac D l.1.1)⁻¹ b j)
        (Ψ := fun l x => l.1.2.1.famMapInv D l.1.1 x) (fun l => famMapInv_zero hζ _ _)
        (fun l => (contDiff_famJacInv hζ l.1.2.1 (hW l) l.1.1 b j).of_le
          (by exact_mod_cast le_top))
        (fun l => (contDiff_famMapInv l.1.2.1 l.1.1).of_le (by exact_mod_cast le_top)) hG
        (fun b' => jetRepG_ctx_famMapInv hζ hW r b')
      refine hcomp.congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
      simp only [dLabelG]
      rw [dLabel_famMapInv hζ l.1.2.1 (hW l) l.1.1 b j x]⟩

/-- The appended children of the contexts (with nonzero partition weight) as a family index. -/
def childW (D : OCData) (i : ℕ) (k : ℤ) (P : ℝ → RealChain → Vec 2 → Prop) :
    Set (ℝ × RealChain) :=
  {q | ∃ t ch z, P t ch z ∧ ocCutoff D.α D.q D.Λ (i + 1) k t ≠ 0 ∧
    q = (t, ch.appendChild D k t z)}

/-- **Jets at the appended child.** If `G` has represented family jets of order `r` on the
appended children, then `x ↦ ϖ_{i+1,k}(t) G(t, 𝒜^♮_k, x)` has represented context jets. -/
theorem jetRepG_evalChild (k : ℤ) (hk : Odd k ∧ IsScheduledIn D i k pc) :
    ∀ (r : ℕ) {G : ℝ → RealChain → Vec 2 → ℝ},
      JetRepG (famAlg D bw j₀ 𝒮 (i + 1) k (childW D i k P)) r (fun q y => G q.1.1 q.1.2 y) →
      JetRepG (ctxAlg D bw j₀ 𝒮 i pc P) r (fun l x =>
        ocCutoff D.α D.q D.Λ (i + 1) k l.1.1 * G l.1.1 (l.1.2.1.appendChild D k l.1.1 l.1.2.2) x)
  | 0, G, hG => by
      obtain ⟨c, hs, hf, fc, hd, hv⟩ := famAlg_toFam (G := fun t B => G t B 0) hG
      exact ctxAlg_evalChild (G := fun t B => G t B 0) k hk hs hf hd fun t ch z hP hc =>
        (hv (t, ch.appendChild D k t z) ⟨t, ch, z, hP, hc, rfl⟩).symm
  | r + 1, G, hG => by
      refine ⟨?_, fun j => ?_⟩
      · obtain ⟨c, hs, hf, fc, hd, hv⟩ := famAlg_toFam (G := fun t B => G t B 0) hG.1
        exact ctxAlg_evalChild (G := fun t B => G t B 0) k hk hs hf hd fun t ch z hP hc =>
          (hv (t, ch.appendChild D k t z) ⟨t, ch, z, hP, hc, rfl⟩).symm
      · have h := jetRepG_evalChild k hk r (G := fun t B y => fderiv ℝ (G t B) y (basisVec j))
          (hG.2 j)
        refine h.congr_germ fun l => Filter.Eventually.of_forall fun x => ?_
        simp only [dLabelG]
        exact (fderiv_const_mul_apply' _ _ _ _).symm
end

end AVRegularity.Providers.GenSem
end
