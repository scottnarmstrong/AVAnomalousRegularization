-- Copyright (c) 2026 Scott Armstrong and Vlad Vicol.
-- Released under Apache 2.0 license.
module

public import AVRegularity.EntryTerminal.Assembly.Route.Ingredients

/-! A terminal reserve plan meets arbitrary finite order and seed constant floors. The plan fixes
the skeleton `k₀` of the seed constants (the envelope constants at `0`), then raises `C_a`, `C_m`
above the floors read at `k₀`; the skeleton of the result is `k₀` (`seedSkeleton`). -/

@[expose] public noncomputable section

open AVenhance

namespace AVRegularity.EntryTerminal.Route

/-- Choose the orders and producer allocation before the weak families are supplied. -/
theorem plan : PlanStatement := by
  intro X A hA Kmin F
  let Lt := max A.L0w A.LpT
  let Kw := max Kmin (Lt + A.DW + max (A.Lw + 5) A.k₀)
  let nW : ℕ+ := ⟨max Lt (max (max A.LpT (max A.LoT A.LfT)) (max A.Lpr (max A.Lc A.Lf))) + 1,
    Nat.zero_lt_succ _⟩
  let G0 := max 1 A.stepCount + A.r0 + A.Dt
  let K := max Kmin A.Kres
  let k0 : InvConsts :=
    { c₀ := min 1 A.c₀max
      cr := 1
      Γk := F.Γk nW
      Cwid := F.Cwid nW
      σf := ocDelta X.α X.q
      lamC := A.lamE
      Ca := 0
      mEnv := 0
      Cm := fun _ => 0
      cker := F.cker nW
      Kan := K
      Lan := K
      Jm := K
      Ks := K
      Lker := max A.Lpr (max A.Lc A.Lf)
      Lstar := succLstar A.Kres G0 A.H A.J A.N A.p
      G0 := G0
      Hprod := G0 + A.H + 1 }
  let kS : InvConsts :=
    { k0 with
      Ca := max (F.Ca nW) (F.CaO nW k0)
      Cm := fun j => max (F.Cm nW j) (F.CmO nW k0 j) }
  have hfloor : Lt + A.DW + max (A.Lw + 5) A.k₀ ≤ Kw := le_max_right _ _
  have hk : A.k₀ ≤ Kw := ((le_max_right _ _).trans (Nat.le_add_left _ _)).trans hfloor
  have hL : A.Lw + 5 ≤ Kw := ((le_max_left _ _).trans (Nat.le_add_left _ _)).trans hfloor
  have hn : Lt + 1 ≤ 2 * (nW : ℕ) := by
    simp only [nW, PNat.mk_coe]
    omega
  have horders : IsTerminalKernelOrders nW A.LoT A.LfT A.LpT A.Lpr A.Lc A.Lf := by
    unfold IsTerminalKernelOrders
    simp only [nW, PNat.mk_coe]
    constructor <;> omega
  have halloc : IsSeedAllocation kS A.r0 A.Dt A.H A.J A.N A.p A.Kres A.Lpr A.Lc A.Lf := by
    refine ⟨le_rfl, le_max_right _ _, le_max_right _ _, le_max_right _ _, le_max_right _ _,
      le_rfl, ?_, ?_, rfl, le_rfl, ?_⟩
    · intro g
      change succSchedR A.r0 A.J g ≤ succSchedR 0 A.J (G0 + g)
      rw [succSchedR_shift]
      exact succSchedR_mono A.J ((by dsimp only [G0]; omega : A.r0 ≤ G0).trans
        (le_succSchedR 0 A.J G0)) g
    · intro g
      change succSchedD A.Dt A.N A.p g ≤ succSchedD 2 A.N A.p (G0 + g)
      rw [succSchedD_eq, succSchedD_eq, Nat.add_mul]
      have hd : A.Dt ≤ G0 := by dsimp only [G0]; omega
      have hm : G0 ≤ G0 * (2 * A.N + 4 * A.p + 4) :=
        Nat.le_mul_of_pos_right _ (by omega)
      omega
    · change (0 : ℝ) < 1 / (((G0 + A.H + 1 : ℕ) : ℝ) + 1)
      positivity
  refine ⟨Kw, Lt, nW, hk, hL, 1, kS, le_max_left _ _, le_max_right _ _, hn, horders,
    zero_lt_one, rfl, rfl, lt_min zero_lt_one hA.1, le_rfl, le_rfl, rfl, rfl, halloc, le_rfl,
    le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, le_max_left _ _, ?_, ?_,
    rfl, rfl, rfl, rfl, hfloor⟩
  · change max 1 A.stepCount ≤ G0
    dsimp only [G0]
    omega
  · exact ⟨fun _ => le_rfl, le_rfl, le_rfl, le_max_left _ _, fun _ => le_max_left _ _,
      le_max_right _ _, fun _ => le_max_right _ _⟩

end AVRegularity.EntryTerminal.Route
