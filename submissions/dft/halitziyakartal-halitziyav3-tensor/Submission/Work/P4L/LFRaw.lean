import Submission.Work.P4L.LFBase
-- changed for the tensor-power extension (26159999/10000000000); see Submission.lean

/-!
# P4-L-fresh RAW (no pad, no split) on the #2979 gauge44 provider: `rawCert_exists`

`P4L.certGen` (generic) with the raw end sets `Dr q` (`|Dr q|` = the residual rank of slot `q`): every helper ends at
the block of its residual rank, the windows are ONE block per owner.  Per gauge copy (`G = |Orth (LC (Fin 8) (Fin 9)
l0)|` copies): live target ranks `TrawLF` = 4:234 5:18 6:144 7:468 8:891 9:1917 25:448 41:224 73:224, paid blocks
`PrawLF` = 1:22005 2:6354 3:2088 4:972 5:162 8:744 16:448 32:224 (literally the tensor route's `TK4F`, `PK4F`).
The instance only proves the one-copy facts `hP_raw` (price) and `hL_raw` (targets); the gauge group is a factor
of `certGen`, never reduced.
No `sorry`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxRecDepth 100000

namespace OAI
namespace PowerSaving
namespace P4L
namespace LF
open Binary Matrix Finset RAM SS CB RF BC GX GF XHostTW P4Ctrl

noncomputable section

/-- the paid blocks of the raw word (per gauge copy). -/
def PrawLF : List (ℕ × ℕ) :=
  [(1, 22005), (2, 6354), (3, 2088), (4, 972), (5, 162), (8, 744), (16, 448), (32, 224)]

/-- the live target ranks of the raw word (per gauge copy). -/
def TrawLF : List (ℕ × ℕ) :=
  [(4, 234), (5, 18), (6, 144), (7, 468), (8, 891), (9, 1917), (25, 448), (41, 224), (73, 224)]

/-- one gauge copy of the raw price: nine calls, the window blocks of the 112 ports, free helper ends. -/
lemma hP_raw (φ : ℕ → ℝ) :
    9 * I1.cost φ + (Fintype.card (Fin 112) : ℝ) * (6 * bcost φ 8 + 4 * bcost φ 16 + 2 * bcost φ 32)
      + 9 * ∑ q, bcost φ ((Dr q).card - (Fintype.card (Fin 9) - (I1.ent q).dim)) = listCost φ PrawLF := by
  rw [cost1]
  simp only [Dr_card, Nat.sub_self, bcost_zero, Finset.sum_const_zero, mul_zero, add_zero, Fintype.card_fin]
  simp only [listCost, PrawLF, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, bcost, Nat.cast_ofNat]
  norm_num
  ring

/-- one gauge copy of the raw targets: 112 main roles per kind, 9 helpers per slot. -/
lemma hL_raw (r : ℕ) :
    ∑ i, Fintype.card (Fin 112) * (if rankM i = r then 1 else 0) + 9 * ∑ q, (if (Dr q).card = r then 1 else 0)
      = BlockAccounting.histFn TrawLF r := by
  simp only [Dr_res, Fintype.card_fin]
  rw [res_sumN (fun x => if x = r then 1 else 0), R8_sum]
  rcases (show r = 4 ∨ r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8 ∨ r = 9 ∨ r = 25 ∨ r = 41 ∨ r = 73 ∨
      (r ≠ 4 ∧ r ≠ 5 ∧ r ≠ 6 ∧ r ≠ 7 ∧ r ≠ 8 ∧ r ≠ 9 ∧ r ≠ 25 ∧ r ≠ 41 ∧ r ≠ 73) by omega) with
    h | h | h | h | h | h | h | h | h | ⟨h4, h5, h6, h7, h8, h9, h25, h41, h73⟩
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · subst h; norm_num [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil]
  · simp [rankM, TrawLF, BlockAccounting.histFn_cons, BlockAccounting.histFn_nil,
      h4, h5, h6, h7, h8, h9, h25, h41, h73, Ne.symm h4, Ne.symm h5, Ne.symm h6, Ne.symm h7, Ne.symm h8,
      Ne.symm h9, Ne.symm h25, Ne.symm h41, Ne.symm h73]

/-- the raw target ranks lie in `[1, 73]`. -/
lemma rank_raw (base : Fin 112 → OBase (Fin 9)) (l' : PLive (Orth (LC (Fin 8) (Fin 9) l0)) (Fin 112) (Fin 408)) :
    1 ≤ (rawTz base l0 Dr l').1 ∧ (rawTz base l0 Dr l').1 ≤ 73 := by
  rcases l' with ⟨g, i, t⟩ | ⟨g, k, q⟩
  · rw [rawTz_main base l0 (Fintype.card_fin 9) Dr g i t]
    cases i <;> simp [rankM]
  · rw [rawTz_fresh base l0 Dr g k q, Dr_res q]
    have := res_bounds q
    omega

/-- **The raw P4-L-fresh certificate** (no pad, no split): `G` copies of the raw unit, in the shape the tensor route
takes (targets `G * TrawLF`, paid blocks `G * PrawLF`). -/
theorem rawCert_exists : ∃ (α ρ σ : Type) (_ : Fintype α) (_ : DecidableEq α) (_ : Fintype ρ)
    (_ : DecidableEq ρ) (_ : Fintype σ) (_ : DecidableEq σ),
    ∃ (e : σ → ρ) (tr : σ → ℕ) (tz : ∀ l, Fin (tr l) → Space α) (wd : GWord α ρ) (G : ℕ),
      Function.Injective e ∧ (∀ l, LinearIndependent F (tz l)) ∧ wd.Proper (Fintype.card α) ∧
      MX.GLiveKernelM e (fun l => blockMat (tz l)) wd ∧
      1 ≤ G ∧ Fintype.card α = 73 ∧
      (∀ l, 1 ≤ tr l ∧ tr l ≤ 73) ∧
      (∀ r, (Finset.univ.filter fun l => tr l = r).card = G * BlockAccounting.histFn TrawLF r) ∧
      (∀ r, wd.hist r = G * BlockAccounting.histFn PrawLF r) := by
  obtain ⟨base, hbase⟩ := base_exists
  obtain ⟨wd, hP, hk, hh, hc⟩ := certGen (I := I1) (base := base) (l := l0) (hbase := hbase)
    (hH := Fintype.card_fin 9) (hOk := hOk1 l0) (C := Fin 99) Dr (fun q => (Dr_card q).ge)
    (fun q => by rw [Dr_card q, Nat.sub_self, card_LC0]; norm_num) PrawLF TrawLF hP_raw hL_raw
  refine ⟨LC (Fin 8) (Fin 9) l0, PRole (Orth (LC (Fin 8) (Fin 9) l0)) (Fin 112) (Fin 408) (Fin 99),
    PLive (Orth (LC (Fin 8) (Fin 9) l0)) (Fin 112) (Fin 408), _, _, _, _, _, inferInstance, Sum.inl,
    fun l' => (rawTz base l0 Dr l').1, fun l' => (rawTz base l0 Dr l').2, wd, _, Sum.inl_injective,
    fun l' => rawTz_indep base l0 Dr l', hP, hk, ?_, card_LC0, rank_raw base, hc, hh⟩
  exact Orth.card_pos

end
end LF
end P4L
end PowerSaving
end OAI

#print axioms OAI.PowerSaving.P4L.LF.rawCert_exists
