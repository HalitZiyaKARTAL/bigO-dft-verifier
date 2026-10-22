import Submission.Work.BlockAccounting.Moment
-- changed for the head-cut extension (1959540039/1000000000000); see Submission.lean

/-!
# Fifth-order term bound for the moment certificates

`term_le5` is `term_le4` with the fifth-order bound
`exp x ≤ 1 + x + x²/2 + x³/6 + x⁴/24 + x⁵/100` on `[0,1]` (`Real.exp_bound'` with `n = 5`: the remainder is
`x^5 * 6 / (5! * 5) = x^5 / 100`).  Same arguments and conclusion as `term_le4`.
-/

namespace OAI.PowerSaving.BlockAccounting
open Finset

/-- Fifth-order upper bound of `exp` on `[0,1]`. -/
lemma exp_le_quintic (x : ℝ) (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    Real.exp x ≤ 1 + x + x^2/2 + x^3/6 + x^4/24 + x^5*(1/100) := by
  have h := Real.exp_bound' h0 h1 (n := 5) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

lemma rpow_ratio_le5 (r m L ε : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log (m/r) ≤ L) (hx : ε * L ≤ 1) :
    (r/m)^(1-ε) ≤ r/m * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6 + (ε*L)^4/24 + (ε*L)^5*(1/100)) := by
  have hx0 : (0:ℝ) < r/m := div_pos hr hm
  have hlog : Real.log (r/m) = - Real.log (m/r) := by
    rw [← Real.log_inv, inv_div]
  have h1 : (r/m)^(1-ε) = r/m * Real.exp (ε * Real.log (m/r)) := by
    rw [Real.rpow_def_of_pos hx0, hlog,
      show -Real.log (m/r) * (1-ε) = -Real.log (m/r) + ε * Real.log (m/r) by ring,
      Real.exp_add, ← hlog, Real.exp_log hx0]
  rw [h1]
  apply mul_le_mul_of_nonneg_left _ hx0.le
  have h2 : Real.exp (ε * Real.log (m/r)) ≤ Real.exp (ε * L) :=
    Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hL hε)
  exact h2.trans (exp_le_quintic (ε*L) (mul_nonneg hε hL0) hx)

/-- Upper bound for one term of the moment at `z = 1 - ε` (fifth order; drop-in for `term_le4`). -/
lemma term_le5 (m r n : ℕ) (ε L q : ℝ) (hr : 0 < r) (hm : 0 < m) (hε : 0 ≤ ε) (hL0 : 0 ≤ L)
    (hL : Real.log ((m:ℝ)/(r:ℝ)) ≤ L) (hx : ε * L ≤ 1)
    (hq : (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6 + (ε*L)^4/24 + (ε*L)^5*(1/100))) ≤ q) :
    T m (1-ε) r n ≤ q := by
  have hr' : (0:ℝ) < (r:ℝ) := by exact_mod_cast hr
  have hm' : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm
  have h := rpow_ratio_le5 (r:ℝ) (m:ℝ) L ε hr' hm' hε hL0 hL hx
  have h' : T m (1-ε) r n
      ≤ (n:ℝ) * ((r:ℝ)/(m:ℝ) * (1 + ε*L + (ε*L)^2/2 + (ε*L)^3/6 + (ε*L)^4/24 + (ε*L)^5*(1/100))) :=
    mul_le_mul_of_nonneg_left h (by positivity)
  exact h'.trans hq

end OAI.PowerSaving.BlockAccounting

#print axioms OAI.PowerSaving.BlockAccounting.term_le5
