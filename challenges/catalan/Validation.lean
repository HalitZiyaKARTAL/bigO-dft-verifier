import Statement
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.Real.Irrational
import Mathlib.Analysis.PSeries
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Order.Filter.AtTopBot.Basic

/-!
# Validation of `Statement.lean` (not part of the trusted target)

No finite bound has a verified proof here. These checks replace a baseline proof:

* `irrational_of_upperBound`: the target implies irrationality (the Oct 21 ask).
* `bound_nonneg`, `upperBoundFor_mono`: the range and the direction of "smaller is better".
* `rational_not_upperBound`: a rational number never satisfies the inequality, at any exponent.
* `endpoint_mono`, `upperBoundFor_of_endpoint`: a fixed-exponent proof `Endpoint constant e` gives
  `UpperBoundFor constant e`, the form of the Lean claims on the site.
* `summable_series`: the series is summable, so `constant` is the true sum.
* `sqrt_two_upperBound`: a positive control. The same inequality holds for `√2` at exponent
  `2` (a proved case, so the quantifiers are not vacuous), and `√2` fails at the exponent `-1`.
-/

namespace BigOSpeedrun.Catalan

theorem rational_not_endpoint (q : ℚ) (s : ℝ) : ¬ Endpoint (q : ℝ) s := by
  intro h
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 h
  set b : ℕ := q.den * (B + 1) with hb
  have hden : 0 < q.den := q.den_pos
  have hbB : B ≤ b := by
    have : B + 1 ≤ q.den * (B + 1) := Nat.le_mul_of_pos_left _ hden
    omega
  have hbpos : (0 : ℝ) < b := by
    have : 0 < b := Nat.mul_pos hden (Nat.succ_pos B)
    exact_mod_cast this
  have h1 := hB b hbB (q.num * (B + 1))
  have h2 : (q : ℝ) - ((q.num * (B + 1) : ℤ) : ℝ) / (b : ℝ) = 0 := by
    have hq : (q : ℝ) = (q.num : ℝ) / (q.den : ℝ) := by
      exact_mod_cast (Rat.num_div_den q).symm
    have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast hden.ne'
    have hB1 : ((B : ℝ) + 1) ≠ 0 := by positivity
    rw [hq, hb]
    push_cast
    field_simp
    ring
  rw [h2, abs_zero] at h1
  exact absurd h1 (not_lt.2 (Real.rpow_nonneg hbpos.le _))

theorem irrational_of_upperBound {x r : ℝ} (h : UpperBoundFor x r) : Irrational x := by
  rintro ⟨q, rfl⟩
  exact rational_not_endpoint q (|r| + 1) (h _ (by linarith [le_abs_self r]))

theorem rational_not_upperBound (q : ℚ) (r : ℝ) : ¬ UpperBoundFor (q : ℝ) r :=
  fun h => irrational_of_upperBound h ⟨q, rfl⟩

theorem upperBoundFor_mono {x r r' : ℝ} (h : UpperBoundFor x r) (hr : r ≤ r') :
    UpperBoundFor x r' :=
  fun s hs => h s (lt_of_le_of_lt hr hs)

theorem bound_nonneg {r : ℚ} (h : Bound r) : 0 ≤ r := h.1

theorem not_bound_neg {r : ℚ} (hr : r < 0) : ¬ Bound r := fun h => absurd h.1 (not_le.2 hr)

/-- A lower bound `1 / (4 b²)` for all fractions gives exponent `2`. -/
theorem upperBoundFor_two_of_lower {x : ℝ}
    (h : ∀ b : ℕ, 1 ≤ b → ∀ a : ℤ, 1 / (4 * (b : ℝ) ^ 2) ≤ |x - (a : ℝ) / (b : ℝ)|) :
    UpperBoundFor x 2 := by
  intro s hs
  have ht : Filter.Tendsto (fun b : ℕ => (b : ℝ) ^ (2 - s)) Filter.atTop (nhds 0) := by
    have := tendsto_rpow_neg_atTop (y := s - 2) (by linarith)
    exact (this.comp tendsto_natCast_atTop_atTop).congr (fun b => by simp [neg_sub])
  have hev : ∀ᶠ b : ℕ in Filter.atTop, (b : ℝ) ^ (2 - s) < 1 / 4 :=
    ht.eventually (gt_mem_nhds (by norm_num))
  filter_upwards [hev, Filter.eventually_ge_atTop 1] with b hb hb1 a
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb1
  have key : (b : ℝ) ^ (-s) < 1 / (4 * (b : ℝ) ^ 2) := by
    have e : (b : ℝ) ^ (-s) * ((b : ℝ) ^ 2) = (b : ℝ) ^ (2 - s) := by
      rw [← Real.rpow_natCast, ← Real.rpow_add hbpos]; push_cast; ring_nf
    rw [lt_div_iff₀ (by positivity)]
    nlinarith [e, hb]
  exact lt_of_lt_of_le key (h b hb1 a)

theorem sqrt_two_upperBound : UpperBoundFor (Real.sqrt 2) 2 := by
  apply upperBoundFor_two_of_lower
  intro b hb a
  have hbpos : (0 : ℝ) < b := by exact_mod_cast hb
  have hs2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hirr : Irrational (Real.sqrt 2) := irrational_sqrt_two
  -- the integer `2 b² - a²` is nonzero
  have hne : (2 * (b : ℤ) ^ 2 - a ^ 2) ≠ 0 := by
    intro h0
    have : (a : ℝ) ^ 2 = 2 * (b : ℝ) ^ 2 := by
      have := congrArg (fun z : ℤ => (z : ℝ)) h0
      push_cast at this; linarith
    have hr : (Real.sqrt 2) = |(a : ℝ)| / b := by
      have h3 : (|(a : ℝ)| / b) ^ 2 = 2 := by
        rw [div_pow, sq_abs, this]; field_simp
      have h4 : 0 ≤ |(a : ℝ)| / b := by positivity
      rw [← h3]; exact Real.sqrt_sq h4
    apply hirr
    refine ⟨(|a| : ℤ) / (b : ℚ), ?_⟩
    rw [hr]; push_cast; simp
  have hge : (1 : ℝ) ≤ |2 * (b : ℝ) ^ 2 - (a : ℝ) ^ 2| := by
    have h : (1 : ℤ) ≤ |2 * (b : ℤ) ^ 2 - a ^ 2| := Int.one_le_abs hne
    have := (Int.cast_le (R := ℝ)).2 h
    simpa [Int.cast_abs] using this
  have hs : Real.sqrt 2 < 3 / 2 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs0 := Real.sqrt_nonneg 2
  set u : ℝ := Real.sqrt 2 - (a : ℝ) / b with hu
  have hprod : 2 * (b : ℝ) ^ 2 - (a : ℝ) ^ 2 = (b : ℝ) ^ 2 * (u * (2 * Real.sqrt 2 - u)) := by
    rw [hu]; field_simp; nlinarith [hs2]
  by_cases hbig : 1 ≤ |u|
  · have : 1 / (4 * (b : ℝ) ^ 2) ≤ 1 := by
      have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb
      rw [div_le_one (by positivity)]; nlinarith
    linarith
  · rw [not_le] at hbig
    have hsum : |2 * Real.sqrt 2 - u| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith [abs_lt.1 hbig]
    have h1 : (1 : ℝ) ≤ (b : ℝ) ^ 2 * (|u| * 4) := by
      calc (1 : ℝ) ≤ |2 * (b : ℝ) ^ 2 - (a : ℝ) ^ 2| := hge
        _ = (b : ℝ) ^ 2 * (|u| * |2 * Real.sqrt 2 - u|) := by
          rw [hprod, abs_mul, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < (b : ℝ) ^ 2)]
        _ ≤ (b : ℝ) ^ 2 * (|u| * 4) := by gcongr
    rw [div_le_iff₀ (by positivity)]
    nlinarith

/-- Negative control: `√2` has no bound at exponent `-1` (here `b^1 < |√2 - a/b|` fails at `a = 0`
for the large `b`). -/
theorem sqrt_two_not_endpoint_neg_one : ¬ Endpoint (Real.sqrt 2) (-1) := by
  intro h
  obtain ⟨B, hB⟩ := Filter.eventually_atTop.1 h
  have h1 := hB (B + 2) (by omega) 0
  have hb : (2 : ℝ) ≤ ((B + 2 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg B : (0 : ℝ) ≤ B)]
  have hs : Real.sqrt 2 < 3 / 2 := by rw [Real.sqrt_lt' (by norm_num)]; norm_num
  simp only [neg_neg, Real.rpow_one, Int.cast_zero, zero_div, sub_zero] at h1
  rw [abs_of_nonneg (Real.sqrt_nonneg 2)] at h1
  linarith

#print axioms irrational_of_upperBound
#print axioms upperBoundFor_mono
#print axioms sqrt_two_upperBound
#print axioms sqrt_two_not_endpoint_neg_one

/-- A larger exponent is weaker, for `b ≥ 1`. -/
theorem endpoint_mono {x s s' : ℝ} (h : Endpoint x s) (hs : s ≤ s') : Endpoint x s' := by
  filter_upwards [h, Filter.eventually_ge_atTop 1] with b hb hb1 a
  have h1 : (1 : ℝ) ≤ b := by exact_mod_cast hb1
  exact lt_of_le_of_lt (Real.rpow_le_rpow_of_exponent_le h1 (by linarith)) (hb a)

/-- Transfer: a fixed-exponent result `Endpoint x r` gives `UpperBoundFor x r`. This is the form of
the existing Lean claims on the site. -/
theorem upperBoundFor_of_endpoint {x r : ℝ} (h : Endpoint x r) : UpperBoundFor x r :=
  fun _ hs => endpoint_mono h hs.le

/-- The series is summable, so `constant` is its sum and not the junk value `0` of `tsum`. -/
theorem summable_series :
    Summable (fun j : ℕ => (-1 : ℝ) ^ j / ((2 * j + 1 : ℕ) : ℝ) ^ 2) := by
  have hg : Summable (fun j : ℕ => 1 / ((j + 1 : ℕ) : ℝ) ^ 2) :=
    (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 one_lt_two)
  refine Summable.of_norm_bounded hg fun j => ?_
  rw [norm_div, norm_pow, norm_neg, norm_one, one_pow, norm_pow, Real.norm_natCast]
  have h1 : (0 : ℝ) < ((j + 1 : ℕ) : ℝ) := by positivity
  have h2 : ((j + 1 : ℕ) : ℝ) ≤ ((2 * j + 1 : ℕ) : ℝ) := by push_cast; linarith [(Nat.cast_nonneg j : (0 : ℝ) ≤ j)]
  exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_left₀ h1.le h2 2)

#print axioms rational_not_upperBound
#print axioms not_bound_neg
#print axioms bound_nonneg
#print axioms endpoint_mono
#print axioms upperBoundFor_of_endpoint
#print axioms summable_series

end BigOSpeedrun.Catalan
